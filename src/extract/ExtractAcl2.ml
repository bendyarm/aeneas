(** ACL2 backend: prints the pure AST as ACL2 s-expressions (v0).

    Design (see the ACL2 backend plan §3.2): FTY tagsums/defprods for ADTs, the
    rust-primitives book's [result]/[error]/b* conventions for the error monad,
    fuel for recursion. Unsupported constructs raise [CFailure] and the
    declaration is skipped with a comment — never mistranslated.

    This deliberately bypasses the [ExtractBase] formatter machinery: sexp
    output needs no precedence or indentation-sensitivity, and v0 keeps its own
    (simple, deterministic) name mangling. *)

open Pure
open PureUtils
open TranslateCore
open Errors
module F = Format

let log = Logging.extract_log

(* ---------------------------------------------------------------- names *)

(* demo::mul2_add1 -> demo-mul2-add1 (lowercase; ACL2 reads case-insensitively) *)
let mangle_string (s : string) : string =
  String.concat ""
    (List.map
       (fun c ->
         match c with
         | 'A' .. 'Z' -> String.make 1 (Char.lowercase_ascii c)
         | 'a' .. 'z' | '0' .. '9' -> String.make 1 c
         | _ -> "-")
       (List.init (String.length s) (String.get s)))

(* Collapse consecutive dashes introduced by e.g. "::" *)
let collapse_dashes (s : string) : string =
  let buf = Buffer.create (String.length s) in
  let prev_dash = ref false in
  String.iter
    (fun c ->
      if c = '-' then (
        if not !prev_dash then Buffer.add_char buf '-';
        prev_dash := true)
      else (
        prev_dash := false;
        Buffer.add_char buf c))
    s;
  Buffer.contents buf

let mangle_name (trans_ctx : trans_ctx) (n : Types.name) : string =
  collapse_dashes (mangle_string (name_to_string trans_ctx n))

let int_ty_name (int_ty : Values.integer_type) : string =
  match int_ty with
  | Values.Signed Values.Isize -> "isize"
  | Values.Signed Values.I8 -> "i8"
  | Values.Signed Values.I16 -> "i16"
  | Values.Signed Values.I32 -> "i32"
  | Values.Signed Values.I64 -> "i64"
  | Values.Signed Values.I128 -> "i128"
  | Values.Unsigned Values.Usize -> "usize"
  | Values.Unsigned Values.U8 -> "u8"
  | Values.Unsigned Values.U16 -> "u16"
  | Values.Unsigned Values.U32 -> "u32"
  | Values.Unsigned Values.U64 -> "u64"
  | Values.Unsigned Values.U128 -> "u128"

(* ------------------------------------------------------------------ ctx *)

(* A mutable-borrow backward closure we have delegated to data: the second
   component of an [index_mut]/[array_to_slice_mut] pair, keyed by the
   (globally unique) name of the variable it was bound to.  Applying it is
   printed as the corresponding write-back; any other use of the variable
   yields an unbound ACL2 variable, which fails certification loudly (never
   a silent mistranslation). *)
type closure_kind =
  | CloRangeBack of { arr : string; lo : string; hi : string }
      (** [&mut a[lo..hi]]: applying to sub prints
          (vec-update-range arr lo hi sub) *)
  | CloElemBack of { arr : string; idx : string }
      (** [&mut a[i]] (single element): applying to v prints
          (update-nth idx v arr) *)
  | CloIdentityBack
      (** [array_to_slice_mut]: the whole array IS the slice on the list
          model, so the write-back is the identity *)

type actx = {
  trans_ctx : trans_ctx;
  fun_names : string FunDeclId.Map.t;
  opaque_funs : FunDeclId.Set.t;
  global_names : string GlobalDeclId.Map.t;
  trans_funs : pure_fun_translation FunDeclId.Map.t;
  type_names : string TypeDeclId.Map.t;
  types : Pure.type_decl TypeDeclId.Map.t;
  mutable gensym : int;
  mutable skipped : (FunDeclId.id * (LoopId.id * bool) option) list;
      (** Functions whose emission failed: calls to them must fail too *)
  closures : (string, closure_kind) Hashtbl.t;
      (** live backward closures, keyed by bound-variable name *)
  pending_pairs : (string, closure_kind * string) Hashtbl.t;
      (** (subslice, backward) pair variables awaiting destructuring: maps
          the pair variable's name to the backward kind and the name the
          forward value was bound to *)
}

(* Variable environment: a stack of binder groups (for BVar de Bruijn
   lookups: scope = index in the stack, id = index in the group), plus a
   map for free variables. Names are ACL2-safe (sanitized basenames);
   shadowing is fine because the emitted b*/let nesting mirrors the
   binder structure exactly. *)
type venv = { bvars : string BVarId.Map.t list; fvars : string FVarId.Map.t }

let empty_venv : venv = { bvars = []; fvars = FVarId.Map.empty }

let clean_var_name (basename : string option) (i : int) : string =
  let s =
    match basename with
    | Some s ->
        let s = collapse_dashes (mangle_string s) in
        if s = "" || s = "-" then "v" ^ string_of_int i else s
    | None -> "v" ^ string_of_int i
  in
  (* Names that cannot be ACL2 variables: constant syntax (t/nil) and the
     state stobj *)
  match s with
  | "t" | "nil" | "state" -> s ^ "-var"
  | _ -> s

(* Bind the variables of a list of patterns as ONE binder group (this is
   the convention for function inputs, let-bindings and match branches:
   indices are assigned by depth-first search). Returns the names in DFS
   order and, separately, one "surface name" per top-level pattern
   ("&" for ignored patterns). *)
let bind_tpats ?(toplevel = false) (ctx : actx) (env : venv) (pats : tpat list)
    : venv * string list =
  let idx = ref 0 in
  let group = ref BVarId.Map.empty in
  let names = ref [] in
  let rec walk (p : tpat) : string =
    match p.pat with
    | PBound (v, _) ->
        let i = !idx in
        idx := i + 1;
        let name =
          if toplevel then
            (* Function formals are a single binder group: per-index clean
               names, distinct within the group. Kept readable for proofs. *)
            let n = clean_var_name v.basename i in
            if List.mem n !names then n ^ "-" ^ string_of_int i else n
          else (
            (* Internal bindings must be globally unique within the
               function: nested single-binding b* groups otherwise reuse a
               name and an expression referencing two distinct earlier
               temporaries would collapse them (e.g. (xor v0 v0)). *)
            ctx.gensym <- ctx.gensym + 1;
            let uniq = ctx.gensym in
            clean_var_name v.basename uniq ^ "_" ^ string_of_int uniq)
        in
        group := BVarId.Map.add (BVarId.of_int i) name !group;
        names := name :: !names;
        name
    | POpen (_, _) ->
        (* We only print closed bodies *)
        raise (Failure "ExtractAcl2: unexpected open binder")
    | PIgnored -> "&"
    | PConstant _ -> "&"
    | PAdt { fields; _ } ->
        List.iter (fun f -> ignore (walk f)) fields;
        "&"
  in
  let surface = List.map walk pats in
  ({ env with bvars = !group :: env.bvars }, surface)

let venv_bvar (env : venv) (v : bvar) : string =
  match Collections.List.nth_opt env.bvars v.scope with
  | None -> raise (Failure "ExtractAcl2: unbound bvar scope")
  | Some names -> (
      match BVarId.Map.find_opt v.id names with
      | None -> raise (Failure "ExtractAcl2: unbound bvar id")
      | Some name -> name)

let fresh_tmp (ctx : actx) : string =
  ctx.gensym <- ctx.gensym + 1;
  "acl2tmp" ^ string_of_int ctx.gensym

(* Known opaque std functions we map to primitives-book operations.
   Matches the mangled name; returns the ACL2 primitive name (a function
   returning result). Extend as coverage grows -- the systematic home for
   this is ExtractBuiltin, but a table here keeps v0 self-contained. *)
let std_fun_mapping (mangled : string) : string option =
  let ok_types = [ "u8"; "u16"; "u32"; "u64"; "u128"; "usize" ] in
  let try_wrap op =
    List.find_map
      (fun t ->
        if mangled = "core-num-" ^ t ^ "-wrapping-" ^ op then
          Some (t ^ "-wrapping-" ^ op)
        else None)
      ok_types
  in
  let try_rot dir =
    List.find_map
      (fun t ->
        if mangled = "core-num-" ^ t ^ "-rotate-" ^ dir then
          Some (t ^ "-rotate-" ^ dir)
        else None)
      ok_types
  in
  let has sub =
    try
      ignore (Str.search_forward (Str.regexp_string sub) mangled 0);
      true
    with Not_found -> false
  in
  let starts p =
    String.length mangled >= String.length p
    && String.sub mangled 0 (String.length p) = p
  in
  match List.find_map try_wrap [ "add"; "sub"; "mul" ] with
  | Some s -> Some s
  | None -> (
      match List.find_map try_rot [ "left"; "right" ] with
      | Some s -> Some s
      | None ->
      (* alloc::vec::Vec ops. The mangled name carries an [alloc-vec]
         prefix in both the generic and monomorphized forms; we key off
         that plus the method substring. v0 requires --monomorphize for
         Vec (it resolves the SliceIndex trait plumbing). *)
      if starts "alloc-vec" && has "-push" then Some "vec-push"
      else if starts "alloc-vec" && has "-insert" then Some "vec-insert"
      else if starts "alloc-vec" && has "-new" then Some "vec-new"
      else if starts "alloc-vec" && has "-with-capacity" then Some "vec-new"
      else if starts "alloc-vec" && has "-len" then Some "vec-len"
      else if starts "core-slice" && has "-len" then Some "vec-len"
      else if starts "alloc-vec" && has "-index" then Some "array-index"
      (* LE byte plumbing (roadmap item 6) *)
      else if mangled = "core-num-u32-from-le-bytes" then
        Some "u32-from-le-bytes"
      else if mangled = "core-num-u32-to-le-bytes" then Some "u32-to-le-bytes"
      else if starts "core-slice" && has "-copy-from-slice" then
        Some "slice-copy-from-slice"
      else None)

(* The monomorphized Range<_> iterator methods a `for i in a..b` loop lowers
   to. They are opaque in core (their real bodies pull in ub_checks /
   unchecked_add), so instead of extracting the body we synthesize a
   first-order one (see [synth_range_iter_body]): `next` is the fused
   Range -> (Option, Range), `into_iter` is the identity. We key off the
   mangled monomorphic name. *)
let str_contains (name : string) (sub : string) : bool =
  try
    ignore (Str.search_forward (Str.regexp_string sub) name 0);
    true
  with Not_found -> false

let is_range_iter_next (name : string) : bool =
  str_contains name "iterator-iterator-for-core-ops-range-range"
  && str_contains name "-next-"

let is_range_iter_into_iter (name : string) : bool =
  str_contains name "intoiterator-for-core-ops-range-range"
  && str_contains name "into-iter"

(* `(a..b).rev()` additionally needs: Range's DoubleEndedIterator::next_back
   (the reverse advance -- opaque in core for the same ub_checks reason as
   `next`) and the blanket `IntoIterator for Rev<_>` into_iter (identity).
   `Iterator::rev` and `Rev::next` have real bodies and translate as-is. *)
let is_range_iter_next_back (name : string) : bool =
  str_contains name "doubleendediterator-for-core-ops-range-range"
  && str_contains name "next-back"

let is_rev_into_iter (name : string) : bool =
  str_contains name "intoiterator-for-core-iter-adapters-rev-rev"
  && str_contains name "into-iter"

(* Fallback syntheses for when the build environment lacks the Miri-built
   sysroot: without it, rustc's default sysroot carries no MIR for
   non-lang-item core items, so `Iterator::rev` and `Rev::next` arrive
   opaque (with the sysroot they have real bodies, which win: synthesis
   only fires for body-less declarations).  Rev<Range> is a newtype and
   ACL2 is untyped, so the fallback represents a Rev value AS its inner
   range: `rev` is the identity and `Rev::next` is the reverse advance on
   the range itself.  Both syntheses fire together or not at all (opacity
   is a property of the sysroot, not the item). *)
let is_iter_rev_ctor (name : string) : bool =
  str_contains name "iterator-iterator-rev-core-ops-range-range"

let is_rev_next (name : string) : bool =
  str_contains name "iterator-iterator-for-core-iter-adapters-rev-rev"
  && str_contains name "-next-"

(* Monomorphized subslice-borrow ops (de-vendoring roadmap item 7):
   <[T; N] as Index<RangeX<usize>>>::index and the IndexMut counterpart
   (array and slice impls; RangeX is Range, RangeTo or RangeFrom -- the
   substring "core-ops-range-range" is a prefix of all three mangled type
   names).  Shared reads synthesize to first-order defuns over
   [vec-index-range]; the mutable ones return (subslice, backward) pairs
   and are recognized at their let sites (see [let_to_acl2]). *)
let is_subslice_index_shared (name : string) : bool =
  str_contains name "-core-ops-index-index-core-ops-range-range"

let is_subslice_index_mut (name : string) : bool =
  str_contains name "-core-ops-index-indexmut-core-ops-range-range"

(* single-element &mut a[i] as a monomorphized IndexMut<usize> decl *)
let is_elem_index_mut (name : string) : bool =
  str_contains name "-core-ops-index-indexmut-usize-"

(* StepBy<Range<usize>> (the key schedule's (8..72).step_by(32) fold):
   ctor, blanket into_iter (identity) and next, all synthesized against our
   own defprod model of the (opaque) StepBy struct. *)
let is_stepby_ctor (name : string) : bool =
  str_contains name "iterator-iterator-step-by-core-ops-range-range"

let is_stepby_into_iter (name : string) : bool =
  str_contains name "intoiterator-for-core-iter-adapters-step-by-stepby"
  && str_contains name "into-iter"

let is_stepby_next (name : string) : bool =
  str_contains name "iterator-iterator-for-core-iter-adapters-step-by-stepby"
  && str_contains name "-next-"

(* LE byte plumbing (de-vendoring roadmap item 6): `slice.try_into()` to a
   fixed-size byte array (returning core's own Result) and `Result::unwrap`
   on it.  Both synthesize to first-order bodies against the crate-local
   monomorphic Result tagsum. *)
let is_try_into_array (name : string) : bool =
  str_contains name "-core-convert-tryinto-" && str_contains name "-try-into-"

let is_result_unwrap (name : string) : bool =
  String.length name >= 12
  && String.sub name 0 12 = "core-result-"
  && str_contains name "-unwrap-"

let is_range_iter_method (name : string) : bool =
  is_range_iter_next name || is_range_iter_into_iter name
  || is_range_iter_next_back name
  || is_rev_into_iter name || is_iter_rev_ctor name || is_rev_next name
  || is_subslice_index_shared name
  || is_try_into_array name || is_result_unwrap name
  || is_stepby_ctor name || is_stepby_into_iter name || is_stepby_next name

let fun_name (span : Meta.span) (ctx : actx) (id : FunDeclId.id) : string =
  match FunDeclId.Map.find_opt id ctx.fun_names with
  (* Synthesized Range iterator methods resolve even though they are opaque. *)
  | Some s when is_range_iter_method s -> s
  | _ ->
      if FunDeclId.Set.mem id ctx.opaque_funs then
        [%craise] span
          "ACL2: call to an opaque/std function with no ACL2 mapping yet"
      else (
        match FunDeclId.Map.find_opt id ctx.fun_names with
        | Some s -> s
        | None ->
            [%craise] span "ACL2: call to a function without a name (builtin?)")

let type_name (span : Meta.span) (ctx : actx) (id : TypeDeclId.id) : string =
  match TypeDeclId.Map.find_opt id ctx.type_names with
  | Some s -> s
  | None -> [%craise] span "ACL2: reference to an unknown type"

let variant_kw (v : Pure.variant) : string =
  ":" ^ collapse_dashes (mangle_string v.variant_name)

let field_names (fields : Pure.field list) : string list =
  List.mapi
    (fun i (f : Pure.field) ->
      match f.field_name with
      | Some n -> collapse_dashes (mangle_string n)
      | None -> "f" ^ string_of_int i)
    fields

(* ---------------------------------------------------------------- exprs *)

let literal_to_acl2 (span : Meta.span) (l : Pure.literal) : string =
  match l with
  | VScalar (Values.UnsignedScalar (_, v)) -> Z.to_string v
  | VScalar (Values.SignedScalar (_, v)) -> Z.to_string v
  | VBool true -> "t"
  | VBool false -> "nil"
  | VPureNat v | VPureInt v -> Z.to_string v
  | _ -> [%craise] span "ACL2: unsupported literal (char/str/float)"

let binop_to_acl2 (span : Meta.span) (b : binop) : string =
  match b with
  | Add (Expressions.OPanic, it) -> int_ty_name it ^ "-add"
  | Sub (Expressions.OPanic, it) -> int_ty_name it ^ "-sub"
  | Mul (Expressions.OPanic, it) -> int_ty_name it ^ "-mul"
  | Div (Expressions.OPanic, it) -> int_ty_name it ^ "-div"
  | Rem (Expressions.OPanic, it) -> int_ty_name it ^ "-rem"
  | Lt _ -> "<"
  | Le _ -> "<="
  | Gt _ -> ">"
  | Ge _ -> ">="
  | Eq _ -> "equal"
  | Ne _ -> "acl2::nequal" (* printed specially below *)
  | BitXor it -> int_ty_name it ^ "-xor"
  | BitAnd it -> int_ty_name it ^ "-and"
  | BitOr it -> int_ty_name it ^ "-or"
  | Shl (Expressions.OPanic, it, _) -> int_ty_name it ^ "-shl"
  | Shr (Expressions.OPanic, it, _) -> int_ty_name it ^ "-shr"
  | _ -> [%craise] span "ACL2: unsupported binop (wrapping/checked-shift)"

(* An application in sexp form *)
let sexp (parts : string list) : string = "(" ^ String.concat " " parts ^ ")"

let rec texpr_to_acl2 (span : Meta.span) (ctx : actx) (env : venv) (e : texpr) :
    string =
  match e.e with
  | FVar id -> (
      match FVarId.Map.find_opt id env.fvars with
      | Some n -> n
      | None -> [%craise] span "ACL2: unbound free variable")
  | BVar v -> venv_bvar env v
  | CVar _ -> [%craise] span "ACL2: const generics not supported yet"
  | Const l -> literal_to_acl2 span l
  | App _ -> app_to_acl2 span ctx env e
  | Lambda _ ->
      [%craise] span
        "ACL2: lambda in output (backward function or closure); not supported \
         in v0 -- see the defunctionalization plan"
  | Qualif _ -> app_to_acl2 span ctx env e
  | Let (monadic, pat, e1, e2) -> let_to_acl2 span ctx env monadic pat e1 e2
  | Switch (scrut, If (e_then, e_else)) ->
      sexp
        [
          "if";
          texpr_to_acl2 span ctx env scrut;
          texpr_to_acl2 span ctx env e_then;
          texpr_to_acl2 span ctx env e_else;
        ]
  | Switch (scrut, Match branches) -> match_to_acl2 span ctx env scrut branches
  | Loop _ -> [%craise] span "ACL2: Loop node in output; use -loops-to-rec"
  | StructUpdate su -> struct_update_to_acl2 span ctx env su
  | Meta (_, e1) -> texpr_to_acl2 span ctx env e1
  | EError (_, msg) -> [%craise] span ("ACL2: error node: " ^ msg)

and app_to_acl2 (span : Meta.span) (ctx : actx) (env : venv) (e : texpr) :
    string =
  let head, args = destruct_apps e in
  let args_s = List.map (texpr_to_acl2 span ctx env) args in
  match head.e with
  | Qualif q -> qualif_app_to_acl2 span ctx env q args args_s
  | FVar _ | BVar _ -> (
      (* Application of a locally-bound function value.  The ONLY such
         values we accept are the backward closures of mutable subslice /
         array-to-slice borrows, recorded at their let sites: applying one
         prints the corresponding write-back. *)
      let hname =
        match head.e with
        | FVar id -> (
            match FVarId.Map.find_opt id env.fvars with
            | Some n -> n
            | None -> [%craise] span "ACL2: unbound free variable")
        | BVar v -> venv_bvar env v
        | _ -> [%craise] span "ACL2: impossible application head"
      in
      match (Hashtbl.find_opt ctx.closures hname, args_s) with
      | Some (CloRangeBack { arr; lo; hi }), [ x ] ->
          sexp [ "vec-update-range"; arr; lo; hi; x ]
      | Some (CloElemBack { arr; idx }), [ x ] ->
          sexp [ "update-nth"; idx; x; arr ]
      | Some CloIdentityBack, [ x ] -> x
      | _ ->
          [%craise] span "ACL2: application of a function-typed variable (HO)")
  | _ -> [%craise] span "ACL2: unsupported application head"

and qualif_app_to_acl2 (span : Meta.span) (ctx : actx) (_env : venv)
    (q : qualif) (args : texpr list) (args_s : string list) : string =
  match q.id with
  | FunOrOp (Fun (FromLlbc (FunId (FRegular id), lp))) -> (
      (* opaque std function with a known primitive mapping wins first *)
      match
        Option.bind (FunDeclId.Map.find_opt id ctx.fun_names) std_fun_mapping
      with
      | Some prim -> sexp (prim :: args_s)
      | None ->
          if List.mem (id, lp) ctx.skipped then
            [%craise] span "ACL2: call to a function that was itself skipped"
          else
            let base = fun_name span ctx id in
            let name =
              match lp with
              | None -> base
              | Some (lp_id, is_body) ->
                  base ^ "-loop" ^ LoopId.to_string lp_id
                  ^ if is_body then "-body" else ""
            in
            sexp (name :: args_s))
  | FunOrOp (Fun (FromLlbc (FunId (FBuiltin bid), _))) -> (
      match bid with
      | Types.BoxNew -> (
          (* Box is transparent in the pure model *)
          match args_s with
          | [ a ] -> a
          | _ -> [%craise] span "ACL2: ill-formed Box::new")
      | Types.ArrayToSliceShared -> (
          (* identity on the list model *)
          match args_s with
          | [ a ] -> a
          | _ -> [%craise] span "ACL2: ill-formed array-to-slice")
      | Types.ArrayToSliceMut ->
          (* returns a (slice, backward) pair: only meaningful at a
             pair-destructuring let, which [mut_borrow_let] intercepts *)
          [%craise] span
            "ACL2: array_to_slice_mut outside a pair-destructuring let"
      | Types.ArrayRepeat -> (
          (* [x; N]: N is a const generic. After --monomorphize it is a
             concrete literal, so we can build (array-repeat N x). *)
          match (q.generics.const_generics, args_s) with
          | [ CgValue n_lit ], [ x ] ->
              sexp [ "array-repeat"; literal_to_acl2 span n_lit; x ]
          | _ ->
              [%craise] span
                "ACL2: array-repeat needs a literal length and one element")
      | Types.Index { is_range = false; mutability = Types.RShared; _ } ->
          sexp ("array-index" :: args_s)
      | Types.Index { is_range = false; mutability = Types.RMut; _ } ->
          (* mutable single-element index: micro-passes usually turn the
             write side into UpdateAtIndex; a surviving &mut index means a
             backward function, which we reject *)
          [%craise] span
            "ACL2: &mut index survived to extraction (backward function)"
      | Types.Index { is_range = true; mutability = Types.RShared; _ } -> (
          (* a[r] shared: bounds-checked window read *)
          match (args, args_s) with
          | [ _; r ], [ a_s; r_s ] ->
              let a_tmp = fresh_tmp ctx in
              let r_tmp = fresh_tmp ctx in
              let lo, hi = range_window_sexps span ctx r.ty a_tmp r_tmp in
              "(b* ((" ^ a_tmp ^ " " ^ a_s ^ ") (" ^ r_tmp ^ " " ^ r_s
              ^ ")) " ^ sexp [ "vec-index-range"; a_tmp; lo; hi ] ^ ")"
          | _ -> [%craise] span "ACL2: ill-formed shared subslice index")
      | Types.Index { is_range = true; _ } ->
          [%craise] span
            "ACL2: mutable subslice index outside a pair-destructuring let"
      | Types.PtrFromParts _ ->
          [%craise] span "ACL2: raw pointers not supported")
  | FunOrOp (Fun (FromLlbc (TraitMethod _, _))) ->
      [%craise] span "ACL2: trait method call; run charon with --monomorphize"
  | FunOrOp (Fun (Pure Return)) -> sexp ("ok" :: args_s)
  | FunOrOp (Fun (Pure Fail)) -> sexp ("result-fail" :: args_s)
  | FunOrOp (Fun (Pure Assert)) -> sexp ("massert" :: args_s)
  | FunOrOp (Fun (Pure FuelDecrease)) -> sexp ("1-" :: args_s)
  | FunOrOp (Fun (Pure FuelEqZero)) -> sexp ("zp" :: args_s)
  | FunOrOp (Fun (Pure (UpdateAtIndex _))) -> sexp ("array-update" :: args_s)
  | FunOrOp (Fun (Pure _)) ->
      [%craise] span "ACL2: unsupported pure builtin function"
  | FunOrOp (Unop (Not None)) -> sexp ("not" :: args_s)
  | FunOrOp (Unop (Cast (CastLit (src, tgt)))) -> (
      (* Mirror the F*/Coq reference semantics (Primitives.scalar_cast /
         scalar_cast_bool = mk_scalar tgt x): the cast yields (ok x) when x
         is in range for the target integer type, else (fail). Widening
         casts (byte -> index/word, the AES S-box case) are the identity;
         narrowing an out-of-range value is a checked panic, exactly as in
         the reference backends. *)
      match src with
      | _ when literal_type_is_integer src && literal_type_is_integer tgt ->
          sexp ((int_ty_name (literal_as_integer tgt) ^ "-cast") :: args_s)
      | TBool when literal_type_is_integer tgt ->
          sexp ((int_ty_name (literal_as_integer tgt) ^ "-cast-bool") :: args_s)
      | _ ->
          [%craise] span
            "ACL2: only integer and bool->integer casts are supported")
  | FunOrOp (Unop (Cast (CastRawPtr _))) ->
      [%craise] span "ACL2: raw-pointer casts not supported"
  | FunOrOp (Unop _) ->
      [%craise] span
        "ACL2: unsupported unop (neg / bitwise-not / array-to-slice)"
  | FunOrOp (Binop b) -> (
      match binop_to_acl2 span b with
      | "acl2::nequal" -> sexp [ "not"; sexp ("equal" :: args_s) ]
      | s -> sexp (s :: args_s))
  | Global gid -> (
      match GlobalDeclId.Map.find_opt gid ctx.global_names with
      | Some n -> n
      | None -> [%craise] span "ACL2: reference to an unsupported global")
  | AdtCons { adt_id; variant_id } ->
      adt_cons_to_acl2 span ctx adt_id variant_id args args_s
  | Proj { adt_id; field_id } -> proj_to_acl2 span ctx adt_id field_id args_s
  | ScalarValProj _ -> (
      (* Scalars are raw integers in our model: the projection is the identity *)
      match args_s with
      | [ a ] -> a
      | _ -> [%craise] span "ACL2: ill-formed scalar projection")
  | TraitConst _ -> [%craise] span "ACL2: trait constants not supported"
  | MkDynTrait _ -> [%craise] span "ACL2: dyn traits not supported"
  | LoopOp -> [%craise] span "ACL2: loop operator; use -loops-to-rec"

and adt_cons_to_acl2 (span : Meta.span) (ctx : actx) (adt_id : type_id)
    (variant_id : VariantId.id option) (_args : texpr list)
    (args_s : string list) : string =
  match adt_id with
  | TBuiltin TResult ->
      if variant_id = Some result_ok_id then sexp ("ok" :: args_s)
      else if variant_id = Some result_fail_id then sexp ("result-fail" :: args_s)
      else [%craise] span "ACL2: ill-formed result"
  | TBuiltin TError ->
      if variant_id = Some error_failure_id then "(err-failure)"
      else if variant_id = Some error_out_of_fuel_id then "(err-out-of-fuel)"
      else [%craise] span "ACL2: ill-formed error"
  | TBuiltin TFuel -> [%craise] span "ACL2: fuel constructor not expected"
  | TBuiltin TArray ->
      (* array literal [v0, ..., vn] *)
      sexp ("list" :: args_s)
  | TBuiltin _ -> [%craise] span "ACL2: unsupported builtin ADT constructor"
  | TTuple -> (
      match args_s with
      | [] -> "(unit)"
      | [ a ] -> a
      | [ a; b ] -> sexp [ "cons"; a; b ]
      | _ -> [%craise] span "ACL2: tuples of arity > 2 not supported in v0")
  | TAdtId id -> (
      let tname = type_name span ctx id in
      let decl = TypeDeclId.Map.find id ctx.types in
      match (decl.kind, variant_id) with
      | Struct _, None ->
          (* defprod positional constructor is just the type name *)
          sexp (tname :: args_s)
      | Enum variants, Some vid ->
          let v = VariantId.nth variants vid in
          let cons =
            tname ^ "-" ^ collapse_dashes (mangle_string v.variant_name)
          in
          sexp (cons :: args_s)
      | _ -> [%craise] span "ACL2: ill-formed ADT constructor")

and proj_to_acl2 (span : Meta.span) (ctx : actx) (adt_id : type_id)
    (field_id : FieldId.id) (args_s : string list) : string =
  let arg =
    match args_s with
    | [ a ] -> a
    | _ -> [%craise] span "ACL2: ill-formed projection"
  in
  match adt_id with
  | TTuple ->
      if FieldId.to_int field_id = 0 then sexp [ "car"; arg ]
      else if FieldId.to_int field_id = 1 then sexp [ "cdr"; arg ]
      else [%craise] span "ACL2: tuple projection arity > 2"
  | TAdtId id -> (
      let tname = type_name span ctx id in
      let decl = TypeDeclId.Map.find id ctx.types in
      match decl.kind with
      | Struct fields ->
          let fnames = field_names fields in
          let fname = List.nth fnames (FieldId.to_int field_id) in
          sexp [ tname ^ "->" ^ fname; arg ]
      | _ -> [%craise] span "ACL2: projection on a non-struct")
  | _ -> [%craise] span "ACL2: unsupported projection"

(* The bounds of a (monomorphic) RangeX<usize> value [r_var], as sexps.
   The missing bound of RangeTo/RangeFrom defaults to 0 / (len [arr_var]). *)
and range_window_sexps (span : Meta.span) (ctx : actx) (rty : ty)
    (arr_var : string) (r_var : string) : string * string =
  let range_id =
    match rty with
    | TAdt (TAdtId id, _) -> id
    | _ -> [%craise] span "ACL2: subslice borrow: range is not an ADT"
  in
  let rname = type_name span ctx range_id in
  let rdecl = TypeDeclId.Map.find range_id ctx.types in
  let fields =
    match rdecl.kind with
    | Struct fs -> field_names fs
    | _ -> [%craise] span "ACL2: subslice borrow: range is not a struct"
  in
  if str_contains rname "-rangeto-" then
    match fields with
    | [ fe ] -> ("0", "(" ^ rname ^ "->" ^ fe ^ " " ^ r_var ^ ")")
    | _ -> [%craise] span "ACL2: RangeTo has unexpected fields"
  else if str_contains rname "-rangefrom-" then
    match fields with
    | [ fs ] ->
        ("(" ^ rname ^ "->" ^ fs ^ " " ^ r_var ^ ")", "(len " ^ arr_var ^ ")")
    | _ -> [%craise] span "ACL2: RangeFrom has unexpected fields"
  else
    match fields with
    | [ fs; fe ] ->
        ( "(" ^ rname ^ "->" ^ fs ^ " " ^ r_var ^ ")",
          "(" ^ rname ^ "->" ^ fe ^ " " ^ r_var ^ ")" )
    | _ -> [%craise] span "ACL2: Range has unexpected fields"

(* Mutable subslice / array-to-slice borrows arrive as pair-lets
     let (sub, back) = <borrow> in ...
   where [back] is a first-class backward function.  We print the forward
   read, bind BOTH pattern variables (de Bruijn alignment), and record
   [back] in [ctx.closures]; its applications print as write-backs. *)
and mut_borrow_let (span : Meta.span) (ctx : actx) (env : venv)
    (monadic : bool) (pat : tpat) (e1 : texpr) (e2 : texpr) : string option =
  match pat.pat with
  | PAdt { variant_id = None; fields = [ f_sub; f_back ] } -> (
      let head, args = destruct_apps (unmeta e1) in
      let head = unmeta head in
      (if Option.is_some (Sys.getenv_opt "ACL2_DEBUG_BORROW") then
         let hs =
           match head.e with
           | Qualif { id = FunOrOp (Fun (FromLlbc (FunId (FRegular id), _))); _ }
             -> (
               match FunDeclId.Map.find_opt id ctx.fun_names with
               | Some n -> "FRegular:" ^ n
               | None -> "FRegular:?")
           | Qualif _ -> "Qualif:other"
           | _ -> "head:other"
         in
         Printf.eprintf "[borrow-dbg] pair-let head=%s args=%d\n%!" hs
           (List.length args));
      let shape =
        match (head.e, args) with
        | ( Qualif { id = FunOrOp (Fun (FromLlbc (FunId (FRegular id), _))); _ },
            [ arr; r ] )
          when (match FunDeclId.Map.find_opt id ctx.fun_names with
               | Some n -> is_subslice_index_mut n
               | None -> false) -> Some (`Subslice (arr, r))
        | ( Qualif
              {
                id =
                  FunOrOp
                    (Fun
                       (FromLlbc
                          ( FunId
                              (FBuiltin
                                 (Types.Index
                                    { is_range = true; mutability = Types.RMut; _ })),
                            _ )));
                _;
              },
            [ arr; r ] ) -> Some (`Subslice (arr, r))
        | ( Qualif
              {
                id =
                  FunOrOp
                    (Fun (FromLlbc (FunId (FBuiltin Types.ArrayToSliceMut), _)));
                _;
              },
            [ arr ] ) -> Some (`ArrToSlice arr)
        | _ -> None
      in
      match shape with
      | None -> None
      | Some sh -> (
          let env', names = bind_tpats ctx env [ f_sub; f_back ] in
          let sub_n, back_n =
            match names with
            | [ a; b ] -> (a, b)
            | _ -> [%craise] span "ACL2: mut-borrow pair arity"
          in
          match sh with
          | `Subslice (arr, r) ->
              if not monadic then
                [%craise] span "ACL2: index_mut let is unexpectedly non-monadic";
              let arr_s = texpr_to_acl2 span ctx env arr in
              let r_s = texpr_to_acl2 span ctx env r in
              let a_tmp = fresh_tmp ctx in
              let r_tmp = fresh_tmp ctx in
              let lo, hi = range_window_sexps span ctx r.ty a_tmp r_tmp in
              if back_n <> "&" then
                Hashtbl.replace ctx.closures back_n
                  (CloRangeBack { arr = a_tmp; lo; hi });
              let fwd = sexp [ "vec-index-range"; a_tmp; lo; hi ] in
              let sub_bind =
                "((ok " ^ (if sub_n = "&" then "&" else sub_n) ^ ") " ^ fwd ^ ")"
              in
              let body = texpr_to_acl2 span ctx env' e2 in
              Some
                ("(b* ((" ^ a_tmp ^ " " ^ arr_s ^ ")\n     (" ^ r_tmp ^ " "
               ^ r_s ^ ")\n     " ^ sub_bind ^ ")\n  " ^ body ^ ")")
          | `ArrToSlice arr ->
              if monadic then
                [%craise] span
                  "ACL2: array_to_slice_mut let is unexpectedly monadic";
              let arr_s = texpr_to_acl2 span ctx env arr in
              if back_n <> "&" then
                Hashtbl.replace ctx.closures back_n CloIdentityBack;
              let body = texpr_to_acl2 span ctx env' e2 in
              if sub_n = "&" then Some body
              else Some ("(b* ((" ^ sub_n ^ " " ^ arr_s ^ "))\n  " ^ body ^ ")")))
  | _ -> None

(* Monadic borrows bind the (subslice, backward) PAIR to a plain variable
   first and destructure it in a separate non-monadic let:
     (pair : (Slice * (Slice -> Array))) <-- index_mut a r;
     let (sub, back) = pair in ...
   [mut_borrow_pair_let] handles the first form (emit the forward read,
   remember the pair variable); [pending_pair_destructure] the second
   (bind sub to the forward value, register back as a closure). *)
and mut_borrow_pair_let (span : Meta.span) (ctx : actx) (env : venv)
    (monadic : bool) (pat : tpat) (e1 : texpr) (e2 : texpr) : string option =
  match pat.pat with
  | PBound (_, _) when monadic -> (
      let head, args = destruct_apps (unmeta e1) in
      let head = unmeta head in
      let kind =
        match head.e with
        | Qualif { id = FunOrOp (Fun (FromLlbc (FunId (FRegular id), _))); _ }
          -> (
            match FunDeclId.Map.find_opt id ctx.fun_names with
            | Some n when is_subslice_index_mut n -> Some `Range
            | Some n when is_elem_index_mut n -> Some `Elem
            | _ -> None)
        | Qualif
            {
              id =
                FunOrOp
                  (Fun
                     (FromLlbc
                        ( FunId
                            (FBuiltin
                               (Types.Index
                                  { is_range; mutability = Types.RMut; _ })),
                          _ )));
              _;
            } -> if is_range then Some `Range else Some `Elem
        | _ -> None
      in
      match (kind, args) with
      | Some `Range, [ arr; r ] ->
          let arr_s = texpr_to_acl2 span ctx env arr in
          let r_s = texpr_to_acl2 span ctx env r in
          let a_tmp = fresh_tmp ctx in
          let r_tmp = fresh_tmp ctx in
          let sub_tmp = fresh_tmp ctx in
          let lo, hi = range_window_sexps span ctx r.ty a_tmp r_tmp in
          let env', names = bind_tpats ctx env [ pat ] in
          let pair_n =
            match names with
            | [ n ] -> n
            | _ -> [%craise] span "ACL2: mut-borrow pair binder arity"
          in
          if pair_n <> "&" then
            Hashtbl.replace ctx.pending_pairs pair_n
              (CloRangeBack { arr = a_tmp; lo; hi }, sub_tmp);
          let body = texpr_to_acl2 span ctx env' e2 in
          Some
            ("(b* ((" ^ a_tmp ^ " " ^ arr_s ^ ")\n     (" ^ r_tmp ^ " " ^ r_s
           ^ ")\n     ((ok " ^ sub_tmp ^ ") "
            ^ sexp [ "vec-index-range"; a_tmp; lo; hi ]
            ^ "))\n  " ^ body ^ ")")
      | Some `Elem, [ arr; i ] ->
          let arr_s = texpr_to_acl2 span ctx env arr in
          let i_s = texpr_to_acl2 span ctx env i in
          let a_tmp = fresh_tmp ctx in
          let i_tmp = fresh_tmp ctx in
          let sub_tmp = fresh_tmp ctx in
          let env', names = bind_tpats ctx env [ pat ] in
          let pair_n =
            match names with
            | [ n ] -> n
            | _ -> [%craise] span "ACL2: mut-borrow pair binder arity"
          in
          if pair_n <> "&" then
            Hashtbl.replace ctx.pending_pairs pair_n
              (CloElemBack { arr = a_tmp; idx = i_tmp }, sub_tmp);
          let body = texpr_to_acl2 span ctx env' e2 in
          Some
            ("(b* ((" ^ a_tmp ^ " " ^ arr_s ^ ")\n     (" ^ i_tmp ^ " " ^ i_s
           ^ ")\n     ((ok " ^ sub_tmp ^ ") "
            ^ sexp [ "array-index"; a_tmp; i_tmp ]
            ^ "))\n  " ^ body ^ ")")
      | _ -> None)
  | _ -> None

and pending_pair_destructure (span : Meta.span) (ctx : actx) (env : venv)
    (monadic : bool) (pat : tpat) (e1 : texpr) (e2 : texpr) : string option =
  match (pat.pat, monadic) with
  | PAdt { variant_id = None; fields = [ f_sub; f_back ] }, false -> (
      let rhs = unmeta e1 in
      let pair_name =
        match rhs.e with
        | FVar id -> FVarId.Map.find_opt id env.fvars
        | BVar v -> ( try Some (venv_bvar env v) with _ -> None)
        | _ -> None
      in
      match Option.bind pair_name (Hashtbl.find_opt ctx.pending_pairs) with
      | None -> None
      | Some (kind, sub_tmp) ->
          let env', names = bind_tpats ctx env [ f_sub; f_back ] in
          let sub_n, back_n =
            match names with
            | [ a; b ] -> (a, b)
            | _ -> [%craise] span "ACL2: pair destructure arity"
          in
          if back_n <> "&" then Hashtbl.replace ctx.closures back_n kind;
          let body = texpr_to_acl2 span ctx env' e2 in
          if sub_n = "&" then Some body
          else Some ("(b* ((" ^ sub_n ^ " " ^ sub_tmp ^ "))\n  " ^ body ^ ")"))
  | _ -> None

and let_to_acl2 (span : Meta.span) (ctx : actx) (env : venv) (monadic : bool)
    (pat : tpat) (e1 : texpr) (e2 : texpr) : string =
  match mut_borrow_let span ctx env monadic pat e1 e2 with
  | Some s -> s
  | None ->
  match mut_borrow_pair_let span ctx env monadic pat e1 e2 with
  | Some s -> s
  | None ->
  match pending_pair_destructure span ctx env monadic pat e1 e2 with
  | Some s -> s
  | None ->
  let e1_s = texpr_to_acl2 span ctx env e1 in
  (* Bind the pattern's variables (one binder group) *)
  match pat.pat with
  | PBound (_, _) | PIgnored ->
      let env', surface = bind_tpats ctx env [ pat ] in
      let name_s = List.hd surface in
      let body = texpr_to_acl2 span ctx env' e2 in
      let bind_s =
        if monadic then "((ok " ^ name_s ^ ") " ^ e1_s ^ ")"
        else if name_s = "&" then "(- " ^ e1_s ^ ")"
        else "(" ^ name_s ^ " " ^ e1_s ^ ")"
      in
      "(b* (" ^ bind_s ^ ")\n  " ^ body ^ ")"
  | POpen (_, _) -> [%craise] span "ACL2: unexpected open binder in let"
  | PAdt { variant_id = None; fields } ->
      (* Tuple destructuring let: bind a temp, project fields *)
      let tmp = fresh_tmp ctx in
      let env', fnames = bind_tpats ctx env fields in
      let accessors =
        match fields with
        | [ _; _ ] -> [ "(car " ^ tmp ^ ")"; "(cdr " ^ tmp ^ ")" ]
        | _ -> [%craise] span "ACL2: destructuring let arity <> 2"
      in
      let binds =
        List.filter_map
          (fun (n, a) ->
            match n with
            | "&" -> None
            | _ -> Some ("(" ^ n ^ " " ^ a ^ ")"))
          (List.combine fnames accessors)
      in
      let first_bind =
        if monadic then "((ok " ^ tmp ^ ") " ^ e1_s ^ ")"
        else "(" ^ tmp ^ " " ^ e1_s ^ ")"
      in
      let body = texpr_to_acl2 span ctx env' e2 in
      "(b* ("
      ^ String.concat "\n     " (first_bind :: binds)
      ^ ")\n  " ^ body ^ ")"
  | PAdt _ -> [%craise] span "ACL2: variant-destructuring let not supported"
  | PConstant _ -> [%craise] span "ACL2: constant pattern in let"

and match_to_acl2 (span : Meta.span) (ctx : actx) (env : venv) (scrut : texpr)
    (branches : match_branch list) : string =
  let scrut_s = texpr_to_acl2 span ctx env scrut in
  (* v0: only matches on user enums, with one PAdt pattern per variant *)
  let ty_id =
    match scrut.ty with
    | TAdt (TAdtId id, _) -> id
    | _ -> [%craise] span "ACL2: match on a non-enum scrutinee"
  in
  let tname = type_name span ctx ty_id in
  let decl = TypeDeclId.Map.find ty_id ctx.types in
  let variants =
    match decl.kind with
    | Enum vs -> vs
    | _ -> [%craise] span "ACL2: match on a non-enum type"
  in
  (* Bind the scrutinee once *)
  let tmp = fresh_tmp ctx in
  let branch_to_acl2 (b : match_branch) : string =
    match b.pat.pat with
    | PAdt { variant_id = Some vid; fields } ->
        let v = VariantId.nth variants vid in
        let kw = variant_kw v in
        let cons_name =
          tname ^ "-" ^ collapse_dashes (mangle_string v.variant_name)
        in
        let fnames_decl = field_names v.fields in
        let env', pnames = bind_tpats ctx env fields in
        let binds =
          List.filter_map
            (fun (n, fdecl) ->
              match n with
              | "&" -> None
              | _ ->
                  Some
                    ("(" ^ n ^ " (" ^ cons_name ^ "->" ^ fdecl ^ " " ^ tmp
                   ^ "))"))
            (List.combine pnames fnames_decl)
        in
        let body = texpr_to_acl2 span ctx env' b.branch in
        let body =
          if binds = [] then body
          else "(b* (" ^ String.concat " " binds ^ ") " ^ body ^ ")"
        in
        kw ^ " " ^ body
    | _ -> [%craise] span "ACL2: unsupported match branch pattern"
  in
  let branches_s = List.map branch_to_acl2 branches in
  "(b* ((" ^ tmp ^ " " ^ scrut_s ^ "))\n  (" ^ tname ^ "-case " ^ tmp ^ "\n    "
  ^ String.concat "\n    " branches_s
  ^ "))"

and struct_update_to_acl2 (span : Meta.span) (ctx : actx) (env : venv)
    (su : struct_update) : string =
  match su.struct_id with
  | TBuiltin TArray ->
      (* array literal [v0; ...; vn] built as an aggregate: no [init] for a
         fresh array, and the updates cover every index in order *)
      if su.init <> None then
        [%craise] span "ACL2: array update-with-init not supported in v0"
      else
        let sorted =
          List.sort (fun (a, _) (b, _) -> FieldId.compare_id a b) su.updates
        in
        let elems =
          List.map (fun (_, e) -> texpr_to_acl2 span ctx env e) sorted
        in
        sexp ("list" :: elems)
  | TAdtId id -> (
      let tname = type_name span ctx id in
      let decl = TypeDeclId.Map.find id ctx.types in
      let fnames =
        match decl.kind with
        | Struct fields -> field_names fields
        | _ -> [%craise] span "ACL2: struct update on a non-struct"
      in
      let upd_strs =
        List.map
          (fun (fid, e) ->
            let fname = List.nth fnames (FieldId.to_int fid) in
            ":" ^ fname ^ " " ^ texpr_to_acl2 span ctx env e)
          su.updates
      in
      match su.init with
      | Some base ->
          sexp
            (("change-" ^ tname) :: texpr_to_acl2 span ctx env base :: upd_strs)
      | None -> sexp (("make-" ^ tname) :: upd_strs))
  | _ -> [%craise] span "ACL2: unsupported struct update"

(* ----------------------------------------------------------------- decls *)

let type_decl_to_acl2 (ctx : actx) (decl : Pure.type_decl) : string =
  let span = decl.item_meta.span in
  let tname = type_name span ctx decl.def_id in
  (* Fields referencing the type itself (Box is already transparent in the
     pure AST) get the type's own predicate so FTY builds a genuine
     recursive fixtype (with its -count measure); everything else is
     erased to any-p in v0. *)
  let field_ty (f : Pure.field) : string =
    match f.field_ty with
    | TAdt (TAdtId id, _) when id = decl.def_id -> tname ^ "-p"
    | _ -> "acl2::any-p"
  in
  let field_entry (n : string) (f : Pure.field) : string =
    "(" ^ n ^ " " ^ field_ty f ^ ")"
  in
  match decl.kind with
  | Struct [] -> ";; unit struct " ^ tname ^ " (values are (unit))"
  | Struct fields ->
      let fields_s = List.map2 field_entry (field_names fields) fields in
      "(fty::defprod " ^ tname ^ "\n  (" ^ String.concat " " fields_s
      ^ ")\n  :xvar the-" ^ tname ^ ")"
  | Enum variants ->
      let variant_s (v : Pure.variant) : string =
        let fields_s = List.map2 field_entry (field_names v.fields) v.fields in
        "(" ^ variant_kw v ^ " (" ^ String.concat " " fields_s ^ "))"
      in
      "(fty::deftagsum " ^ tname ^ "\n  "
      ^ String.concat "\n  " (List.map variant_s variants)
      ^ "\n  :xvar the-" ^ tname ^ ")"
  | Opaque ->
      if str_contains tname "-step-by-stepby-" then
        (* StepBy<I> is opaque without the Miri sysroot; we own its model:
           Rust's own fields are { iter, step (holding step-1), first_take }
           (see the ctor/next syntheses in [synth_range_iter_body]). *)
        "(fty::defprod " ^ tname
        ^ "\n  ((iter acl2::any-p) (step acl2::any-p) (first-take acl2::any-p))"
        ^ "\n  :xvar the-" ^ tname ^ ")"
      else ";; opaque type " ^ tname ^ " (skipped)"

(* Functions are keyed by (def_id, loop_id): Aeneas gives a loop function
   the SAME def_id as its wrapper, distinguished only by [loop_id]. *)
type fkey = FunDeclId.id * (LoopId.id * bool) option

let decl_key (d : Pure.fun_decl) : fkey = (d.def_id, d.loop_id)

(* The keys of the group members that [d]'s body calls *)
let group_callees (keys : fkey list) (d : Pure.fun_decl) : fkey list =
  let found = ref [] in
  let visitor =
    object
      inherit [_] iter_expr

      method! visit_qualif _ q =
        match q.id with
        | FunOrOp (Fun (FromLlbc (FunId (FRegular id), lp)))
          when List.mem (id, lp) keys ->
            if not (List.mem (id, lp) !found) then found := (id, lp) :: !found
        | _ -> ()
    end
  in
  (match d.body with
  | Some b -> visitor#visit_texpr () b.body
  | None -> ());
  !found

(* Order a recursive group for ACL2 admission: compute SCCs of the call
   graph restricted to the group, emit them callee-first; a singleton SCC
   without a self-call is a plain (measure-less) defun; a singleton with a
   self-call gets a measure; a larger SCC becomes a mutual-recursion. This
   matters because Aeneas groups a loop's wrapper function with the loop
   function: the wrapper calls the loop with EQUAL fuel and must not be in
   the measured clique. *)
type fun_scc = { members : Pure.fun_decl list; is_rec : bool }

let group_to_sccs (decls : Pure.fun_decl list) : fun_scc list =
  let keys = List.map decl_key decls in
  let callees = List.map (fun d -> (decl_key d, group_callees keys d)) decls in
  let callees_of k = List.assoc k callees in
  (* reachable k = keys reachable from k via >=1 call edge *)
  let reachable k =
    let rec go visited frontier =
      match frontier with
      | [] -> visited
      | _ ->
          let next =
            List.concat_map callees_of frontier
            |> List.filter (fun x -> not (List.mem x visited))
            |> List.sort_uniq compare
          in
          go (visited @ next) next
    in
    go [] (callees_of k)
  in
  let same_scc a b =
    a = b || (List.mem b (reachable a) && List.mem a (reachable b))
  in
  let sccs : Pure.fun_decl list list =
    List.fold_left
      (fun acc (d : Pure.fun_decl) ->
        let rec insert = function
          | [] -> [ [ d ] ]
          | grp :: rest ->
              if same_scc (decl_key (List.hd grp)) (decl_key d) then
                (grp @ [ d ]) :: rest
              else grp :: insert rest
        in
        insert acc)
      [] decls
  in
  let scc_of_key k =
    List.find (fun grp -> List.exists (fun d -> decl_key d = k) grp) sccs
  in
  let scc_callees grp =
    List.concat_map (fun d -> callees_of (decl_key d)) grp
    |> List.map scc_of_key
    |> List.filter (fun g -> g != grp)
  in
  let rec topo (remaining : Pure.fun_decl list list)
      (emitted : Pure.fun_decl list list) : Pure.fun_decl list list =
    match remaining with
    | [] -> List.rev emitted
    | _ ->
        let ready, blocked =
          List.partition
            (fun grp ->
              List.for_all
                (fun dep -> List.memq dep emitted || dep == grp)
                (scc_callees grp))
            remaining
        in
        if ready = [] then List.rev emitted @ remaining
        else topo blocked (List.rev_append ready emitted)
  in
  let ordered = topo sccs [] in
  List.map
    (fun grp ->
      let is_rec =
        match grp with
        | [ d ] -> List.mem (decl_key d) (callees_of (decl_key d))
        | _ -> true
      in
      { members = grp; is_rec })
    ordered

(* Synthesize a first-order body for an opaque Range iterator method.
   [into_iter] : Range -> result Range is the identity; [next] : Range ->
   result (Option * Range) is the fused advance (yield start, step start+1).
   The Option/Range constructors are the ones we emit for those (per-crate,
   monomorphic) ADTs, recovered from the method's own signature so the names
   match the generated deftagsum/defprod exactly. *)
let synth_range_iter_body (span : Meta.span) (ctx : actx) (decl : Pure.fun_decl)
    (name : string) : string =
  if is_try_into_array name then
    (* <[u8; N] as TryFrom<&[u8]>>::try_into: Ok(the slice as an array) when
       the length matches, Err(TryFromSliceError) otherwise -- core's OWN
       Result value either way (the call itself never panics). *)
    let result_id =
      match decl.signature.output with
      | TAdt (TBuiltin TResult, { types = [ TAdt (TAdtId id, _) ]; _ }) -> id
      | _ -> [%craise] span "ACL2: try_into: unexpected output signature"
    in
    let rname = type_name span ctx result_id in
    let rdecl = TypeDeclId.Map.find result_id ctx.types in
    let n =
      match rdecl.kind with
      | Enum (okv :: _) -> (
          match okv.fields with
          | [ { field_ty = TAdt (TBuiltin TArray, generics); _ } ] -> (
              match generics.const_generics with
              | [ CgValue lit ] -> literal_to_acl2 span lit
              | _ ->
                  [%craise] span "ACL2: try_into: array length not a literal")
          | _ -> [%craise] span "ACL2: try_into: unexpected Ok payload")
      | _ -> [%craise] span "ACL2: try_into: result type is not an enum"
    in
    "(defun " ^ name ^ " (self)\n  (if (equal (len self) " ^ n ^ ")\n      (ok ("
    ^ rname ^ "-ok self))\n    (ok (" ^ rname ^ "-err (unit)))))"
  else if is_result_unwrap name then
    (* core::result::Result::unwrap on a monomorphic Result: the Ok payload,
       or a panic (= result-fail) on Err. *)
    let result_id =
      match decl.signature.inputs with
      | TAdt (TAdtId id, _) :: _ -> id
      | _ -> [%craise] span "ACL2: unwrap: unexpected input signature"
    in
    let rname = type_name span ctx result_id in
    "(defun " ^ name ^ " (self)\n  (if (eq (" ^ rname
    ^ "-kind self) :ok)\n      (ok (" ^ rname
    ^ "-ok->f0 self))\n    (result-fail (err-failure))))"
  else if is_subslice_index_shared name then
    (* <[T;N] as Index<RangeX<usize>>>::index -- a[r] as a bounds-checked
       window read.  RangeX's missing bound defaults to 0 / (len self). *)
    let range_id =
      match decl.signature.inputs with
      | [ _; TAdt (TAdtId id, _) ] -> id
      | _ -> [%craise] span "ACL2: subslice index: unexpected signature"
    in
    let rname = type_name span ctx range_id in
    let rdecl = TypeDeclId.Map.find range_id ctx.types in
    let fields =
      match rdecl.kind with
      | Struct fs -> field_names fs
      | _ -> [%craise] span "ACL2: subslice index: range is not a struct"
    in
    let lo, hi =
      if str_contains rname "-rangeto-" then
        match fields with
        | [ fe ] -> ("0", "(" ^ rname ^ "->" ^ fe ^ " r)")
        | _ -> [%craise] span "ACL2: RangeTo has unexpected fields"
      else if str_contains rname "-rangefrom-" then
        match fields with
        | [ fs ] -> ("(" ^ rname ^ "->" ^ fs ^ " r)", "(len self)")
        | _ -> [%craise] span "ACL2: RangeFrom has unexpected fields"
      else
        match fields with
        | [ fs; fe ] ->
            ("(" ^ rname ^ "->" ^ fs ^ " r)", "(" ^ rname ^ "->" ^ fe ^ " r)")
        | _ -> [%craise] span "ACL2: Range has unexpected fields"
    in
    "(defun " ^ name ^ " (self r) (vec-index-range self " ^ lo ^ " " ^ hi
    ^ "))"
  else if is_stepby_ctor name then
    (* Iterator::step_by(self, step): Rust asserts step != 0 (a panic ->
       result-fail) and stores step - 1 in the [step] field. *)
    let stepby_id =
      match decl.signature.output with
      | TAdt (TBuiltin TResult, { types = [ TAdt (TAdtId id, _) ]; _ }) -> id
      | TAdt (TAdtId id, _) -> id
      | _ -> [%craise] span "ACL2: step_by: unexpected output signature"
    in
    let sbname = type_name span ctx stepby_id in
    "(defun " ^ name ^ " (self step)\n  (if (equal step 0)\n      (result-fail \
     (err-failure))\n    (ok (" ^ sbname ^ " self (- step 1) t))))"
  else if is_stepby_next name then
    (* StepBy::next: if first_take { first_take = false; iter.next() }
       else { iter.nth(step) } -- specialized to Range<usize>:
       nth(n) yields start+n and sets start = start+n+1 when start+n < end,
       else sets start = end and yields None. *)
    let stepby_id =
      match decl.signature.inputs with
      | TAdt (TAdtId id, _) :: _ -> id
      | _ -> [%craise] span "ACL2: StepBy::next: unexpected input signature"
    in
    let sbname = type_name span ctx stepby_id in
    let range_id =
      let prefix = "core-iter-adapters-step-by-stepby-" in
      let plen = String.length prefix in
      let rname =
        if String.length sbname > plen && String.sub sbname 0 plen = prefix
        then String.sub sbname plen (String.length sbname - plen)
        else [%craise] span "ACL2: StepBy::next: unexpected StepBy type name"
      in
      match
        TypeDeclId.Map.fold
          (fun id n acc -> if n = rname then Some id else acc)
          ctx.type_names None
      with
      | Some id -> id
      | None -> [%craise] span "ACL2: StepBy::next: range instance not in crate"
    in
    let option_id =
      match decl.signature.output with
      | TAdt
          ( TBuiltin TResult,
            {
              types =
                [ TAdt (TTuple, { types = TAdt (TAdtId oid, _) :: _; _ }) ];
              _;
            } ) -> oid
      | _ -> [%craise] span "ACL2: StepBy::next: unexpected output signature"
    in
    let rname = type_name span ctx range_id in
    let oname = type_name span ctx option_id in
    let rdecl = TypeDeclId.Map.find range_id ctx.types in
    let fstart, fend =
      match rdecl.kind with
      | Struct fields -> (
          match field_names fields with
          | s :: e :: _ -> (s, e)
          | _ -> [%craise] span "ACL2: Range has unexpected fields")
      | _ -> [%craise] span "ACL2: Range is not a struct"
    in
    String.concat "\n"
      [
        "(defun " ^ name ^ " (self)";
        "  (b* ((it (" ^ sbname ^ "->iter self))";
        "       (smo (" ^ sbname ^ "->step self))";
        "       (s (" ^ rname ^ "->" ^ fstart ^ " it))";
        "       (e (" ^ rname ^ "->" ^ fend ^ " it)))";
        "  (if (" ^ sbname ^ "->first-take self)";
        "      (if (< s e)";
        "          (ok (cons (" ^ oname ^ "-some s) (" ^ sbname ^ " (" ^ rname
        ^ " (+ s 1) e) smo nil)))";
        "        (ok (cons (" ^ oname ^ "-none) (" ^ sbname ^ " it smo nil))))";
        "    (if (< (+ s smo) e)";
        "        (ok (cons (" ^ oname ^ "-some (+ s smo)) (" ^ sbname ^ " ("
        ^ rname ^ " (+ s smo 1) e) smo nil)))";
        "      (ok (cons (" ^ oname ^ "-none) (" ^ sbname ^ " (" ^ rname
        ^ " e e) smo nil)))))))";
      ]
  else if
    is_range_iter_into_iter name || is_rev_into_iter name
    || is_iter_rev_ctor name || is_stepby_into_iter name
  then "(defun " ^ name ^ " (self) (ok self))"
  else if is_rev_next name then
    (* self is (represented as) the inner range; reverse advance. *)
    let range_id =
      (* the mangled Rev instance name embeds the range instance name *)
      let prefix = "core-iter-adapters-rev-rev-" in
      let rname =
        match decl.signature.inputs with
        | TAdt (TAdtId id, _) :: _ ->
            let n = type_name span ctx id in
            let plen = String.length prefix in
            if String.length n > plen && String.sub n 0 plen = prefix then
              String.sub n plen (String.length n - plen)
            else [%craise] span "ACL2: Rev::next: unexpected Rev type name"
        | _ -> [%craise] span "ACL2: Rev::next: unexpected input signature"
      in
      match
        TypeDeclId.Map.fold
          (fun id n acc -> if n = rname then Some id else acc)
          ctx.type_names None
      with
      | Some id -> id
      | None -> [%craise] span "ACL2: Rev::next: range instance not in crate"
    in
    let option_id =
      match decl.signature.output with
      | TAdt
          ( TBuiltin TResult,
            {
              types =
                [ TAdt (TTuple, { types = TAdt (TAdtId oid, _) :: _; _ }) ];
              _;
            } ) -> oid
      | _ -> [%craise] span "ACL2: Rev::next: unexpected output signature"
    in
    let rname = type_name span ctx range_id in
    let oname = type_name span ctx option_id in
    let rdecl = TypeDeclId.Map.find range_id ctx.types in
    let fstart, fend =
      match rdecl.kind with
      | Struct fields -> (
          match field_names fields with
          | s :: e :: _ -> (s, e)
          | _ -> [%craise] span "ACL2: Range has unexpected fields")
      | _ -> [%craise] span "ACL2: Range is not a struct"
    in
    String.concat "\n"
      [
        "(defun " ^ name ^ " (self)";
        "  (b* ((s (" ^ rname ^ "->" ^ fstart ^ " self))";
        "       (e (" ^ rname ^ "->" ^ fend ^ " self)))";
        "  (if (< s e)";
        "      (ok (cons (" ^ oname ^ "-some (- e 1)) (" ^ rname
        ^ " s (- e 1))))";
        "    (ok (cons (" ^ oname ^ "-none) self)))))";
      ]
  else
    let range_id =
      match decl.signature.inputs with
      | TAdt (TAdtId id, _) :: _ -> id
      | _ -> [%craise] span "ACL2: Range::next: unexpected input signature"
    in
    let option_id =
      match decl.signature.output with
      | TAdt
          ( TBuiltin TResult,
            {
              types =
                [ TAdt (TTuple, { types = TAdt (TAdtId oid, _) :: _; _ }) ];
              _;
            } ) -> oid
      | _ -> [%craise] span "ACL2: Range::next: unexpected output signature"
    in
    let rname = type_name span ctx range_id in
    let oname = type_name span ctx option_id in
    let rdecl = TypeDeclId.Map.find range_id ctx.types in
    let fstart, fend =
      match rdecl.kind with
      | Struct fields -> (
          match field_names fields with
          | s :: e :: _ -> (s, e)
          | _ -> [%craise] span "ACL2: Range has unexpected fields")
      | _ -> [%craise] span "ACL2: Range is not a struct"
    in
    if is_range_iter_next_back name then
      (* Rust: if start < end { end -= 1; Some(end) } else { None } *)
      String.concat "\n"
        [
          "(defun " ^ name ^ " (self)";
          "  (b* ((s (" ^ rname ^ "->" ^ fstart ^ " self))";
          "       (e (" ^ rname ^ "->" ^ fend ^ " self)))";
          "  (if (< s e)";
          "      (ok (cons (" ^ oname ^ "-some (- e 1)) (" ^ rname
          ^ " s (- e 1))))";
          "    (ok (cons (" ^ oname ^ "-none) self)))))";
        ]
    else
      String.concat "\n"
        [
          "(defun " ^ name ^ " (self)";
          "  (b* ((s (" ^ rname ^ "->" ^ fstart ^ " self))";
          "       (e (" ^ rname ^ "->" ^ fend ^ " self)))";
          "  (if (< s e)";
          "      (ok (cons (" ^ oname ^ "-some s) (" ^ rname ^ " (+ s 1) e)))";
          "    (ok (cons (" ^ oname ^ "-none) self)))))";
        ]

let fun_decl_to_acl2 (ctx : actx) (is_rec : bool) (decl : Pure.fun_decl) :
    string =
  let span = decl.item_meta.span in
  let base = fun_name span ctx decl.def_id in
  let name =
    match decl.loop_id with
    | None -> base
    | Some (lp_id, is_body) ->
        base ^ "-loop" ^ LoopId.to_string lp_id
        ^ if is_body then "-body" else ""
  in
  (if Option.is_some (Sys.getenv_opt "ACL2_DEBUG_BODY") && str_contains name "-go"
   then
     match decl.body with
     | Some _ ->
         let fmt_env = PrintPure.decls_ctx_to_fmt_env ctx.trans_ctx in
         Printf.eprintf "[body-dbg] %s:\n%s\n%!" name
           (PrintPure.fun_decl_to_string fmt_env decl)
     | None -> ());
  match decl.body with
  | None ->
      if is_range_iter_method name then synth_range_iter_body span ctx decl name
      else ";; opaque function " ^ name ^ " (skipped)"
  | Some body ->
      let env, input_names =
        bind_tpats ~toplevel:true ctx empty_venv body.inputs
      in
      List.iter
        (fun n ->
          if n = "&" then
            [%craise] span "ACL2: composite input pattern not supported")
        input_names;
      (* Find the fuel input (if any) for the measure *)
      let fuel_input =
        List.find_map
          (fun ((n, p) : string * tpat) ->
            match p.ty with
            | TAdt (TBuiltin TFuel, _) -> Some n
            | _ -> None)
          (List.combine input_names body.inputs)
      in
      let measure =
        match (is_rec, fuel_input) with
        | true, Some fuel ->
            (* The fuel measure decreases by 1 per call, so the termination
               obligation never needs crate-level reasoning.  Pin the theory to
               ground-zero: otherwise ACL2 opens the (enabled, non-recursive)
               crate functions appearing in the recursive call's governors --
               e.g. a loop body chaining several array-window ops -- and the
               ok-monad if-nests blow up clausification of a trivial goal. *)
            "\n  (declare (xargs :measure (nfix " ^ fuel
            ^ ")\n                  :hints ((\"Goal\" :in-theory (theory \
               'ground-zero)))))"
        | true, None ->
            [%craise] span
              "ACL2: recursive function without fuel; use -use-fuel"
        | false, _ -> ""
      in
      let body_s = texpr_to_acl2 span ctx env body.body in
      "(defun " ^ name ^ " ("
      ^ String.concat " " input_names
      ^ ")" ^ measure ^ "\n  " ^ body_s ^ ")"

(* ----------------------------------------------------------------- crate *)

(* Emit a global as (defconst *name* value). v0 only supports globals
   whose initializer is a single constant expression (after stripping the
   monadic return) -- the crypto case (round constants like DELTA). *)
let global_decl_to_acl2 (ctx : actx) (gid : GlobalDeclId.id) : string =
  let g = GlobalDeclId.Map.find gid ctx.trans_ctx.crate.global_decls in
  let span = g.item_meta.span in
  let name = GlobalDeclId.Map.find gid ctx.global_names in
  match Charon.GAstUtils.init_fun_id_of_global g with
  | None -> [%craise] span "ACL2: global without an initializer"
  | Some init_id -> (
      match FunDeclId.Map.find_opt init_id ctx.trans_funs with
      | None -> [%craise] span "ACL2: global initializer not found"
      | Some t -> (
          match t.f.body with
          | None -> [%craise] span "ACL2: opaque global"
          | Some body ->
              (* strip a leading monadic return: `ok e` -> `e` *)
              let e = body.body in
              let e =
                match opt_destruct_qualif_apps e with
                | Some (q, [ arg ]) -> (
                    match q.id with
                    | FunOrOp (Fun (Pure Return)) -> arg
                    | _ -> e)
                | _ -> e
              in
              let env, _ = bind_tpats ctx empty_venv body.inputs in
              let v = texpr_to_acl2 span ctx env e in
              "(defconst " ^ name ^ " " ^ v ^ ")"))

let extract_crate (out : out_channel) (rust_module_name : string)
    (ctx : ExtractBase.extraction_ctx) : unit =
  let trans_ctx = ctx.trans_ctx in
  (* Build the name maps *)
  let type_names =
    TypeDeclId.Map.mapi
      (fun _ (d : Pure.type_decl) -> mangle_name trans_ctx d.item_meta.name)
      ctx.trans_types
  in
  let fun_names =
    FunDeclId.Map.fold
      (fun id (t : pure_fun_translation) m ->
        let n = mangle_name trans_ctx t.f.item_meta.name in
        let m = FunDeclId.Map.add id n m in
        (* loops and bodies share the base name; suffixes are added at
           print time from [loop_id] *)
        List.fold_left
          (fun m (d : Pure.fun_decl) -> FunDeclId.Map.add d.def_id n m)
          m (t.loops @ t.bodies))
      ctx.trans_funs FunDeclId.Map.empty
  in
  let opaque_funs =
    FunDeclId.Map.fold
      (fun id (t : pure_fun_translation) s ->
        if t.f.body = None then FunDeclId.Set.add id s else s)
      ctx.trans_funs FunDeclId.Set.empty
  in

  (* Globals: name each as a defconst symbol *<mangled>*, and remember its
     initializer function id so we can emit its value. *)
  let global_names =
    GlobalDeclId.Map.fold
      (fun id (g : LlbcAst.global_decl) m ->
        let n = "*" ^ mangle_name trans_ctx g.item_meta.name ^ "*" in
        GlobalDeclId.Map.add id n m)
      ctx.trans_ctx.crate.global_decls GlobalDeclId.Map.empty
  in
  let actx =
    {
      trans_ctx;
      fun_names;
      opaque_funs;
      global_names;
      trans_funs = ctx.trans_funs;
      type_names;
      types = ctx.trans_types;
      gensym = 0;
      skipped = [];
      closures = Hashtbl.create 16;
      pending_pairs = Hashtbl.create 16;
    }
  in
  (* Header *)
  Printf.fprintf out ";; THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS\n";
  Printf.fprintf out ";; [%s]\n" rust_module_name;
  Printf.fprintf out "(in-package \"ACL2\")\n\n";
  Printf.fprintf out "(include-book \"rust-primitives\")\n\n";
  (* v0: extracted code may contain dead let-bindings (e.g. from functions
     that panic) and formals that ACL2's irrelevance check flags; relax
     both rather than analyzing liveness at print time. TODO: emit precise
     ignorable declarations instead. *)
  Printf.fprintf out "(set-ignore-ok t)\n";
  Printf.fprintf out "(set-irrelevant-formals-ok t)\n\n";
  (* Emit following the crate's declaration order *)
  let emit_decl (kind : string) (name : string) (f : unit -> string) : bool =
    match f () with
    | s ->
        Printf.fprintf out "%s\n\n" s;
        true
    | exception CFailure err ->
        Printf.fprintf out ";; SKIPPED %s %s: %s\n\n" kind name
          (match err.msg with
          | s -> s);
        false
  in
  let emit_group (dg : LlbcAst.declaration_group) : unit =
      match dg with
      | LlbcAst.TypeGroup (NonRecGroup id) | LlbcAst.TypeGroup (RecGroup [ id ])
        -> (
          match TypeDeclId.Map.find_opt id ctx.trans_types with
          | Some d ->
              ignore
                (emit_decl "type" (TypeDeclId.Map.find id type_names) (fun () ->
                     type_decl_to_acl2 actx d))
          | None -> ())
      | LlbcAst.TypeGroup (RecGroup _) ->
          Printf.fprintf out ";; SKIPPED mutually recursive type group\n\n"
      | LlbcAst.FunGroup g ->
          let ids =
            match g with
            | NonRecGroup id -> [ id ]
            | RecGroup ids -> ids
          in
          let decls =
            List.filter_map
              (fun id ->
                match FunDeclId.Map.find_opt id ctx.trans_funs with
                | Some t ->
                    if t.f.is_global_decl_body then None
                    else if
                      t.f.body = None
                      && Option.is_some
                           (Option.bind
                              (FunDeclId.Map.find_opt id fun_names)
                              std_fun_mapping)
                    then None (* provided by the primitives book *)
                    else Some ((t.f :: t.loops) @ t.bodies)
                | None -> None)
              ids
          in
          let decls = List.concat decls in
          if decls = [] then ()
          else
            let sccs = group_to_sccs decls in
            List.iter
              (fun (scc : fun_scc) ->
                let one (d : Pure.fun_decl) : string =
                  fun_decl_to_acl2 actx scc.is_rec d
                in
                match scc.members with
                | [ d ] ->
                    let ok =
                      emit_decl "function"
                        (FunDeclId.Map.find d.def_id fun_names) (fun () ->
                          one d)
                    in
                    if not ok then actx.skipped <- decl_key d :: actx.skipped
                | ds ->
                    let ok =
                      emit_decl "recursive functions"
                        (String.concat "/"
                           (List.map
                              (fun (d : Pure.fun_decl) ->
                                FunDeclId.Map.find d.def_id fun_names)
                              ds))
                        (fun () ->
                          "(mutual-recursion\n"
                          ^ String.concat "\n" (List.map one ds)
                          ^ ")")
                    in
                    if not ok then
                      actx.skipped <- List.map decl_key ds @ actx.skipped)
              sccs
      | LlbcAst.GlobalGroup g ->
          let gids =
            match g with
            | NonRecGroup id -> [ id ]
            | RecGroup ids -> ids
          in
          List.iter
            (fun gid ->
              ignore
                (emit_decl "global" (GlobalDeclId.Map.find gid global_names)
                   (fun () -> global_decl_to_acl2 actx gid)))
            gids
      | LlbcAst.TraitDeclGroup _ | LlbcAst.MixedGroup _ ->
          Printf.fprintf out
            ";; SKIPPED trait/mixed declaration group (run with \
             --monomorphize)\n\n"
      | LlbcAst.TraitImplGroup _ ->
          Printf.fprintf out
            ";; SKIPPED trait impl (run with --monomorphize)\n\n"
  in
  (* Two-pass emission: all type groups first, then functions and globals.
     Charon's declaration order is topological for the dependencies it can
     see, but synthesized bodies (e.g. the fallback [Rev::next], which reads
     the fields of the underlying [Range] type) can introduce type
     dependencies charon doesn't know about. Types never depend on
     functions, so hoisting every type group preserves well-formedness and
     makes all such references well-defined. *)
  let type_groups, value_groups =
    List.partition
      (fun (dg : LlbcAst.declaration_group) ->
        match dg with LlbcAst.TypeGroup _ -> true | _ -> false)
      ctx.crate.declarations
  in
  List.iter emit_group type_groups;
  List.iter emit_group value_groups;
  Printf.fprintf out ";; END OF GENERATED FILE\n"
