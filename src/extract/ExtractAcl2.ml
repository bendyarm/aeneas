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
let bind_tpats ?(toplevel = false) (ctx : actx) (env : venv)
    (pats : tpat list) : venv * string list =
  let idx = ref 0 in
  let group = ref BVarId.Map.empty in
  let names = ref [] in
  let rec walk (p : tpat) : string =
    match p.pat with
    | PBound (v, _) ->
        let i = !idx in
        idx := i + 1;
        let name =
          if toplevel then (
            (* Function formals are a single binder group: per-index clean
               names, distinct within the group. Kept readable for proofs. *)
            let n = clean_var_name v.basename i in
            if List.mem n !names then n ^ "-" ^ string_of_int i else n)
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
  match List.find_map try_wrap [ "add"; "sub"; "mul" ] with
  | Some s -> Some s
  | None -> None

let fun_name (span : Meta.span) (ctx : actx) (id : FunDeclId.id) : string =
  if FunDeclId.Set.mem id ctx.opaque_funs then
    [%craise] span
      "ACL2: call to an opaque/std function with no ACL2 mapping yet"
  else
    match FunDeclId.Map.find_opt id ctx.fun_names with
    | Some s -> s
    | None ->
        [%craise] span "ACL2: call to a function without a name (builtin?)"

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
  | FVar _ | BVar _ ->
      (* Application of a locally-bound function value: higher-order *)
      [%craise] span "ACL2: application of a function-typed variable (HO)"
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
  | FunOrOp (Fun (FromLlbc (FunId (FBuiltin _), _))) ->
      [%craise] span "ACL2: builtin (std) function not mapped in v0"
  | FunOrOp (Fun (FromLlbc (TraitMethod _, _))) ->
      [%craise] span "ACL2: trait method call; run charon with --monomorphize"
  | FunOrOp (Fun (Pure Return)) -> sexp ("ok" :: args_s)
  | FunOrOp (Fun (Pure Fail)) -> sexp ("fail" :: args_s)
  | FunOrOp (Fun (Pure Assert)) -> sexp ("massert" :: args_s)
  | FunOrOp (Fun (Pure FuelDecrease)) -> sexp ("1-" :: args_s)
  | FunOrOp (Fun (Pure FuelEqZero)) -> sexp ("zp" :: args_s)
  | FunOrOp (Fun (Pure _)) ->
      [%craise] span "ACL2: unsupported pure builtin function"
  | FunOrOp (Unop (Not None)) -> sexp ("not" :: args_s)
  | FunOrOp (Unop _) -> [%craise] span "ACL2: unsupported unop (neg/cast)"
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
      else if variant_id = Some result_fail_id then sexp ("fail" :: args_s)
      else [%craise] span "ACL2: ill-formed result"
  | TBuiltin TError ->
      if variant_id = Some error_failure_id then "(err-failure)"
      else if variant_id = Some error_out_of_fuel_id then "(err-out-of-fuel)"
      else [%craise] span "ACL2: ill-formed error"
  | TBuiltin TFuel -> [%craise] span "ACL2: fuel constructor not expected"
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

and let_to_acl2 (span : Meta.span) (ctx : actx) (env : venv) (monadic : bool)
    (pat : tpat) (e1 : texpr) (e2 : texpr) : string =
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

and struct_update_to_acl2 (span : Meta.span) (_ctx : actx) (_env : venv)
    (_su : struct_update) : string =
  [%craise] span "ACL2: struct update not supported in v0"

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
  | Opaque -> ";; opaque type " ^ tname ^ " (skipped)"

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
  match decl.body with
  | None -> ";; opaque function " ^ name ^ " (skipped)"
  | Some body ->
      let env, input_names = bind_tpats ~toplevel:true ctx empty_venv body.inputs in
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
            "\n  (declare (xargs :measure (nfix " ^ fuel ^ ")))"
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
  List.iter
    (fun (dg : LlbcAst.declaration_group) ->
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
            match g with NonRecGroup id -> [ id ] | RecGroup ids -> ids
          in
          List.iter
            (fun gid ->
              ignore
                (emit_decl "global"
                   (GlobalDeclId.Map.find gid global_names)
                   (fun () -> global_decl_to_acl2 actx gid)))
            gids
      | LlbcAst.TraitDeclGroup _ | LlbcAst.MixedGroup _ ->
          Printf.fprintf out
            ";; SKIPPED trait/mixed declaration group (run with \
             --monomorphize)\n\n"
      | LlbcAst.TraitImplGroup _ ->
          Printf.fprintf out
            ";; SKIPPED trait impl (run with --monomorphize)\n\n")
    ctx.crate.declarations;
  Printf.fprintf out ";; END OF GENERATED FILE\n"
