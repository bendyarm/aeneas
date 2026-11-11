(** ACL2 backend: prints the pure AST as ACL2 s-expressions (v0).

    Design (see the ACL2 backend plan §3.2): FTY tagsums/defprods for ADTs, the
    rust-primitives book's [result]/[error]/b* conventions for the error monad,
    fuel for recursion. Unsupported constructs raise [CFailure] and the
    declaration is skipped with a comment — never mistranslated.

    The input is polymorphic LLBC (charon's stock `--preset=aeneas`). ACL2
    functions have no type parameters, so type arguments are dropped and one
    function serves every instantiation; const generics become ordinary
    parameters; the standard-library functions the backend models are
    recognized by name pattern ([std_fun_table]). ACL2 functions are also
    first order, so a function that calls through one of its trait bounds is
    printed once per instance of the bound it is used at (see [dict]): trait
    methods, and with them closures, become calls to known functions. What is
    not handled is a function value that is not a trait instance: a backward
    function outside the shapes the let printers recognize.

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

(* A name that ends in a brace ends in a dash: the type of a closure,
   f::{closure}, or an impl. *)
let trim_dashes (s : string) : string =
  let n = ref (String.length s) in
  while !n > 0 && s.[!n - 1] = '-' do
    decr n
  done;
  String.sub s 0 !n

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
  | CloIterMutBack of { tyname : string }
      (** [slice::iter_mut]'s backward: on the {lst, pos} iterator model the
          final write-back is reading the list back out: applying to [im]
          prints (tyname->lst im) *)
  | CloZipBack of { tyname : string }
      (** [Iterator::zip]'s backward: recover the &mut side, i.e. the [a]
          component: applying to [z] prints (tyname->a z) *)
  | CloNextBack
      (** the third component of IterMut/Zip::next's triple.  Applying it to
          [(iter, None)] is the identity (prints as the iterator); [Some]
          applications only occur inside the loop's wrap lambdas, which
          [defunct_lambda] rewrites wholesale, so any other use fails. *)
  | CloBackParam of { apply_fn : string }
      (** a loop function's defunctionalized back-continuation formal: the
          variable holds a LIST of pending write values (latest first) and
          applying it to [im] prints (apply_fn var im); see the companion
          -apply-back/-wb-some defuns emitted with the iterator models *)

(* Functions are keyed by (def_id, loop_id): Aeneas gives a loop function
   the SAME def_id as its wrapper, distinguished only by [loop_id]. *)
type fkey = FunDeclId.id * (LoopId.id * bool) option

let decl_key (d : Pure.fun_decl) : fkey = (d.def_id, d.loop_id)

let loop_suffix (lp : (LoopId.id * bool) option) : string =
  match lp with
  | None -> ""
  | Some (lp_id, is_body) ->
      "-loop" ^ LoopId.to_string lp_id ^ if is_body then "-body" else ""

(* Specialization of trait-generic code.

   A trait bound is a function-valued parameter in disguise: a function
   [total<S: Shape>(s: &S)] calls whatever [Shape::area] its caller picks, and
   ACL2 functions are first order.  So a function whose code depends on a
   trait bound is not printed once: it is printed once per INSTANCE of the
   bound it is used at, with the calls through the bound resolved to the
   functions of the impl.  This is what rustc's monomorphization does, except
   that only the trait instances are specialized: type arguments stay erased
   and const generics stay ordinary parameters, so one function still serves
   every type.

   A [dict] is a trait instance with nothing left open: an impl, applied to
   the instances its own trait clauses stand for (those its code depends on:
   [impl_rel]).  A builtin instance -- Copy, the Clone of a tuple, the Fn of a
   function item -- has no impl to look into. *)
type dict = DImpl of TraitImplId.id * dict list | DBuiltin

(* A function at an instance: one [dict] per trait clause in [fun_rel] *)
type inst_key = fkey * dict list

(* The payload is the name of the instance's defun *)
type inst_state =
  | InstInProgress of string
  | InstDone of string
  | InstFailed of string

type actx = {
  trans_ctx : trans_ctx;
  fun_names : string FunDeclId.Map.t;
  opaque_funs : FunDeclId.Set.t;
  global_names : string GlobalDeclId.Map.t;
  trans_funs : pure_fun_translation FunDeclId.Map.t;
  type_names : string TypeDeclId.Map.t;
  types : Pure.type_decl TypeDeclId.Map.t;
  trait_impls : Pure.trait_impl TraitImplId.Map.t;
  fun_rel : (fkey, TraitClauseId.id list) Hashtbl.t;
      (** the trait clauses of a function that its code depends on, in the
          order of the declaration ([compute_relevance]).  A function without
          any is printed once, as before; a bound that is never consulted
          (a [T: Copy], say) costs nothing. *)
  impl_rel : (TraitImplId.id, TraitClauseId.id list) Hashtbl.t;
      (** the same for a trait impl: the clauses its methods, constants and
          supertrait instances depend on *)
  mutable dict_env : (TraitClauseId.id * dict) list;
      (** the instance being printed: what the clauses in [fun_rel] of the
          current declaration stand for (empty outside an instance) *)
  insts : (inst_key, inst_state) Hashtbl.t;
  inst_names : (string, inst_key) Hashtbl.t;
  impl_long : (TraitImplId.id, unit) Hashtbl.t;
      (** the impls whose instances go by the impl's own name
          ([compute_impl_naming]) *)
  mutable inst_stack : inst_key list;
      (** the instances being generated, innermost first *)
  mutable inst_log : (inst_key * string) list;
      (** the instances generated, latest first *)
  inst_out : Buffer.t;
      (** the text of the instances generated since the last declaration was
          written out: they go before the declaration that asked for them *)
  mutable printing : fkey list;
      (** the declarations of the group being printed that are not out yet *)
  mutable gensym : int;
  mutable cg_names : (ConstGenericVarId.id * string) list;
      (** the const generic parameters of the declaration being printed, and
          the formals they are printed as *)
  mutable skipped : (FunDeclId.id * (LoopId.id * bool) option) list;
      (** Functions whose emission failed: calls to them must fail too *)
  closures : (string, closure_kind) Hashtbl.t;
      (** live backward closures, keyed by bound-variable name *)
  pending_pairs : (string, closure_kind * string) Hashtbl.t;
      (** (subslice, backward) pair variables awaiting destructuring: maps
          the pair variable's name to the backward kind and the name the
          forward value was bound to *)
  std_used : (string, unit) Hashtbl.t;
      (** the modeled std functions the crate's own code calls, by the name
          of the defun the call prints (for indexing by a range, the name
          with its range-kind suffix): models nobody calls are not emitted *)
  pending_triples : (string, unit) Hashtbl.t;
      (** variables bound to an IterMut/Zip::next result awaiting their
          (elem option, iter, next_back) destructuring: the synthesized
          next returns (cons opt iter), so the destructure binds car/cdr
          and registers next_back as [CloNextBack] *)
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

(* ------------------------------------------------------------ std models *)

let str_contains (name : string) (sub : string) : bool =
  try
    ignore (Str.search_forward (Str.regexp_string sub) name 0);
    true
  with Not_found -> false

let str_starts (name : string) (p : string) : bool =
  String.length name >= String.length p
  && String.sub name 0 (String.length p) = p

(* The standard-library functions the backend models by hand.

   The input is polymorphic LLBC (charon's stock `--preset=aeneas`): each of
   these is ONE generic declaration, opaque in core/alloc (the real bodies go
   through ub_checks, raw pointers or trait clauses).  A declaration is
   recognized by its Rust NAME PATTERN -- the mechanism the reference backends
   use for their builtin tables (ExtractBuiltin) -- and gets a stable ACL2
   name chosen here wherever the mangled impl path would carry charon's
   internal clause names.  One model serves every instantiation, so the call
   sites check that the instantiation is one the model is valid for
   ([std_call_to_acl2]).

   A kind is realized in one of three ways:
   - a defun synthesized at the declaration ([synth_std_body]);
   - a form printed at the call site (array repeat, array-to-slice, indexing
     by usize);
   - a shape recognized at a let, for the calls that return a backward
     function (iter_mut, zip, mutable indexing, mutable array-to-slice). *)
type std_fun =
  | StdRangeNext  (** <Range<A> as Iterator>::next *)
  | StdRangeNextBack  (** <Range<A> as DoubleEndedIterator>::next_back *)
  | StdIterRev  (** Iterator::rev *)
  | StdRevNext  (** <Rev<I> as Iterator>::next *)
  | StdIterStepBy  (** Iterator::step_by *)
  | StdStepByNext  (** <StepBy<I> as Iterator>::next *)
  | StdSliceIter  (** <[T]>::iter *)
  | StdSliceIterMut  (** <[T]>::iter_mut *)
  | StdSliceIntoIter  (** <&[T] as IntoIterator>::into_iter *)
  | StdSliceIterNext  (** <slice::Iter<T> as Iterator>::next *)
  | StdSliceIterMutNext  (** <slice::IterMut<T> as Iterator>::next *)
  | StdIterZip  (** Iterator::zip *)
  | StdZipNext  (** <Zip<A, B> as Iterator>::next *)
  | StdBitXorAssignRef  (** <uN as BitXorAssign<&uN>>::bitxor_assign *)
  | StdArrayIndex  (** <[T; N] as Index<I>>::index *)
  | StdArrayIndexMut  (** <[T; N] as IndexMut<I>>::index_mut *)
  | StdSliceIndex  (** <[T] as Index<I>>::index *)
  | StdSliceIndexMut  (** <[T] as IndexMut<I>>::index_mut *)
  | StdVecIndex  (** <Vec<T> as Index<I>>::index *)
  | StdVecIndexMut  (** <Vec<T> as IndexMut<I>>::index_mut *)
  | StdArrayTryFromSlice  (** <[T; N] as TryFrom<&[T]>>::try_from *)
  | StdResultUnwrap  (** Result::unwrap *)
  | StdArrayRepeat  (** core::array::repeat, i.e. [x; N] *)
  | StdArrayAsSlice  (** <[T; N]>::as_slice, the &[T; N] -> &[T] coercion *)
  | StdArrayAsMutSlice  (** <[T; N]>::as_mut_slice *)

(* (name pattern, kind, ACL2 name).  [None] keeps the mangled Rust path,
   which for inherent and provided methods is already stable.  To write a
   new entry, run with ACL2_DEBUG_PATTERNS set: it prints every declaration's
   pattern next to its mangled name. *)
let std_fun_table : (string * std_fun * string option) list =
  [
    ( "core::iter::range::{core::iter::traits::iterator::Iterator<core::ops::range::Range<@A>, \
       @A>}::next",
      StdRangeNext,
      Some "core-ops-range-range-next" );
    ( "core::iter::range::{core::iter::traits::double_ended::DoubleEndedIterator<core::ops::range::Range<@A>, \
       @A>}::next_back",
      StdRangeNextBack,
      Some "core-ops-range-range-next-back" );
    ("core::iter::traits::iterator::Iterator::rev", StdIterRev, None);
    ( "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, \
       @Item>}::next",
      StdRevNext,
      Some "core-iter-adapters-rev-rev-next" );
    ("core::iter::traits::iterator::Iterator::step_by", StdIterStepBy, None);
    ( "core::iter::adapters::step_by::{core::iter::traits::iterator::Iterator<core::iter::adapters::step_by::StepBy<@I>, \
       @Item>}::next",
      StdStepByNext,
      Some "core-iter-adapters-step-by-stepby-next" );
    ("core::slice::{[@T]}::iter", StdSliceIter, None);
    ("core::slice::{[@T]}::iter_mut", StdSliceIterMut, None);
    ( "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, \
       core::slice::iter::Iter<'a, @T>>}::into_iter",
      StdSliceIntoIter,
      Some "core-slice-iter-into-iter" );
    ( "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, \
       @T>, &'a @T>}::next",
      StdSliceIterNext,
      Some "core-slice-iter-iter-next" );
    ( "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::IterMut<'a, \
       @T>, &'a mut @T>}::next",
      StdSliceIterMutNext,
      Some "core-slice-iter-itermut-next" );
    ("core::iter::traits::iterator::Iterator::zip", StdIterZip, None);
    ( "core::iter::adapters::zip::{core::iter::traits::iterator::Iterator<core::iter::adapters::zip::Zip<@A, \
       @B>, (@ItemA, @ItemB)>}::next",
      StdZipNext,
      Some "core-iter-adapters-zip-zip-next" );
    ( "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index",
      StdArrayIndex,
      Some "core-array-index" );
    ( "core::array::{core::ops::index::IndexMut<[@T; @N], @I, @O>}::index_mut",
      StdArrayIndexMut,
      Some "core-array-index-mut" );
    ( "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index",
      StdSliceIndex,
      Some "core-slice-index" );
    ( "core::slice::index::{core::ops::index::IndexMut<[@T], @I, @O>}::index_mut",
      StdSliceIndexMut,
      Some "core-slice-index-mut" );
    ( "alloc::vec::{core::ops::index::Index<alloc::vec::Vec<@T>, @I, @O>}::index",
      StdVecIndex,
      Some "alloc-vec-vec-index" );
    ( "alloc::vec::{core::ops::index::IndexMut<alloc::vec::Vec<@T>, @I, \
       @O>}::index_mut",
      StdVecIndexMut,
      Some "alloc-vec-vec-index-mut" );
    ( "core::array::{core::convert::TryFrom<[@T; @N], &'0 [@T], \
       core::array::TryFromSliceError>}::try_from",
      StdArrayTryFromSlice,
      Some "core-array-try-from-slice" );
    ( "core::result::{core::result::Result<@T, @E>}::unwrap",
      StdResultUnwrap,
      Some "core-result-result-unwrap" );
    ("core::array::repeat", StdArrayRepeat, None);
    ("core::array::{[@T; @N]}::as_slice", StdArrayAsSlice, None);
    ("core::array::{[@T; @N]}::as_mut_slice", StdArrayAsMutSlice, None);
  ]
  @ List.map
      (fun t ->
        ( "core::ops::bit::{core::ops::bit::BitXorAssign<" ^ t ^ ", &'0 " ^ t
          ^ ">}::bitxor_assign",
          StdBitXorAssignRef,
          Some (t ^ "-bitxor-assign-ref") ))
      [ "u8"; "u16"; "u32"; "u64"; "u128"; "usize" ]

(* The modeled declarations of the crate being printed, by ACL2 name.  Filled
   by [extract_crate] (one crate per run). *)
let std_kind_tbl : (string, std_fun) Hashtbl.t = Hashtbl.create 64

let std_kind (name : string) : std_fun option =
  Hashtbl.find_opt std_kind_tbl name

let is_std (k : std_fun) (name : string) : bool = std_kind name = Some k

(* Does the kind have a defun at its declaration ([synth_std_body])?  The
   others are printed at their call sites or recognized at a let. *)
let std_has_defun (k : std_fun) : bool =
  match k with
  | StdRangeNext | StdRangeNextBack | StdIterRev | StdRevNext | StdIterStepBy
  | StdStepByNext | StdSliceIter | StdSliceIntoIter | StdSliceIterNext
  | StdSliceIterMutNext | StdZipNext | StdBitXorAssignRef | StdArrayIndex
  | StdSliceIndex | StdArrayTryFromSlice | StdResultUnwrap -> true
  | StdSliceIterMut | StdIterZip | StdArrayIndexMut | StdSliceIndexMut
  | StdVecIndex | StdVecIndexMut | StdArrayRepeat | StdArrayAsSlice
  | StdArrayAsMutSlice -> false

let is_slice_iter_mut_ctor : string -> bool = is_std StdSliceIterMut
let is_slice_itermut_next : string -> bool = is_std StdSliceIterMutNext
let is_zip_next : string -> bool = is_std StdZipNext
let is_zip_ctor : string -> bool = is_std StdIterZip

(* The iterator MODEL types, keyed on the mangled names of the (opaque,
   generic) declarations.  One defprod serves every instantiation: the
   element types are erased to any-p and the {lst, pos} / {a, b} shape is
   instantiation-uniform. *)
let is_itermut_model_ty (tname : string) : bool =
  tname = "core-slice-iter-itermut"

let is_iter_model_ty (tname : string) : bool = tname = "core-slice-iter-iter"
let is_zip_model_ty (tname : string) : bool = tname = "core-iter-adapters-zip-zip"

let is_stepby_model_ty (tname : string) : bool =
  tname = "core-iter-adapters-step-by-stepby"

(* core::ops::Range / RangeTo / RangeFrom, by the mangled name of the (generic)
   struct *)
type range_kind = RkRange | RkRangeTo | RkRangeFrom

let range_kind_of_type_name (tname : string) : range_kind option =
  match tname with
  | "core-ops-range-range" -> Some RkRange
  | "core-ops-range-rangeto" -> Some RkRangeTo
  | "core-ops-range-rangefrom" -> Some RkRangeFrom
  | _ -> None

let range_kind_suffix (k : range_kind) : string =
  match k with
  | RkRange -> "range"
  | RkRangeTo -> "rangeto"
  | RkRangeFrom -> "rangefrom"

let ty_is_int (t : ty) : bool =
  match t with
  | TLiteral (TInt _ | TUInt _) -> true
  | _ -> false

let ty_is_usize (t : ty) : bool =
  match t with
  | TLiteral (TUInt Usize) -> true
  | _ -> false

(* Is [t] a Range / RangeTo / RangeFrom whose bounds satisfy [elem]? *)
let ty_range_kind (ctx : actx) (elem : ty -> bool) (t : ty) : range_kind option
    =
  match t with
  | TAdt (TAdtId id, { types = [ a ]; _ }) when elem a ->
      Option.bind
        (TypeDeclId.Map.find_opt id ctx.type_names)
        range_kind_of_type_name
  | _ -> None

let ty_adt_name (ctx : actx) (t : ty) : string option =
  match t with
  | TAdt (TAdtId id, _) -> TypeDeclId.Map.find_opt id ctx.type_names
  | _ -> None

let fun_std_kind (ctx : actx) (id : FunDeclId.id) : std_fun option =
  Option.bind (FunDeclId.Map.find_opt id ctx.fun_names) std_kind

(* The index type of a call to one of the Index / IndexMut impls: their
   type parameters are <T, I, ..>. *)
let index_ty_arg (g : generic_args) : ty option =
  match g.types with
  | _ :: i :: _ -> Some i
  | _ -> None

(* &mut a[r] with r a Range / RangeTo / RangeFrom<usize>, a an array or slice *)
let is_range_index_mut (ctx : actx) (id : FunDeclId.id) (g : generic_args) :
    bool =
  match fun_std_kind ctx id with
  | Some (StdArrayIndexMut | StdSliceIndexMut) ->
      Option.fold ~none:false
        ~some:(fun t -> ty_range_kind ctx ty_is_usize t <> None)
        (index_ty_arg g)
  | _ -> false

(* &mut v[i] on a Vec (on arrays and slices Aeneas itself turns the call into
   the pure [IndexMutAtIndex]) *)
let is_vec_elem_index_mut (ctx : actx) (id : FunDeclId.id) (g : generic_args) :
    bool =
  match fun_std_kind ctx id with
  | Some StdVecIndexMut ->
      Option.fold ~none:false ~some:ty_is_usize (index_ty_arg g)
  | _ -> false

(* The operator, comparison and clone methods of the integer types: the std
   impls behind [x + y], [x < y], [x.clone()] where they are written in
   generic code, and so are calls through an [Add], [PartialOrd], [Clone]
   bound.  (name pattern, primitive, whether the primitive returns a
   [result]).  The patterns name the impl by its trait instantiation, as in
   [std_fun_table]: Add<Self, Rhs, Output>, PartialOrd<Self, Rhs>, Clone<Self>. *)
let std_prim_table : (string * string * bool) list =
  let uints = [ "u8"; "u16"; "u32"; "u64"; "u128"; "usize" ] in
  let sints = [ "i8"; "i16"; "i64"; "i128"; "isize" ] in
  (* comparisons are ACL2's own, and a clone is the value *)
  let cmp (t : string) =
    List.map
      (fun (tr, meth, prim) ->
        ( Printf.sprintf "core::cmp::impls::{core::cmp::%s<%s, %s>}::%s" tr t t
            meth,
          prim,
          false ))
      [
        ("PartialEq", "eq", "equal");
        ("PartialEq", "ne", "/=");
        ("PartialOrd", "lt", "<");
        ("PartialOrd", "le", "<=");
        ("PartialOrd", "gt", ">");
        ("PartialOrd", "ge", ">=");
      ]
    @ [
        ( Printf.sprintf "core::clone::impls::{core::clone::Clone<%s>}::clone" t,
          "identity",
          false );
      ]
  in
  let op (m : string) (tr : string) (meth : string) (t : string) (prim : string)
      (monadic : bool) : string * string * bool =
    ( Printf.sprintf "core::ops::%s::{core::ops::%s::%s<%s, %s, %s>}::%s" m m tr
        t t t meth,
      t ^ "-" ^ prim,
      monadic )
  in
  let arith (t : string) =
    [
      op "arith" "Add" "add" t "add" true;
      op "arith" "Sub" "sub" t "sub" true;
      op "arith" "Mul" "mul" t "mul" true;
      op "arith" "Div" "div" t "div" true;
      op "arith" "Rem" "rem" t "rem" true;
    ]
  in
  let bits (t : string) =
    [
      op "bit" "BitXor" "bitxor" t "xor" false;
      op "bit" "BitAnd" "bitand" t "and" false;
      op "bit" "BitOr" "bitor" t "or" false;
    ]
  in
  List.concat_map arith (uints @ sints)
  (* the primitives book has no i32-mul / i32-rem *)
  @ [
      op "arith" "Add" "add" "i32" "add" true;
      op "arith" "Sub" "sub" "i32" "sub" true;
      op "arith" "Div" "div" "i32" "div" true;
    ]
  @ List.concat_map bits uints
  @ List.concat_map cmp (uints @ sints @ [ "i32" ])
  @ [
      ("core::cmp::impls::{core::cmp::PartialEq<bool, bool>}::eq", "equal", false);
      ("core::cmp::impls::{core::cmp::PartialEq<bool, bool>}::ne", "/=", false);
      ("core::clone::impls::{core::clone::Clone<bool>}::clone", "identity", false);
    ]

(* The declarations of the crate being printed that [std_prim_table]
   recognizes, by mangled name.  Filled by [extract_crate]. *)
let std_prim_tbl : (string, string * bool) Hashtbl.t = Hashtbl.create 64

(* Opaque std functions that map to an operation of the primitives book:
   the primitive's name, and whether the primitive returns a [result].  Keyed
   on the mangled name (plain Rust paths: inherent methods of integers, Vec
   and slices), after the declarations recognized by pattern. *)
let std_fun_mapping (mangled : string) : (string * bool) option =
  match Hashtbl.find_opt std_prim_tbl mangled with
  | Some p -> Some p
  | None ->
  let ok_types = [ "u8"; "u16"; "u32"; "u64"; "u128"; "usize" ] in
  let try_wrap op =
    List.find_map
      (fun t ->
        if mangled = "core-num-" ^ t ^ "-wrapping-" ^ op then
          Some (t ^ "-wrapping-" ^ op, true)
        else None)
      ok_types
  in
  let try_rot dir =
    List.find_map
      (fun t ->
        if mangled = "core-num-" ^ t ^ "-rotate-" ^ dir then
          Some (t ^ "-rotate-" ^ dir, true)
        else None)
      ok_types
  in
  match List.find_map try_wrap [ "add"; "sub"; "mul" ] with
  | Some s -> Some s
  | None -> (
      match List.find_map try_rot [ "left"; "right" ] with
      | Some s -> Some s
      | None -> (
          match mangled with
          | "alloc-vec-alloc-vec-vec-t-push" -> Some ("vec-push", true)
          | "alloc-vec-alloc-vec-vec-t-insert" -> Some ("vec-insert", true)
          | "alloc-vec-alloc-vec-vec-t-new" -> Some ("vec-new", true)
          (* the capacity is not part of the list model *)
          | "alloc-vec-alloc-vec-vec-t-with-capacity" -> Some ("vec-new", true)
          | "alloc-vec-alloc-vec-vec-t-len" -> Some ("vec-len", true)
          | "core-slice-t-len" -> Some ("vec-len", true)
          | "core-slice-t-copy-from-slice" ->
              Some ("slice-copy-from-slice", true)
          (* LE byte plumbing *)
          | "core-num-u32-from-le-bytes" -> Some ("u32-from-le-bytes", false)
          | "core-num-u32-to-le-bytes" -> Some ("u32-to-le-bytes", false)
          | _ -> None))

(* Aeneas treats some of the functions above as infallible and binds their
   results without the monad ([T]::len, Vec::len, Vec::new), where the
   primitive returns a [result].  The value they compute, as a plain form. *)
let prim_pure_form (prim : string) (args_s : string list) : string option =
  match (prim, args_s) with
  | "vec-len", [ v ] -> Some ("(len " ^ v ^ ")")
  | "vec-new", [] -> Some "nil"
  | _ -> None

let fun_name (span : Meta.span) (ctx : actx) (id : FunDeclId.id) : string =
  let name = FunDeclId.Map.find_opt id ctx.fun_names in
  let what = Option.value name ~default:"(unnamed)" in
  match name with
  (* Modeled std functions resolve even though they are opaque. *)
  | Some s when Option.fold ~none:false ~some:std_has_defun (std_kind s) -> s
  | _ ->
      if FunDeclId.Set.mem id ctx.opaque_funs then
        [%craise] span
          ("ACL2: call to an opaque/std function with no ACL2 mapping yet: "
         ^ what)
      else (
        match name with
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
  | VScalar (Values.UnsignedInteger (_, v)) -> Z.to_string v
  | VScalar (Values.SignedInteger (_, v)) -> Z.to_string v
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

(* A const generic argument, as a value.  Const generics are ordinary
   parameters on the ACL2 side: a function with const generic parameters
   takes them as its first formals ([fun_decl_to_acl2]), and a call passes
   them first. *)
let const_generic_to_acl2 (span : Meta.span) (ctx : actx) (cg : const_generic)
    : string =
  match cg with
  | CgValue lit -> literal_to_acl2 span lit
  | CgVar (Free id) -> (
      match List.assoc_opt id ctx.cg_names with
      | Some n -> n
      | None -> [%craise] span "ACL2: unbound const generic variable")
  | CgVar (Bound _) -> [%craise] span "ACL2: bound const generic variable"
  | CgGlobal gid -> (
      match GlobalDeclId.Map.find_opt gid ctx.global_names with
      | Some n -> n
      | None -> [%craise] span "ACL2: const generic refers to an unknown global")

(* Recognize a constructor of the core::option::Option enum: returns the
   variant name (lowercased: "none"/"some") and the payload arguments. *)
let destruct_option_cons (ctx : actx) (e : texpr) : (string * texpr list) option
    =
  let head, args = destruct_apps (unmeta e) in
  match (unmeta head).e with
  | Qualif { id = AdtCons { adt_id = TAdtId id; variant_id = Some vid }; _ }
    -> (
      match TypeDeclId.Map.find_opt id ctx.types with
      | Some { kind = Enum variants; _ } ->
          let v = VariantId.nth variants vid in
          Some (String.lowercase_ascii v.variant_name, args)
      | _ -> None)
  | _ -> None

(* -------------------------------------------------------- specialization *)

let find_fun_decl (ctx : actx) ((id, lp) : fkey) : Pure.fun_decl option =
  Option.bind (FunDeclId.Map.find_opt id ctx.trans_funs)
    (fun (t : pure_fun_translation) ->
      List.find_opt
        (fun (d : Pure.fun_decl) -> d.loop_id = lp)
        ((t.f :: t.loops) @ t.bodies))

(* Is the function printed from its own body?  A modeled std function, or one
   that maps to a primitive, is the same whatever trait instances it is
   given. *)
let fun_is_code (ctx : actx) (id : FunDeclId.id) : bool =
  match FunDeclId.Map.find_opt id ctx.fun_names with
  | None -> false
  | Some n -> std_kind n = None && std_fun_mapping n = None

let fun_rel (ctx : actx) (k : fkey) : TraitClauseId.id list =
  Option.value (Hashtbl.find_opt ctx.fun_rel k) ~default:[]

let impl_rel (ctx : actx) (i : TraitImplId.id) : TraitClauseId.id list =
  Option.value (Hashtbl.find_opt ctx.impl_rel i) ~default:[]

(* Of the trait references given for [clauses], the ones for the clauses in
   [rel].  None if the references do not line up with the clauses: not as
   many, or one for another trait than its clause's. *)
let refs_at (clauses : trait_param list) (rel : TraitClauseId.id list)
    (refs : trait_ref list) : trait_ref list option =
  if
    List.length clauses <> List.length refs
    || not
         (List.for_all2
            (fun (p : trait_param) (r : trait_ref) ->
              p.trait_id = r.trait_decl_ref.trait_decl_id)
            clauses refs)
  then None
  else
    Some
      (List.filter_map
         (fun ((p : trait_param), r) ->
           if List.mem p.clause_id rel then Some r else None)
         (List.combine clauses refs))

(* The trait clauses (of the enclosing declaration) that a trait instance is
   built from, as far as anyone will look: the arguments of an impl count
   only for the clauses the impl depends on. *)
let rec inst_clauses (ctx : actx) (tid : trait_instance_id) :
    TraitClauseId.id list =
  match tid with
  | Clause (Free c) -> [ c ]
  | Clause (Bound _) | Self | BuiltinOrAuto _ | UnknownTrait _ -> []
  | ParentClause (inst, _, _) -> inst_clauses ctx inst
  | TraitImpl (i, g) -> (
      match TraitImplId.Map.find_opt i ctx.trait_impls with
      | None -> []
      | Some (impl : Pure.trait_impl) ->
          let refs =
            match
              refs_at impl.generics.trait_clauses (impl_rel ctx i) g.trait_refs
            with
            | Some rs -> rs
            | None -> g.trait_refs
          in
          List.concat_map
            (fun (r : trait_ref) -> inst_clauses ctx r.trait_id)
            refs)

(* Which trait clauses does the code of each function, and of each impl,
   depend on?  A clause matters to a function when its body calls a method or
   reads a constant of an instance built from the clause, or passes such an
   instance to a function for a clause that matters there; to an impl, when
   one of its methods, constants or supertrait instances is given such an
   instance.  The least fixed point: the tables only grow. *)
let compute_relevance (ctx : actx) : unit =
  let changed = ref true in
  let add tbl k (cs : TraitClauseId.id list) : unit =
    let old = Option.value (Hashtbl.find_opt tbl k) ~default:[] in
    let fresh =
      List.filter (fun c -> not (List.mem c old)) (List.sort_uniq compare cs)
    in
    if fresh <> [] then (
      Hashtbl.replace tbl k (old @ fresh);
      changed := true)
  in
  let ref_uses (r : trait_ref) : TraitClauseId.id list =
    inst_clauses ctx r.trait_id
  in
  (* giving the generic arguments [g] to the function [k] *)
  let call_uses (k : fkey) (g : generic_args) : TraitClauseId.id list =
    match (fun_rel ctx k, find_fun_decl ctx k) with
    | [], _ | _, None -> []
    | rel, Some d ->
        let refs =
          match refs_at d.signature.generics.trait_clauses rel g.trait_refs with
          | Some rs -> rs
          | None -> g.trait_refs
        in
        List.concat_map ref_uses refs
  in
  let body_uses (d : Pure.fun_decl) : TraitClauseId.id list =
    let acc = ref [] in
    let visitor =
      object
        inherit [_] iter_expr

        method! visit_qualif _ q =
          match q.id with
          | FunOrOp (Fun (FromLlbc (FunId id, lp))) ->
              acc := call_uses (id, lp) q.generics @ !acc
          | FunOrOp (Fun (FromLlbc (TraitMethod (tr, _), _))) ->
              (* which function gets the instances given for the method's
                 own trait clauses depends on the instance: count them all *)
              acc :=
                ref_uses tr
                @ List.concat_map ref_uses q.generics.trait_refs
                @ !acc
          | TraitConst (tr, _) | MkDynTrait tr -> acc := ref_uses tr @ !acc
          | _ -> ()
      end
    in
    (match d.body with
    | Some b -> visitor#visit_texpr () b.body
    | None -> ());
    !acc
  in
  while !changed do
    changed := false;
    FunDeclId.Map.iter
      (fun id (t : pure_fun_translation) ->
        if fun_is_code ctx id then
          List.iter
            (fun (d : Pure.fun_decl) ->
              add ctx.fun_rel (decl_key d) (body_uses d))
            ((t.f :: t.loops) @ t.bodies))
      ctx.trans_funs;
    TraitImplId.Map.iter
      (fun i (impl : Pure.trait_impl) ->
        let of_methods =
          List.concat_map
            (fun ((_, _, b) : _ * _ * fun_decl_ref binder) ->
              call_uses
                (b.binder_value.fun_id, None)
                b.binder_value.fun_generics)
            impl.methods
        in
        let of_parents = List.concat_map ref_uses impl.parent_trait_refs in
        let of_consts =
          List.concat_map
            (fun ((_, _, g) : _ * _ * global_decl_ref) ->
              List.concat_map ref_uses g.global_generics.trait_refs)
            impl.consts
        in
        add ctx.impl_rel i (of_methods @ of_parents @ of_consts))
      ctx.trait_impls
  done;
  (* keep each set in the order of the declaration's clauses *)
  let in_order (clauses : trait_param list) (cs : TraitClauseId.id list) :
      TraitClauseId.id list =
    List.filter_map
      (fun (p : trait_param) ->
        if List.mem p.clause_id cs then Some p.clause_id else None)
      clauses
  in
  Hashtbl.filter_map_inplace
    (fun k cs ->
      match find_fun_decl ctx k with
      | Some d -> Some (in_order d.signature.generics.trait_clauses cs)
      | None -> Some cs)
    ctx.fun_rel;
  Hashtbl.filter_map_inplace
    (fun i cs ->
      match TraitImplId.Map.find_opt i ctx.trait_impls with
      | Some (impl : Pure.trait_impl) ->
          Some (in_order impl.generics.trait_clauses cs)
      | None -> Some cs)
    ctx.impl_rel

let find_impl (span : Meta.span) (ctx : actx) (i : TraitImplId.id) :
    Pure.trait_impl =
  match TraitImplId.Map.find_opt i ctx.trait_impls with
  | Some impl -> impl
  | None -> [%craise] span "ACL2: reference to an unknown trait impl"

(* What the clauses of an impl stand for in the instance [DImpl (i, dargs)] *)
let impl_env (span : Meta.span) (ctx : actx) (i : TraitImplId.id)
    (dargs : dict list) : (TraitClauseId.id * dict) list =
  let rel = impl_rel ctx i in
  if List.length rel <> List.length dargs then
    [%craise] span "ACL2: internal: ill-formed trait instance"
  else List.combine rel dargs

(* Close a trait instance: [env] gives what the trait clauses in scope stand
   for.  The method table of an impl has a second scope, the trait clauses of
   the method itself ([fn visit<S: Shape>(&self, ..)]), which [meth] gives;
   they are the bound variables there.  (The index of a bound variable is not
   to be relied on -- Aeneas drops the region binders of charon's trait
   references without renumbering -- but nothing else binds trait clauses.) *)
let rec resolve_ref ?(meth : (TraitClauseId.id * dict) list = [])
    (span : Meta.span) (ctx : actx) (env : (TraitClauseId.id * dict) list)
    (r : trait_ref) : dict =
  let d = resolve_inst ~meth span ctx env r.trait_id in
  (* The impl has to be an impl of the trait the reference is for: if it
     were not -- a parent clause or an argument out of place -- the methods
     of another trait would be looked up in it. *)
  (match d with
  | DImpl (i, _) ->
      let impl = find_impl span ctx i in
      if impl.impl_trait.trait_decl_id <> r.trait_decl_ref.trait_decl_id then
        [%craise] span "ACL2: internal: a trait instance of the wrong trait"
  | DBuiltin -> ());
  d

and resolve_inst ?(meth : (TraitClauseId.id * dict) list = [])
    (span : Meta.span) (ctx : actx) (env : (TraitClauseId.id * dict) list)
    (tid : trait_instance_id) : dict =
  match tid with
  | Clause (Free c) -> (
      match List.assoc_opt c env with
      | Some d -> d
      | None ->
          (* [fun_rel] puts every clause a function consults in its
             instances; what is left is code that is never specialized *)
          [%craise] span
            "ACL2: use of a trait bound outside a function (a constant that \
             depends on the trait bounds of its impl is not supported yet)")
  | Clause (Bound (_, c)) -> (
      match List.assoc_opt c meth with
      | Some d -> d
      | None -> [%craise] span "ACL2: internal: a bound trait clause")
  | TraitImpl (i, g) -> (
      let impl = find_impl span ctx i in
      match refs_at impl.generics.trait_clauses (impl_rel ctx i) g.trait_refs with
      | Some refs ->
          DImpl (i, List.map (resolve_ref ~meth span ctx env) refs)
      | None ->
          [%craise] span
            "ACL2: internal: a trait impl given the wrong number of instances")
  | ParentClause (inst, _, pid) -> (
      (* the supertrait instance of an instance: recorded in its impl *)
      match resolve_inst ~meth span ctx env inst with
      | DImpl (i, dargs) -> (
          let impl = find_impl span ctx i in
          match TraitClauseId.nth_opt impl.parent_trait_refs pid with
          | Some r -> resolve_ref span ctx (impl_env span ctx i dargs) r
          | None ->
              [%craise] span "ACL2: internal: missing supertrait instance")
      | DBuiltin ->
          [%craise] span "ACL2: supertrait of a builtin trait instance")
  | BuiltinOrAuto _ -> DBuiltin
  | Self -> [%craise] span "ACL2: Self trait instance outside a trait"
  | UnknownTrait s -> [%craise] span ("ACL2: unknown trait instance: " ^ s)

(* The type an impl is for, when it has a name of its own (tr-sq, u32): what
   an instance of the impl is called in the name of a specialized function.
   A blanket impl ([impl<T: Shape> Describe for T]) is for a type variable. *)
let impl_self_head (ctx : actx) (impl : Pure.trait_impl) :
    [ `Name of string | `Var | `Other ] =
  match impl.impl_trait.decl_generics.types with
  | TLiteral lt :: _ when literal_type_is_integer lt ->
      `Name (int_ty_name (literal_as_integer lt))
  | TLiteral TBool :: _ -> `Name "bool"
  | TLiteral TChar :: _ -> `Name "char"
  | TAdt (TAdtId id, _) :: _ -> (
      match TypeDeclId.Map.find_opt id ctx.type_names with
      | Some s -> `Name s
      | None -> `Other)
  | TVar _ :: _ -> `Var
  | _ -> `Other

(* Which impls go by their own, long name (tr-impl-tr-shape-for-tr-wrap-u8)
   instead of the name of the type they are for: those that would share the
   short name with another impl of the same trait -- [Shape for Wrap<u8>] and
   [Shape for Wrap<u32>], [From<u8> for u64] and [From<u16> for u64].  The
   place of an instance in a name fixes its trait, so this is enough to keep
   the names apart; and it depends on the impls of the crate only, not on the
   order the instances are met in, so a name never changes its meaning. *)
let compute_impl_naming (ctx : actx) : unit =
  let impls = ref [] in
  TraitImplId.Map.iter
    (fun i (impl : Pure.trait_impl) -> impls := (i, impl) :: !impls)
    ctx.trait_impls;
  List.iter
    (fun (i, (impl : Pure.trait_impl)) ->
      let others =
        List.filter
          (fun (j, (o : Pure.trait_impl)) ->
            j <> i
            && o.impl_trait.trait_decl_id = impl.impl_trait.trait_decl_id)
          !impls
      in
      let long =
        match impl_self_head ctx impl with
        | `Other -> true
        | `Var -> others <> []
        | `Name s ->
            List.exists (fun (_, o) -> impl_self_head ctx o = `Name s) others
      in
      if long then Hashtbl.replace ctx.impl_long i ())
    !impls

(* The name of an instance: the type its impl is for, followed by the
   instances the impl is itself applied to (tr-two[tr-sq]).  A blanket impl
   is for whatever its one argument is for, and goes by that. *)
let rec dict_name (ctx : actx) (d : dict) : string =
  match d with
  | DBuiltin -> "builtin"
  | DImpl (i, args) -> (
      let args_s () =
        String.concat ""
          (List.map (fun a -> "[" ^ dict_name ctx a ^ "]") args)
      in
      match TraitImplId.Map.find_opt i ctx.trait_impls with
      | None -> "impl" ^ TraitImplId.to_string i ^ args_s ()
      | Some (impl : Pure.trait_impl) -> (
          let full () =
            trim_dashes (mangle_name ctx.trans_ctx impl.item_meta.name)
            ^ args_s ()
          in
          if Hashtbl.mem ctx.impl_long i then full ()
          else
            match (impl_self_head ctx impl, args) with
            | `Name s, _ -> s ^ args_s ()
            | `Var, [ a ] -> dict_name ctx a
            | _ -> full ()))

(* The name of the defun for an instance: the function's name followed by
   one bracketed instance per trait clause the function depends on, e.g.
   tr-total[tr-sq][tr-rect] -- the convention of the SOFT library for the
   instances of a second-order function. *)
let name_instance (span : Meta.span) (ctx : actx) (key : inst_key) : string =
  let (id, lp), dicts = key in
  let base =
    match FunDeclId.Map.find_opt id ctx.fun_names with
    | Some s -> s ^ loop_suffix lp
    | None -> [%craise] span "ACL2: function without a name"
  in
  let n =
    base
    ^ String.concat "" (List.map (fun d -> "[" ^ dict_name ctx d ^ "]") dicts)
  in
  (match Hashtbl.find_opt ctx.inst_names n with
  | Some k when k <> key ->
      [%craise] span ("ACL2: two specializations with the same name: " ^ n)
  | _ -> ());
  Hashtbl.replace ctx.inst_names n key;
  n

(* Printing a declaration keeps state in the context (bound-variable
   numbering, registered backward closures, the names of the const generics,
   the instance): run [f], which prints another declaration, and put the
   state back. *)
let with_saved_decl_state (ctx : actx) (f : unit -> 'a) : 'a =
  let gensym = ctx.gensym in
  let cg_names = ctx.cg_names in
  let dict_env = ctx.dict_env in
  let closures = Hashtbl.copy ctx.closures in
  let pending_pairs = Hashtbl.copy ctx.pending_pairs in
  let pending_triples = Hashtbl.copy ctx.pending_triples in
  let refill dst src =
    Hashtbl.reset dst;
    Hashtbl.iter (Hashtbl.replace dst) src
  in
  Fun.protect
    ~finally:(fun () ->
      ctx.gensym <- gensym;
      ctx.cg_names <- cg_names;
      ctx.dict_env <- dict_env;
      refill ctx.closures closures;
      refill ctx.pending_pairs pending_pairs;
      refill ctx.pending_triples pending_triples)
    f

(* Prints the defun of an instance: [fun_decl_to_acl2], which is defined
   after the expression printers that need it. *)
let print_instance_ref :
    (actx ->
    Pure.fun_decl ->
    string ->
    (TraitClauseId.id * dict) list ->
    string)
    ref =
  ref (fun _ _ _ _ -> raise (Failure "ExtractAcl2: instance printer not set"))

(* Rust rejects a generic function that calls itself at ever larger
   instances; this bounds the damage if one gets here. *)
let max_inst_depth = 64

(* The name of the defun for an instance, generating the defun the first
   time the instance is asked for.  The text goes to [ctx.inst_out], so the
   instances an instance needs come out before it, and all of them before
   the declaration being printed. *)
let instance_name (span : Meta.span) (ctx : actx) (key : inst_key) : string =
  match Hashtbl.find_opt ctx.insts key with
  | Some (InstDone n) -> n
  | Some (InstFailed n) ->
      [%craise] span ("ACL2: call to a function that was itself skipped: " ^ n)
  | Some (InstInProgress n) -> (
      match ctx.inst_stack with
      | top :: _ when top = key -> (* a recursive call *) n
      | _ ->
          [%craise] span
            ("ACL2: mutually recursive specializations are not supported yet: "
           ^ n))
  | None -> (
      let fk, dicts = key in
      let decl =
        match find_fun_decl ctx fk with
        | Some d -> d
        | None -> [%craise] span "ACL2: specialization of an unknown function"
      in
      let rel = fun_rel ctx fk in
      if List.length rel <> List.length dicts then
        [%craise] span "ACL2: internal: ill-formed specialization";
      let n = name_instance span ctx key in
      if List.length ctx.inst_stack >= max_inst_depth then
        [%craise] span
          ("ACL2: specializations nested too deep (polymorphic recursion?): "
         ^ n);
      Hashtbl.replace ctx.insts key (InstInProgress n);
      ctx.inst_stack <- key :: ctx.inst_stack;
      let res =
        with_saved_decl_state ctx (fun () ->
            match !print_instance_ref ctx decl n (List.combine rel dicts) with
            | s -> Ok s
            | exception CFailure err -> Error err.msg)
      in
      ctx.inst_stack <- List.tl ctx.inst_stack;
      match res with
      | Ok s ->
          Buffer.add_string ctx.inst_out (s ^ "\n\n");
          Hashtbl.replace ctx.insts key (InstDone n);
          ctx.inst_log <- (key, n) :: ctx.inst_log;
          n
      | Error msg ->
          Buffer.add_string ctx.inst_out
            (";; SKIPPED function " ^ n ^ ": " ^ msg ^ "\n\n");
          Hashtbl.replace ctx.insts key (InstFailed n);
          [%craise] span
            ("ACL2: call to a function that was itself skipped: " ^ n))

let rec texpr_to_acl2 (span : Meta.span) (ctx : actx) (env : venv) (e : texpr) :
    string =
  match e.e with
  | FVar id -> (
      match FVarId.Map.find_opt id env.fvars with
      | Some n -> n
      | None -> [%craise] span "ACL2: unbound free variable")
  | BVar v -> venv_bvar env v
  | CVar id -> (
      match List.assoc_opt id ctx.cg_names with
      | Some n -> n
      | None -> [%craise] span "ACL2: unbound const generic variable")
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
  (* Lambda arguments are defunctionalized ONLY at loop-function call
     sites (the back-continuation convention: the loop's arrow formal is
     data applied via -apply-back).  A lambda anywhere else keeps the loud
     v0 failure -- e.g. an identity closure in a RETURNED pair must not
     silently become nil. *)
  let is_loop_call =
    match head.e with
    | Qualif { id = FunOrOp (Fun (FromLlbc (FunId _, Some _))); _ } -> true
    | _ -> false
  in
  let arg_to_s (a : texpr) : string =
    match (unmeta a).e with
    | Lambda _ when is_loop_call -> defunct_lambda span ctx env a
    | Lambda _ ->
        [%craise] span
          "ACL2: lambda in output (backward function or closure); not \
           supported in v0 -- see the defunctionalization plan"
    | _ -> texpr_to_acl2 span ctx env a
  in
  let args_s = List.map arg_to_s args in
  (* Is the application a monadic value?  This is the AST's own answer to
     "can this call fail", which for std functions depends on Aeneas's
     builtin tables rather than on anything the printer knows. *)
  let monadic =
    match e.ty with
    | TAdt (TBuiltin TResult, _) -> true
    | _ -> false
  in
  match head.e with
  | Qualif q -> qualif_app_to_acl2 span ctx env q ~monadic args args_s
  | FVar _ | BVar _ -> (
      (* Application of a locally-bound function value.  The ONLY such
         values we accept are the backward closures of mutable subslice /
         array-to-slice / iterator borrows and the defunctionalized loop
         back-parameters, recorded at their let/binder sites: applying one
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
      match (Hashtbl.find_opt ctx.closures hname, args, args_s) with
      | Some (CloRangeBack { arr; lo; hi }), _, [ x ] ->
          sexp [ "vec-update-range"; arr; lo; hi; x ]
      | Some (CloElemBack { arr; idx }), _, [ x ] ->
          sexp [ "update-nth"; idx; x; arr ]
      | Some CloIdentityBack, _, [ x ] -> x
      | Some (CloIterMutBack { tyname }), _, [ x ] ->
          sexp [ tyname ^ "->lst"; x ]
      | Some (CloZipBack { tyname }), _, [ x ] -> sexp [ tyname ^ "->a"; x ]
      | Some (CloBackParam { apply_fn }), _, [ x ] ->
          sexp [ apply_fn; hname; x ]
      | Some CloNextBack, [ _; opt ], [ x_s; _ ] -> (
          (* next_back applied to None is the identity on the iterator;
             Some applications only occur inside wrap lambdas, which
             [defunct_lambda] consumes wholesale. *)
          match destruct_option_cons ctx opt with
          | Some ("none", []) -> x_s
          | _ ->
              [%craise] span
                "ACL2: next_back applied to Some outside a back-continuation \
                 lambda")
      | _ ->
          [%craise] span "ACL2: application of a function-typed variable (HO)")
  | _ -> [%craise] span "ACL2: unsupported application head"

(* Defunctionalize a lambda literal appearing as a call argument: the loop
   back-continuations.  On the ACL2 side the continuation is DATA -- the
   list of pending write-back values, latest first -- applied via the
   iterator model's -apply-back (see [CloBackParam]).  Exactly two shapes
   are accepted:
     fun im => im                                              ~>  nil
     fun im => let im1 = next_back im (Some v) in back im1     ~>  (cons v back)
   where [next_back] is a registered [CloNextBack] and [back] the enclosing
   loop's [CloBackParam] formal.  Anything else fails loudly (never a
   silent mistranslation). *)
and defunct_lambda (span : Meta.span) (ctx : actx) (env : venv) (lam : texpr) :
    string =
  (* On failure, restore the gensym counter (shape probing binds pattern
     variables) and fail with the same message as before this machinery
     existed: a skipped declaration must consume no gensyms, so the
     numbering of every later declaration stays byte-identical. *)
  let saved_gensym = ctx.gensym in
  let fail () : 'a =
    ctx.gensym <- saved_gensym;
    [%craise] span
      "ACL2: lambda in output (backward function or closure); not supported \
       in v0 -- see the defunctionalization plan"
  in
  match (unmeta lam).e with
  | Lambda (pat, body) -> (
      let env', names = bind_tpats ctx env [ pat ] in
      let lam_n =
        match names with
        | [ n ] -> n
        | _ -> fail ()
      in
      let var_name (env : venv) (e : texpr) : string option =
        match (unmeta e).e with
        | FVar id -> FVarId.Map.find_opt id env.fvars
        | BVar v -> ( try Some (venv_bvar env v) with _ -> None)
        | _ -> None
      in
      match (unmeta body).e with
      | (FVar _ | BVar _)
        when lam_n <> "&" && var_name env' body = Some lam_n -> "nil"
      | Let (false, pat2, rhs, body2) -> (
          (* rhs must be: next_back <lam binder> (Some payload) *)
          let rhs_head, rhs_args = destruct_apps (unmeta rhs) in
          let nb_ok =
            match var_name env' rhs_head with
            | Some n -> Hashtbl.find_opt ctx.closures n = Some CloNextBack
            | None -> false
          in
          let payload =
            match rhs_args with
            | [ a1; a2 ] when lam_n <> "&" && var_name env' a1 = Some lam_n
              -> (
                match destruct_option_cons ctx a2 with
                | Some ("some", [ p ]) -> Some p
                | _ -> None)
            | _ -> None
          in
          let env2, names2 = bind_tpats ctx env' [ pat2 ] in
          let let_n =
            match names2 with
            | [ n ] -> n
            | _ -> fail ()
          in
          let back_name =
            let b_head, b_args = destruct_apps (unmeta body2) in
            match (var_name env2 b_head, b_args) with
            | Some bn, [ barg ]
              when (match Hashtbl.find_opt ctx.closures bn with
                   | Some (CloBackParam _) -> true
                   | _ -> false)
                   && let_n <> "&"
                   && var_name env2 barg = Some let_n -> Some bn
            | _ -> None
          in
          match (nb_ok, payload, back_name) with
          | true, Some p, Some bn ->
              (* the payload lives under the lambda binder only *)
              "(cons " ^ texpr_to_acl2 span ctx env' p ^ " " ^ bn ^ ")"
          | _ -> fail ())
      | _ -> fail ())
  | _ -> fail ()

(* A call to the function [id] (loop [lp]) with the generic arguments [g].
   The trait references in [g] are in terms of the trait clauses of the
   declaration being printed -- or, for a function found in the method table
   of an impl, of that impl and of the method: [via] is then what the impl's
   clauses, and the method's, stand for. *)
and fun_call_to_acl2 (span : Meta.span) (ctx : actx) ~(monadic : bool)
    ~(via :
       ((TraitClauseId.id * dict) list * (TraitClauseId.id * dict) list) option)
    (id : FunDeclId.id) (lp : (LoopId.id * bool) option) (q : qualif)
    (g : generic_args) (args : texpr list) (args_s : string list) : string =
  let name = FunDeclId.Map.find_opt id ctx.fun_names in
  match Option.bind name std_kind with
  | Some k ->
      (* The models check the instantiation by its type arguments, which an
         instance does not record. *)
      if via <> None then
        [%craise] span
          ("ACL2: " ^ Option.get name
         ^ " called through a trait bound: the modeled std functions are \
            supported only where they are called directly")
      else std_call_to_acl2 span ctx k (Option.get name) q args args_s
  | None -> (
      (* opaque std function with a known primitive mapping wins first *)
      match Option.bind name std_fun_mapping with
      | Some (prim, prim_monadic) -> (
          let args_s = if prim = "vec-new" then [] else args_s in
          match (monadic, prim_monadic) with
          | true, true | false, false -> sexp (prim :: args_s)
          | true, false -> sexp [ "ok"; sexp (prim :: args_s) ]
          | false, true -> (
              match prim_pure_form prim args_s with
              | Some s -> s
              | None ->
                  [%craise] span
                    ("ACL2: " ^ prim
                   ^ " returns a result but the call is bound as a plain value"
                    )))
      | None ->
          let suffix = loop_suffix lp in
          if List.mem (id, lp) ctx.skipped then
            [%craise] span
              ("ACL2: call to a function that was itself skipped: "
              ^ Option.value name ~default:"(unnamed)"
              ^ suffix)
          else
            let base = fun_name span ctx id ^ suffix in
            let callee = find_fun_decl ctx (id, lp) in
            let name =
              match fun_rel ctx (id, lp) with
              | [] ->
                  (* An instance comes out before the declaration that asked
                     for it, so it cannot call that declaration back. *)
                  if ctx.inst_stack <> [] && List.mem (id, lp) ctx.printing then
                    [%craise] span
                      ("ACL2: recursion through a specialization is not \
                        supported yet: " ^ base);
                  base
              | rel ->
                  (* The callee depends on some of its trait clauses: call
                     its instance at what this call gives for them. *)
                  let clauses =
                    match callee with
                    | Some d -> d.signature.generics.trait_clauses
                    | None -> []
                  in
                  let refs =
                    match refs_at clauses rel g.trait_refs with
                    | Some rs -> rs
                    | None ->
                        [%craise] span
                          ("ACL2: internal: the trait instances do not match \
                            the trait clauses in a call to " ^ base)
                  in
                  let denv, meth =
                    Option.value via ~default:(ctx.dict_env, [])
                  in
                  let dicts = List.map (resolve_ref ~meth span ctx denv) refs in
                  instance_name span ctx ((id, lp), dicts)
            in
            (* const generics are the callee's first formals *)
            let cg_args =
              match callee with
              | Some d when d.signature.generics.const_generics <> [] ->
                  (* an instance does not record the const generic arguments
                     of its impl either *)
                  if via <> None then
                    [%craise] span
                      ("ACL2: " ^ base
                     ^ " called through a trait bound: a method with const \
                        generic parameters (not supported yet)");
                  List.map (const_generic_to_acl2 span ctx) g.const_generics
              | _ -> []
            in
            sexp ((name :: cg_args) @ args_s))

and qualif_app_to_acl2 (span : Meta.span) (ctx : actx) (_env : venv)
    (q : qualif) ~(monadic : bool) (args : texpr list) (args_s : string list) :
    string =
  match q.id with
  | FunOrOp (Fun (FromLlbc (FunId id, lp))) ->
      fun_call_to_acl2 span ctx ~monadic ~via:None id lp q q.generics args
        args_s
  | FunOrOp (Fun (FromLlbc (TraitMethod (tr, mid), lp))) -> (
      (* A method of a trait instance.  In an instance of the declaration the
         trait instance is known: the call is a call to the function the impl
         gives for the method (for a provided method the impl does not
         override, the trait's default, at this very instance). *)
      match resolve_ref span ctx ctx.dict_env tr with
      | DBuiltin ->
          [%craise] span "ACL2: call to a method of a builtin trait instance"
      | DImpl (i, dargs) -> (
          let impl = find_impl span ctx i in
          match List.find_opt (fun (m, _, _) -> m = mid) impl.methods with
          | None ->
              [%craise] span
                ("ACL2: a trait impl without the method called: "
                ^ mangle_name ctx.trans_ctx impl.item_meta.name)
          | Some (_, mname, (b : fun_decl_ref binder)) ->
              (* the method's own trait clauses: the call gives their
                 instances, in terms of the clauses in scope here *)
              let mclauses = b.binder_generics.trait_clauses in
              let all = List.map (fun (p : trait_param) -> p.clause_id) mclauses in
              let mrefs =
                match refs_at mclauses all q.generics.trait_refs with
                | Some rs -> rs
                | None ->
                    [%craise] span
                      ("ACL2: internal: the trait instances do not match the \
                        trait clauses in a call to the trait method " ^ mname)
              in
              let meth =
                List.map2
                  (fun (p : trait_param) (r : trait_ref) ->
                    (p.clause_id, resolve_ref span ctx ctx.dict_env r))
                  mclauses mrefs
              in
              fun_call_to_acl2 span ctx ~monadic
                ~via:(Some (impl_env span ctx i dargs, meth))
                b.binder_value.fun_id lp q b.binder_value.fun_generics args
                args_s))
  | FunOrOp (Fun (Pure Return)) -> sexp ("ok" :: args_s)
  | FunOrOp (Fun (Pure Fail)) -> sexp ("result-fail" :: args_s)
  | FunOrOp (Fun (Pure Assert)) -> sexp ("massert" :: args_s)
  | FunOrOp (Fun (Pure FuelDecrease)) -> sexp ("1-" :: args_s)
  | FunOrOp (Fun (Pure FuelEqZero)) -> sexp ("zp" :: args_s)
  | FunOrOp (Fun (Pure (UpdateAtIndex _))) -> sexp ("array-update" :: args_s)
  | FunOrOp (Fun (Pure (IndexAtIndex _))) ->
      (* Shared single-element index.  Upstream no longer has LLBC builtin
         function ids: charon desugars [a[i]] to a standard-library call and a
         micro-pass turns that into this pure builtin.  Same primitive the
         former builtin [Index] arm printed. *)
      sexp ("array-index" :: args_s)
  | FunOrOp (Fun (Pure (IndexMutAtIndex _))) ->
      (* mutable single-element index: micro-passes usually turn the write
         side into UpdateAtIndex; a surviving &mut index means a backward
         function, which [mut_borrow_pair_let] intercepts at a let *)
      [%craise] span
        "ACL2: &mut index survived to extraction (backward function)"
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
  | FunOrOp (Unop ArrayToSlice) -> (
      (* shared array-to-slice unsizing: identity on the list model (was the
         LLBC builtin [ArrayToSliceShared]) *)
      match args_s with
      | [ a ] -> a
      | _ -> [%craise] span "ACL2: ill-formed array-to-slice")
  | FunOrOp (Unop _) ->
      [%craise] span "ACL2: unsupported unop (neg / bitwise-not)"
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
  | TraitConst (tr, cid) -> (
      (* An associated constant of a trait instance: the impl gives a global
         for it. *)
      match resolve_ref span ctx ctx.dict_env tr with
      | DBuiltin ->
          [%craise] span "ACL2: constant of a builtin trait instance"
      | DImpl (i, _) -> (
          let impl = find_impl span ctx i in
          match List.find_opt (fun (c, _, _) -> c = cid) impl.consts with
          | None ->
              [%craise] span
                ("ACL2: a trait impl without the constant read: "
                ^ mangle_name ctx.trans_ctx impl.item_meta.name)
          | Some (_, cname, (gref : global_decl_ref)) -> (
              (* A constant that depends on the parameters of its impl (or a
                 trait's default, which depends on the instance) would need
                 instances of its own. *)
              (match
                 GlobalDeclId.Map.find_opt gref.global_id
                   ctx.trans_ctx.crate.global_decls
               with
              | Some (gd : LlbcAst.global_decl)
                when gd.generics.trait_clauses = []
                     && gd.generics.const_generics = [] -> ()
              | _ ->
                  [%craise] span
                    ("ACL2: the associated constant " ^ cname
                   ^ " is generic (not supported yet)"));
              match GlobalDeclId.Map.find_opt gref.global_id ctx.global_names with
              | Some n -> if monadic then sexp [ "ok"; n ] else n
              | None -> [%craise] span "ACL2: reference to an unsupported global")))
  | MkDynTrait _ -> [%craise] span "ACL2: dyn traits not supported"
  | LoopOp -> [%craise] span "ACL2: loop operator; use -loops-to-rec"

(* A call to a modeled std function.  One model serves every instantiation
   of the generic declaration, so check here that this instantiation is one
   the model is valid for. *)
and std_call_to_acl2 (span : Meta.span) (ctx : actx) (k : std_fun)
    (name : string) (q : qualif) (_args : texpr list) (args_s : string list) :
    string =
  let tys = q.generics.types in
  let require (ok : bool) (what : string) : unit =
    if not ok then
      [%craise] span ("ACL2: " ^ name ^ " is modeled only for " ^ what)
  in
  let first_ty_is (p : ty -> bool) : bool =
    match tys with
    | t :: _ -> p t
    | [] -> false
  in
  let is_int_range (t : ty) : bool =
    ty_range_kind ctx ty_is_int t = Some RkRange
  in
  let is_usize_range (t : ty) : bool =
    ty_range_kind ctx ty_is_usize t = Some RkRange
  in
  let adt_is (p : string -> bool) (t : ty) : bool =
    Option.fold ~none:false ~some:p (ty_adt_name ctx t)
  in
  match k with
  | StdRangeNext | StdRangeNextBack ->
      require (first_ty_is ty_is_int) "ranges of integers";
      sexp (name :: args_s)
  | StdIterRev | StdRevNext ->
      (* a Rev value is represented as the range it reverses *)
      require (first_ty_is is_int_range) "ranges of integers";
      sexp (name :: args_s)
  | StdIterStepBy | StdStepByNext ->
      require (first_ty_is is_usize_range) "Range<usize>";
      sexp (name :: args_s)
  | StdZipNext ->
      require
        (match tys with
        | a :: b :: _ ->
            adt_is is_itermut_model_ty a && adt_is is_iter_model_ty b
        | _ -> false)
        "a slice IterMut zipped with a slice Iter";
      sexp (name :: args_s)
  | StdSliceIter | StdSliceIntoIter | StdSliceIterNext | StdSliceIterMutNext
  | StdBitXorAssignRef | StdResultUnwrap -> sexp (name :: args_s)
  | StdArrayTryFromSlice -> (
      (* the array length is a const generic of the declaration: the model
         takes it as its first argument *)
      match (q.generics.const_generics, args_s) with
      | [ n ], [ s ] -> sexp [ name; const_generic_to_acl2 span ctx n; s ]
      | _ -> [%craise] span "ACL2: ill-formed try_from")
  | StdArrayRepeat -> (
      (* [x; N] (was the LLBC builtin [ArrayRepeat]): N is a const generic
         of the call *)
      match (q.generics.const_generics, args_s) with
      | [ n ], [ x ] ->
          sexp [ "array-repeat"; const_generic_to_acl2 span ctx n; x ]
      | _ -> [%craise] span "ACL2: ill-formed array repeat")
  | StdArrayAsSlice -> (
      (* shared array-to-slice unsizing: identity on the list model (was the
         LLBC builtin [ArrayToSliceShared]) *)
      match args_s with
      | [ a ] -> a
      | _ -> [%craise] span "ACL2: ill-formed array-to-slice")
  | StdArrayIndex | StdSliceIndex | StdVecIndex -> (
      (* a[i] and a[r], shared.  Indexing arrays and slices by usize never
         gets here (Aeneas turns it into the pure [IndexAtIndex]); a Vec
         does. *)
      let ity =
        match index_ty_arg q.generics with
        | Some t -> t
        | None -> [%craise] span "ACL2: index: unexpected generics"
      in
      match (args_s, ty_range_kind ctx ty_is_usize ity) with
      | [ a; i ], _ when ty_is_usize ity -> sexp [ "array-index"; a; i ]
      | [ _; _ ], Some rk when k <> StdVecIndex ->
          sexp ((name ^ "-" ^ range_kind_suffix rk) :: args_s)
      | _ ->
          [%craise] span
            ("ACL2: " ^ name
           ^ " is modeled only for usize and Range / RangeTo / RangeFrom<usize> \
              indices"))
  | StdSliceIterMut | StdIterZip | StdArrayIndexMut | StdSliceIndexMut
  | StdVecIndexMut | StdArrayAsMutSlice ->
      (* these return a (value, backward function) pair, which only the let
         printers know how to take apart *)
      [%craise] span
        ("ACL2: " ^ name
       ^ " returns a backward function: supported only at a destructuring let")

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
      | Struct [], None ->
          (* a struct without fields has no defprod: its one value is (unit)
             (see [type_decl_to_acl2]) *)
          "(unit)"
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

(* The bounds of a Range / RangeTo / RangeFrom value [r_var], as sexps.
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
  let acc (f : string) : string = "(" ^ rname ^ "->" ^ f ^ " " ^ r_var ^ ")" in
  match (range_kind_of_type_name rname, fields) with
  | Some RkRangeTo, [ fe ] -> ("0", acc fe)
  | Some RkRangeFrom, [ fs ] -> (acc fs, "(len " ^ arr_var ^ ")")
  | Some RkRange, [ fs; fe ] -> (acc fs, acc fe)
  | _ -> [%craise] span "ACL2: subslice borrow: unsupported range type"

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
           | Qualif { id = FunOrOp (Fun (FromLlbc (FunId id, _))); _ }
             -> (
               match FunDeclId.Map.find_opt id ctx.fun_names with
               | Some n -> "Fun:" ^ n
               | None -> "Fun:?")
           | Qualif _ -> "Qualif:other"
           | _ -> "head:other"
         in
         Printf.eprintf "[borrow-dbg] pair-let head=%s args=%d\n%!" hs
           (List.length args));
      let shape =
        match (head.e, args) with
        (* &mut a[r]: a call to the array / slice IndexMut impl with a range
           index *)
        | ( Qualif { id = FunOrOp (Fun (FromLlbc (FunId id, _))); generics },
            [ arr; r ] )
          when is_range_index_mut ctx id generics -> Some (`Subslice (arr, r))
        (* the &mut [T; N] -> &mut [T] coercion, a non-monadic pair-let on
           core::array::{[T; N]}::as_mut_slice (was the LLBC builtin
           [ArrayToSliceMut]):
             let (s, as_mut_slice_back) = as_mut_slice T N a in ... *)
        | Qualif { id = FunOrOp (Fun (FromLlbc (FunId id, _))); _ }, [ arr ]
          when fun_std_kind ctx id = Some StdArrayAsMutSlice ->
            Some (`ArrToSlice arr)
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
        | Qualif { id = FunOrOp (Fun (FromLlbc (FunId id, _))); generics } ->
            if is_range_index_mut ctx id generics then Some `Range
            else if is_vec_elem_index_mut ctx id generics then Some `Elem
            else None
        | Qualif { id = FunOrOp (Fun (Pure (IndexMutAtIndex _))); _ } ->
            (* &mut a[i] on an array or slice (was the LLBC builtin
               [Index {is_range = false; RMut}]) *)
            Some `Elem
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

(* Slice-iterator ctor pair-lets (roadmap item 8).  Both ctors return a
   (forward, backward) pair bound to a plain variable and destructured by a
   later non-monadic let (which [pending_pair_destructure] handles):
     (pair : (IterMut * (IterMut -> Slice)))  <-- slice::iter_mut xs
     (pair : (Zip * (Zip -> IterMut)))        <-- Iterator::zip self other
   We bind the forward MODEL value ({lst, pos} / {a, b}) to a temp and
   record the backward kind; the ctors are infallible on the model, so the
   monadic bind collapses to a plain one. *)
and iter_pair_let (span : Meta.span) (ctx : actx) (env : venv) (monadic : bool)
    (pat : tpat) (e1 : texpr) (e2 : texpr) : string option =
  match pat.pat with
  | PBound (_, _) when monadic -> (
      let head, args = destruct_apps (unmeta e1) in
      let hname =
        match (unmeta head).e with
        | Qualif { id = FunOrOp (Fun (FromLlbc (FunId id, _))); _ }
          -> FunDeclId.Map.find_opt id ctx.fun_names
        | _ -> None
      in
      (* the forward component of the returned pair, Result stripped *)
      let fwd_ty =
        let strip_result (ty : ty) : ty =
          match ty with
          | TAdt (TBuiltin TResult, { types = [ t ]; _ }) -> t
          | _ -> ty
        in
        match strip_result e1.ty with
        | TAdt (TTuple, { types = [ fwd; _ ]; _ }) -> Some fwd
        | _ -> None
      in
      let mk (kind : closure_kind) (fwd_s : string) : string option =
        let tmp = fresh_tmp ctx in
        let env', names = bind_tpats ctx env [ pat ] in
        let pair_n =
          match names with
          | [ n ] -> n
          | _ -> [%craise] span "ACL2: iterator pair binder arity"
        in
        if pair_n <> "&" then
          Hashtbl.replace ctx.pending_pairs pair_n (kind, tmp);
        let body = texpr_to_acl2 span ctx env' e2 in
        Some ("(b* ((" ^ tmp ^ " " ^ fwd_s ^ "))\n  " ^ body ^ ")")
      in
      match (hname, fwd_ty, args) with
      | Some n, Some (TAdt (TAdtId im_id, _)), [ xs ]
        when is_slice_iter_mut_ctor n ->
          let imname = type_name span ctx im_id in
          let xs_s = texpr_to_acl2 span ctx env xs in
          mk
            (CloIterMutBack { tyname = imname })
            (sexp [ imname; xs_s; "0" ])
      | Some n, Some (TAdt (TAdtId zip_id, zgen)), [ self; other ]
        when is_zip_ctor n -> (
          let zipname = type_name span ctx zip_id in
          match zgen.types with
          | [ _; it_ty ] -> (
              let self_s = texpr_to_acl2 span ctx env self in
              let other_s = texpr_to_acl2 span ctx env other in
              (* zip(self, other: impl IntoIterator): wrap a raw slice /
                 array as a fresh Iter; pass an existing iterator through *)
              let other_wrapped =
                match ((unmeta other).ty, it_ty) with
                | TAdt (TBuiltin (TSlice | TArray), _), TAdt (TAdtId it_id, _)
                  -> sexp [ type_name span ctx it_id; other_s; "0" ]
                | TAdt (TAdtId oid, _), TAdt (TAdtId it_id, _)
                  when oid = it_id -> other_s
                | _ ->
                    [%craise] span
                      "ACL2: zip: unsupported IntoIterator source"
              in
              mk
                (CloZipBack { tyname = zipname })
                (sexp [ zipname; self_s; other_wrapped ]))
          | _ -> [%craise] span "ACL2: zip: unexpected Zip generics")
      | _ -> None)
  | _ -> None

(* IterMut/Zip::next triple-lets, step 1: the (elem option, iter, next_back)
   triple is bound to a plain variable.  The synthesized next returns only
   (cons opt iter); we record the variable so the later destructuring
   ([pending_triple_destructure]) binds car/cdr and turns next_back into a
   [CloNextBack]. *)
and next_triple_let (span : Meta.span) (ctx : actx) (env : venv)
    (monadic : bool) (pat : tpat) (e1 : texpr) (e2 : texpr) : string option =
  match pat.pat with
  | PBound (_, _) when monadic -> (
      let head, _ = destruct_apps (unmeta e1) in
      let hname =
        match (unmeta head).e with
        | Qualif { id = FunOrOp (Fun (FromLlbc (FunId id, _))); _ }
          -> FunDeclId.Map.find_opt id ctx.fun_names
        | _ -> None
      in
      match hname with
      | Some n when is_slice_itermut_next n || is_zip_next n ->
          let e1_s = texpr_to_acl2 span ctx env e1 in
          let env', names = bind_tpats ctx env [ pat ] in
          let tmp_n =
            match names with
            | [ n ] -> n
            | _ -> [%craise] span "ACL2: next triple binder arity"
          in
          if tmp_n <> "&" then Hashtbl.replace ctx.pending_triples tmp_n ();
          let body = texpr_to_acl2 span ctx env' e2 in
          Some ("(b* (((ok " ^ tmp_n ^ ") " ^ e1_s ^ "))\n  " ^ body ^ ")")
      | _ -> None)
  | _ -> None

(* Step 2: let (o, iter1, next_back) = <recorded triple var> *)
and pending_triple_destructure (span : Meta.span) (ctx : actx) (env : venv)
    (monadic : bool) (pat : tpat) (e1 : texpr) (e2 : texpr) : string option =
  match (pat.pat, monadic) with
  | PAdt { variant_id = None; fields = [ f_o; f_it; f_nb ] }, false -> (
      let tuple_name =
        match (unmeta e1).e with
        | FVar id -> FVarId.Map.find_opt id env.fvars
        | BVar v -> ( try Some (venv_bvar env v) with _ -> None)
        | _ -> None
      in
      match tuple_name with
      | Some tn when Hashtbl.mem ctx.pending_triples tn ->
          let env', names = bind_tpats ctx env [ f_o; f_it; f_nb ] in
          let o_n, it_n, nb_n =
            match names with
            | [ a; b; c ] -> (a, b, c)
            | _ -> [%craise] span "ACL2: next triple destructure arity"
          in
          if nb_n <> "&" then Hashtbl.replace ctx.closures nb_n CloNextBack;
          let binds =
            List.filter_map
              (fun (n, acc) ->
                if n = "&" then None else Some ("(" ^ n ^ " " ^ acc ^ ")"))
              [
                (o_n, "(car " ^ tn ^ ")"); (it_n, "(cdr " ^ tn ^ ")");
              ]
          in
          let body = texpr_to_acl2 span ctx env' e2 in
          if binds = [] then Some body
          else
            Some
              ("(b* (" ^ String.concat "\n     " binds ^ ")\n  " ^ body ^ ")")
      | _ -> None)
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
  match iter_pair_let span ctx env monadic pat e1 e2 with
  | Some s -> s
  | None ->
  match next_triple_let span ctx env monadic pat e1 e2 with
  | Some s -> s
  | None ->
  match pending_triple_destructure span ctx env monadic pat e1 e2 with
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
      (* Destructuring let: bind a temp, project the fields.  A tuple is a
         cons; a struct is an FTY product, read through its accessors. *)
      let tmp = fresh_tmp ctx in
      let env', fnames = bind_tpats ctx env fields in
      let accessors =
        match (pat.ty, fields) with
        | TAdt (TTuple, _), [ _; _ ] ->
            [ "(car " ^ tmp ^ ")"; "(cdr " ^ tmp ^ ")" ]
        | TAdt (TTuple, _), _ ->
            [%craise] span "ACL2: destructuring let on a tuple of arity <> 2"
        | TAdt (TAdtId id, _), _ -> (
            let tname = type_name span ctx id in
            match (TypeDeclId.Map.find id ctx.types).kind with
            | Struct sfields when List.length sfields = List.length fields ->
                List.map
                  (fun f -> "(" ^ tname ^ "->" ^ f ^ " " ^ tmp ^ ")")
                  (field_names sfields)
            | _ -> [%craise] span "ACL2: destructuring let on a non-struct")
        | _ -> [%craise] span "ACL2: destructuring let on an unexpected type"
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
      (* print each field value once: printing allocates fresh names *)
      let upd_vals =
        List.map (fun (fid, e) -> (fid, texpr_to_acl2 span ctx env e)) su.updates
      in
      let upd_strs =
        List.map
          (fun (fid, v) ->
            let fname = List.nth fnames (FieldId.to_int fid) in
            ":" ^ fname ^ " " ^ v)
          upd_vals
      in
      match su.init with
      | Some base ->
          sexp
            (("change-" ^ tname) :: texpr_to_acl2 span ctx env base :: upd_strs)
      | None ->
          (* A struct literal.  When it gives every field in declaration
             order -- the usual case -- print the positional constructor,
             which is what make- expands to. *)
          let in_order =
            List.length upd_vals = List.length fnames
            && List.for_all2
                 (fun (fid, _) i -> FieldId.to_int fid = i)
                 upd_vals
                 (List.init (List.length fnames) (fun i -> i))
          in
          if fnames = [] then "(unit)"
          else if in_order then sexp (tname :: List.map snd upd_vals)
          else sexp (("make-" ^ tname) :: upd_strs))
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
      if is_stepby_model_ty tname then
        (* StepBy<I> is opaque without the Miri sysroot; we own its model:
           Rust's own fields are { iter, step (holding step-1), first_take }
           (see the ctor/next syntheses in [synth_std_body]). *)
        "(fty::defprod " ^ tname
        ^ "\n  ((iter acl2::any-p) (step acl2::any-p) (first-take acl2::any-p))"
        ^ "\n  :xvar the-" ^ tname ^ ")"
      else if is_itermut_model_ty tname || is_iter_model_ty tname then
        (* slice Iter/IterMut model: the (remaining) list plus a cursor.
           next reads lst[pos] and advances; IterMut's write-backs run in
           composed order, walking pos back down (see the -wb-some
           companion emitted after the type groups). *)
        "(fty::defprod " ^ tname ^ "\n  ((lst acl2::any-p) (pos acl2::any-p))"
        ^ "\n  :xvar the-" ^ tname ^ ")"
      else if is_zip_model_ty tname then
        (* Zip<A, B> model: the two component iterators; A is the &mut
           side (zip's backward extracts it). *)
        "(fty::defprod " ^ tname ^ "\n  ((a acl2::any-p) (b acl2::any-p))"
        ^ "\n  :xvar the-" ^ tname ^ ")"
      else ";; opaque type " ^ tname ^ " (skipped)"

(* The keys of the group members that [d]'s body calls *)
let group_callees (keys : fkey list) (d : Pure.fun_decl) : fkey list =
  let found = ref [] in
  let visitor =
    object
      inherit [_] iter_expr

      method! visit_qualif _ q =
        match q.id with
        | FunOrOp (Fun (FromLlbc (FunId id, lp)))
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

(* Synthesize the defun of a modeled std function ([std_fun]) at its
   declaration.  The declarations are generic; the Option / Result / Range /
   iterator-model types a body mentions are the crate's own (generic) ADTs,
   recovered from the declaration's signature -- or, where the signature only
   has a type variable, looked up by name -- so the names match the emitted
   deftagsum / defprod exactly. *)
let synth_std_body (span : Meta.span) (ctx : actx) (decl : Pure.fun_decl)
    (name : string) (k : std_fun) : string =
  let bad : 'a. string -> 'a =
   fun what -> [%craise] span ("ACL2: " ^ name ^ ": " ^ what)
  in
  let type_named (tname : string) : TypeDeclId.id option =
    TypeDeclId.Map.fold
      (fun id n acc -> if n = tname then Some id else acc)
      ctx.type_names None
  in
  (* the ADT of the first input *)
  let self_adt () : TypeDeclId.id =
    match decl.signature.inputs with
    | TAdt (TAdtId id, _) :: _ -> id
    | _ -> bad "unexpected input signature"
  in
  (* the Option of an iterator method returning Result (Option<_> * _) *)
  let output_option () : string =
    match decl.signature.output with
    | TAdt
        ( TBuiltin TResult,
          { types = [ TAdt (TTuple, { types = TAdt (TAdtId oid, _) :: _; _ }) ]; _ }
        ) -> type_name span ctx oid
    | _ -> bad "unexpected output signature"
  in
  (* core::ops::Range and its two field names *)
  let range_model () : string * string * string =
    match type_named "core-ops-range-range" with
    | None -> bad "the crate has no core::ops::Range"
    | Some id -> (
        match (TypeDeclId.Map.find id ctx.types).kind with
        | Struct fields -> (
            match field_names fields with
            | [ s; e ] -> (type_name span ctx id, s, e)
            | _ -> bad "Range has unexpected fields")
        | _ -> bad "Range is not a struct")
  in
  match k with
  | StdArrayTryFromSlice ->
      (* <[T; N] as TryFrom<&[T]>>::try_from (what `slice.try_into()` resolves
         to): Ok(the slice as an array) when the length is N, else
         Err(TryFromSliceError) -- core's OWN Result value either way (the
         call itself never panics).  N is a const generic of the declaration:
         the model takes it as its first formal. *)
      let rname =
        match decl.signature.output with
        | TAdt (TBuiltin TResult, { types = [ TAdt (TAdtId id, _) ]; _ }) ->
            type_name span ctx id
        | _ -> bad "unexpected output signature"
      in
      "(defun " ^ name ^ " (n self)\n  (if (equal (len self) n)\n      (ok ("
      ^ rname ^ "-ok self))\n    (ok (" ^ rname ^ "-err (unit)))))"
  | StdResultUnwrap ->
      (* Result::unwrap: the Ok payload, or a panic (= result-fail) on Err. *)
      let rname = type_name span ctx (self_adt ()) in
      "(defun " ^ name ^ " (self)\n  (if (eq (" ^ rname
      ^ "-kind self) :ok)\n      (ok (" ^ rname
      ^ "-ok->f0 self))\n    (result-fail (err-failure))))"
  | StdSliceIter | StdSliceIntoIter ->
      (* <[T]>::iter / <&[T] as IntoIterator>::into_iter: wrap the slice as
         a fresh {lst, pos} iterator. *)
      let iname =
        match decl.signature.output with
        | TAdt (TBuiltin TResult, { types = [ TAdt (TAdtId id, _) ]; _ })
        | TAdt (TAdtId id, _) -> type_name span ctx id
        | _ -> bad "unexpected output signature"
      in
      "(defun " ^ name ^ " (self) (ok (" ^ iname ^ " self 0)))"
  | StdSliceIterNext | StdSliceIterMutNext ->
      (* Iterator::next for Iter/IterMut: yield lst[pos] and advance.  The
         triple's next_back component is defunctionalized away (the
         synthesized value is just (opt . iter'), see
         [pending_triple_destructure]). *)
      let iname = type_name span ctx (self_adt ()) in
      let oname = output_option () in
      String.concat "\n"
        [
          "(defun " ^ name ^ " (self)";
          "  (b* ((lst (" ^ iname ^ "->lst self))";
          "       (pos (" ^ iname ^ "->pos self)))";
          "  (if (< pos (len lst))";
          "      (ok (cons (" ^ oname ^ "-some (nth pos lst)) (" ^ iname
          ^ " lst (+ pos 1))))";
          "    (ok (cons (" ^ oname ^ "-none) self)))))";
        ]
  | StdZipNext ->
      (* Zip::next: yield (a[pa] . b[pb]) while both sides have elements,
         advancing both.  (Upstream advances `a` before discovering `b` is
         exhausted -- observable only for UNEQUAL lengths, and only through
         the iterator value itself, which the write-back path never reads
         past its cursor; AES zips equal-length sides, asserted upstream.)
         The declaration is generic in both sides; the model is for a slice
         IterMut zipped with a slice Iter, which the call sites check. *)
      let model (tname : string) (what : string) : string =
        match type_named tname with
        | Some id -> type_name span ctx id
        | None -> bad ("the crate has no slice " ^ what)
      in
      let zname = type_name span ctx (self_adt ()) in
      let aname = model "core-slice-iter-itermut" "IterMut" in
      let bname = model "core-slice-iter-iter" "Iter" in
      let oname = output_option () in
      String.concat "\n"
        [
          "(defun " ^ name ^ " (self)";
          "  (b* ((ia (" ^ zname ^ "->a self))";
          "       (ib (" ^ zname ^ "->b self))";
          "       (la (" ^ aname ^ "->lst ia))";
          "       (pa (" ^ aname ^ "->pos ia))";
          "       (lb (" ^ bname ^ "->lst ib))";
          "       (pb (" ^ bname ^ "->pos ib)))";
          "  (if (and (< pa (len la)) (< pb (len lb)))";
          "      (ok (cons (" ^ oname ^ "-some (cons (nth pa la) (nth pb lb)))";
          "                (" ^ zname ^ " (" ^ aname ^ " la (+ pa 1)) (" ^ bname
          ^ " lb (+ pb 1)))))";
          "    (ok (cons (" ^ oname ^ "-none) self)))))";
        ]
  | StdBitXorAssignRef ->
      (* value-level <uN as BitXorAssign<&uN>>::bitxor_assign *)
      let ity =
        match decl.signature.inputs with
        | TLiteral (TUInt uty) :: _ -> int_ty_name (Values.Unsigned uty)
        | _ -> bad "unexpected input signature"
      in
      "(defun " ^ name ^ " (self other) (ok (" ^ ity ^ "-xor self other)))"
  | StdArrayIndex | StdSliceIndex ->
      (* a[r], shared, as a bounds-checked window read: one defun per range
         type the crate uses (the index type is a type parameter of the
         declaration, so the call sites pick the defun).  A missing bound
         defaults to 0 / (len self). *)
      let one (tname : string) (rk : range_kind) : string option =
        match type_named tname with
        | Some id
          when Hashtbl.mem ctx.std_used (name ^ "-" ^ range_kind_suffix rk) ->
            let rname = type_name span ctx id in
            let fields =
              match (TypeDeclId.Map.find id ctx.types).kind with
              | Struct fs -> field_names fs
              | _ -> bad "range is not a struct"
            in
            let acc (f : string) : string = "(" ^ rname ^ "->" ^ f ^ " r)" in
            let lo, hi =
              match (rk, fields) with
              | RkRange, [ fs; fe ] -> (acc fs, acc fe)
              | RkRangeTo, [ fe ] -> ("0", acc fe)
              | RkRangeFrom, [ fs ] -> (acc fs, "(len self)")
              | _ -> bad "range has unexpected fields"
            in
            Some
              ("(defun " ^ name ^ "-" ^ range_kind_suffix rk
             ^ " (self r) (vec-index-range self " ^ lo ^ " " ^ hi ^ "))")
        | _ -> None
      in
      let defuns =
        List.filter_map
          (fun (tname, rk) -> one tname rk)
          [
            ("core-ops-range-range", RkRange);
            ("core-ops-range-rangeto", RkRangeTo);
            ("core-ops-range-rangefrom", RkRangeFrom);
          ]
      in
      String.concat "\n\n" defuns
  | StdIterStepBy ->
      (* Iterator::step_by(self, step): Rust asserts step != 0 (a panic ->
         result-fail) and stores step - 1 in the [step] field. *)
      let sbname =
        match decl.signature.output with
        | TAdt (TBuiltin TResult, { types = [ TAdt (TAdtId id, _) ]; _ })
        | TAdt (TAdtId id, _) -> type_name span ctx id
        | _ -> bad "unexpected output signature"
      in
      "(defun " ^ name ^ " (self step)\n  (if (equal step 0)\n      (result-fail \
       (err-failure))\n    (ok (" ^ sbname ^ " self (- step 1) t))))"
  | StdStepByNext ->
      (* StepBy::next: if first_take { first_take = false; iter.next() }
         else { iter.nth(step) } -- for a Range<usize> (checked at the call
         sites): nth(n) yields start+n and sets start = start+n+1 when
         start+n < end, else sets start = end and yields None. *)
      let sbname = type_name span ctx (self_adt ()) in
      let rname, fstart, fend = range_model () in
      let oname = output_option () in
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
  | StdIterRev ->
      (* Iterator::rev.  Rev<I> is a newtype around I: a Rev value is
         represented AS the iterator it reverses, so `rev` is the identity
         and Rev::next is the reverse advance on that iterator. *)
      "(defun " ^ name ^ " (self) (ok self))"
  | StdRevNext | StdRangeNextBack ->
      (* the reverse advance of a range of integers (checked at the call
         sites): if start < end { end -= 1; Some(end) } else { None } *)
      let rname, fstart, fend = range_model () in
      let oname = output_option () in
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
  | StdRangeNext ->
      (* the fused advance of a range of integers (checked at the call
         sites): yield start, step start+1 *)
      let rname, fstart, fend = range_model () in
      let oname = output_option () in
      String.concat "\n"
        [
          "(defun " ^ name ^ " (self)";
          "  (b* ((s (" ^ rname ^ "->" ^ fstart ^ " self))";
          "       (e (" ^ rname ^ "->" ^ fend ^ " self)))";
          "  (if (< s e)";
          "      (ok (cons (" ^ oname ^ "-some s) (" ^ rname ^ " (+ s 1) e)))";
          "    (ok (cons (" ^ oname ^ "-none) self)))))";
        ]
  | StdSliceIterMut | StdIterZip | StdArrayIndexMut | StdSliceIndexMut
  | StdVecIndex | StdVecIndexMut | StdArrayRepeat | StdArrayAsSlice
  | StdArrayAsMutSlice -> bad "has no defun (printed at its uses)"

(* [inst] prints the declaration at an instance of its trait clauses: the name
   of the defun, and what the clauses in [fun_rel] stand for. *)
let fun_decl_to_acl2 ?(inst : (string * (TraitClauseId.id * dict) list) option)
    (ctx : actx) (is_rec : bool) (decl : Pure.fun_decl) : string =
  let span = decl.item_meta.span in
  (* Every declaration is printed on its own terms: bound-variable numbering
     restarts, and no backward-closure registration survives from the
     previous declaration (the tables are keyed by variable name).  A
     function's text then does not depend on what else is in the crate or on
     the order charon lists it in. *)
  ctx.gensym <- 0;
  Hashtbl.reset ctx.closures;
  Hashtbl.reset ctx.pending_pairs;
  Hashtbl.reset ctx.pending_triples;
  ctx.dict_env <-
    (match inst with
    | Some (_, env) -> env
    | None -> []);
  (* Const generic parameters become the first formals, named const-<name>
     so that `N` cannot collide with the fuel formal `n`. *)
  ctx.cg_names <-
    List.map
      (fun (p : const_generic_param) ->
        (p.index, "const-" ^ collapse_dashes (mangle_string p.name)))
      decl.signature.generics.const_generics;
  let base =
    match FunDeclId.Map.find_opt decl.def_id ctx.fun_names with
    | Some s -> s
    | None -> [%craise] span "ACL2: function without a name"
  in
  let name =
    match inst with
    | Some (n, _) -> n
    | None -> base ^ loop_suffix decl.loop_id
  in
  (if
     (* Dump the pure AST of every function whose printed name contains the
        env var's value (a debugging aid for designing new syntheses). *)
     match Sys.getenv_opt "ACL2_DEBUG_BODY" with
     | Some sub -> str_contains name sub
     | None -> false
   then
     match decl.body with
     | Some _ ->
         let fmt_env = PrintPure.decls_ctx_to_fmt_env ctx.trans_ctx in
         Printf.eprintf "[body-dbg] %s:\n%s\n%!" name
           (PrintPure.fun_decl_to_string fmt_env decl)
     | None -> ());
  match (std_kind name, decl.body) with
  (* A modeled std function is its model, whether or not charon had a body
     for it: a real body is generic over trait clauses. *)
  | Some k, _ when decl.loop_id = None -> synth_std_body span ctx decl name k
  | _, None -> ";; opaque function " ^ name ^ " (skipped)"
  | _, Some body ->
      let env, input_names =
        bind_tpats ~toplevel:true ctx empty_venv body.inputs
      in
      (* An input the body ignores (the `()` a closure without arguments is
         called with) is still a formal. *)
      let input_names =
        List.mapi
          (fun i ((n, p) : string * tpat) ->
            match (n, p.pat) with
            | "&", PIgnored -> "acl2unused" ^ string_of_int i
            | _ -> n)
          (List.combine input_names body.inputs)
      in
      List.iter
        (fun n ->
          if n = "&" then
            [%craise] span "ACL2: composite input pattern not supported")
        input_names;
      (* Loop functions take their back-continuation as an arrow-typed
         formal; on the ACL2 side the formal is DATA (the defunctionalized
         list of pending writes) and applying it prints through the
         iterator model's -apply-back.  Formals keep their surface names
         (unlike gensym-unique internal binders), so first clear any stale
         closure registration a previous declaration left under the same
         name. *)
      List.iter (fun n -> Hashtbl.remove ctx.closures n) input_names;
      List.iter
        (fun ((n, p) : string * tpat) ->
          match p.ty with
          | TArrow (TAdt (TAdtId id, _), _) ->
              Hashtbl.replace ctx.closures n
                (CloBackParam
                   { apply_fn = type_name span ctx id ^ "-apply-back" })
          | _ ->
              (* Other arrow-typed formals (e.g. genuine closures over
                 scalars) stay unregistered: their applications fail
                 loudly at the use site, exactly as before. *)
              ())
        (List.combine input_names body.inputs);
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
      ^ String.concat " " (List.map snd ctx.cg_names @ input_names)
      ^ ")" ^ measure ^ "\n  " ^ body_s ^ ")"

(* An instance is generated when a call asks for it, on its own: it is
   recursive when it calls the function it is an instance of (necessarily at
   the same instance: [instance_name]). *)
let () =
  print_instance_ref :=
    fun ctx decl name env ->
      let is_rec = group_callees [ decl_key decl ] decl <> [] in
      fun_decl_to_acl2 ~inst:(name, env) ctx is_rec decl

(* ----------------------------------------------------------------- crate *)

(* Emit a global as (defconst *name* value). v0 only supports globals
   whose initializer is a single constant expression (after stripping the
   monadic return) -- the crypto case (round constants like DELTA). *)
let global_decl_to_acl2 (ctx : actx) (gid : GlobalDeclId.id) : string =
  let g = GlobalDeclId.Map.find gid ctx.trans_ctx.crate.global_decls in
  let span = g.item_meta.span in
  ctx.gensym <- 0;
  ctx.cg_names <- [];
  ctx.dict_env <- [];
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
    TypeDeclId.Map.map
      (fun (d : Pure.type_decl) ->
        trim_dashes (mangle_name trans_ctx d.item_meta.name))
      ctx.trans_types
  in
  (* Upstream's declaration-id maps are now read-only hash maps (no [add] /
     [empty]): collect the bindings as lists and convert once. *)
  (* The modeled std functions ([std_fun_table]): recognize each declaration
     by its name pattern and give it the table's ACL2 name. *)
  let std_patterns =
    List.map
      (fun (pat, k, acl2_name) ->
        (Charon.NameMatcher.parse_pattern pat, k, acl2_name))
      std_fun_table
  in
  let prim_patterns =
    List.map
      (fun (pat, prim, monadic) ->
        (Charon.NameMatcher.parse_pattern pat, prim, monadic))
      std_prim_table
  in
  Hashtbl.reset std_kind_tbl;
  Hashtbl.reset std_prim_tbl;
  let fun_names =
    FunDeclId.Map.of_list
      (FunDeclId.Map.fold
         (fun id (t : pure_fun_translation) acc ->
           let mangled = mangle_name trans_ctx t.f.item_meta.name in
           let matches pat =
             ExtractName.match_name trans_ctx.crate pat t.f.item_meta.name
           in
           let n =
             match
               List.find_opt (fun (pat, _, _) -> matches pat) std_patterns
             with
             | Some (_, k, acl2_name) ->
                 let n = Option.value acl2_name ~default:mangled in
                 Hashtbl.replace std_kind_tbl n k;
                 n
             | None ->
                 (* only the std declarations without a body can be one of
                    the primitives *)
                 (if t.f.body = None && not t.f.item_meta.is_local then
                    match
                      List.find_opt
                        (fun (pat, _, _) -> matches pat)
                        prim_patterns
                    with
                    | Some (_, prim, monadic) ->
                        Hashtbl.replace std_prim_tbl mangled (prim, monadic)
                    | None -> ());
                 mangled
           in
           (* loops and bodies share the base name; suffixes are added at
              print time from [loop_id] *)
           List.fold_left
             (fun acc (d : Pure.fun_decl) -> (d.def_id, n) :: acc)
             ((id, n) :: acc)
             (t.loops @ t.bodies))
         ctx.trans_funs [])
  in
  let opaque_funs =
    FunDeclId.Set.of_list
      (FunDeclId.Map.fold
         (fun id (t : pure_fun_translation) acc ->
           if t.f.body = None then id :: acc else acc)
         ctx.trans_funs [])
  in

  (* Globals: name each as a defconst symbol *<mangled>*, and remember its
     initializer function id so we can emit its value. *)
  let global_names =
    GlobalDeclId.Map.of_list
      (GlobalDeclId.Map.fold
         (fun id (g : LlbcAst.global_decl) acc ->
           (id, "*" ^ mangle_name trans_ctx g.item_meta.name ^ "*") :: acc)
         ctx.trans_ctx.crate.global_decls [])
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
      trait_impls = ctx.trans_trait_impls;
      fun_rel = Hashtbl.create 64;
      impl_rel = Hashtbl.create 64;
      dict_env = [];
      insts = Hashtbl.create 64;
      inst_names = Hashtbl.create 64;
      impl_long = Hashtbl.create 16;
      inst_stack = [];
      inst_log = [];
      inst_out = Buffer.create 4096;
      printing = [];
      gensym = 0;
      cg_names = [];
      skipped = [];
      closures = Hashtbl.create 16;
      pending_pairs = Hashtbl.create 16;
      std_used = Hashtbl.create 16;
      pending_triples = Hashtbl.create 16;
    }
  in
  compute_relevance actx;
  compute_impl_naming actx;
  (* Which modeled std functions does the code call?  (Charon declares every
     method of every impl the crate touches.) *)
  (let visitor =
     object
       inherit [_] iter_expr

       method! visit_qualif _ q =
         match q.id with
         | FunOrOp (Fun (FromLlbc (FunId id, _))) -> (
             match FunDeclId.Map.find_opt id fun_names with
             | None -> ()
             | Some n -> (
                 match std_kind n with
                 | None -> ()
                 | Some (StdArrayIndex | StdSliceIndex) -> (
                     match
                       Option.bind
                         (index_ty_arg q.generics)
                         (ty_range_kind actx ty_is_usize)
                     with
                     | Some rk ->
                         Hashtbl.replace actx.std_used
                           (n ^ "-" ^ range_kind_suffix rk)
                           ()
                     | None -> ())
                 | Some _ -> Hashtbl.replace actx.std_used n ()))
         | _ -> ()
     end
   in
   FunDeclId.Map.iter
     (fun _ (t : pure_fun_translation) ->
       List.iter
         (fun (d : Pure.fun_decl) ->
           match d.body with
           | Some b -> visitor#visit_texpr () b.body
           | None -> ())
         ((t.f :: t.loops) @ t.bodies))
     ctx.trans_funs);
  (* Debugging aid for writing std recognizers: dump, for every function and
     type declaration, the mangled ACL2 name next to its Rust name pattern
     (the syntax [NameMatcher.parse_pattern] accepts). *)
  (if Option.is_some (Sys.getenv_opt "ACL2_DEBUG_PATTERNS") then
     let pat (span : Meta.span) (n : Types.name) : string =
       try TranslateCore.name_to_pattern_string (Some span) trans_ctx n
       with CFailure _ -> "(no pattern)"
     in
     FunDeclId.Map.iter
       (fun id (t : pure_fun_translation) ->
         Printf.eprintf "[pattern-dbg] fun %s%s || %s\n%!"
           (FunDeclId.Map.find id fun_names)
           (if t.f.body = None then " (opaque)" else "")
           (pat t.f.item_meta.span t.f.item_meta.name))
       ctx.trans_funs;
     TypeDeclId.Map.iter
       (fun id (d : Pure.type_decl) ->
         Printf.eprintf "[pattern-dbg] type %s || %s\n%!"
           (TypeDeclId.Map.find id type_names)
           (pat d.item_meta.span d.item_meta.name))
       ctx.trans_types);
  (* Debugging aid for the trait machinery: dump every trait impl (its
     clauses, the ones its code depends on, its parent trait refs and method
     table), every trait declaration's default methods, and the clauses each
     function depends on. *)
  (if Option.is_some (Sys.getenv_opt "ACL2_DEBUG_TRAITS") then
     let fmt_env = PrintPure.decls_ctx_to_fmt_env trans_ctx in
     let fref (r : fun_decl_ref) : string =
       (match FunDeclId.Map.find_opt r.fun_id fun_names with
       | Some n -> n
       | None -> "?")
       ^ " "
       ^ PrintPure.generic_args_to_string fmt_env r.fun_generics
     in
     let clauses_s (cs : TraitClauseId.id list) : string =
       String.concat ", " (List.map TraitClauseId.to_string cs)
     in
     Hashtbl.iter
       (fun ((id, lp) : fkey) cs ->
         if cs <> [] then
           Printf.eprintf "[traits-dbg] fun %s%s depends on its clauses {%s}\n%!"
             (Option.value (FunDeclId.Map.find_opt id fun_names) ~default:"?")
             (loop_suffix lp) (clauses_s cs))
       actx.fun_rel;
     TraitImplId.Map.iter
       (fun id (i : Pure.trait_impl) ->
         Printf.eprintf
           "[traits-dbg] impl %s: %d type params, %d clauses, depends on \
            {%s}; parents [%s]\n\
            %!"
           (mangle_name trans_ctx i.item_meta.name)
           (List.length i.generics.types)
           (List.length i.generics.trait_clauses)
           (clauses_s (impl_rel actx id))
           (String.concat "; "
              (List.map
                 (PrintPure.trait_ref_to_string fmt_env false)
                 i.parent_trait_refs));
         List.iter
           (fun ((_, mname, b) : _ * string * fun_decl_ref binder) ->
             Printf.eprintf
               "[traits-dbg]   method %s (binder: %d clauses) := %s\n%!" mname
               (List.length b.binder_generics.trait_clauses)
               (fref b.binder_value))
           i.methods)
       ctx.trans_trait_impls;
     TraitDeclId.Map.iter
       (fun _ (d : Pure.trait_decl) ->
         List.iter
           (fun (m : trait_method) ->
             match m.default.binder_value with
             | Some r ->
                 Printf.eprintf "[traits-dbg] decl %s default %s := %s\n%!"
                   (mangle_name trans_ctx d.item_meta.name)
                   m.item_name (fref r)
             | None -> ())
           d.methods)
       ctx.trans_trait_decls);
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
  (* Emit following the crate's declaration order.  The emitters write to
     [!cur]: the functions are generated first, so that the type declarations
     can be limited to the ones the generated code mentions (charon pulls in
     the types of every signature in every impl the crate touches). *)
  let cur : Buffer.t ref = ref (Buffer.create 65536) in
  let emit_decl (kind : string) (name : string) (f : unit -> string) : bool =
    let res =
      match f () with
      | s -> Ok s
      | exception CFailure err -> Error err.msg
    in
    (* the instances the declaration asked for come first; they stand on
       their own, so they stay even when the declaration itself fails *)
    Buffer.add_buffer !cur actx.inst_out;
    Buffer.clear actx.inst_out;
    match res with
    | Ok s ->
        Printf.bprintf !cur "%s\n\n" s;
        true
    | Error msg ->
        Printf.bprintf !cur ";; SKIPPED %s %s: %s\n\n" kind name msg;
        false
  in
  (* A comment whose text depends on what comes after it: a marker takes its
     place until the functions and globals are all printed.  The function
     gets that text and gives the comment, if there is to be one. *)
  let notes : (string -> string option) list ref = ref [] in
  let add_note (f : string -> string option) : unit =
    Printf.bprintf !cur ";;@note@%d@\n\n" (List.length !notes);
    notes := !notes @ [ f ]
  in
  (* The functions of the crate that depend on a trait clause are not printed
     where they are declared, only at the instances they are used at: a note
     takes their place, listing the instances. *)
  let generic_note ((key, name) : fkey * string) (_ : string) : string option =
    match
      List.filter_map
        (fun (((k, _), n) : inst_key * string) ->
          if k = key then Some n else None)
        (List.rev actx.inst_log)
    with
    | [] ->
        if Hashtbl.fold (fun (k, _) _ found -> found || k = key) actx.insts false
        then
          (* each failed instance has its own SKIPPED line *)
          Some
            (";; " ^ name
           ^ " depends on its trait bounds: one function per instance, none \
              of which could be generated")
        else
          Some
            (";; SKIPPED function " ^ name
           ^ ": ACL2: depends on its trait bounds, and the crate uses it at \
              no instance (a function is printed once per instance of the \
              bounds it calls through)")
    | names ->
        Some
          (";; " ^ name
         ^ " depends on its trait bounds: one function per instance,\n"
          ^ String.concat "\n" (List.map (fun n -> ";;   " ^ n) names))
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
          Printf.bprintf !cur ";; SKIPPED mutually recursive type group\n\n"
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
                | Some t -> (
                    let name = FunDeclId.Map.find_opt id fun_names in
                    if t.f.is_global_decl_body then None
                    else
                      match Option.bind name std_kind with
                      | Some k ->
                          (* a modeled std function: its model, if the model
                             is a defun and the crate calls it; else nothing *)
                          let n = Option.get name in
                          let used =
                            match k with
                            | StdArrayIndex | StdSliceIndex ->
                                List.exists
                                  (fun rk ->
                                    Hashtbl.mem actx.std_used
                                      (n ^ "-" ^ range_kind_suffix rk))
                                  [ RkRange; RkRangeTo; RkRangeFrom ]
                            | _ -> Hashtbl.mem actx.std_used n
                          in
                          if std_has_defun k && used then Some [ t.f ]
                          else None
                      | None ->
                          if t.f.body <> None then
                            Some ((t.f :: t.loops) @ t.bodies)
                          else if t.f.item_meta.is_local then
                            (* a function of the crate without a body: say so *)
                            Some [ t.f ]
                          else
                            (* An opaque std declaration: provided by the
                               primitives book, or simply not modeled.  Charon
                               pulls in every method of every impl the crate
                               touches; a declaration nobody calls is not
                               worth a line, and a call to one fails at the
                               call site, naming it. *)
                            None)
                | None -> None)
              ids
          in
          let printed_name (d : Pure.fun_decl) : string =
            FunDeclId.Map.find d.def_id fun_names ^ loop_suffix d.loop_id
          in
          (* the functions that depend on a trait clause are printed at
             their instances, where a call asks for one *)
          let generic, decls =
            List.partition
              (fun (d : Pure.fun_decl) -> fun_rel actx (decl_key d) <> [])
              (List.concat decls)
          in
          List.iter
            (fun (d : Pure.fun_decl) ->
              if d.item_meta.is_local && d.loop_id = None then
                add_note (generic_note (decl_key d, printed_name d)))
            generic;
          if decls = [] then ()
          else
            let sccs = group_to_sccs decls in
            (* what an instance generated from here on must not call: it
               would come out before them *)
            actx.printing <- List.map decl_key decls;
            List.iter
              (fun (scc : fun_scc) ->
                let one (d : Pure.fun_decl) : string =
                  fun_decl_to_acl2 actx scc.is_rec d
                in
                (match scc.members with
                | [ d ] ->
                    let ok =
                      emit_decl "function" (printed_name d) (fun () -> one d)
                    in
                    if not ok then actx.skipped <- decl_key d :: actx.skipped
                | ds ->
                    let ok =
                      emit_decl "recursive functions"
                        (String.concat "/" (List.map printed_name ds))
                        (fun () ->
                          "(mutual-recursion\n"
                          ^ String.concat "\n" (List.map one ds)
                          ^ ")")
                    in
                    if not ok then
                      actx.skipped <- List.map decl_key ds @ actx.skipped);
                actx.printing <-
                  List.filter
                    (fun k ->
                      not (List.exists (fun d -> decl_key d = k) scc.members))
                    actx.printing)
              sccs
      | LlbcAst.GlobalGroup g ->
          let gids =
            match g with
            | NonRecGroup id -> [ id ]
            | RecGroup ids -> ids
          in
          List.iter
            (fun gid ->
              let name = GlobalDeclId.Map.find gid global_names in
              let g =
                GlobalDeclId.Map.find gid ctx.trans_ctx.crate.global_decls
              in
              let has_body =
                match Charon.GAstUtils.init_fun_id_of_global g with
                | Some init_id -> (
                    match FunDeclId.Map.find_opt init_id ctx.trans_funs with
                    | Some t -> t.f.body <> None
                    | None -> false)
                | None -> false
              in
              if g.item_meta.is_local || has_body then
                ignore
                  (emit_decl "global" name (fun () ->
                       global_decl_to_acl2 actx gid))
              else
                (* An opaque global of another crate, like an opaque std
                   function, is worth a line only if the code refers to it. *)
                add_note (fun text ->
                    if str_contains text name then
                      Some (";; SKIPPED global " ^ name ^ ": ACL2: opaque global")
                    else None))
            gids
      | LlbcAst.TraitDeclGroup _ | LlbcAst.TraitImplGroup _ ->
          (* Trait declarations and impls have no ACL2 counterpart: a method
             of an impl is an ordinary function (printed with the function
             groups), and a call through a trait bound is resolved in each
             instance of the function that makes it. *)
          ()
      | LlbcAst.MixedGroup _ ->
          Printf.bprintf !cur ";; SKIPPED mixed declaration group\n\n"
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
      (Option.get ctx.crate.declarations)
  in
  (* 1. functions and globals *)
  let vbuf = !cur in
  List.iter emit_group value_groups;
  (* the comments that waited for all of it *)
  let vtext =
    let text = Buffer.contents vbuf in
    Str.global_substitute
      (Str.regexp ";;@note@\\([0-9]+\\)@\n\n")
      (fun s ->
        match (List.nth !notes (int_of_string (Str.matched_group 1 s))) text with
        | Some note -> note ^ "\n\n"
        | None -> "")
      text
  in
  (* does the code mention the type?  Its name is followed by a dash (an
     accessor, constructor or -case), a space or a parenthesis, never by a
     letter: that would be another, longer name. *)
  let mentioned (tname : string) : bool =
    try
      ignore
        (Str.search_forward
           (Str.regexp (Str.quote tname ^ "\\([^a-z0-9]\\|$\\)"))
           vtext 0);
      true
    with Not_found -> false
  in
  (* 2. the types: the crate's own, and the std ones the code mentions *)
  let tbuf = Buffer.create 4096 in
  cur := tbuf;
  let type_used (id : TypeDeclId.id) : bool =
    match
      (TypeDeclId.Map.find_opt id ctx.trans_types,
       TypeDeclId.Map.find_opt id type_names)
    with
    | Some d, Some n -> d.item_meta.is_local || mentioned n
    | _ -> false
  in
  List.iter
    (fun (dg : LlbcAst.declaration_group) ->
      match dg with
      | LlbcAst.TypeGroup (NonRecGroup id) | LlbcAst.TypeGroup (RecGroup [ id ])
        -> if type_used id then emit_group dg
      | LlbcAst.TypeGroup (RecGroup ids) ->
          if List.exists type_used ids then emit_group dg
      | _ -> ())
    type_groups;
  (* Iterator-model companions: the decrement-model write-back and the
     defunctionalized continuation applier, one pair per IterMut model and
     per Zip model.  A Zip's write-back goes through its &mut component's
     -wb-some, and the component defprod need not precede the Zip in
     charon's type order, so these are emitted after ALL type groups (and
     before any function that applies a continuation). *)
  let opaque_model_names (pred : string -> bool) : string list =
    TypeDeclId.Map.fold
      (fun id (d : Pure.type_decl) acc ->
        match d.kind with
        | Opaque -> (
            match TypeDeclId.Map.find_opt id type_names with
            | Some n when pred n -> n :: acc
            | _ -> acc)
        | _ -> acc)
      ctx.trans_types []
    |> List.rev
  in
  let itermut_models =
    List.filter mentioned (opaque_model_names is_itermut_model_ty)
  in
  let zip_models = List.filter mentioned (opaque_model_names is_zip_model_ty) in
  List.iter
    (fun im ->
      Printf.bprintf !cur
        "(defun %s-wb-some (v im)\n\
        \  (%s (update-nth (- (%s->pos im) 1) v (%s->lst im))\n\
        \      (- (%s->pos im) 1)))\n\n" im im im im im;
      Printf.bprintf !cur
        "(defun %s-apply-back (vs im)\n\
        \  (if (atom vs)\n\
        \      im\n\
        \    (%s-apply-back (cdr vs) (%s-wb-some (car vs) im))))\n\n" im im im)
    itermut_models;
  (match (zip_models, itermut_models) with
  | [], _ -> ()
  | zs, [ im ] ->
      List.iter
        (fun z ->
          Printf.bprintf !cur
            "(defun %s-wb-some (v z)\n\
            \  (%s (%s-wb-some (car v) (%s->a z)) (%s->b z)))\n\n" z z im z z;
          Printf.bprintf !cur
            "(defun %s-apply-back (vs z)\n\
            \  (if (atom vs)\n\
            \      z\n\
            \    (%s-apply-back (cdr vs) (%s-wb-some (car vs) z))))\n\n" z z z)
        zs
  | zs, _ ->
      List.iter
        (fun z ->
          Printf.bprintf !cur
            ";; SKIPPED %s companions: needs exactly one IterMut model\n\n" z)
        zs);
  output_string out (Buffer.contents tbuf);
  output_string out vtext;
  Printf.fprintf out ";; END OF GENERATED FILE\n"
