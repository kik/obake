type id = string

type const =
| CInt of int
| CBreak
| CGetc
| CPutc
| CRealWorld

type mu_type =
| NegMu
| PosMu

type term =
| Var of id
| Pat of term pattern
| Mu of mu_type * id pattern * command
| Up of term
| InL of term
| InR of term
| Proj of (id pattern * command) * (id pattern * command)
| Const of const
and command =
| Cmd of term * term
and 'a pattern =
| Id of 'a
| Floor of 'a
| Unit
| Tuple of 'a pattern * 'a pattern

type btype =
| TyVar of int * string
| TyInt
| TyWorld

type ptype =
| PBase of btype
| PTensor of ptype * ptype
| POne
| PSum of ptype * ptype
| PZero
| POfCourse of ptype
| PDown of ntype
and ntype =
| NBase of btype
| NPar of ntype * ntype
| NBot
| NAnd of ntype * ntype
| NTop
| NWhyNot of ntype
| NUp of ptype

let mvar_index = ref 0
let alloc_type ~hint () =
  incr mvar_index;
  let bt = TyVar(!mvar_index, hint) in
  (PBase(bt), NBase(bt))

type ty =
| Pos of ptype
| Neg of ntype

let rec neg_ptype = function
  | PBase(id) -> NBase(id)
  | PTensor(pt1, pt2) ->
    NPar(neg_ptype pt1, neg_ptype pt2)
  | POne -> NBot
  | PSum(pt1, pt2) ->
    NAnd(neg_ptype pt1, neg_ptype pt2)
  | PZero -> NTop
  | POfCourse(pt) ->
    NWhyNot(neg_ptype pt)
  | PDown(nt) ->
    NUp(neg_ntype nt)
    
and neg_ntype = function
  | NBase(id) -> PBase(id)
  | NPar(nt1, nt2) ->
    PTensor(neg_ntype nt1, neg_ntype nt2)
  | NBot -> POne
  | NAnd(nt1, nt2) ->
    PSum(neg_ntype nt1, neg_ntype nt2)
  | NTop -> PZero
  | NWhyNot(nt) ->
    POfCourse(neg_ntype nt)
  | NUp(pt) ->
    PDown(neg_ptype pt)

let neg_type = function
  | Pos(tp) -> Neg(neg_ptype tp)
  | Neg(tn) -> Pos(neg_ntype tn)

type decl =
| Linear of ty
| Duplicable of ty

let is_duplicable = function
  | Linear(_) -> false
  | Duplicable(_) -> true

module IdSet = Set.Make(String)
module IdMap = Map.Make(String)

let id_map_merge_strict =
  IdMap.merge (fun i x y -> match x, y with
  | Some(_), Some(_) -> failwith ("duplicated binder: " ^ i)
  | Some(_), _ -> x
  | _, _ -> y)

let id_map_merge_left =
  IdMap.merge (fun i x y -> match x with
  | Some(_) -> x
  | _ -> y)

let rec freevars_pattern f = function
  | Id(t) | Floor(t) -> f t
  | Unit -> IdSet.empty
  | Tuple(p1, p2) ->
    let fv1 = freevars_pattern f p1 and
        fv2 = freevars_pattern f p2
    in
    IdSet.union fv1 fv2

let rec freevars =
  let open IdSet in
  function
  | Var(id) -> singleton id
  | Pat(p) -> freevars_pattern freevars p
  | Mu(_, p, c) -> freevars_binder p c
  | Up(t) -> freevars t
  | InL(t) -> freevars t
  | InR(t) -> freevars t
  | Proj((pl, cl), (pr, cr)) ->
    let fvl = freevars_binder pl cl and
        fvr = freevars_binder pr cr
    in
    union fvl fvr
  | Const(_) -> empty

and freevars_binder p = function
  | Cmd(t, u) ->
    let open IdSet in
    let pv = freevars_pattern singleton p and
        tv = freevars t and
        uv = freevars u in
    diff (union tv uv) pv


let assert_unused f assum =
  IdMap.iter
    (fun i decl ->
      if f i decl then () else
        failwith ("unused variable: " ^ i))
    assum

let split_assumption assum fvs =
  let (dup, lin) = IdMap.partition (fun _ -> is_duplicable) assum in
  let lins =
    List.map (fun fv ->
      IdMap.filter (fun i _ -> IdSet.mem i fv) lin)
      fvs
  in
  IdMap.iter (fun i _ ->
    match List.find_all (IdMap.mem i) lins with
    | [_] -> ()
    | [] -> failwith ("unused variable: " ^ i)
    | _ -> failwith ("duplicated variable: " ^ i))
    lin;
  List.map (id_map_merge_strict dup) lins

let split_assumption2 assum fv1 fv2 =
  match split_assumption assum [fv1; fv2] with
  | [a1; a2] -> (a1, a2)
  | _ -> assert false

let rec constraints_term_pattern assum =
  function
  | Id(t) -> constraints_term assum t
  | Floor(t) -> begin
    assert_unused (fun _ decl -> is_duplicable decl) assum;
    let (cs, ty) = constraints_term assum t in
    match ty with
    | Pos(tp) -> (cs, Pos(POfCourse(tp)))
    | Neg(_) -> failwith "can not floor negative type"
  end
  | Unit -> ([], Pos(POne))
  | Tuple(p1, p2) ->
    let fv1 = freevars_pattern freevars p1 and
        fv2 = freevars_pattern freevars p2
    in
    let (assum1, assum2) = split_assumption2 assum fv1 fv2 in
    let (cs1, ty1) = constraints_term_pattern assum1 p1 and
        (cs2, ty2) = constraints_term_pattern assum2 p2
    in
    (cs1 @ cs2, Pos(match ty1, ty2 with
    | Pos(tp1), Pos(tp2) -> PTensor(tp1, tp2)
    | _, _ -> failwith "can not tensor negative type"))

and constraints_binder_pattern =
  function
  | Id(t) ->
    let (pty, nty) = alloc_type ~hint:t () in
    (IdMap.singleton t (Linear(Pos(pty))), Neg(nty))
  | Floor(t) ->
    let (pty, nty) = alloc_type ~hint:t () in
    (IdMap.singleton t (Duplicable(Pos(pty))), Neg(NWhyNot(nty)))
  | Unit ->
    (IdMap.empty, Neg(NBot))
  | Tuple(p1, p2) ->
    let (bs1, ty1) = constraints_binder_pattern p1 and
        (bs2, ty2) = constraints_binder_pattern p2
    in
    (id_map_merge_strict bs1 bs2, Neg(match ty1, ty2 with
    | Neg(tn1), Neg(tn2) -> NPar(tn1, tn2)
    | _, _ -> failwith "can not par positive type"))

and constraints assum = function
  | Cmd(t, u) -> (* cut *)
    let fv_t = freevars t and
        fv_u = freevars u in
    let (assum1, assum2) = split_assumption2 assum fv_t fv_u in
    let (ct, tt) = constraints_term assum1 t and
        (cu, tu) = constraints_term assum2 u
    in
    match tt with
    | Pos(_) ->
      let cs = [tt, neg_type tu] in
      cs @ ct @ cu
    | Neg(_) ->
      failwith "type of first term must be positive"

and constraints_term assum =
  let open IdMap in
  function
  | Var(i) -> begin
    match find i assum with
    | Linear(ty) -> (* id *)
      assert_unused (fun j decl -> is_duplicable decl || i = j) assum;
      ([], ty)
    | Duplicable(ty) -> (* id' *)
      assert_unused (fun _ decl -> is_duplicable decl) assum;
      ([], ty)
    | exception Not_found -> failwith ("unbound variable: " ^ i)
  end
  | Pat(p) -> constraints_term_pattern assum p
  | Mu(NegMu, p, c) -> constraints_binder assum p c
  | Mu(PosMu, p, c) -> begin
    let (cs, ty) = constraints_binder assum p c in
    match ty with
    | Neg(nt) -> (cs, Pos(PDown(nt)))
    | Pos(_) -> assert false
  end
  | Up(t) -> begin
    let (cs, ty) = constraints_term assum t in
    match ty with
    | Pos(tp) -> (cs, Neg(NUp(tp)))
    | Neg(_) -> failwith "can not up negative type"
  end
  | InL(t) -> begin
    let (cs, ty) = constraints_term assum t in
    match ty with
    | Pos(tp1) ->
      let (tp2, _) = alloc_type ~hint:"InL" () in
      (cs, Pos(PSum(tp1, tp2)))
    | Neg(_) ->
      failwith "can not sum negative type"
  end
  | InR(t) -> begin
    let (cs, ty) = constraints_term assum t in
    match ty with
    | Pos(tp2) ->
      let (tp1, _) = alloc_type ~hint:"InR" () in
      (cs, Pos(PSum(tp1, tp2)))
    | Neg(_) ->
      failwith "can not sum negative type"
  end
  | Proj((pl, cl), (pr, cr)) ->
    let (csl, tyl) = constraints_binder assum pl cl and
        (csr, tyr) = constraints_binder assum pr cr
    in
    (csl @ csr, Neg(
      match tyl, tyr with
      | Neg(tnl), Neg(tnr) -> NAnd(tnl, tnr)
      | _, _ -> failwith "can not and positive type"))
  | Const(CInt(_)) -> ([], Pos(PBase(TyInt)))
  | Const(CBreak) -> ([], Neg(NBase(TyWorld)))
  | Const(CGetc) ->
    ([], Neg(
      NPar(NBase(TyWorld), NUp(PTensor(PBase(TyWorld), PBase(TyInt))))))
  | Const(CPutc) ->
    ([], Neg(
      NPar(NBase(TyWorld), NPar(NBase(TyInt), NUp(PBase(TyWorld))))))
  | Const(CRealWorld) ->
    ([], Pos(PBase(TyWorld)))

and constraints_binder assum p c =
  let (bs, ty) = constraints_binder_pattern p in
  let assum' = id_map_merge_left bs assum in
  let cs = constraints assum' c in
  (cs, ty)

let constraints_program t =
  let w = "#real_world" in
  let assum = IdMap.singleton w (Linear(Pos(PBase(TyWorld)))) in
  constraints assum (Cmd(Var(w), t))

module IntMap = Map.Make(struct type t = int let compare = compare end)

let rec unify ss = function
  | [] -> ss
  | (Pos(p1), Pos(p2))::cs -> unify_ptype ss p1 p2 cs
  | (Neg(n1), Neg(n2))::cs -> unify_ntype ss n1 n2 cs
  | _ -> failwith "can not unify positive type and negative type"

and unify_ptype ss p1 p2 cs =
  match p1, p2 with
  | _, _ when p1 = p2 -> unify ss cs
  | PBase(TyVar(id, h)), pt
  | pt, PBase(TyVar(id, h)) ->
    unify_var id pt ss cs
  | PTensor(p11, p12), PTensor(p21, p22)
  | PSum(p11, p12), PSum(p21, p22) ->
    unify ss ((Pos(p11), Pos(p21))::(Pos(p12), Pos(p22))::cs)
  | POfCourse(p1), POfCourse(p2) ->
    unify_ptype ss p1 p2 cs
  | PDown(n1), PDown(n2) ->
    unify_ntype ss n1 n2 cs
  | _, _ -> failwith "unification failed"

and unify_ntype ss n1 n2 cs =
  match n1, n2 with
  | _, _ when n1 = n2 -> unify ss cs
  | NBase(TyVar(id, h)), nt
  | nt, NBase(TyVar(id, h)) ->
    unify_var id (neg_ntype nt) ss cs
  | NPar(n11, n12), NPar(n21, n22)
  | NAnd(n11, n12), NAnd(n21, n22) ->
    unify ss ((Neg(n11), Neg(n21))::(Neg(n12), Neg(n22))::cs)
  | NWhyNot(n1), NWhyNot(n2) ->
    unify_ntype ss n1 n2 cs
  | NUp(p1), NUp(p2) ->
    unify_ptype ss p1 p2 cs
  | _, _ -> failwith "unification failed"

and unify_var id pt ss cs =
  occurs_check id pt;
  let ty = Pos(pt) in
  let sub = substitute (IntMap.singleton id ty) in
  unify
    (IntMap.add id ty (IntMap.map sub ss))
    (List.map (fun (tl, tr) -> (sub tl, sub tr)) cs)

and substitute ss = function
  | Pos(pt) -> Pos(substitute_ptype ss pt)
  | Neg(nt) -> Neg(substitute_ntype ss nt)

and substitute_ptype ss =
  let r = substitute_ptype in
  function
  | PBase(TyVar(id, _)) as pt -> begin
    match IntMap.find id ss with
    | Pos(pt) -> pt
    | Neg(nt) -> assert false
    | exception Not_found -> pt
  end
  | PTensor(pt1, pt2) -> PTensor(r ss pt1, r ss pt2)
  | PSum(pt1, pt2) -> PSum(r ss pt1, r ss pt2)
  | POfCourse(pt) -> POfCourse(r ss pt)
  | PDown(nt) -> PDown(substitute_ntype ss nt)
  | _ as pt -> pt

and substitute_ntype ss =
  let r = substitute_ntype in
  function
  | NBase(TyVar(id, _)) as nt -> begin
    match IntMap.find id ss with
    | Pos(pt) -> neg_ptype pt
    | Neg(nt) -> assert false
    | exception Not_found -> nt
  end
  | NPar(n1, n2) -> NPar(r ss n1, r ss n2)
  | NAnd(n1, n2) -> NAnd(r ss n1, r ss n2)
  | NWhyNot(nt) -> NWhyNot(r ss nt)
  | NUp(pt) -> NUp(substitute_ptype ss pt)
  | _ as nt -> nt

and occurs_check id =
  let r = occurs_check in
  function
  | PBase(TyVar(id', _)) when id = id' ->
    failwith "occurence check failed"
  | PTensor(pt1, pt2)
  | PSum(pt1, pt2) -> r id pt1; r id pt2
  | POfCourse(pt) -> r id pt
  | PDown(nt) -> r id (neg_ntype nt)
  | _ -> ()

let run_unify cs ty =
  let ss = unify IntMap.empty cs in
  (ss, substitute ss ty)

let check_unify cs =
  let ss = unify IntMap.empty cs in
  ignore ss

type value =
| VPat of value pattern
| VMu of id pattern * command * value IdMap.t
| VInL of value
| VInR of value
| VConst of const

let rec to_value env = function
  | Var(id) -> IdMap.find id env
  | Pat(p) -> VPat(to_value_pattern env p)
  | Mu(_, p, c) -> VMu(p, c, env)
  | Up(t) -> assert false
  | InL(t) -> VInL(to_value env t)
  | InR(t) -> VInR(to_value env t)
  | Proj(c1, c2) -> assert false
  | Const(c) -> VConst(c)

and to_value_pattern env = function
  | Id(t) -> Id(to_value env t)
  | Floor(t) -> Floor(to_value env t)
  | Unit -> Unit
  | Tuple(p1, p2) -> Tuple(to_value_pattern env p1, to_value_pattern env p2)

let rec add_env env p v = match p, v with
  | Id(id), VPat(Id(v))
  | Id(id), v
  | Floor(id), VPat(Floor(v)) ->
    IdMap.add id v env
  | Unit, VPat(Unit) -> env
  | Tuple(p1, p2), VPat(Tuple(v1, v2)) ->
    add_env (add_env env p1 (VPat(v1))) p2 (VPat(v2))
  | _, _ -> assert false

let step_cmd env = function
  | Cmd(t, u) -> Some(env, to_value env t, u)

let step env v u = match u, v with
  | Mu(_, p, c), v
  | Proj((p, c), _), VInL(v)
  | Proj(_, (p, c)), VInR(v) ->
    step_cmd (add_env env p v) c
  | Const(CBreak), VConst(CRealWorld) -> None
  | Const(CPutc), VPat(Tuple(Id(VConst(CRealWorld)), Tuple(Id(VConst(CInt(ch))), Id(ret)))) ->
    output_byte stdout ch;
    Some(env, ret, Up(Const(CRealWorld)))
  | Const(CGetc), VPat(Tuple(Id(VConst(CRealWorld)), Id(ret))) ->
    let ch =
      try input_byte stdin
      with End_of_file -> -1
    in
    Some(env, ret, Up(Pat(Tuple(Id(Const(CRealWorld)), Id(Const(CInt(ch)))))))
  | Up(u), VMu(p, c, env') ->
    step_cmd (add_env env' p (to_value env u)) c
  | _, _ ->
    assert false


open Format

let pp_const fmt = function
  | CInt(n) ->
    fprintf fmt "%d" n
  | CBreak -> pp_print_string fmt "break"
  | CGetc -> pp_print_string fmt "getc"
  | CPutc -> pp_print_string fmt "putc"
  | CRealWorld -> pp_print_string fmt "#world"

let rec pp_pattern pp_a fmt = function
  | Id(t) -> fprintf fmt "(%a)" pp_a t
  | Floor(t) ->
    fprintf fmt "!%a" pp_a t
  | Unit -> pp_print_string fmt "()"
  | Tuple(p1, p2) ->
    fprintf fmt "(%a, %a)"
      (pp_pattern pp_a) p1
      (pp_pattern pp_a) p2

let rec pp_term fmt = function
  | Var(id) -> pp_print_string fmt id
  | Pat(p) -> pp_pattern pp_term fmt p
  | Mu(m, p, c) ->
    begin
      match m with
      | NegMu -> pp_print_string fmt "(mu"
      | PosMu -> pp_print_string fmt "('mu"
    end;
    fprintf fmt " %a, %a)"
      (pp_pattern pp_print_string) p
      pp_command c
  | Up(t) ->
    fprintf fmt "^%a"
      pp_term t
  | InL(t) ->
    fprintf fmt "(inl %a)"
      pp_term t
  | InR(t) ->
    fprintf fmt "(inr %a)"
      pp_term t
  | Proj((pl, cl), (pr, cr)) ->
    fprintf fmt "{ case inl(%a) -> %a; case inr(%a) -> %a }"
      (pp_pattern pp_print_string) pl
      pp_command cl
      (pp_pattern pp_print_string) pr
      pp_command cr
  | Const(c) -> pp_const fmt c

and pp_command fmt = function
  | Cmd(t1, t2) ->
    fprintf fmt "<%a | %a>"
      pp_term t1
      pp_term t2

let rec pp_type fmt = function
  | Pos(pt) -> pp_ptype fmt pt
  | Neg(nt) -> pp_ntype fmt nt

and pp_ptype fmt = function
  | PBase(bt) -> pp_btype fmt bt
  | PTensor(p1, p2) ->
    fprintf fmt "(%a * %a)"
      pp_ptype p1
      pp_ptype p2
  | POne -> pp_print_string fmt "1"
  | PSum(p1, p2) ->
    fprintf fmt "(%a + %a)"
      pp_ptype p1
      pp_ptype p2
  | PZero -> pp_print_string fmt "0"
  | POfCourse(pt) ->
    fprintf fmt "!%a" pp_ptype pt
  | PDown(nt) ->
    fprintf fmt "#%a" pp_ntype nt

and pp_ntype fmt = function
  | NBase(bt) ->
    fprintf fmt "-%a" pp_btype bt
  | NPar(n1, n2) ->
    fprintf fmt "(%a @@ %a)"
      pp_ntype n1
      pp_ntype n2
  | NBot -> pp_print_string fmt "_|_"
  | NAnd(n1, n2) ->
    fprintf fmt "(%a & %a)"
      pp_ntype n1
      pp_ntype n2
  | NTop -> pp_print_string fmt "~|~"
  | NWhyNot(nt) ->
    fprintf fmt "?%a" pp_ntype nt
  | NUp(pt) ->
    fprintf fmt "^%a" pp_ptype pt

and pp_btype fmt = function
  | TyVar(n, hint) -> fprintf fmt "'%s<%d>" hint n
  | TyInt -> pp_print_string fmt "int"
  | TyWorld -> pp_print_string fmt "world"

let rec pp_value fmt = function
  | VPat(p) ->
    pp_pattern pp_value fmt p
  | VMu _ -> pp_print_string fmt "#closure"
  | VInL(v) ->
    fprintf fmt "inl(%a)" pp_value v
  | VInR(v) ->
    fprintf fmt "inr(%a)" pp_value v
  | VConst(c) -> pp_const fmt c
