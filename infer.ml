open Syntax

let mvar_index = ref 0
let alloc_type2 ~hint () =
  incr mvar_index;
  let bt = TyVar(!mvar_index, hint) in
  (PBase(bt), NBase(bt))

let alloc_ptype ~hint () =
  fst (alloc_type2 ~hint ())

let alloc_ntype ~hint () =
  snd (alloc_type2 ~hint ())

let alloc_type ~hint () =
  Pos(alloc_ptype ~hint ())

let type_of_const =
  let unpos = function | Pos(t) -> t | _ -> assert false
  and unneg = function | Neg(t) -> t | _ -> assert false
  in
  let int   = Pos(PBase(TyInt))
  and world = Pos(PBase(TyWorld))
  and one   = Pos(POne)
  and (~~)  = neg_type
  and ( * ) t1 t2 = Pos(PTensor(unpos t1, unpos t2))
  and (+)   t1 t2 = Pos(PSum(unpos t1, unpos t2))
  and (@)   t1 t2 = Neg(NPar(unneg t1, unneg t2))
  and (!.) t = Pos(POfCourse(unpos t))
  and up   t = Neg(NUp(unpos t))
  and down t = Pos(PDown(unneg t))
  in
  let (^-->) t1 t2 = ~~t1 @ t2 (* -o *) in
  let absty ~hint f = f (alloc_type ~hint ()) in
  let bool = one + one in
  function
  | CInt(_) -> int
  | CBreak -> ~~world
  | CGetc -> world ^--> up (world * (one + int))
  | CPutc -> world ^--> int ^--> up world
  | CPrintInt -> world ^--> int ^--> up world
  | CRealWorld -> world
  | CFix ->
    absty ~hint:"fix" (fun t ->
      !.(down (
        !.(down ~~t) ^--> ~~t)
      )
      ^--> ~~t)
  | CNeg -> int ^--> up !.int
  | CAdd | CSub -> int ^--> int ^--> up !.int
  | CLt | CGt | CLe | CGe | CEq | CNe -> int ^--> int ^--> up bool


type decl =
| Linear of ty
| Duplicable of ty

let is_duplicable = function
  | Linear(_) -> false
  | Duplicable(_) -> true

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
  | Unit | False -> IdSet.empty
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
  | False -> assert false
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
    let (pty, nty) = alloc_type2 ~hint:t () in
    (IdMap.singleton t (Linear(Pos(pty))), Neg(nty))
  | Floor(t) ->
    let (pty, nty) = alloc_type2 ~hint:t () in
    (IdMap.singleton t (Duplicable(Pos(pty))), Neg(NWhyNot(nty)))
  | Unit ->
    (IdMap.empty, Neg(NBot))
  | False ->
    (IdMap.empty, Neg(NTop))
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
    | Neg(_) ->
      let cs = [tt, neg_type tu] in
      cs @ ct @ cu
    | Pos(_) ->
      failwith "type of first term must be negative"

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
      let tp2 = alloc_ptype ~hint:"InL" () in
      (cs, Pos(PSum(tp1, tp2)))
    | Neg(_) ->
      failwith "can not sum negative type"
  end
  | InR(t) -> begin
    let (cs, ty) = constraints_term assum t in
    match ty with
    | Pos(tp2) ->
      let tp1 = alloc_ptype ~hint:"InR" () in
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
  | Const(c) -> ([], type_of_const c)

and constraints_binder assum p c =
  let (bs, ty) = constraints_binder_pattern p in
  let assum' = id_map_merge_left bs assum in
  let cs = constraints assum' c in
  (cs, ty)

let constraints_program t =
  let w = "#real_world" in
  let assum = IdMap.singleton w (Linear(Pos(PBase(TyWorld)))) in
  constraints assum (Cmd(t, Var(w)))

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
