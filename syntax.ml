type id = string

type const =
| CInt of int
| CBreak
| CGetc
| CPutc
| CPrintInt
| CRealWorld
| CFix
| CNeg
| CAdd
| CSub
| CLt
| CGt
| CLe
| CGe
| CEq
| CNe

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
| False
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

module IdSet = Set.Make(String)
module IdMap = Map.Make(String)

type value =
| VUnit
| VTuple of value * value
| VMu  of id pattern * command * value IdMap.t
| VFix of id pattern * command * value IdMap.t
| VInL of value
| VInR of value
| VConst of const
