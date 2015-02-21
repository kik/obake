open Syntax
open Format

let pp_const fmt =
  let p = pp_print_string fmt in
  function
  | CInt(n) ->
    fprintf fmt "%d" n
  | CBreak -> p "break"
  | CGetc -> p "getc"
  | CPutc -> p "putc"
  | CPrintInt -> p "print_int"
  | CRealWorld -> p "#world"
  | CFix -> p "fix"
  | CNeg -> p "neg"
  | CAdd -> p "add"
  | CSub -> p "sub"
  | CLt -> p "lt"
  | CGt -> p "gt"
  | CLe -> p "le"
  | CGe -> p "ge"
  | CEq -> p "eq"
  | CNe -> p "ne"

let rec pp_pattern pp_a fmt = function
  | Id(t) -> pp_a fmt t
  | Floor(t) ->
    fprintf fmt "!%a" pp_a t
  | Unit -> pp_print_string fmt "()"
  | False -> pp_print_string fmt "{}"
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
  | VUnit -> pp_print_string fmt "()"
  | VTuple(v1, v2) ->
    fprintf fmt "(%a, %a)" pp_value v1 pp_value v2
  | VMu _  -> pp_print_string fmt "#closure"
  | VFix _ -> pp_print_string fmt "#fix"
  | VInL(v) ->
    fprintf fmt "inl(%a)" pp_value v
  | VInR(v) ->
    fprintf fmt "inr(%a)" pp_value v
  | VConst(c) -> pp_const fmt c
