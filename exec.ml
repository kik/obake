open Syntax

let rec to_value env = function
  | Var(id) -> IdMap.find id env
  | Pat(p) -> to_value_pattern env p
  | Mu(_, p, c) -> VMu(p, c, env)
  | Up(t) -> assert false
  | InL(t) -> VInL(to_value env t)
  | InR(t) -> VInR(to_value env t)
  | Proj(c1, c2) -> assert false
  | Const(c) -> VConst(c)

and to_value_pattern env = function
  | Id(t) -> to_value env t
  | Floor(t) -> to_value env t
  | Unit -> VUnit
  | False -> assert false
  | Tuple(p1, p2) -> VTuple(to_value_pattern env p1, to_value_pattern env p2)

let rec add_env env p v = match p, v with
  | Id(id), v
  | Floor(id), v ->
    IdMap.add id v env
  | Unit, VUnit -> env
  | Tuple(p1, p2), VTuple(v1, v2) ->
    add_env (add_env env p1 v1) p2 v2
  | _, _ -> assert false

let step_cmd env = function
  | Cmd(t, u) -> Some(env, to_value env t, u)

let step env v u = match u, v with
  | Mu(_, p, c), v
  | Proj((p, c), _), VInL(v)
  | Proj(_, (p, c)), VInR(v) ->
    step_cmd (add_env env p v) c
  | Const(CBreak), VConst(CRealWorld) -> None
  | Const(CPutc), VTuple(VConst(CRealWorld), VTuple(VConst(CInt(ch)), ret)) ->
    output_byte stdout ch;
    flush stdout;
    Some(env, ret, Up(Const(CRealWorld)))
  | Const(CGetc), VTuple(VConst(CRealWorld), ret) ->
    let ch =
      try InR(Const(CInt(input_byte stdin)))
      with End_of_file -> InL(Pat(Unit))
    in
    Some(env, ret, Up(Pat(Tuple(Id(Const(CRealWorld)), Id(ch)))))
  | Const(CFix), VTuple(VMu(p, c, env'), ret) ->
    step_cmd (add_env env' p (VTuple(VFix(p, c, env'), ret))) c
  | Up(u), VMu(p, c, env') ->
    step_cmd (add_env env' p (to_value env u)) c
  | Up(u), (VFix(p, c, env') as f) ->
    step_cmd (add_env env' p (VTuple(f, to_value env u))) c
  | _, _ ->
    assert false
