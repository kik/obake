open Syntax

let () =
  let p t =
    Format.printf "%a@." pp_term t;
    begin
      try
        let (cs, ty) = constraints_term IdMap.empty t in
        Format.printf "  : %a@." pp_type ty;
        List.iter (fun (c1, c2) ->
          Format.printf "  %a = %a@."
            pp_type c1
            pp_type c2) cs;
        let ty = run_unify cs ty in
        Format.printf "  : %a@." pp_type ty
      with
      | Failure(s) ->
        Format.printf "error: %s@." s
    end;
    Format.printf "@."
  in
  Var("x") |> p;
  Mu(Id("x"), Cmd(Var("x"), Const(CBreak))) |> p;
  Const(CBreak) |> p;
  Mu(Tuple(Id("x"), Id("a")),
     Cmd(Var("x"), Var("a"))) |> p;
  ()


