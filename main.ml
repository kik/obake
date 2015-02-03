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

let () =
  let p t =
    Format.printf "Term: %a@." pp_term t;
    begin
      try
        let cs = constraints_program t in
        Format.printf "Type constraints:@.";
        List.iter (fun (c1, c2) ->
          Format.printf "  %a = %a@."
            pp_type c1
            pp_type c2) cs;
        check_unify cs;
        Format.printf "Execute:@.";
        let rec loop env c =
          Format.printf "--------@.";
          Format.printf "  [@.";
          IdMap.iter (fun id v ->
            Format.printf "    %s := %a@." id pp_value v)
            env;
          Format.printf "  ]@.";
          Format.printf "  %a ===>@.@." pp_command c;
          match step env c with
          | Some(env, c) -> loop env c
          | None -> ()
        in
        let r = "__internal_real_world" in
        let c = Cmd(Var(r), t) in
        loop (IdMap.singleton r VRealWorld) c;
        Format.printf "Done@."
      with
      | Failure(s) ->
        Format.printf "error: %s@." s
    end;
    Format.printf "@."
  in
  Const(CBreak) |> p;
  Mu(Id("world"), Cmd(Var("world"), Const(CBreak))) |> p;

  ()

