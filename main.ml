open Syntax

(*
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
*)
(*
let () =
  let p s =
    let t = Parser.term Lexer.token (Lexing.from_string s) in
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
  "break" |> p;
  "mu world, < world | break >" |> p;
  "mu w, < (w, w) | mu (x, y), < x | break >>" |> p;
  "mu w, < w | mu w, < w | break > >" |> p;

  ()
*)

let run_type_checker ~verbose t =
  let fv = freevars t in
  let assum =
    IdSet.fold (fun id a ->
      let (pt, _) = alloc_type () in
      IdMap.add id (Duplicable(Pos(pt))) a
    ) fv IdMap.empty
  in
  Format.printf "input: %a@." pp_term t;
  begin
    try
      let (cs, ty) = constraints_term assum t in
      Format.printf "  type: %a@." pp_type ty;
      Format.printf "  constraints:@.";
      List.iter (fun (c1, c2) ->
        Format.printf "    %a = %a@."
          pp_type c1
          pp_type c2) cs;
      let ty = run_unify cs ty in
      Format.printf "  inferred type: %a@." pp_type ty
    with
    | Failure(s) ->
      Format.printf "error: %s@." s
  end

let run_interp ~verbose t =
  if verbose then
    Format.eprintf "input: %a@." pp_term t;
  try
    let cs = constraints_program t in
    check_unify cs;
    if verbose then
      Format.eprintf "Execute:@.";
    let rec loop env c =
      if verbose then begin
        Format.eprintf "--------@.";
        Format.eprintf "  [@.";
        IdMap.iter (fun id v ->
          Format.eprintf "    %s := %a@." id pp_value v)
          env;
        Format.eprintf "  ]@.";
        Format.eprintf "  %a ===>@.@." pp_command c;
      end;
      match step env c with
      | Some(env, c) -> loop env c
      | None -> ()
    in
    let r = "__internal_real_world" in
    let c = Cmd(Var(r), t) in
    loop (IdMap.singleton r VRealWorld) c;
    if verbose then
      Format.eprintf "Done@.";
  with
  | Failure(s) ->
    Format.eprintf "error: %s@." s

let main ~type_check_only ~enable_cpp ~verbose file =
  let t =
    let ch = open_in file in
    let t = Parser.term Lexer.token (Lexing.from_channel ch) in
    close_in ch; t
  in
  if type_check_only then
    run_type_checker ~verbose t
  else
    run_interp ~verbose t

let () =
  let open Arg in
  let type_check_only = ref false and
      enable_cpp = ref false and
      verbose = ref false and
      files = ref []
  in
  let s = [
    ("-t", Arg.Set type_check_only, "run type checker only (can handle open term)");
    ("-p", Arg.Set enable_cpp, "enable preprocessor (not implemented)");
    ("-v", Arg.Set verbose, "verbose mode");
  ] in
  Arg.parse s (fun arg -> files := !files @ [arg])  "";

  List.iter (main ~type_check_only:!type_check_only ~enable_cpp:!enable_cpp ~verbose:!verbose) !files

