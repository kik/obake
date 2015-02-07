open Syntax
open Pp
open Infer
open Exec

let run_type_checker ~verbose t =
  let fv = freevars t in
  let assum =
    IdSet.fold (fun id a ->
      let (pt, _) = alloc_type ~hint:id () in
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
      let (ss, ty) = run_unify cs ty in
      Format.printf "  inferred type: %a@." pp_type ty;
      Format.printf "  substitute:@.";
      IntMap.iter (fun i ty ->
        Format.printf "    %d := %a@." i pp_type ty)
        ss
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
    let rec loop env v u =
      if verbose then begin
        Format.eprintf "--------@.";
        Format.eprintf "  [@.";
        IdMap.iter (fun id v ->
          Format.eprintf "    %s := %a@." id pp_value v)
          env;
        Format.eprintf "  ]@.";
        Format.eprintf "  <%a | %a> ===>@.@." pp_term v pp_value u;
      end;
      match step env v u with
      | Some(env, v, u) -> loop env v u
      | None -> ()
    in
    loop IdMap.empty t (VConst(CRealWorld));
    if verbose then
      Format.eprintf "Done@.";
  with
  | Failure(s) ->
    Format.eprintf "error: %s@." s

let main ~type_check_only ~enable_cpp ~verbose file =
  let t =
    let cmd = if enable_cpp
      then "cpp -w " ^ file
      else "cat " ^ file
    in
    let ch = Unix.open_process_in cmd in
    let t = Parser.term Lexer.token (Lexing.from_channel ch) in
    ignore (Unix.close_process_in ch); t
  in
  if type_check_only then
    run_type_checker ~verbose t
  else
    run_interp ~verbose t

let () =
  let open Arg in
  let type_check_only = ref false and
      disable_cpp = ref false and
      verbose = ref false and
      files = ref []
  in
  let s = [
    ("-t", Arg.Set type_check_only, "run type checker only (can handle open term)");
    ("-p", Arg.Set disable_cpp, "disable preprocessor");
    ("-v", Arg.Set verbose, "verbose mode");
  ] in
  Arg.parse s (fun arg -> files := !files @ [arg])  "";

  let files =
    match !files with
    | [] -> ["-"]
    | x -> x
  in
  List.iter (main ~type_check_only:!type_check_only ~enable_cpp:(not !disable_cpp) ~verbose:!verbose) files

