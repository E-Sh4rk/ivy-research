open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Some (Parser.next_expression (Lexer.read false) lexbuf) with
  | Lexer.SyntaxError msg ->
    Printf.fprintf stderr "[Lexing] %a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    Printf.fprintf stderr "[Parsing] %a: syntax error\n" print_position lexbuf;
    None

let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | None ->
    ()
  | Some ast ->
    Printf.fprintf stdout "Result: %s" (Sexplib.Sexp.to_string (Sexplib.Conv.sexp_of_unit ())) ;
    parse_and_print lexbuf


let () =
  let filename = "stdin" in
  let lexbuf = Lexing.from_channel (stdin) in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
