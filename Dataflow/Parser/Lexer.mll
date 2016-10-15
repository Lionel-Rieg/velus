(* *********************************************************************)
(*                                                                     *)
(*                    The Velus Lustre compiler                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* This lexer draws on the work of Jacques-Henri Jourdan for the CompCert
   project (CompCert/cparser/Lexer.mll). *)

{
open Specif
open Lexing
open Parser
open !Aut.GramDefs

module SSet = Set.Make(String)

let lexicon : (string, Ast.astloc -> token) Hashtbl.t = Hashtbl.create 17

let tok t loc = Coq_existT (t, Obj.magic loc)

let () =
  List.iter (fun (key, builder) -> Hashtbl.add lexicon key builder)
    [
      ("else",     fun loc -> tok ELSE't     loc);
      ("float",    fun loc -> tok FLOAT't    loc);
      ("double",   fun loc -> tok DOUBLE't   loc);
      ("bool",     fun loc -> tok BOOL't     loc);
      ("if",       fun loc -> tok IF't       loc);
      ("then",     fun loc -> tok THEN't     loc);
      ("int8_t",   fun loc -> tok INT8_T't   loc);
      ("uint8_t",  fun loc -> tok UINT8_T't  loc);
      ("int16_t",  fun loc -> tok INT16_T't  loc);
      ("uint16_t", fun loc -> tok UINT16_T't loc);
      ("int32_t",  fun loc -> tok INT32_T't  loc);
      ("uint32_t", fun loc -> tok UINT32_T't loc);
      ("int64_t",  fun loc -> tok INT64_T't  loc);
      ("uint64_t", fun loc -> tok UINT64_T't loc);
      ("returns",  fun loc -> tok RETURNS't  loc);
      ("lsl",      fun loc -> tok LSL't      loc);
      ("lsr",      fun loc -> tok LSR't      loc);
      ("land",     fun loc -> tok LAND't     loc);
      ("lxor",     fun loc -> tok LXOR't     loc);
      ("lor",      fun loc -> tok LOR't      loc);
      ("lnot",     fun loc -> tok LNOT't     loc);
      ("xor",      fun loc -> tok XOR't      loc);
      ("not",      fun loc -> tok NOT't      loc);
      ("and",      fun loc -> tok AND't      loc);
      ("or",       fun loc -> tok OR't       loc);
      ("mod",      fun loc -> tok MOD't      loc);
      ("let",      fun loc -> tok LET't      loc);
      ("tel",      fun loc -> tok TEL't      loc);
      ("node",     fun loc -> tok NODE't     loc);
      ("var",      fun loc -> tok VAR't      loc);
      ("fby",      fun loc -> tok FBY't      loc);
      ("when",     fun loc -> tok WHEN't     loc);
      ("whenot",   fun loc -> tok WHENOT't   loc);
      ("merge",    fun loc -> tok MERGE't    loc);
      ("on",       fun loc -> tok ON't       loc);
      ("onot",     fun loc -> tok ONOT't     loc);
      ("",         fun loc -> tok RETURNS't  loc);
    ]

let init filename channel : Lexing.lexbuf =
  let lb = Lexing.from_channel channel in
  lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = filename; pos_lnum = 1};
  lb

let currentLoc =
  let nextident = ref 0 in
  let getident () =
    nextident := !nextident + 1;
    !nextident
  in
  fun lb ->
    let p = Lexing.lexeme_start_p lb in
    Ast.({ lineno   = p.Lexing.pos_lnum;
            filename = p.Lexing.pos_fname;
            byteno   = p.Lexing.pos_cnum;
            ident    = getident ();})

(* Error reporting *)

exception Abort

let fatal_error lb fmt =
  Format.kfprintf
    (fun _ -> raise Abort)
    Format.err_formatter
    ("@[<hov 2>%s:%d: Error:@ " ^^ fmt
      ^^ ".@]@.@[<hov 0>Fatal error; compilation aborted.@]@.")
      lb.lex_curr_p.pos_fname lb.lex_curr_p.pos_lnum

let error lb fmt =
  Format.eprintf  ("@[<hov 2>%s:%d: Error:@ " ^^ fmt ^^ ".@]@.")
      lb.lex_curr_p.pos_fname lb.lex_curr_p.pos_lnum

let warning lb fmt =
  Format.eprintf  ("@[<hov 2>%s:%d: Warning:@ " ^^ fmt ^^ ".@]@.")
      lb.lex_curr_p.pos_fname lb.lex_curr_p.pos_lnum

(* Simple character escapes *)

let convert_escape = function
  | 'a' -> 7L  (* bell *)
  | 'b' -> 8L  (* backspace  *)
  | 'e' -> 27L (* escape (GCC extension) *)
  | 'f' -> 12L (* form feed *)
  | 'n' -> 10L (* new line *)
  | 'r' -> 13L (* carriage return *)
  | 't' -> 9L  (* horizontal tab *)
  | 'v' -> 11L (* vertical tab *)
  | c   -> Int64.of_int (Char.code c)
}

(* Identifiers *)
let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let nondigit = ['_' 'a'-'z' 'A'-'Z']

let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" (hex_quad as n)
  | "\\U" (hex_quad hex_quad as n)

let identifier_nondigit =
    nondigit
(*| universal_character_name*)
  | '$'

let identifier = identifier_nondigit (identifier_nondigit|digit)*

(* Whitespaces *)
let whitespace_char_no_newline = [' ' '\t' '\012' '\r']

(* Integer constants *)
let nonzero_digit = ['1'-'9']
let decimal_constant = nonzero_digit digit*

let octal_digit = ['0'-'7']
let octal_constant = '0' octal_digit*

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_constant =
  hexadecimal_prefix hexadecimal_digit+

let unsigned_suffix = ['u' 'U']
let long_suffix = ['l' 'L']
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?

let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?

(* Floating constants *)
let sign = ['-' '+']
let digit_sequence = digit+
let floating_suffix = ['f' 'l' 'F' 'L'] as suffix

let fractional_constant =
    (digit_sequence as intpart)? '.' (digit_sequence as frac)
  | (digit_sequence as intpart) '.'
let exponent_part =
    'e' ((sign? digit_sequence) as expo)
  | 'E' ((sign? digit_sequence) as expo)
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | (digit_sequence as intpart) exponent_part floating_suffix?

let hexadecimal_digit_sequence = hexadecimal_digit+
let hexadecimal_fractional_constant =
    (hexadecimal_digit_sequence as intpart)? '.' (hexadecimal_digit_sequence
                                                    as frac)
  | (hexadecimal_digit_sequence as intpart) '.'
let binary_exponent_part =
    'p' ((sign? digit_sequence) as expo)
  | 'P' ((sign? digit_sequence) as expo)
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix (hexadecimal_digit_sequence as intpart)
        binary_exponent_part floating_suffix?

(* Character and string constants *)
let simple_escape_sequence =
  '\\' ( ['\''  '\"'  '?'  '\\'  'a'  'b'  'e'  'f'  'n'  'r'  't'  'v'] as c)
let octal_escape_sequence =
  '\\' ((octal_digit
         | octal_digit octal_digit
         | octal_digit octal_digit octal_digit) as n)
let hexadecimal_escape_sequence = "\\x" (hexadecimal_digit+ as n)
let escape_sequence =
    simple_escape_sequence
  | octal_escape_sequence
  | hexadecimal_escape_sequence
  | universal_character_name

rule initial = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline +  { initial lexbuf }
  | "(*"                          { multiline_comment lexbuf; initial lexbuf }
  | "//"                          { singleline_comment lexbuf; initial lexbuf }
  | integer_constant as s         { tok CONSTANT't (Ast.CONST_INT s,
                                                    currentLoc lexbuf) }
  | decimal_floating_constant     { tok CONSTANT't (Ast.CONST_FLOAT
                                      {Ast.isHex_FI = false;
                                       Ast.integer_FI = intpart;
                                       Ast.fraction_FI = frac;
                                       Ast.exponent_FI = expo;
                                       Ast.suffix_FI =
                                         match suffix with
                                         | None -> None
                                         | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf) }
  | hexadecimal_floating_constant { tok CONSTANT't (Ast.CONST_FLOAT
                                      {Ast.isHex_FI = true;
                                       Ast.integer_FI = intpart;
                                       Ast.fraction_FI = frac;
                                       Ast.exponent_FI = Some expo;
                                       Ast.suffix_FI =
                                         match suffix with
                                           | None -> None
                                           | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf)}
  | "'"                           { let l = char_literal lexbuf.lex_start_p []
                                              lexbuf in
                                    tok CONSTANT't (Ast.CONST_CHAR(false, l),
                                                    currentLoc lexbuf) }
  | "L'"                          { let l = char_literal lexbuf.lex_start_p []
                                              lexbuf in
                                    tok CONSTANT't (Ast.CONST_CHAR(true, l),
                                                    currentLoc lexbuf) }
  | "<>"                          { tok NEQ't (currentLoc lexbuf) }
  | "<="                          { tok LEQ't (currentLoc lexbuf) }
  | ">="                          { tok GEQ't (currentLoc lexbuf) }
  | "="                           { tok EQ't (currentLoc lexbuf) }
  | "<"                           { tok LT't (currentLoc lexbuf) }
  | ">"                           { tok GT't (currentLoc lexbuf) }
  | "+"                           { tok PLUS't (currentLoc lexbuf) }
  | "-"                           { tok MINUS't (currentLoc lexbuf) }
  | "*"                           { tok STAR't (currentLoc lexbuf) }
  | "/"                           { tok SLASH't (currentLoc lexbuf) }
  | ":"                           { tok COLON't (currentLoc lexbuf) }
  | "("                           { tok LPAREN't (currentLoc lexbuf) }
  | ")"                           { tok RPAREN't (currentLoc lexbuf) }
  | ";"                           { tok SEMICOLON't (currentLoc lexbuf) }
  | ","                           { tok COMMA't (currentLoc lexbuf) }
  | "."                           { tok DOT't (currentLoc lexbuf) }
  | identifier as id              {
      try Hashtbl.find lexicon id (currentLoc lexbuf)
      with Not_found -> tok VAR_NAME't (id, currentLoc lexbuf) }
  | eof                           { tok EOF't () }
  | _ as c                        { fatal_error lexbuf "invalid symbol %C" c }

and initial_linebegin = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline    { initial_linebegin lexbuf }
  | ""                            { initial lexbuf }

and char = parse
  | universal_character_name
      { try
          Int64.of_string ("0x" ^ n)
        with Failure _ ->
          error lexbuf "overflow in universal character name";
          0L
      }
  | hexadecimal_escape_sequence
      { try
          Int64.of_string ("0x" ^ n)
        with Failure _ ->
          error lexbuf "overflow in hexadecimal escape sequence";
          0L
      }
  | octal_escape_sequence
      { Int64.of_string  ("0o" ^ n) }
  | simple_escape_sequence
      { convert_escape c }
  | '\\' (_ as c)
      { error lexbuf "incorrect escape sequence '\\%c'" c;
        Int64.of_int (Char.code c) }
  | _ as c
      { Int64.of_int (Char.code c) }

and char_literal startp accu = parse
  | '\''       { lexbuf.lex_start_p <- startp;
                 List.rev accu }
  | '\n' | eof { fatal_error lexbuf "missing terminating \"'\" character" }
  | ""         { let c = char lexbuf in char_literal startp (c :: accu) lexbuf }

(* Multi-line comment terminated by "* )" *)
and multiline_comment = parse
  | "*)"   { () }
  | "(*"   { multiline_comment lexbuf;
             multiline_comment lexbuf }
  | eof    { error lexbuf "unterminated comment" }
  | '\n'   { new_line lexbuf; multiline_comment lexbuf }
  | _      { multiline_comment lexbuf }

(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | '\n'   { new_line lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }

{
  open Streams

  let tokens_stream filename : Parser.Aut.GramDefs.token coq_Stream =
    let lexbuf = Lexer.init filename (open_in filename) in
    let rec loop () =
      Cons (Lexer.initial lexbuf, Lazy.from_fun loop)
    in
    Lazy.from_fun loop
}

