(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)


let map_token (tok : LustreParser.Aut.GramDefs.token) =
  let open LustreParser.Aut.GramDefs in
  match tok with
  | ASSERT     loc -> (LustreParser2.ASSERT     loc)
  | AND        loc -> (LustreParser2.AND        loc)
  | BOOL       loc -> (LustreParser2.BOOL       loc)
  | COLONCOLON loc -> (LustreParser2.COLONCOLON loc)
  | COLON      loc -> (LustreParser2.COLON      loc)
  | COMMA      loc -> (LustreParser2.COMMA      loc)
  | CONSTANT  cloc -> (LustreParser2.CONSTANT  cloc)
  | DOT        loc -> (LustreParser2.DOT        loc)
  | ELSE       loc -> (LustreParser2.ELSE       loc)
  | EVERY      loc -> (LustreParser2.EVERY      loc)
  | EOF        loc -> (LustreParser2.EOF        loc)
  | EQ         loc -> (LustreParser2.EQ         loc)
  | HASH       loc -> (LustreParser2.HASH       loc)
  | FALSE      loc -> (LustreParser2.FALSE      loc)
  | FBY        loc -> (LustreParser2.FBY        loc)
  | FLOAT32    loc -> (LustreParser2.FLOAT32    loc)
  | FLOAT64    loc -> (LustreParser2.FLOAT64    loc)
  | FUNCTION   loc -> (LustreParser2.FUNCTION   loc)
  | GEQ        loc -> (LustreParser2.GEQ        loc)
  | GT         loc -> (LustreParser2.GT         loc)
  | IFE        loc -> (LustreParser2.IFE        loc)
  | INT16      loc -> (LustreParser2.INT16      loc)
  | INT32      loc -> (LustreParser2.INT32      loc)
  | INT64      loc -> (LustreParser2.INT64      loc)
  | INT8       loc -> (LustreParser2.INT8       loc)
  | LAND       loc -> (LustreParser2.LAND       loc)
  | LEQ        loc -> (LustreParser2.LEQ        loc)
  | LET        loc -> (LustreParser2.LET        loc)
  | LNOT       loc -> (LustreParser2.LNOT       loc)
  | LOR        loc -> (LustreParser2.LOR        loc)
  | LPAREN     loc -> (LustreParser2.LPAREN     loc)
  | LSL        loc -> (LustreParser2.LSL        loc)
  | LSR        loc -> (LustreParser2.LSR        loc)
  | LT         loc -> (LustreParser2.LT         loc)
  | LXOR       loc -> (LustreParser2.LXOR       loc)
  | MERGE      loc -> (LustreParser2.MERGE      loc)
  | MINUS      loc -> (LustreParser2.MINUS      loc)
  | MOD        loc -> (LustreParser2.MOD        loc)
  | NEQ        loc -> (LustreParser2.NEQ        loc)
  | NODE       loc -> (LustreParser2.NODE       loc)
  | NOT        loc -> (LustreParser2.NOT        loc)
  | ON         loc -> (LustreParser2.ON         loc)
  | ONOT       loc -> (LustreParser2.ONOT       loc)
  | OR         loc -> (LustreParser2.OR         loc)
  | PLUS       loc -> (LustreParser2.PLUS       loc)
  | RARROW     loc -> (LustreParser2.RARROW     loc)
  | RESTART    loc -> (LustreParser2.RESTART    loc)
  | RETURNS    loc -> (LustreParser2.RETURNS    loc)
  | RPAREN     loc -> (LustreParser2.RPAREN     loc)
  | SEMICOLON  loc -> (LustreParser2.SEMICOLON  loc)
  | SLASH      loc -> (LustreParser2.SLASH      loc)
  | STAR       loc -> (LustreParser2.STAR       loc)
  | TEL        loc -> (LustreParser2.TEL        loc)
  | THEN       loc -> (LustreParser2.THEN       loc)
  | TRUE       loc -> (LustreParser2.TRUE       loc)
  | UINT16     loc -> (LustreParser2.UINT16     loc)
  | UINT32     loc -> (LustreParser2.UINT32     loc)
  | UINT64     loc -> (LustreParser2.UINT64     loc)
  | UINT8      loc -> (LustreParser2.UINT8      loc)
  | VAR        loc -> (LustreParser2.VAR        loc)
  | VAR_NAME  iloc -> (LustreParser2.VAR_NAME  iloc)
  | WHEN       loc -> (LustreParser2.WHEN       loc)
  | WHENOT     loc -> (LustreParser2.WHENOT     loc)
  | XOR        loc -> (LustreParser2.XOR        loc)

(* TODO: is it already present somewhere? *)
let token_loc (tok : LustreParser2.token) : LustreAst.astloc =
  match tok with
  | LustreParser2.ASSERT     loc -> loc
  | LustreParser2.AND        loc -> loc
  | LustreParser2.BOOL       loc -> loc
  | LustreParser2.COLONCOLON loc -> loc
  | LustreParser2.COLON      loc -> loc
  | LustreParser2.COMMA      loc -> loc
  | LustreParser2.CONSTANT (_,l) -> l
  | LustreParser2.DOT        loc -> loc
  | LustreParser2.ELSE       loc -> loc
  | LustreParser2.EVERY      loc -> loc
  | LustreParser2.EOF        loc -> loc
  | LustreParser2.EQ         loc -> loc
  | LustreParser2.HASH       loc -> loc
  | LustreParser2.FALSE      loc -> loc
  | LustreParser2.FBY        loc -> loc
  | LustreParser2.FLOAT32    loc -> loc
  | LustreParser2.FLOAT64    loc -> loc
  | LustreParser2.FUNCTION   loc -> loc
  | LustreParser2.GEQ        loc -> loc
  | LustreParser2.GT         loc -> loc
  | LustreParser2.IFE        loc -> loc
  | LustreParser2.INT16      loc -> loc
  | LustreParser2.INT32      loc -> loc
  | LustreParser2.INT64      loc -> loc
  | LustreParser2.INT8       loc -> loc
  | LustreParser2.LAND       loc -> loc
  | LustreParser2.LEQ        loc -> loc
  | LustreParser2.LET        loc -> loc
  | LustreParser2.LNOT       loc -> loc
  | LustreParser2.LOR        loc -> loc
  | LustreParser2.LPAREN     loc -> loc
  | LustreParser2.LSL        loc -> loc
  | LustreParser2.LSR        loc -> loc
  | LustreParser2.LT         loc -> loc
  | LustreParser2.LXOR       loc -> loc
  | LustreParser2.MERGE      loc -> loc
  | LustreParser2.MINUS      loc -> loc
  | LustreParser2.MOD        loc -> loc
  | LustreParser2.NEQ        loc -> loc
  | LustreParser2.NODE       loc -> loc
  | LustreParser2.NOT        loc -> loc
  | LustreParser2.ON         loc -> loc
  | LustreParser2.ONOT       loc -> loc
  | LustreParser2.OR         loc -> loc
  | LustreParser2.PLUS       loc -> loc
  | LustreParser2.RARROW     loc -> loc
  | LustreParser2.RESTART    loc -> loc
  | LustreParser2.RETURNS    loc -> loc
  | LustreParser2.RPAREN     loc -> loc
  | LustreParser2.SEMICOLON  loc -> loc
  | LustreParser2.SLASH      loc -> loc
  | LustreParser2.STAR       loc -> loc
  | LustreParser2.TEL        loc -> loc
  | LustreParser2.THEN       loc -> loc
  | LustreParser2.TRUE       loc -> loc
  | LustreParser2.UINT16     loc -> loc
  | LustreParser2.UINT32     loc -> loc
  | LustreParser2.UINT64     loc -> loc
  | LustreParser2.UINT8      loc -> loc
  | LustreParser2.VAR        loc -> loc
  | LustreParser2.VAR_NAME (_,l) -> l
  | LustreParser2.WHEN       loc -> loc
  | LustreParser2.WHENOT     loc -> loc
  | LustreParser2.XOR        loc -> loc

