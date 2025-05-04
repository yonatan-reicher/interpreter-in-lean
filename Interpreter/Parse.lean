import Interpreter.Types.Ast
import Interpreter.Types.Token
import Utils.Parser
open Utils (Parser)


namespace Interpreter.Parse


open Interpreter.Types (Ident Token Ast Name Symbol)


inductive Error
  | expectedExpressionAfterColonEqual
  | expectedSemicolonAfterLocalVarDecl
  | expectedExpressionAfterSemicolon
  deriving Inhabited, Repr, DecidableEq, Hashable


private abbrev Tokens := List Token
private abbrev Parser α := Utils.Parser { token := Token, error := Error } α


abbrev ident : Parser Ident :=
  Parser.token.choose fun
    | .ident i => some i
    | _ => none


def expr : Parser Ast := .recursive fun expr => do
  -- let startingAtom <- atom expr
  match <- Parser.token with
  | .int val => return Ast.val val
  | .ident i =>
    (do
      Symbol.colonEqual
      let rhs <- expr <|> .error .expectedExpressionAfterColonEqual
      Symbol.semicolon <|> .error .expectedSemicolonAfterLocalVarDecl
      let body <- expr <|> .error .expectedExpressionAfterSemicolon
      return Ast.letIn i rhs body)
    <|> pure (Ast.var i)
  | _ => failure
  where
    atom : Parser Ast := do
    match <- Parser.token with
    | .int val => return Ast.val val
    | .ident i => return Ast.var i
    -- TODO: Add parenthesis
    | _ => failure




/-
def decl : Parser Ast := do
  Keyword.def_
  let name <- ident
  Symbol.colonEqual
  let rhs <- expr
  Symbol.semicolon
  return Ast.def_ name rhs
-/


/-
def prog : Parser Ast := do
  let decls <- Parser.many decl
  let expr <- expr
-/


def parse : List Token -> Except Error Ast := fun tokens =>
  match expr.run tokens with
  | .none => panic! "Could not recognize expression"
  | .some (.error e) => .error e
  | .some (.ok { value := ast, rest := [] }) => pure ast
  | .some (.ok { rest := rest, .. }) => panic! s!"Leftover tokens: {repr rest}"
  

instance {ε α} [BEq ε] [BEq α]
: BEq (Except ε α) := 
  ⟨ fun
    | Except.ok a, Except.ok b => a == b
    | Except.error e, Except.error f => e == f
    | _, _ => false ⟩
#assert (Except.ok (Ast.val 10)) == parse [10]
def a := Name.of "a".toList |>.get!
#assert (Except.ok (Ast.letIn a (Ast.val 10) (Ast.var a))) == parse [a, Symbol.colonEqual, 10, Symbol.semicolon, a]
#assert (Except.error Error.expectedSemicolonAfterLocalVarDecl) == parse [a, Symbol.colonEqual, 10, a]

