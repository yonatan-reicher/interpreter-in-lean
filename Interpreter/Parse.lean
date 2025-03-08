import Interpreter.Ast
import Interpreter.Token

abbrev Tokens := List Token

def expr : StateM Tokens (Option Ast) := do
  match <- get with
  | Token.int val :: rest => do
    set rest
    pure (some (Ast.val val))
  | _ => pure none

def parse : List Token -> Ast := fun tokens =>
  match expr.run tokens with
  | (some ast, []) => ast
  | (some _, _) => panic! "Leftover tokens: {rest}"
  | (none, _) => panic! "Not a beginning of an expression"
  
example
: parse [Token.int 10] = Ast.val 10 := rfl
