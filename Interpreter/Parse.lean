import Interpreter.Types.Ast
import Interpreter.Types.Token

abbrev Tokens := List Token

partial def expr : OptionT (StateM Tokens) Ast := do
  match <- get with
  | .int val :: rest => do
    set rest
    pure (Ast.val val)
  | .ident i :: .symbol .colonEqual :: rest => do
    set rest
    let rhs <- expr
    match <- get with
    | .symbol .semicolon :: rest => do
      set rest
      let body <- expr
      pure (Ast.let_ i rhs body)
    | _ => .fail
  | .ident i :: rest => do
    set rest
    pure (Ast.var i)
  | _ => .fail

def parse : List Token -> Ast := fun tokens =>
  match expr.run tokens with
  | (some ast, []) => ast
  | (some _, rest) => panic! s!"Leftover tokens: {repr rest}"
  | (none, _) => panic! "Not a beginning of an expression"
  
#assert (Ast.val 10) == parse [Token.int 10]
def a := Name.of "a".toList |>.get!
#assert (Ast.let_ a (Ast.val 10) (Ast.var a)) == parse [Token.ident a, Token.symbol Symbol.colonEqual, Token.int 10, .symbol .semicolon, Token.ident a]

