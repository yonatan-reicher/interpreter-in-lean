import AssertCmd
import Interpreter.Lex.Basic
import Interpreter.Types.Identifier
import Interpreter.Types.KeywordsAndSymbols


namespace Lex


private def filterAttach {α p} (parser : Parser p α) (cond : α -> Bool)
: Parser p { a // cond a } :=
  parser.choose fun c => if h : cond c then some ⟨c, h⟩ else none


def name : Lexer Name := do
  let c₁ <- filterAttach Parser.token Name.isHead
  let cs <- Parser.many (filterAttach Parser.token Name.isTail)
  pure <| Name.mk c₁ cs


def identifier : Lexer Ident := do
  .name <$> name


def identifierOrKeyword : Lexer (Sum Ident Keyword) := do
  let ident <- identifier
  match ident with
  | .name name => 
    match ofString name.toList.asString with
    | some keyword => pure (Sum.inr keyword)
    | none => pure (Sum.inl ident)
  -- | _ => ident

