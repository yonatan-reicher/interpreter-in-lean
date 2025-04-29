import AssertCmd
import Interpreter.Types.Token
import Interpreter.Lex.Basic
import Interpreter.Lex.Numbers
import Interpreter.Lex.Identifier
import Utils.Parser
open Utils (Parser ParseSuccess)


variable {α β γ : Type}


namespace Lex


def ignore := fun (_ : α) => ()


def whitespace : Lexer Unit :=
  ignore <$> Parser.token.filter (·.isWhitespace)


def token : Lexer Token :=
  Parser.not Parser.eof *> (
    Token.int <$> int
    <|> ofIOrK <$> identifierOrKeyword
    <|> .error Error.couldNotRecognizeToken
  )
  where ofIOrK : Sum Ident Keyword -> Token
    | Sum.inl ident => Token.ident ident
    | Sum.inr keyword => Token.keyword keyword


def lexer : Lexer (List Token) :=
  .many (Parser.many whitespace *> token)


def lex (input : List Char) : Except Error (List Token) :=
  match lexer.parse input with
  | .none => panic "lexer returned none" -- This will never happen
  | .some r => ParseSuccess.value <$> r
  /-
  <- Parser.many whitespace
  match token input' with
  | none => .ok []
  | some (.error e) => .error e
  | some (.ok ⟨ t, rest, h1, h2 ⟩) =>
    -- This proves termination!
    have : sizeOf rest < sizeOf input := by
      change rest.length < input.length
      exact Nat.lt_of_lt_of_le h2 (skipWhitespace_length_le)
    (lex rest).map (t :: .)
  termination_by input
  -/


instance {ε α} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
  | Except.ok a, Except.ok b => a == b
  | Except.error e, Except.error f => e == f
  | _, _ => false


#assert (lex "124".toList) == Except.ok [Token.int 124]
#assert
  (lex "  -124  2  -2  ".toList)
  == Except.ok [Token.int (-124), Token.int 2, Token.int (-2)]
#assert
  (lex "  -124  2  - 2  ".toList)
  == Except.error Error.noNumberAfterMinus
#eval lex "hellow world! 124".toList
