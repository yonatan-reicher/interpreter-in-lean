import Interpreter.Parser


variable {α β : Type}


inductive Error : Type where
  | noNumberAfterPlus : Error
  | noNumberAfterMinus : Error
  | couldNotRecognizeToken
  deriving Inhabited, Repr, DecidableEq


private abbrev Input := List Char


abbrev p : Parsing := { token := Char, error := Error }


abbrev LexSuccess (α : Type) := ParseSuccess p α


abbrev Lexer (α : Type) := Parser p α
