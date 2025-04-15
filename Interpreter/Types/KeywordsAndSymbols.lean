import Interpreter.Strings


inductive Symbol : Type where
  | fatArrow
  | colonEqual
  | semicolon
  deriving Inhabited, DecidableEq, Hashable


instance : Strings Symbol where
  all := [
    (Symbol.fatArrow, "=>"),
    (Symbol.colonEqual, ":="),
    (Symbol.semicolon, ";"),
  ]


inductive Keyword : Type where
  | fun_ : Keyword
  deriving Repr, Inhabited, DecidableEq, Hashable


instance : Strings Keyword where
  all := [
    (Keyword.fun_, "fun"),
  ]
