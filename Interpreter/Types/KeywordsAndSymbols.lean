import Utils.Strings


namespace Interpreter.Types


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
  | let_ : Keyword
  | def_ : Keyword
  | fun_ : Keyword
  deriving Repr, Inhabited, DecidableEq, Hashable


instance : Strings Keyword where
  all := [
    (Keyword.let_, "let"),
    (Keyword.def_, "def"),
    (Keyword.fun_, "fun"),
  ]
