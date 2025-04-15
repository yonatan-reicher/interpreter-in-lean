import Interpreter.Types.KeywordsAndSymbols
import Interpreter.Types.Identifier


inductive Token where
  | int (val : Int)
  | ident (i : Ident)
  | keyword (kw : Keyword)
  | symbol (sym : Symbol)
  deriving Repr, DecidableEq, Inhabited, Hashable
