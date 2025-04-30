import Interpreter.Types.KeywordsAndSymbols
import Interpreter.Types.Identifier


inductive Token where
  | int (val : Int)
  | ident (i : Ident)
  | keyword (kw : Keyword)
  | symbol (sym : Symbol)
  deriving Repr, DecidableEq, Inhabited, Hashable


instance : Coe Int Token := ⟨.int⟩
instance : Coe Ident Token := ⟨.ident⟩
instance : Coe Keyword Token := ⟨.keyword⟩
instance : Coe Symbol Token := ⟨.symbol⟩

instance {n} : OfNat Token n := ⟨Token.int $ Int.ofNat n⟩
