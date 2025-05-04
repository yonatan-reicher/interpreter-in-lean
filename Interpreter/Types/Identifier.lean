import Interpreter.Types.Name


namespace Interpreter.Types


inductive Ident
  | name : Name -> Ident
  deriving Repr, Inhabited, DecidableEq, Hashable


instance : Coe Name Ident := ⟨.name⟩



