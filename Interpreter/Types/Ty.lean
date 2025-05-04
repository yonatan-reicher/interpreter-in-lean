namespace Interpreter.Types


inductive Ty
  | int
  | bool
  deriving Inhabited, DecidableEq, Hashable, Repr
