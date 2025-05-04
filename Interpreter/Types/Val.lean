import Interpreter.Types.Ty


namespace Interpreter.Types


def Val : Ty -> Type
  | .int => Int
  | .bool => Bool


variable {ty : Ty}


--- This macro infers the underlying instance of the type `Val ty`
syntax "underlying_instance" Lean.Parser.Tactic.elimTarget : tactic
macro_rules
  | `(tactic| underlying_instance $ty) =>
    `(tactic|
      cases $ty;
      all_goals
        unfold Val
        infer_instance)


instance : Inhabited (Val ty) := by underlying_instance ty
instance : Repr (Val ty) := by underlying_instance ty
instance : ToString (Val ty) := by underlying_instance ty
instance : DecidableEq (Val ty) := by underlying_instance ty
instance : Hashable (Val ty) := by underlying_instance ty
