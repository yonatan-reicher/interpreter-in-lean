import Interpreter.Types.Ty


namespace Interpreter.Types


def Val : Ty -> Type
  | .int => Int
  | .bool => Bool




--- This macro infers the underlying instance of the type `Val ty`
syntax "underlying_instance" term : command
macro_rules
  | `(command| underlying_instance $typeclass) =>
    `(command|
      instance
      {ty : Ty}
      : $typeclass (Val ty) := by
        cases ty
        all_goals
          unfold Val
          infer_instance)


-- Implements some classes for `Val`
underlying_instance Inhabited
underlying_instance Repr
underlying_instance Std.ToFormat
underlying_instance ToString
underlying_instance DecidableEq
