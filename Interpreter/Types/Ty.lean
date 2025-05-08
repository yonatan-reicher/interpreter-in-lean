namespace Interpreter.Types


inductive Ty
  | int
  | bool
  deriving Inhabited, DecidableEq, Hashable, Repr


def Ty.toFormat : Ty -> Std.Format
    | .int => "int"
    | .bool => "bool"
instance : Std.ToFormat Ty := ⟨Ty.toFormat⟩
instance : ToString Ty := ⟨fun ty => ty.toFormat.pretty⟩
