namespace Interpreter.Types


inductive Ty
  | int
  | bool
  | func (arg ret : Ty)
  deriving Inhabited, DecidableEq, Hashable, Repr


def Ty.toFormat : Ty -> Std.Format
    | .int => "int"
    | .bool => "bool"
    | .func arg ret =>
      if needsParens arg then
        f!"({arg.toFormat}) -> {ret.toFormat}"
      else
        f!"{arg.toFormat} -> {ret.toFormat}"
    where needsParens
      | .func _ _ => true
      | _ => false
instance : Std.ToFormat Ty := ⟨Ty.toFormat⟩
instance : ToString Ty := ⟨fun ty => ty.toFormat.pretty⟩
