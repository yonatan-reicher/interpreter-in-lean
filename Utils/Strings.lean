variable {α : Type}


/--
A class for a type that is like an enum with string values.
-/
class Strings (α : Type) where
  all : List (α × String)
  mem_all : ∀ a : α, a ∈ all.map Prod.fst := by
    intro a
    cases a <;> decide


export Strings (all mem_all)


instance [BEq α] [Strings α] : ToString α where
  toString a :=
    match all.find? (·.1 == a) with
    | some (_, s) => s
    | none => panic "This should never happen"


instance [BEq α] [Strings α] : Repr α where
  reprPrec a _ := "`" ++ toString a ++ "`"


def ofString [BEq α] [Strings α] (s : String) : Option α :=
  all.find? (·.2 == s) |>.map Prod.fst
