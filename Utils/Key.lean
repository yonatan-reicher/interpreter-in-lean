private instance {α} {p : α -> Prop} [BEq α] : BEq (Subtype p) where
  beq x y := x.val == y.val
private instance {α} {p : α -> Prop} [Hashable α] : Hashable (Subtype p) where
  hash x := hash x.val


variable
  {α : Type} {key : Type}
  [membership : Membership key α]
  {a : α} {k : key}


@[ext]
structure Key (a : α) where
  val : key
  mem : val ∈ a
  deriving Repr


@[simp]
theorem Key.eq_iff {k1 k2 : Key a}
: k1 = k2 <-> k1.val = k2.val := by
  apply Iff.intro
  . intro h
    subst h
    rfl
  . intro h
    ext
    exact h


instance [inst : DecidableEq key] : DecidableEq (Key a) := fun x y => by
  rw [Key.eq_iff]
  exact inst x.val y.val


instance [Hashable key] : Hashable (Key a) where
  hash k := hash k.val


instance : CoeHead (Key a) key where coe k := k.val


@[simp]
theorem Key.mem_val (k : Key a) : k.val ∈ a := k.mem


class LawfulEmptyCollectionMembership
(β : Type) (α : Type)
[EmptyCollection α]
[Membership β α]
where
  mem_empty : ∀ b : β, b ∉ (∅ : α)
attribute [simp] LawfulEmptyCollectionMembership.mem_empty


@[simp]
theorem Key.key_empty
[EmptyCollection α]
[LawfulEmptyCollectionMembership key α]
: Key (∅ : α) -> False := by
  intro k
  apply absurd k.mem_val
  exact LawfulEmptyCollectionMembership.mem_empty k.val


@[simp]
theorem Key.val_mk {val mem}
: Key.val (Key.mk val mem : Key a) = (val : key) := rfl
