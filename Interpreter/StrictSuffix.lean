import Aesop
import Paperproof


/-!
This file contains List.StrictSuffix, and a bunch of lemmas about it.
-/


namespace List


variable {α β : Type}


def StrictSuffix (self : List α) (other : List α) : Prop :=
  self.IsSuffix other ∧ self.length < other.length


-- This is obviously a strict suffix
example : [2, 3, 4].StrictSuffix [1, 2, 3, 4] := by
  constructor
  repeat decide


-- This is not, as a strict suffix is a suffix which is shorter
example : ¬([1, 2].StrictSuffix [1, 2]) := by
  intro h
  unfold StrictSuffix at h
  contradiction


@[aesop unsafe]
theorem StrictSuffix.is_suffix {a b : List α}
: a.StrictSuffix b -> a.IsSuffix b := by
  rintro ⟨⟩
  assumption


@[aesop unsafe]
theorem StrictSuffix.length_lt_length {a b : List α}
: a.StrictSuffix b -> a.length < b.length := by
  rintro ⟨⟩
  assumption


@[aesop unsafe]
theorem StrictSuffix.of_suffix_of_length_lt
{l1 l2 : List α}
(suffix : l1.IsSuffix l2)
(length : l1.length < l2.length)
: l1.StrictSuffix l2 := by
  constructor <;> assumption


theorem StrictSuffix.iff
{l1 l2 : List α}
: l1.StrictSuffix l2 ↔ l1.IsSuffix l2 ∧ l1.length < l2.length := by
  apply Iff.intro
  case mp =>
    intro h
    exact And.intro h.is_suffix h.length_lt_length
  case mpr =>
    rintro ⟨suf, len⟩
    exact of_suffix_of_length_lt suf len


@[aesop unsafe]
theorem StrictSuffix.irrefl (l : List α) : ¬ l.StrictSuffix l := by
  intro h
  exact Nat.lt_irrefl _ h.length_lt_length


@[aesop safe]
theorem StrictSuffix.of_ssuffix_of_suffix
{l1 l2 l3 : List α}
(h1 : l1.StrictSuffix l2)
(h2 : l2.IsSuffix l3)
: l1.StrictSuffix l3 := by
  apply of_suffix_of_length_lt
  show l1.IsSuffix l3
  have : l1.IsSuffix l2 := h1.is_suffix
  have : l2.IsSuffix l3 := h2
  apply IsSuffix.trans <;> assumption
  show l1.length < l3.length
  have : l1.length < l2.length := h1.length_lt_length
  have : l2.length ≤ l3.length := h2.length_le
  apply Nat.lt_of_lt_of_le <;> assumption


@[aesop safe]
theorem StrictSuffix.of_suffix_of_ssuffix
{l1 l2 l3 : List α}
(h1 : l1.IsSuffix l2)
(h2 : l2.StrictSuffix l3)
: l1.StrictSuffix l3 := by
  apply of_suffix_of_length_lt
  show l1.IsSuffix l3
  have : l1.IsSuffix l2 := h1
  have : l2.IsSuffix l3 := h2.is_suffix
  apply IsSuffix.trans <;> assumption
  show l1.length < l3.length
  have : l1.length ≤ l2.length := h1.length_le
  have : l2.length < l3.length := h2.length_lt_length
  apply Nat.lt_of_le_of_lt <;> assumption


/-
-- Found out this can be implemented really simply, but leaving this code
-- because I found it interesting.
instance {l1 l2 : List α} : Decidable (l1.IsSuffix l2) := by
  if h1 : l2.length < l1.length then
    apply Decidable.isFalse
    by_contra h2
    have : l1.length <= l2.length := h2.length_le
    apply Nat.not_lt_of_le this h1
  else
    let l := l2.drop (l2.length - l1.length)
    if h2 : l ++ l1 = l2 then exact Decidable.isTrue ⟨l, h2⟩
    else
      apply Decidable.isFalse
      by_contra h3
      obtain ⟨l', h3⟩ := h3
      subst h3
      have : l ≠ l' := by simpa only [append_cancel_right_eq] using h2
      -- We now have to prefixes for our suffix that we must show are not
      -- equal.
      apply absurd this
      show l = l'
      have : (l' ++ l1).drop ((l' ++ l1).length
    apply Decidable.isTrue
    show ∃ l, l ++ l1 = l2
    sorry
-/


instance instDecidableStrictSuffix [DecidableEq α] (l1 l2 : List α)
: Decidable (l1.StrictSuffix l2) := by
  rw [StrictSuffix.iff]
  exact instDecidableAnd


-- @[trans]
def StrictSuffix.trans
{l1 l2 l3 : List α}
: l1.StrictSuffix l2 -> l2.StrictSuffix l3 -> l1.StrictSuffix l3 := by
  intros h1 h2
  exact of_ssuffix_of_suffix h1 h2.is_suffix


@[simp]
def StrictSuffix.ssuffix_cons {head : α} {tail : List α}
: tail.StrictSuffix (head :: tail) := by
  apply of_suffix_of_length_lt
  exact suffix_cons head tail
  exact Nat.lt_add_one tail.length


@[simp]
def StrictSuffix.ssuffix_nil {l : List α}
: l.StrictSuffix [] -> False := by
  intro h
  have := length_lt_length h
  contradiction


end List
