import Mathlib
import Mathlib.Tactic
import Interpreter.Token

variable {α β : Type}

private abbrev Input := List Char

structure LexResult (α : Type) (input : Input) where
  value : α
  rest : Input
  suffix : rest.IsSuffix input
  length_le : rest.length < input.length

abbrev LexResult.map {input} (self : LexResult α input) (f : α -> β)
: LexResult β input := { self with value := f self.value }

inductive Error : Type where
  | noNumberAfterSign : Error

abbrev Lexer (α : Type) :=
  (input : Input) -> Option (Except Error (LexResult α input))

abbrev Digit := Fin 10

def charToDigit : Char -> Option Digit
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | _ => none

/--
This function repeatedly applies the given function as long as it can.
-/
def List.chooseWhile : Input -> (Char -> Option α) -> Input × List α
  | [], _ => ([], [])
  | head :: tail, f =>
    match f head with
    | none => (head :: tail, [])
    | some a =>
      let (rest, as) := tail.chooseWhile f
      (rest, a :: as)

abbrev Prod.flip : α × β -> β × α | (x, y) => (y, x)
def chooseWhile (f : Char -> Option α) : StateM Input (List α) :=
  modifyGet fun input => Prod.flip ( List.chooseWhile input f )

@[simp]
lemma List.chooseWhile_nil {f : Char -> Option α}
: List.chooseWhile [] f = ([], []) := rfl

@[simp]
lemma List.chooseWhile_none {f : Char -> Option α} {head tail}
(h : f head = none)
: (head :: tail).chooseWhile f = (head :: tail, []) := by
  simp [List.chooseWhile, h]

@[simp]
lemma List.chooseWhile_some {f : Char -> Option α} {head tail a}
(h : f head = some a)
: (head :: tail).chooseWhile f
  = (let (rest, as) := tail.chooseWhile f; (rest, a :: as)) := by
  simp [List.chooseWhile, h]


@[simp]
lemma List.chooseWhile_length_plus_length
{res rest} {list : Input} {f : Char -> Option β}
(h : (rest, res) = list.chooseWhile f)
: rest.length + res.length = list.length := by
  induction list generalizing res rest
  case nil =>
    simp_all only [chooseWhile_nil, Prod.mk.injEq, length_nil, add_zero]
  case cons head tail ih =>
    cases f_head : f head
    case none =>
      simp_all only [chooseWhile_none, Prod.mk.injEq, length_cons, length_nil
      , add_zero]
    case some a =>
      have : length rest + length res - 1 = length tail := by
        simp_all only [Option.some.injEq, chooseWhile_some, Prod.mk.injEq,
        length_cons, Nat.add_succ_sub_one, Prod.mk.eta]
      rewrite [length_cons, <- this]
      suffices res.length > 0 by omega
      simp_all only [Option.some.injEq, chooseWhile_some, Prod.mk.injEq,
      length_cons, Nat.add_succ_sub_one, Prod.mk.eta, gt_iff_lt,
      lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true]


example
: let isAlpha' c := if c.isAlpha then some c else none
  List.chooseWhile "abcd efgh".toList isAlpha'
  = (" efgh".toList, "abcd".toList)
  := rfl

abbrev digits (input : Input) := input.chooseWhile charToDigit

/-
def Nat.ofDigits := aux 0
where
  aux
  | acc, [] => acc
  | acc, d :: ds => aux (acc * 10 + d) ds
-/

lemma List.chooseWhile_suffix {rest input} {f : Char -> Option α}
(h : (List.chooseWhile input f).1 = rest)
: rest.IsSuffix input := by
  -- unfold List.chooseWhile at *
  induction input
  case nil => simp_all only [List.chooseWhile, Prod.mk.injEq, List.nil_eq, List.suffix_rfl]
  case cons head tail ih =>
    simp [List.chooseWhile] at h
    split at h
    · have : head :: tail = rest := by
        simp_all only [Prod.mk.injEq, List.nil_eq]
      rw [this]
    · suffices (chooseWhile tail f).1 = rest by
        specialize ih this
        exact List.IsSuffix.trans ih (List.suffix_cons _ _)
      simp_all


lemma List.chooseWhile_length_le {input} {f : Char -> Option α}
: (chooseWhile input f).1.length <= input.length := by
  have : (chooseWhile input f).1.IsSuffix input := chooseWhile_suffix rfl
  exact List.IsSuffix.length_le this
      

lemma List.chooseWhile_length_lt
{head tail d} {f : Char -> Option α}
(h : f head = some d)
: (chooseWhile (head :: tail) f).1.length < (head :: tail).length := by
  suffices (chooseWhile tail f).1.length < tail.length + 1 by
    unfold chooseWhile
    rw [h]
    simpa using this
  suffices (chooseWhile tail f).1.length <= tail.length by
    exact Nat.lt_add_one_iff.mpr this
  exact chooseWhile_length_le


def naturalNumber : Lexer Nat := fun input =>
  -- TODO: Definetly need to clean this up!
  match h_digits_input : digits input with
  | (rest, []) => none
  | (rest, d :: ds) =>
    let n := Nat.ofDigits 10 (d :: ds).reverse
    match h_input : input with
    | [] => by
      rw [digits, List.chooseWhile_nil] at h_digits_input
      injection h_digits_input
      contradiction
    | c :: cs =>
      have h_rest : (digits (c :: cs)).1 = rest := by simp_all only
      have h_ds : (digits (c :: cs)).2 = (d :: ds) := by simp_all only
      have h_suffix : rest.IsSuffix (c :: cs) := by
        apply List.chooseWhile_suffix
        assumption
      have h_length : rest.length < (c :: cs).length := by
        have b : (digits (c :: cs)).1.length < (c :: cs).length := by
          refine List.chooseWhile_length_lt (?_ : charToDigit c = some d)
          show charToDigit c = some d
          simp [digits, List.chooseWhile] at h_ds
          generalize charToDigit c = x at *
          cases x
          case none => simp at h_ds
          case some y => simp at h_ds; tauto
        rw [<-h_rest]
        apply List.chooseWhile_length_lt
        cases q : charToDigit c
        case none => simp_all [digits, List.chooseWhile]
        case some y => simp_all [digits, List.chooseWhile]; tauto
      some (.ok ⟨n, rest, by assumption, by assumption⟩)


@[simp]
lemma naturalNumber_nil : naturalNumber [] = none := rfl


@[simp]
lemma naturalNumber_not_digit
{head tail}
(h : charToDigit head = none)
: naturalNumber (head :: tail) = none := by
  unfold naturalNumber
  aesop


example : naturalNumber "123".toList = some (.ok ⟨123, [], by decide, by decide⟩) := rfl


lemma List.IsSuffix.cons {l1 l2 : List α} {a} (h : l1.IsSuffix l2)
: l1.IsSuffix (a :: l2) := by
  trans
  show l1.IsSuffix l2; assumption
  show l2.IsSuffix (a :: l2); simp


def integer : Lexer Int := fun input =>
  match input with
  | '-' :: rest => naturalPart Int.neg rest _ (by simp)
  | '+' :: rest => naturalPart id rest _ (by simp)
  | [] => none
  | d :: rest =>
    if Option.isSome (charToDigit d) then naturalPart id (d :: rest) _ (by simp)
    else none
where
  naturalPart mapping (start : Input) (input : Input)
  (start_suf_input : start.IsSuffix input)
  : Option (Except Error (LexResult _ input)) :=
    match h_n : naturalNumber start with
    | none => some (.error Error.noNumberAfterSign)
    | some (.error _) => none -- contradiction
    | some (.ok ⟨n, rest, rest_suffix_start, h⟩) =>
      have := List.IsSuffix.trans rest_suffix_start start_suf_input
      have : rest.length < start.length := h
      have : start.length <= input.length := by simp_all [List.IsSuffix.length_le]
      have : rest.length < input.length := by omega
      some <| .ok
        { value := mapping n
        , rest := rest
        , suffix := by assumption
        , length_le := by assumption
        }

example
: integer "-123ahhh!!!".toList = some (.ok ⟨-123, "ahhh!!!".toList, by decide, by decide⟩) := rfl

def token : Lexer Token := fun input =>
  if h : input.isEmpty then none
  else if let some i := integer input then some (i.map (·.map Token.int))
  else some (.ok ⟨Token.int (-1), [], by simp, by
    have : input.length ≠ 0 := by simp_all
    have : input.length > 0 := by omega
    simp_all⟩) -- Fail somehow!

@[reducible]
instance mySizeOf : SizeOf Input where
  sizeOf := List.length


def skipWhitespace : Input -> Input
  | [] => []
  | c :: rest => if c.isWhitespace then skipWhitespace rest else c :: rest


lemma skipWhitespace_length_le {input}
: (skipWhitespace input).length <= input.length := by
  induction input with
  | nil => decide
  | cons c cs ih =>
    unfold skipWhitespace
    cases c.isWhitespace with
    | false => 
      change (c :: cs).length <= (c :: cs).length
      rfl
    | true =>
      trans cs.length
      . exact ih
      . exact Nat.le_succ _


def lex (input : List Char) : Except Error (List Token) := 
  -- TODO: Skip whitespace between tokens!
  let input' := skipWhitespace input
  match token input' with
  | none => .ok []
  | some (.error e) => .error e
  | some (.ok ⟨ t, rest, h1, h2 ⟩) =>
    -- This proves termination!
    have : sizeOf rest < sizeOf input := by
      change rest.length < input.length
      exact Nat.lt_of_lt_of_le h2 (skipWhitespace_length_le)
    (lex rest).map (t :: .)
  termination_by input

#reduce lex "".toList
example : lex "".toList = .ok [] := by
  unfold lex
  rfl
#reduce lex "123".toList
example : lex "123".toList = .ok [Token.int 123] := by
  unfold lex
  simp only [String.toList.eq_1, ↓Char.isValue]
  unfold lex
  rfl
#reduce lex "123 456".toList
example : lex "123 456".toList = .ok [Token.int 123, Token.int 456] := by
  unfold lex
  simp only [String.toList.eq_1, ↓Char.isValue]
  unfold lex
  simp only [↓Char.isValue]
  unfold lex
  rfl

