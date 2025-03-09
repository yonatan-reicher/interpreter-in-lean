import Mathlib
import Interpreter.Token

variable {α β : Type}

private abbrev Input := List Char

inductive ParseRes error result where
  | success : result -> Input -> ParseRes error result
  | failure : error -> ParseRes error result
  deriving DecidableEq

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

def naturalNumber : StateM Input (Option Nat) := do
  let input ← get
  let (rest, d) := digits input
  if d == []
  then pure none
  else
    set rest
    let n := Nat.ofDigits 10 d.reverse
    pure (some n)

@[simp]
lemma naturalNumber_nil : naturalNumber.run [] = (none, []) := rfl

@[simp]
lemma naturalNumber_not_digit
{head tail}
(h : charToDigit head = none)
: naturalNumber.run (head :: tail) = (none, head :: tail) := by
  simp [naturalNumber, h]

example : naturalNumber "123".toList = (some 123, []) := rfl

@[simp]
def peek : StateM Input (Option Char) := do
  (<- get) |> List.head? |> pure

def popEq (c : Char) : StateM Input Bool := do
  if (<- peek) == some c then
    modify List.tail
    pure true
  else
    pure false

@[simp]
lemma popEq_nil {c} : (popEq c).run [] = (false, []) := rfl

@[simp]
lemma popEq_true {c rest} : (popEq c).run (c :: rest) = (true, rest) := by
  simp [popEq]

def integer : StateM Input (Option Int) := do
  if (<- popEq '-') then (Option.map Int.neg) <$> cont
  else if (<- popEq '+') then cont
  else if Option.isSome ((<- peek).bind charToDigit) then cont
  else pure none
where
  cont : StateM Input (Option Int) := naturalNumber.map fun (x : Option ℕ) => x

example
: integer "-123ahhh!!!".toList = (some (-123), "ahhh!!!".toList) := rfl

def token : StateM Input Token := do
  if (<- get).isEmpty then pure Token.eof
  else if let some i := <- integer then pure (Token.int i)
  else pure Token.eof -- TODO

def advances (action : StateM Input (Option α)) : Prop :=
  ∀ input, (action.run input).1.isSome -> (action.run input).2.length < input.length

def advancesIf (pred : α -> Prop) (action : StateM Input α) : Prop :=
  ∀ input, pred (action.run input).1 -> (action.run input).2.length < input.length

lemma advances_chooseWhile {f : Char -> Option α}
: advancesIf (!List.isEmpty .) (chooseWhile f) := by
  intro input h_not_isEmpty
  unfold chooseWhile at *
  induction input
  case nil => simp_all
  case cons head tail ih =>
    cases h : f head
    simp_all
    simp_all
    show_term contradiction


lemma advances_naturalNumber
: advances naturalNumber := by
  intro input h_isSome
  simp_all [naturalNumber]
  generalize List.chooseWhile input charToDigit = a at *
  rcases a with ⟨input', digits⟩
  cases digits
  simp_all
  simp_all

lemma advances_integer
: advances integer := by
  intro input h_isSome
  unfold integer integer.cont at *
  simp_all
  match input with
  | '-' :: input' =>
    simp_all
    sorry
  | _ => sorry

lemma advances_token
: advances token := by
  intro input notNil
  cases input 
  case nil => contradiction
  rw [token]
  simp [get, getThe, MonadStateOf.get]
  unfold StateT.get
  simp


lemma size_token_le_size (input : Input) (notNil : input ≠ [])
: sizeOf (token input).1 < sizeOf input := by
  rw [token]
  simp


def lex (input : List Char) : List Token := 
  match h : token input with
  | (Token.eof, _) => []
  | (t, rest) =>
    have : sizeOf rest < sizeOf input := sorry
    t :: lex rest
termination_by input

example : lex "123 456".toList = [Token.int 123, Token.int 456, Token.eof] := by
  unfold lex

