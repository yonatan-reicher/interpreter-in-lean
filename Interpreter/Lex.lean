import Mathlib
import Interpreter.Token

inductive ParseRes error result where
  | success : result -> List Char -> ParseRes error result
  | failure : error -> ParseRes error result
  deriving DecidableEq

variable {α : Type}

abbrev S := StateM (List Char)
abbrev SM := inferInstanceAs (MonadState _ S)

def chooseChar (pred : Char -> Option α) : S (Option α) :=
  SM.modifyGet fun
  | [] => (none, [])
  | (c::cs) => 
    match pred c with
    | none => (none, cs)
    | some a => (some a, cs)

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

@[simp]
def digit : S (Option Digit) := chooseChar charToDigit

partial def naturalNumber : S (Option Nat) := do
  let leftMost <- digit
  match leftMost with
  | some d => go d
  | none => pure none
where
  go (acc : Nat) : S Nat :=
    do
      match (← digit) with
      | none => pure acc
      | some d => go (acc * 10 + d.val)

@[simp]
theorem chooseChar_run_nil {pred}
: (@chooseChar α pred).run [] = (none, []) := rfl

@[simp]
theorem chooseChar_run_cons {pred c cs}
: (@chooseChar α pred).run (c :: cs) =
  match pred c with
  | none => (none, cs)
  | some a => (some a, cs) := rfl

example : naturalNumber.run "123".toList = (some 123, []) := by
  unfold naturalNumber 
  have : charToDigit '1' = some 1 := rfl
  simp [this]

def tokenParser : Parser Char Error Token := 
  naturalNumber.bind

def lex (input : String) : List Token := sorry
