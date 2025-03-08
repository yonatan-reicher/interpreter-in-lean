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

def naturalNumber : StateM Input Nat := do
  let input ← get
  let (rest, d) := digits input
  set rest
  let n := Nat.ofDigits 10 d.reverse
  pure n

@[simp]
lemma naturalNumber_nil : naturalNumber.run [] = (0, []) := rfl

@[simp]
lemma naturalNumber_not_digit
{head tail}
(h : charToDigit head = none)
: naturalNumber.run (head :: tail) = (0, head :: tail) := by
  simp [naturalNumber, h]

example : naturalNumber "123".toList = (123, []) := rfl

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
  cont : StateM Input (Option Int) := Option.some <$> naturalNumber

example
: integer "-123ahhh!!!".toList = (some (-123), "ahhh!!!".toList) := rfl

def token : StateM Input Token := do
  if (<- get).isEmpty then pure Token.eof
  else if let some i := <- integer then pure (Token.int i)
  else pure Token.eof -- TODO

def advances (action : StateM Input (Option α)) : Prop :=
  ∀ input, (action.run input).1.isSome -> (action.run input).2.length < input.length

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

