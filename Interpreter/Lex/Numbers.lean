import Interpreter.Lex.Basic
import Utils.Parser
open Utils (Parser)


abbrev Digit := Fin 10


@[simp]
private def charToDigit : Char -> Option Digit
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


namespace Interpreter.Lex


def digit : Lexer Digit := do
  let token <- Parser.token
  match charToDigit token with
  | none => Parser.none
  | some d => pure d
/-
instance : Parser.Lawful digit where
  ssuffix {input success} h := by
    match input with
    | [] =>
      replace h : none = some _ := h
      contradiction
    | head :: tail =>
      match charToDigit head with
      | none => 
        replace h : _ = some _ := h
        contradiction
      | some d =>
        replace h : some (Except.ok ⟨d, tail⟩) = some _ := h
        have : success = ⟨d, tail⟩ := simp_all?
        simpa?
-/


/--
Returns a number given by it's digits from least significant to most (opposite
of as it's parsed).
-/
private def Nat.ofDigits : List Digit -> Nat
  | [] => 0
  | (head : Digit) :: tail => (head : Nat) + 10 * Nat.ofDigits tail


def nat : Lexer Nat := do
  (<- Parser.oneOrMore digit)
  |>.reverse
  |> Nat.ofDigits
  |> pure


inductive Sign : Type where
  | plus | minus
def Sign.apply : Sign -> (Nat -> Int) 
  | plus => Int.ofNat
  | minus => (-Int.ofNat .)
def Sign.of
  | '+' => some plus
  | '-' => some minus
  | _ => none


def sign : Lexer Sign := Parser.token.choose Sign.of


def int : Lexer Int :=
  signNat <|> Int.ofNat <$> nat
  where
    signNat := do
      let s <- sign
      let n <- nat
        <|> Parser.error (match s with
          | .plus => Error.noNumberAfterPlus
          | .minus => Error.noNumberAfterMinus)
      pure (s.apply n)
  

#eval digit.parse "12".toList
#eval (Parser.many digit).parse "123".toList
#eval nat.parse "".toList
#eval nat.parse "123".toList
#eval int.parse "".toList
#eval int.parse "+".toList
#eval int.parse "123".toList
#eval int.parse "+123".toList
#eval int.parse "-123".toList
#eval int.parse "-".toList
