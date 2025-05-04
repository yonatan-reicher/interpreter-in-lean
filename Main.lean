import Interpreter


open Std
open Interpreter
open Interpreter.Types (Expr Ty VarTypes Val)
open Interpreter.Parse (parse)
open Interpreter.Eval (eval)


inductive MError
  | lex : Lex.Error -> MError
  | parse : Parse.Error -> MError
  | check : Error -> MError
  deriving Inhabited, Repr
instance : Coe Lex.Error MError := ⟨.lex⟩
instance : Coe Parse.Error MError := ⟨.parse⟩
instance : Coe Error MError := ⟨.check⟩


def IO.FS.Stream.getLines (stream : IO.FS.Stream) : IO (Array String) := do
    let mut array := Array.empty
    let mut line := ←stream.getLine
    while line ≠ "" do
      array := array.push line
      line := ←stream.getLine
    return array

abbrev ParseResult := Except Unit $ (type : Ty) × (Expr type ∅)


def IO.FS.Stream.readText (stream : IO.FS.Stream) : IO String := do
  stream.getLines
  |>.map fun lines => lines.foldl (fun acc line => acc ++ line) "\n"


def coeError {ε α ε'} [∀ e, CoeT ε e ε'] (x : Except ε α) : Except ε' α :=
  x.mapError fun (e : ε) => (↑ e : ε')


-- TODO: Rename
def arstarts (code : String)
: Except MError $ (ty : Ty) × Val ty := do
  let tokens <- Lex.lex code.toList |> coeError
  dbg_trace s!"Tokens: {repr tokens}"
  let ast <- parse tokens |> coeError
  dbg_trace s!"Ast: {repr ast}"
  let ⟨ty, expr⟩ <- check ast |> coeError
  dbg_trace s!"Expr: {repr expr}"
  let val := eval {} expr
  return ⟨ty, val⟩


def main : IO Unit := do
  let stream ← IO.getStdin
  let code <- stream.readText
  let expr := arstarts code
  IO.println s!"Expr: {repr expr}"
