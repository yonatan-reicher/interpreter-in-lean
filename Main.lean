import Interpreter


open Std


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


def parseStream (stream : IO.FS.Stream) : ExceptT Unit IO $ (type : Ty) × (Expr type ∅) := do
  let code <- stream.readText
  let tokens <- Lex.lex code.toList |>.mapError fun _ => ()
  let ast := parse tokens
  sorry

def main : IO Unit := do
  let stream ← IO.getStdin
  let expr ← parseStream stream
  IO.println s!"Parsed: {repr expr}"
