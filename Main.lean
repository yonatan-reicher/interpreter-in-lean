import Interpreter

open Std

def IO.FS.Stream.getLines (stream : IO.FS.Stream) : IO (Array String) := do
    let mut array := Array.empty
    let mut line := ←stream.getLine
    while line ≠ "" do
      array := array.push line
      line := ←stream.getLine
    return array

inductive ParseResult where
  | success : Sigma (Expr . ∅) → ParseResult
  | failure : Unit → ParseResult
deriving Inhabited, Repr

def parseStream (stream : IO.FS.Stream) : IO ParseResult :=
  stream.getLines.map (fun lines =>
    let code := lines.foldl (fun acc line => acc ++ line) "\n"
    match parse code with
    | Option.some expr => ParseResult.success expr
    | Option.none => ParseResult.failure ()
  )

def main : IO Unit := do
  let stream ← IO.getStdin
  let expr ← parseStream stream
  IO.println s!"Parsed: {repr expr}"
