import Interpreter.StrictSuffix


variable {α β : Type}


/--
A context for defining a parser.
-/
structure Parsing where
  token : Type
  error : Type


structure ParseSuccess (p : Parsing) (α : Type) where
  value : α
  rest : List p.token


@[ext]
structure Parser (p : Parsing) (α : Type) where
  parse : List p.token -> Option (Except p.error (ParseSuccess p α))
  deriving Inhabited


namespace Parser


variable {p : Parsing}


instance instMonadParser (p : Parsing) : Monad (Parser p) where
  pure x := Parser.mk fun input => some (.ok ⟨ x, input ⟩)
  bind x f := 
    Parser.mk fun input =>
      match x.parse input with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok { value, rest }) => (f value).parse rest


section -- TODO: Should these two be @[simp]?


theorem map
{parser : Parser p α} {f : α -> β}
: f <$> parser = parser >>= pure ∘ f := rfl


theorem seq
{parser : Parser p α} {g : Parser p (α -> β)}
: g <*> parser = g >>= fun f => f <$> parser := rfl


end


instance : LawfulMonad (Parser p) where
  map_const := rfl -- By definition because we haven't implemented mapConst
  id_map := by
    intros α parser
    /-
    -- TODO: Why does this work?
    simp [Functor.map]
    -/
    rw [map]
    apply Parser.ext
    funext input
    simp only [bind, pure, Function.comp_apply, id_eq]
    match parser.parse input with
    | none => rfl
    | some (.error e) => rfl
    | some (.ok { value, rest }) => rfl
  seqLeft_eq := by
    intros α β parser1 parser2
    apply Parser.ext
    funext input
    simp only [SeqLeft.seqLeft, Seq.seq, Functor.map, Function.comp_apply]
    split <;> rfl
  seqRight_eq := by
    intros α β parser1 parser2
    apply Parser.ext
    funext input
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, Function.comp_apply, Function.const_apply]
    split
    rfl
    rfl
    split <;> trivial
  pure_seq := by
    intros α β f parser
    apply Parser.ext
    funext input
    simp only [pure, seq, bind, map, Function.comp_apply]
  bind_pure_comp := by
    intros α β f parser
    apply Parser.ext
    funext input
    simp only [bind, pure, map, Function.comp_apply]
  bind_map := by
    intros α β f parser 
    apply Parser.ext
    funext input
    simp only [bind, map, Function.comp_apply, seq]
  pure_bind := by
    intros
    rfl
  bind_assoc := by
    intros α β γ x f g
    apply Parser.ext
    funext input
    simp [bind]
    split <;> (split <;> simp_all)


class LawfulParser (x : Parser p α) where
  ssuffix
  {input success}
  (h : x.parse input = some (.ok success))
  : success.rest.StrictSuffix input


@[aesop safe]
theorem ssuffix {x : Parser p α} [l : LawfulParser x] {input success}
(h : x.parse input = some (.ok success))
: success.rest.StrictSuffix input := l.ssuffix h


@[simp]
def success {α : Type} (x : α) : Parser p α := pure x


instance lawful_pure {x} : LawfulParser (pure x : Parser p α) -> False := by
  by_contra l
  have : [].StrictSuffix [] := l.ssuffix rfl
  exact List.StrictSuffix.irrefl [] this
  

@[simp]
def none {α : Type} : Parser p α := mk fun _ => .none
instance : LawfulParser (none : Parser p α) where
  ssuffix := by nofun


@[simp]
def error {α : Type} (e : p.error) : Parser p α :=
  mk fun _ => .some (.error e)
instance : LawfulParser (none : Parser p α) where
  ssuffix := by nofun


end Parser
