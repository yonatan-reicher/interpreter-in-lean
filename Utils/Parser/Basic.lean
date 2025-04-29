import Utils.StrictSuffix


namespace Utils


variable {α β : Type}


/--
A context for defining a parser.
-/
structure Parsing where
  token : Type
  error : Type
  deriving Inhabited, Repr


structure ParseSuccess (p : Parsing) (α : Type) where
  value : α
  rest : List p.token
  deriving Inhabited


instance {p} [Repr α] : Repr (ParseSuccess p α) where
  reprPrec
  | {value, rest := []}, n => reprPrec value n
  | {value, rest}, n =>
    reprPrec value n
    |>.append (" and " ++ toString rest.length ++ " more tokens...")


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


instance : Alternative (Parser p) where
  failure := .mk fun _ => .none
  orElse a b := .mk fun input =>
    a.parse input
    <|> (b ()).parse input


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


class Lawful (x : Parser p α) where
  ssuffix
  {input success}
  (h : x.parse input = some (.ok success))
  : success.rest.StrictSuffix input


-- @[aesop safe]
theorem ssuffix {x : Parser p α} [l : Lawful x] {input success}
(h : x.parse input = some (.ok success))
: success.rest.StrictSuffix input := l.ssuffix h


@[simp]
theorem parse_mk {f : List p.token -> Option (Except _ (ParseSuccess p α))}
: (mk f).parse = f := rfl



@[simp]
def success {α : Type} (x : α) : Parser p α := pure x


@[simp]
instance lawful_pure {x} : Lawful (pure x : Parser p α) -> False := by
  intro l
  have : [].StrictSuffix [] := l.ssuffix rfl
  exact List.StrictSuffix.irrefl [] this
  

@[simp]
def none {α : Type} : Parser p α := Alternative.failure
instance : Lawful (none : Parser p α) where
  ssuffix := by nofun


@[simp]
def error {α : Type} (e : p.error) : Parser p α :=
  mk fun _ => .some (.error e)
instance : Lawful (none : Parser p α) where
  ssuffix := by nofun


def input : Parser p (List p.token) :=
  mk fun input => .some (.ok ⟨ input, input ⟩)


def token : Parser p p.token :=
  mk fun
  | [] => .none
  | token :: rest => .some (.ok ⟨ token, rest ⟩)
instance : Lawful (@token p) where
  ssuffix {input success} h := by
    rw [token, parse_mk] at h
    cases input with
    | nil => contradiction
    | cons token rest =>
      replace h : some (Except.ok ⟨token, rest⟩) = some (.ok success) := h
      repeat injection h with h
      rw [<-h]
      exact List.StrictSuffix.ssuffix_cons


def eof : Parser p Unit :=
  mk fun | [] => .some (.ok ⟨(), []⟩) | _ :: _ => .none


def not (parser : Parser p Unit) : Parser p Unit :=
  mk fun input =>
    match parser.parse input with
    | .some (.error e) => .some (.error e)
    | .none => .some (.ok ⟨(), input⟩)
    | .some (.ok _) => .none


def choose (parser : Parser p α) (f : α -> Option β) : Parser p β := do
  match f (<- parser) with
  | .none => Parser.none
  | .some b => pure b


def filter (parser : Parser p α) (cond : α -> Prop) [DecidablePred cond]
: Parser p α := parser.choose fun x => if cond x then .some x else .none


partial def many (parser : Parser p α) : Parser p (List α) :=
  (do
    let head <- parser
    (head :: .) <$> many parser)
  <|> pure []


def oneOrMore (parser : Parser p α) : Parser p (List α) :=
  many parser |>.filter (·.length > 0)


end Parser
