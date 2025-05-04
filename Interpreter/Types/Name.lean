import AssertCmd


namespace Interpreter.Types


def Name.isHead (c : Char) := c.isAlpha || c == '_'
def Name.isTail (c : Char) := c.isAlphanum || c ∈ "_'+-".toList
abbrev Name.Head := Subtype (isHead .)
abbrev Name.Tail := Subtype (isTail .)


structure Name where
  head : Name.Head
  tail : List Name.Tail
  deriving DecidableEq, Hashable, Repr


def Name.toList (name : Name) : List Char :=
  name.head.val :: name.tail.map (·.val)


def Name.toString (name : Name) : String := name.toList.asString
instance : ToString Name where toString name := name.toString


def Name.toFormat (name : Name) : Std.Format := name.toString.toFormat
instance : Std.ToFormat Name where format name := name.toFormat


def Name.of (str : List Char) : Option Name :=
  match str with
  | [] => none
  | head :: tail =>
    if h_head : isHead head then
      if h_tail : ∀ c ∈ tail, isTail c then
        let tail := tail.attachWith _ h_tail
        some <| Name.mk (Subtype.mk _ h_head) tail
      else none
    else none


#assert (Name.of "yogev".toList |>.isSome) == true


instance : Inhabited Name := by
  let x := Name.of "a".toList
  have h : x.isSome := by decide
  constructor
  exact x.get h
