-- TODO
inductive Token where
  | int (val : Int)
  deriving Repr, DecidableEq, Inhabited
