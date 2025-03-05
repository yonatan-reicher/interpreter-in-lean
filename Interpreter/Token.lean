inductive Token where
  | eof
  | int (val : Int)
  deriving Repr, DecidableEq
