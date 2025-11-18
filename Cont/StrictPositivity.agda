record Wrapper (A : Set) : Set where
  field
    unwrap : A
open Wrapper

data Bad (A : Set) : Set where
  mk : Wrapper (Bad A) → Bad A

