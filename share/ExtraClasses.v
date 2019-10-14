Require Import String.
Open Scope string.

Class Show (A : Type) : Type :=
  {
    show : A -> string
  }.