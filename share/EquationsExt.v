From Equations Require Export Equations.

Ltac apply_args c elimc k :=
  match c with
  | _ ?a ?b ?c ?d ?e ?f => k uconstr:(elimc a b c d e f)
  | _ ?a ?b ?c ?d ?e => k uconstr:(elimc a b c d e)
  | _ ?a ?b ?c ?d => k uconstr:(elimc a b c d)
  | _ ?a ?b ?c => k uconstr:(elimc a b c)
  | _ ?a ?b => k uconstr:(elimc a b)
  | _ ?a => k uconstr:(elimc a)
  end.

Ltac get_first_elim c :=
  match c with
  | ?f ?a ?b ?c ?d ?e ?f => get_elim (f a b c d e f)
  | ?f ?a ?b ?c ?d ?e => get_elim (f a b c d e)
  | ?f ?a ?b ?c ?d => get_elim (f a b c d)
  | ?f ?a ?b ?c => get_elim (f a b c)
  | ?f ?a ?b => get_elim (f a b)
  | ?f ?a => get_elim (f a)
  end.

Ltac apply_funelim c :=
  let elimc := get_first_elim c in
  let elimfn := match elimc with fun_elim (f:=?f) => constr:(f) end in
  let elimn := match elimc with fun_elim (n:=?n) => constr:(n) end in
  let elimt := make_refine elimn elimc in
  apply_args c elimt ltac:(fun elimc =>
                             unshelve refine_ho elimc; cbv beta).
