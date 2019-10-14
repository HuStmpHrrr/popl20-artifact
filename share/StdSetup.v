Require Export Coq.Lists.List.
Require Export FunInd.
Require Export Arith.Wf_nat.
Require Export Recdef.
Require Export Lia.
Close Scope positive_scope.
Require Export Metalib.Metatheory.

Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.

Require Export Concepts.
Require Export LibUtils.
Require Export Monads.
Require Export MetaExt.
Require Export ExtraClasses.
Require Export EtcFacts.

Hint Rewrite -> AtomSetProperties.add_union_singleton : meta_ext.

(** Extraction Configurations. *)

Extraction Inline and_rec and_rect.
Extraction Inline eq_rec eq_rect_r eq_rec_r.
Extraction Inline nat_rec.
Extraction Inline list_rec.
Extraction Inline prod_rect.
Extraction Inline sig_rect sig_rec.
Extraction Inline proj1_sig.
Extraction Inline sumbool_rec.
Extraction Inline eq_rect.
Extraction Inline typ_label_rec typ_label_rect.
Extraction Inline trm_label_rec trm_label_rect.
Extraction Inline label_rec label_rect.

(** More helper tactics *)

Ltac head_of expr :=
  lazymatch expr with
  | ?h _ => head_of h
  | _ => expr
  end.

Ltac case_of expr :=
  let h := head_of expr in
  lazymatch h with
  | match ?c with _ => _ end => c
  | let _ := ?c in _ => c
  end.

Ltac execute_step_trm t :=
  lazymatch t with
  | match ?expr with _ => _ end =>
    destruct expr eqn:?; simpl in *; try congruence
  | let (_, _) := ?expr in _ =>
    destruct expr eqn:?; simpl in *; try congruence
  end.

Ltac execute_step_g :=
  lazymatch goal with
  | |- ?g = _ =>
    let hg := head_of g in
    execute_step_trm hg
  end.

Ltac execute_g :=
  simpl in *;
  repeat execute_step_g;
  reveal_err;
  monads simpl in *; subst.

Ltac execute_step_hyp H :=
  lazymatch type of H with
  | ?l = _ =>
    let hl := head_of l in
    execute_step_trm hl
  end.

Ltac execute_hyp H :=
  simpl in H;
  repeat execute_step_hyp H;
  reveal_err;
  monads simpl in *; subst.

Tactic Notation "execute" := execute_g.
Tactic Notation "execute" hyp(H) := execute_hyp H.

Ltac execute_steps n H :=
  simpl in H;
  doit 0 n ltac:(fun _ => execute_step_hyp H);
  reveal_err;
  monads simpl in *; subst.

Ltac subgoal T tac :=
  let H := fresh "H" in
  unshelve evar (H : T);
  [| let H' := eval unfold H in H in
         clear H; tac H'].

Ltac rec_pose t name :=
  let rec go t' :=
      let T := type of t' in
      let sT := eval simpl in T in
  lazymatch sT with
  | ?T -> ?IGNORE =>
    subgoal T ltac:(fun gl => go constr:(t' gl))
  | forall x : ?T, ?IGNORE =>
    exvar T ltac:(fun x => go constr:(t' x))
  | _ => pose proof t' as name
  end in
      go t.
