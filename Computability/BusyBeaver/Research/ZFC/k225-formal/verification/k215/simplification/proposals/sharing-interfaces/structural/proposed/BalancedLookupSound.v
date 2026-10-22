(** Proposed adapter lemma against the ACTUAL balanced checker API.
    Source reviewed, NOT freshly compiler-checked. *)
From Coq Require Import Bool NArith.
From K230P Require Import Bisim230.
Require Import BalancedBisim.

Lemma lookup_allTree (f : entry -> bool) (T : CTree) :
  forall j x, lookup T j = Some x -> allTree f T = true -> f x = true.
Proof.
  induction T as [|y|cut l IHl r IHr]; intros j x H E.
  - discriminate H.
  - cbn [lookup] in H. destruct (N.eqb j 0); [|discriminate].
    injection H as H. subst x. exact E.
  - cbn [lookup] in H. cbn [allTree] in E.
    apply andb_true_iff in E as [El Er].
    destruct (N.ltb j cut); [eapply IHl | eapply IHr]; eauto.
Qed.

Print Assumptions lookup_allTree.
