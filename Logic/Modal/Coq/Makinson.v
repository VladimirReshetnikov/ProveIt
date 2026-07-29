(**
  The independently checkable part of Makinson's maximality theorem.

  The pinned Foundation proof of the complementary boundary

      L is not included in Ver  ->  KD is included in L

  contains four [sorry] blocks.  We do not turn those admissions into Coq
  axioms.  Instead this module proves the complete KD-to-Triv argument, the
  disjointness of the two families, and the final dichotomy from a named
  hypothesis expressing precisely that missing boundary.
*)

From Stdlib Require Import
  Logic.Classical_Prop Logic.Classical_Pred_Type Logic.ClassicalDescription.
From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure NormalHilbert Boxdot
  MaximalTranslations CanonicalDB5.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Local Definition KD_is_normal : normal_logic (@KD_proves nat) :=
  normal_proves_logic_is_normal schema_D_substitution_closed.

Local Definition KD_is_classical : classical_logic (@KD_proves nat) :=
  quasi_classical (normal_quasi KD_is_normal).

(** Every letterless formula is decided by KD.  The stronger, valuation-
    indexed statement follows the shape of Foundation's proof but uses the
    ordinary classical core of the Hilbert calculus for all Boolean steps. *)
Theorem KD_provability_of_classical_satisfiability :
  forall (p : formula nat) rho,
    formula_letterless p ->
    (classical_eval rho (triv_translate p) -> KD_proves p) /\
    (~ classical_eval rho (triv_translate p) -> KD_proves (Neg p)).
Proof.
  intros p; induction p as [a | | p IHp q IHq | p IHp]; intros rho Hletter.
  - contradiction.
  - split.
    + simpl; contradiction.
    + intros _. apply normal_proves_of_classical_tautology.
      intro theta; unfold Neg; simpl; tauto.
  - destruct Hletter as [Hp Hq].
    specialize (IHp rho Hp); specialize (IHq rho Hq).
    split.
    + simpl. intro Himp.
      destruct (classic (classical_eval rho (triv_translate p))) as [Hpv | Hnpv].
      * pose proof (proj1 IHq (Himp Hpv)) as Hqproof.
        eapply Np_mp; [|exact Hqproof].
        apply normal_proves_of_classical_tautology.
        intro theta; simpl; tauto.
      * pose proof (proj2 IHp Hnpv) as Hnpproof.
        eapply Np_mp; [|exact Hnpproof].
        apply normal_proves_of_classical_tautology.
        intro theta; unfold Neg; simpl; tauto.
    + simpl. intro Hnotimp.
      assert (Hpv : classical_eval rho (triv_translate p)) by tauto.
      assert (Hnqv : ~ classical_eval rho (triv_translate q)) by tauto.
      pose proof (proj1 IHp Hpv) as Hpproof.
      pose proof (proj2 IHq Hnqv) as Hnqproof.
      eapply Np_mp; [|exact Hnqproof].
      eapply Np_mp; [|exact Hpproof].
      apply normal_proves_of_classical_tautology.
      intro theta; unfold Neg; simpl; tauto.
  - specialize (IHp rho Hletter).
    split.
    + simpl. intro Hpval. now apply Np_nec, (proj1 IHp).
    + simpl. intro Hnpval.
      pose proof (Np_nec (proj2 IHp Hnpval)) as Hboxneg.
      assert (HD : KD_proves (D p)).
      { apply Np_extra. now exists p. }
      eapply Np_mp; [|exact Hboxneg].
      eapply Np_mp; [|exact HD].
      apply normal_proves_of_classical_tautology.
      intro theta; unfold D, Dia, Neg; simpl; tauto.
Qed.

Corollary provable_KD_of_classical_satisfiability :
  forall (p : formula nat) rho,
    formula_letterless p ->
    classical_eval rho (triv_translate p) -> KD_proves p.
Proof.
  intros p rho Hletter.
  exact (proj1 (KD_provability_of_classical_satisfiability
    (p := p) rho Hletter)).
Qed.

Corollary provable_KD_of_classical_tautology :
  forall p : formula nat,
    formula_letterless p ->
    classical_tautology (triv_translate p) -> KD_proves p.
Proof.
  intros p Hletter Htaut.
  apply (provable_KD_of_classical_satisfiability
    (p := p) (rho := fun _ => False) Hletter).
  apply Htaut.
Qed.

Corollary provable_not_KD_of_classical_unsatisfiable :
  forall (p : formula nat) rho,
    formula_letterless p ->
    ~ classical_eval rho (triv_translate p) -> KD_proves (Neg p).
Proof.
  intros p rho Hletter.
  exact (proj2 (KD_provability_of_classical_satisfiability
    (p := p) rho Hletter)).
Qed.

(** Select a closed truth constant for every atom. *)
Definition makinson_zero_substitution
    (rho : formula nat -> Prop) (a : nat) : formula nat :=
  if excluded_middle_informative (rho (Atom a)) then Top else Bottom.

Lemma makinson_zero_substitution_letterless :
  forall rho a, formula_letterless (makinson_zero_substitution rho a).
Proof.
  intros rho a; unfold makinson_zero_substitution.
  destruct (excluded_middle_informative (rho (Atom a))); simpl; tauto.
Qed.

Lemma substitute_formula_letterless :
  forall (A B : Type) (sigma : A -> formula B) p,
    (forall a, formula_letterless (sigma a)) ->
    formula_letterless (substitute sigma p).
Proof.
  intros A B sigma p; induction p as [a | | p IHp q IHq | p IHp];
    intro Hsigma; simpl; auto.
Qed.

Lemma makinson_zero_substitution_formula_letterless :
  forall rho p,
    formula_letterless (substitute (makinson_zero_substitution rho) p).
Proof.
  intros rho p. apply substitute_formula_letterless.
  apply makinson_zero_substitution_letterless.
Qed.

Lemma triv_translate_makinson_zero_substitute :
  forall rho p,
    triv_translate (substitute (makinson_zero_substitution rho) p) =
    substitute (makinson_zero_substitution rho) (triv_translate p).
Proof.
  intros rho p; induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - unfold makinson_zero_substitution.
    destruct (excluded_middle_informative (rho (Atom a))); reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - exact IHp.
Qed.

(** The selected closed substitution exactly reproduces the valuation on the
    Triv translation.  This is the zero-substitution readback needed below. *)
Lemma makinson_zero_substitution_readback :
  forall rho p,
    classical_eval rho
      (substitute (makinson_zero_substitution rho) (triv_translate p)) <->
    classical_eval rho (triv_translate p).
Proof.
  intros rho p; induction p as [a | | p IHp q IHq | p IHp]; simpl.
  - unfold makinson_zero_substitution.
    destruct (excluded_middle_informative (rho (Atom a)));
      unfold Top, Neg; simpl; tauto.
  - reflexivity.
  - now rewrite IHp, IHq.
  - exact IHp.
Qed.

(** A consistent normal logic extending KD cannot exceed Triv. *)
Theorem makinson_subset_Triv_of_KD_subset :
  forall (L : modal_logic),
    normal_logic L -> logic_consistent L ->
    logic_included (@KD_proves nat) L ->
    logic_included L (@Triv_proves nat).
Proof.
  intros L Hnormal Hconsistent HKD p Hp.
  apply (proj2 (Triv_proves_iff_classical_tautology p)).
  unfold classical_tautology.
  apply NNPP; intro Hnottaut.
  apply not_all_ex_not in Hnottaut.
  destruct Hnottaut as [rho Hrho].
  set (q := substitute (makinson_zero_substitution rho) p).
  assert (Hq : L q).
  { unfold q.
    apply (quasi_substitution (normal_quasi Hnormal)); exact Hp. }
  assert (Hqletter : formula_letterless q).
  { unfold q. apply makinson_zero_substitution_formula_letterless. }
  assert (Hqfalse : ~ classical_eval rho (triv_translate q)).
  { unfold q. rewrite triv_translate_makinson_zero_substitute.
    intro Hreadback. apply Hrho.
    now apply (proj1 (makinson_zero_substitution_readback rho p)). }
  pose proof
    (provable_not_KD_of_classical_unsatisfiable
       (p := q) (rho := rho) Hqletter Hqfalse)
    as HKDneg.
  pose proof (HKD _ HKDneg) as HLneg.
  pose proof
    (logic_modus_ponens (quasi_classical (normal_quasi Hnormal))
       HLneg Hq) as Hbottom.
  apply Hconsistent. intro r.
  eapply (logic_modus_ponens (quasi_classical (normal_quasi Hnormal)));
    [|exact Hbottom].
  apply (logic_classical_tautology
    (quasi_classical (normal_quasi Hnormal))).
  intro theta; simpl; tauto.
Qed.

Definition makinson_Ver_family (L : modal_logic) : Prop :=
  logic_included L (@Ver_proves nat).

Definition makinson_Triv_family (L : modal_logic) : Prop :=
  logic_included (@KD_proves nat) L /\
  logic_included L (@Triv_proves nat).

(** The two alternatives cannot overlap; [P] is the separating formula. *)
Theorem makinson_families_disjoint :
  forall L : modal_logic,
    ~ (makinson_Ver_family L /\ makinson_Triv_family L).
Proof.
  intros L [HVer [HKD _]].
  apply Ver_unprovable_P.
  apply HVer, HKD, KD_proves_P.
Qed.

(** Exact interface to the portion currently admitted by Foundation. *)
Definition makinson_Ver_boundary (L : modal_logic) : Prop :=
  ~ logic_included L (@Ver_proves nat) ->
  logic_included (@KD_proves nat) L.

Theorem makinson_dichotomy_of_Ver_boundary :
  forall L : modal_logic,
    normal_logic L -> logic_consistent L -> makinson_Ver_boundary L ->
    (makinson_Ver_family L \/ makinson_Triv_family L) /\
    ~ (makinson_Ver_family L /\ makinson_Triv_family L).
Proof.
  intros L Hnormal Hconsistent Hboundary; split.
  - unfold makinson_Ver_family.
    destruct (classic (logic_included L (@Ver_proves nat))) as [HVer | Hnot].
    + now left.
    + right; split.
      * now apply Hboundary.
      * apply makinson_subset_Triv_of_KD_subset; auto.
  - apply makinson_families_disjoint.
Qed.

Corollary makinson_Ver_family_not_Triv_family :
  forall L, makinson_Ver_family L -> ~ makinson_Triv_family L.
Proof.
  intros L HVer HTriv.
  apply (makinson_families_disjoint (L := L)); now split.
Qed.

Corollary makinson_Triv_family_not_Ver_family :
  forall L, makinson_Triv_family L -> ~ makinson_Ver_family L.
Proof.
  intros L HTriv HVer.
  apply (makinson_families_disjoint (L := L)); now split.
Qed.
