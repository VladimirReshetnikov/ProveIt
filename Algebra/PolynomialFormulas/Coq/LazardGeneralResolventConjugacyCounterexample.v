From mathcomp Require Import all_ssreflect all_fingroup.
From PolynomialFormulas Require Import
  QuinticF20Data LazardGeneralResolventCriterion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Why the converse in Lazard's general resolvent criterion selects a
    conjugate subgroup.

    A base-field root of a separable relative resolvent selects an arbitrary
    right coset, not necessarily the base coset.  The right-translation
    stabilizer of [G :* x] is [G :^ x].  Consequently an arbitrary ordering
    of the roots yields containment in a conjugate of the displayed group.

    This file gives a closed witness in [S5].  We conjugate the standard
    Frobenius group [F20] by the explicit three-cycle [(0 1 2)].  The
    conjugated five-cycle fixes the selected non-base coset, but it lies
    outside the displayed standard [F20].  Thus the selected stabilizer is
    not contained in that fixed displayed copy.  Conjugating back by the
    inverse relabeling recovers the standard [F20], which is the corrected
    conclusion of the general criterion. *)
Module PolynomialFormulasLazardGeneralResolventConjugacyCounterexample.

Module F20 := PolynomialFormulasQuinticF20Data.
Module Criterion := PolynomialFormulasLazardGeneralResolventCriterion.

Local Open Scope group_scope.
Local Open Scope action_scope.

(** The same explicit relabeling used by the Lean witness. *)
Definition relabelling : F20.S5 := F20.three_cycle.

(** The subgroup selected by the right coset represented by [relabelling]. *)
Definition relabelled_F20 : {group F20.S5} :=
  F20.standard_F20 :^ relabelling.

Definition base_coset : {set F20.S5} := F20.standard_F20 :* 1.

Definition selected_coset : {set F20.S5} :=
  F20.standard_F20 :* relabelling.

Lemma selected_coset_mem_orbit :
  selected_coset \in
    Criterion.lazard_right_coset_orbit F20.standard_F20.
Proof.
rewrite /selected_coset.
exact: (@Criterion.lazard_right_coset_mem
  F20.S5 F20.standard_F20 relabelling).
Qed.

(** A concrete element of the conjugated subgroup. *)
Definition three_conjugated_five_cycle : F20.S5 :=
  F20.five_cycle ^ relabelling.

Lemma three_conjugated_five_cycle_mem_relabelled_F20 :
  three_conjugated_five_cycle \in relabelled_F20.
Proof.
rewrite /three_conjugated_five_cycle /relabelled_F20 memJ_conjg.
exact: F20.five_cycle_mem_standard_F20.
Qed.

(** This is an ordinary kernel computation on the finite type [S5].  It
    unfolds the displayed permutations and the normalizer membership test;
    it adds no axiom or opaque membership certificate. *)
Lemma three_conjugated_five_cycle_notin_standard_F20 :
  three_conjugated_five_cycle \notin F20.standard_F20.
Proof.
rewrite -F20.normalizes_cyclebE.
vm_compute.
Qed.

Lemma relabelled_F20_not_sub_standard_F20 :
  ~~ (relabelled_F20 \subset F20.standard_F20).
Proof.
apply/negP=> hsub.
have hw_standard :
    three_conjugated_five_cycle \in F20.standard_F20 :=
  (subsetP hsub _ three_conjugated_five_cycle_mem_relabelled_F20).
move: three_conjugated_five_cycle_notin_standard_F20.
by rewrite hw_standard.
Qed.

(** Every element of the conjugate stabilizes the selected right coset. *)
Lemma relabelled_F20_fixes_selected_coset h :
  h \in relabelled_F20 -> selected_coset :* h = selected_coset.
Proof.
move=> hh.
have hfixed : selected_coset \in 'Fix_('Rs)(relabelled_F20).
  by rewrite /selected_coset /relabelled_F20 sub_afixRs_norms.
move: (elimT afixP hfixed h hh).
by rewrite /= rcosetE.
Qed.

(** The witness does not fix the base coset, whose stabilizer is exactly the
    displayed standard [F20]. *)
Lemma three_conjugated_five_cycle_moves_base_coset :
  base_coset :* three_conjugated_five_cycle != base_coset.
Proof.
apply/negP=> /eqP hfix.
have hw_acted :
    three_conjugated_five_cycle \in
      base_coset :* three_conjugated_five_cycle.
  rewrite /base_coset -rcosetM mul1g.
  exact: rcoset_refl three_conjugated_five_cycle.
have hw_base : three_conjugated_five_cycle \in base_coset.
  rewrite -hfix.
  exact: hw_acted.
have hw_standard :
    three_conjugated_five_cycle \in F20.standard_F20.
  move: hw_base.
  by rewrite /base_coset mem_rcoset invg1 mulg1.
move: three_conjugated_five_cycle_notin_standard_F20.
by rewrite hw_standard.
Qed.

Lemma selected_coset_is_not_base_coset :
  selected_coset != base_coset.
Proof.
apply/negP=> /eqP hselected.
have hwfix := relabelled_F20_fixes_selected_coset
  three_conjugated_five_cycle_mem_relabelled_F20.
have hwbase :
    base_coset :* three_conjugated_five_cycle = base_coset.
  move: hwfix.
  by rewrite hselected.
move: three_conjugated_five_cycle_moves_base_coset.
by rewrite hwbase.
Qed.

(** The correction is precisely a relabeling: conjugating the selected
    subgroup back by the inverse permutation recovers the displayed copy. *)
Lemma relabelled_F20_conjugated_back :
  relabelled_F20 :^ relabelling^-1 = F20.standard_F20.
Proof. by rewrite /relabelled_F20 conjsgK. Qed.

(** Closed group-level counterexample to replacing "a conjugate of [F20]"
    by "the displayed [F20]" in the converse for arbitrary root labels. *)
Theorem fixed_displayed_subgroup_conclusion_fails :
  (forall h : F20.S5,
      h \in relabelled_F20 ->
      selected_coset :* h = selected_coset) /\
  ~~ (relabelled_F20 \subset F20.standard_F20) /\
  selected_coset != base_coset /\
  exists h : F20.S5,
    h \in relabelled_F20 /\
    base_coset :* h != base_coset.
Proof.
split; first exact: relabelled_F20_fixes_selected_coset.
split; first exact: relabelled_F20_not_sub_standard_F20.
split; first exact: selected_coset_is_not_base_coset.
exists three_conjugated_five_cycle; split.
- exact: three_conjugated_five_cycle_mem_relabelled_F20.
- exact: three_conjugated_five_cycle_moves_base_coset.
Qed.

Print Assumptions three_conjugated_five_cycle_notin_standard_F20.
Print Assumptions relabelled_F20_fixes_selected_coset.
Print Assumptions fixed_displayed_subgroup_conclusion_fails.

End PolynomialFormulasLazardGeneralResolventConjugacyCounterexample.
