From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantSymmetricModule LazardInvariantSubgroupModule
  LazardInvariantSubgroupReynolds LazardInvariantSubgroupTheoremTwo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's invariant leading-term descent (Lemma 2).

    The reverse Artin basis is the standard-monomial basis supplied by
    Lemma 1.  In Lazard's order one first compares total root degree and,
    only at equal root degree, compares the elementary-symmetric variables.
    Thus a reduced polynomial has an [e]-independent leading monomial as
    soon as

      - every Artin row above degree [d] is zero,
      - every coefficient in row [d] is a ground-field constant, and
      - at least one of those constants is nonzero.

    The last clause is recorded with the actual nonzero ground-field scalar,
    so it cannot be satisfied by a vacuous zero top row.  The generators
    constructed in [LazardInvariantSubgroupTheoremTwo] have exactly these
    properties: their top rows are the nonzero vectors of the canonical
    bases of the constant Reynolds blocks. *)
Module PolynomialFormulasLazardInvariantLeadingTermDescent.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.
Module SR := PolynomialFormulasLazardInvariantSubgroupReynolds.
Module T2 := PolynomialFormulasLazardInvariantSubgroupTheoremTwo.

Section LeadingNormalForm.

Variables (F : fieldType) (n : nat) (H : {group 'S_n}).
Hypothesis cardH_neq0 : (#|[subg H]|%:R : F) != 0.

Local Notation S := {mpoly F[n]}.
Local Notation Inv := (SIM.lazard_subgroup_invariant_module F H).
Local Notation Artin :=
  (SIM.lazard_ambient_artin_homogeneous_decomposition F n).
Local Notation B := (FF.hffd_free Artin).
Local Notation degree := (FF.hffd_degree Artin).
Local Notation N := (#|FF.ffd_index B|).
Local Notation bound := (IM.lazard_degree_bound n).
Local Notation block_image :=
  (SR.lazard_subgroup_reynolds_degree_block_image
    F (n := n) H).
Local Notation block_basis :=
  (SR.lazard_subgroup_reynolds_degree_block_basis
    F (n := n) H).
Local Notation Index :=
  (T2.lazard_theorem_two_index
    F (n := n) H).
Local Notation generator :=
  (T2.lazard_theorem_two_generator
    (F := F) (n := n) (H := H)).
Local Notation generator_degree :=
  (T2.lazard_theorem_two_degree
    (F := F) (n := n) (H := H)).
Local Notation artin_coeff :=
  (T2.lazard_invariant_artin_coeff
    (F := F) (n := n) (H := H)).

(** Exact Artin-coordinate form of the paper's phrase "the leading
    monomial after reduction by [J] is independent of the [e_i]".  Requiring
    the whole top row to be constant is slightly stronger than requiring
    just the tie-broken leading coefficient, and is what the homogeneous
    construction proves directly. *)
Record lazard_paper_leading_normal_form (p : Inv) (d : nat) : Prop := {
  lazard_leading_rows_above_zero :
    forall i : FF.ffd_index B, (d < degree i)%N -> artin_coeff p i = 0;
  lazard_leading_top_row_constant :
    forall j : 'I_N, degree (enum_val j) = d ->
      exists r : F, artin_coeff p (enum_val j) = (r%:MP : S);
  lazard_leading_top_row_nonzero :
    exists (j : 'I_N) (r : F),
      degree (enum_val j) = d /\
      r != 0 /\
      artin_coeff p (enum_val j) = (r%:MP : S)
}.

(** A vector in a canonical degree-block basis is nonzero and is supported
    in its selected degree.  Hence it has a nonzero coordinate in that
    degree. *)
Lemma lazard_block_basis_has_nonzero_degree_coordinate d
    (k : 'I_(\dim (block_image d))) :
  exists j : 'I_N,
    degree (enum_val j) = d /\
    tnth (block_basis d) k 0 j != 0.
Proof.
have hbasis : tnth (block_basis d) k != 0.
  exact: (@basis_not0 F _ (tnth (block_basis d) k)
    (block_image d) (block_basis d)
    (SR.lazard_subgroup_reynolds_degree_block_basisP
      F (n := n) H d) (mem_tnth k _)).
move/rV0Pn: hbasis => [j hj].
have hdegree : degree (enum_val j) = d.
  case hdeg: (degree (enum_val j) == d).
  - by apply/eqP; rewrite hdeg.
  - have hz :=
      SR.lazard_subgroup_reynolds_degree_block_basis_support
        (F := F) (n := n) (H := H) cardH_neq0
        (d := d) (j := j) k.
    have hz0 : tnth (block_basis d) k 0 j = 0.
      apply: hz.
      by rewrite hdeg.
    by rewrite hz0 eqxx in hj.
by exists j.
Qed.

(** Every member of the finite family constructed for Theorem 2 has the
    literal leading-normal-form property used in Lazard's Lemma 2. *)
Theorem lazard_theorem_two_generator_leading_normal_form (g : Index) :
  lazard_paper_leading_normal_form
    (generator g) (generator_degree g).
Proof.
case: g => d k /=.
constructor.
- move=> i hdi.
  exact: (T2.lazard_block_lift_coeff_above
    (F := F) (n := n) (H := H) cardH_neq0 k hdi).
- move=> j hj.
  exists (tnth (block_basis (d : nat)) k 0 j).
  exact: (T2.lazard_block_lift_coeff_top
    (F := F) (n := n) (H := H) cardH_neq0 k hj).
- have [j [hjdegree hj0]] :=
    lazard_block_basis_has_nonzero_degree_coordinate (d := (d : nat)) k.
  exists j, (tnth (block_basis (d : nat)) k 0 j).
  split; first exact: hjdegree.
  split; first exact: hj0.
  exact: (T2.lazard_block_lift_coeff_top
    (F := F) (n := n) (H := H) cardH_neq0 k hjdegree).
Qed.

(** The exact finite-generation statement of Lazard's Lemma 2 for the
    explicit family already constructed in Theorem 2. *)
Definition lazard_paper_lemma_two : Prop :=
  (forall g : Index,
    lazard_paper_leading_normal_form
      (generator g) (generator_degree g)) /\
  (forall p : Inv, exists c : Index -> S,
    p = \sum_g c g *: generator g).

Theorem lazard_paper_lemma_two_proved : lazard_paper_lemma_two.
Proof.
split.
- exact: lazard_theorem_two_generator_leading_normal_form.
- move=> p.
  have [c hc] := T2.lazard_theorem_two_spans
    (F := F) (n := n) (H := H) cardH_neq0 p.
  exists c.
  exact: hc.
Qed.

End LeadingNormalForm.

(** Characteristic zero supplies the only extra hypothesis above: the
    subgroup order is nonzero in the ground field. *)
Theorem lazard_paper_lemma_two_statement
    (F : fieldType) (n : nat) (H : {group 'S_n})
    (pchar0F : [pchar F] =i pred0) :
  lazard_paper_lemma_two F (n := n) H.
Proof.
exact: (lazard_paper_lemma_two_proved
  (F := F) (n := n) (H := H)
  (SR.lazard_subgroup_card_neq0_of_pchar0 H pchar0F)).
Qed.

End PolynomialFormulasLazardInvariantLeadingTermDescent.
