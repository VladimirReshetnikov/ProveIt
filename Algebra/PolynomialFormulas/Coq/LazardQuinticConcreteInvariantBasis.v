(** PAUSED DRAFT CHECKPOINT (not registered in the committed Coq manifests).

    This concrete invariant-basis development has not yet been kernel
    checked against the unfinished Molien coefficient/numerator modules. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  QuinticF20Data LazardDisplayedGroebnerQuintic
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantArtinSuccessor
  LazardInvariantSymmetricModule LazardInvariantSubgroupModule
  LazardInvariantSubgroupTheoremTwo LazardInvariantMolienCoefficients
  LazardInvariantMolienNumeratorSeries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The concrete basis calculation in Lazard's Section 6.

    The six polynomials below are literally [1,i4,i5,i6,i7,i8], with the
    five nonconstant entries written as the ten-term F20 orbit sums printed
    in the paper.  Their invariance, homogeneity, and six selected Artin
    coordinates are closed finite computations.  In particular, no
    statement saying that a supplied matrix or a supplied list of normal
    forms is correct occurs in this file.

    The coordinate computation is performed through the already proved
    paper-oriented Artin decomposition in [LazardDisplayedGroebnerQuintic].
    It is therefore the Coq analogue of the sparse quotient witnesses in
    [LazardQuinticCoinvariantNormalForms.lean], but does not duplicate the
    generated quotient lists: the transparent Artin coordinate function is
    evaluated directly by the kernel.

    Finally, the six candidates are compared with the unconditional
    Reynolds basis from Lazard's Theorem 2.  A closed computation shows that
    this abstract basis has six elements, and the selected-coordinate matrix
    of the six candidates is unit triangular.  The resulting change-of-basis
    matrix is therefore a unit, so the candidates themselves give a
    homogeneous finite-free decomposition over the full symmetric-polynomial
    coefficient ring. *)
Module PolynomialFormulasLazardQuinticConcreteInvariantBasis.

Import GRing.Theory Num.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.
Local Open Scope multi_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module AS := PolynomialFormulasLazardInvariantArtinSuccessor.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.
Module T2 := PolynomialFormulasLazardInvariantSubgroupTheoremTwo.
Module DG := PolynomialFormulasLazardDisplayedGroebnerQuintic.
Module MC := PolynomialFormulasLazardInvariantMolienCoefficients.
Module MN := PolynomialFormulasLazardInvariantMolienNumeratorSeries.

Local Notation Coeff := {mpoly rat[5]}.
Local Notation RootRing := {mpoly rat[5]}.
Local Notation Inv :=
  (SIM.lazard_subgroup_invariant_module rat standard_F20).

Definition r0 : 'I_5 := @Ordinal 5 0 isT.
Definition r1 : 'I_5 := @Ordinal 5 1 isT.
Definition r2 : 'I_5 := @Ordinal 5 2 isT.
Definition r3 : 'I_5 := @Ordinal 5 3 isT.
Definition r4 : 'I_5 := @Ordinal 5 4 isT.

Definition root_variable (i : 'I_5) : RootRing := 'X_i.

Local Notation X0 := (root_variable r0).
Local Notation X1 := (root_variable r1).
Local Notation X2 := (root_variable r2).
Local Notation X3 := (root_variable r3).
Local Notation X4 := (root_variable r4).

(** The common ten-term orbit expression. *)
Definition lazard_orbit_polynomial (a b : nat) : RootRing :=
  X0 ^+ a * X1 ^+ b * X4 ^+ b +
  X0 ^+ a * X2 ^+ b * X3 ^+ b +
  X1 ^+ a * X0 ^+ b * X2 ^+ b +
  X1 ^+ a * X3 ^+ b * X4 ^+ b +
  X2 ^+ a * X0 ^+ b * X4 ^+ b +
  X2 ^+ a * X1 ^+ b * X3 ^+ b +
  X3 ^+ a * X0 ^+ b * X1 ^+ b +
  X3 ^+ a * X2 ^+ b * X4 ^+ b +
  X4 ^+ a * X0 ^+ b * X3 ^+ b +
  X4 ^+ a * X1 ^+ b * X2 ^+ b.

Definition concrete_candidate_tuple : 6.-tuple RootRing := [tuple
  1;
  lazard_orbit_polynomial 2 1;
  lazard_orbit_polynomial 3 1;
  lazard_orbit_polynomial 4 1;
  lazard_orbit_polynomial 3 2;
  lazard_orbit_polynomial 4 2].

Definition concrete_candidate (j : 'I_6) : RootRing :=
  tnth concrete_candidate_tuple j.

Definition concrete_candidate_degrees : 6.-tuple nat :=
  [tuple 0; 4; 5; 6; 7; 8]%N.

Definition concrete_candidate_degree (j : 'I_6) : nat :=
  tnth concrete_candidate_degrees j.

(** These checks range over all six polynomials and all twenty elements of
    the concrete affine F20.  They are proof-producing computations over
    the actual multinomial representation. *)
Definition concrete_candidate_homogeneous_check : bool :=
  [forall j : 'I_6,
    concrete_candidate j \is (concrete_candidate_degree j).-homog].

Lemma concrete_candidate_homogeneous_checkP :
  concrete_candidate_homogeneous_check.
Proof. vm_compute. Qed.

Theorem concrete_candidate_homogeneous j :
  concrete_candidate j \is (concrete_candidate_degree j).-homog.
Proof.
have /forallP h := concrete_candidate_homogeneous_checkP.
exact: h j.
Qed.

Definition concrete_candidate_invariant_check : bool :=
  [forall j : 'I_6, [forall g : [subg standard_F20],
    SM.symmetric_mpoly_left_action (sgval g) (concrete_candidate j) ==
      concrete_candidate j]].

Lemma concrete_candidate_invariant_checkP :
  concrete_candidate_invariant_check.
Proof. vm_compute. Qed.

Theorem concrete_candidate_invariantP j :
  concrete_candidate j
    \in SIM.lazard_subgroup_invariant_pred (F := rat) standard_F20.
Proof.
apply/SIM.lazard_subgroup_invariantP=> g.
have /forallP h := concrete_candidate_invariant_checkP.
have /forallP hj := h j.
exact/eqP: hj g.
Qed.

Definition concrete_invariant (j : 'I_6) : Inv :=
  @SIM.LazardSubgroupInvariant rat 5 standard_F20
    (concrete_candidate j) (concrete_candidate_invariantP j).

Lemma concrete_invariant_val j :
  SIM.lazard_subgroup_invariant_val (concrete_invariant j) =
    concrete_candidate j.
Proof. by []. Qed.

Theorem concrete_invariant_homogeneous j :
  SIM.lazard_invariant_homogeneous (concrete_invariant j)
    (concrete_candidate_degree j).
Proof. exact: concrete_candidate_homogeneous. Qed.

(** * Exact coinvariant coordinates *)

(** Augmenting a paper-oriented Artin coefficient means taking its
    constant coefficient in the formal elementary-symmetric variables. *)
Definition paper_coinvariant_coordinate
    (q : RootRing) (a : IM.artin_index 5) : rat :=
  (DG.paper_artin_coordinate q (DG.reverse_index_of_artin a)) @_ 0%MM.

Definition explicit_pivot_exponents : 6.-tuple 'X_{1..5} := [tuple
  [multinom [tuple 0; 0; 0; 0; 0]];
  [multinom [tuple 0; 1; 2; 1; 0]];
  [multinom [tuple 0; 2; 2; 1; 0]];
  [multinom [tuple 1; 2; 2; 1; 0]];
  [multinom [tuple 2; 2; 2; 1; 0]];
  [multinom [tuple 3; 2; 2; 1; 0]]].

Definition explicit_pivot_standard_check : bool :=
  [forall row : 'I_6, [forall i : 'I_5,
    (tnth explicit_pivot_exponents row) i < 5 - i]].

Lemma explicit_pivot_standard_checkP : explicit_pivot_standard_check.
Proof. vm_compute. Qed.

Lemma explicit_pivot_standard row i :
  (tnth explicit_pivot_exponents row) i < 5 - i.
Proof.
have /forallP h := explicit_pivot_standard_checkP.
have /forallP hr := h row.
exact: hr i.
Qed.

Definition explicit_pivot (row : 'I_6) : IM.artin_index 5 :=
  DG.artin_index_of_standard (tnth explicit_pivot_exponents row)
    (explicit_pivot_standard row).

Definition raw_pivot_diagonal : 6.-tuple rat :=
  [tuple 1; 2; -2; 2; -2; 4].

Definition expected_raw_pivot_entry (row column : 'I_6) : rat :=
  if row == column then tnth raw_pivot_diagonal row else 0.

Definition concrete_coinvariant_pivot_check : bool :=
  [forall row : 'I_6, [forall column : 'I_6,
    paper_coinvariant_coordinate (concrete_candidate column)
        (explicit_pivot row) ==
      expected_raw_pivot_entry row column]].

(** This is the finite normal-form calculation.  Odd-degree diagonal
    entries have the unswitched signs [-2]; the Lean recursive Artin basis
    includes an additional [(-1)^degree], which changes them to [2]. *)
Lemma concrete_coinvariant_pivot_checkP :
  concrete_coinvariant_pivot_check.
Proof. vm_compute. Qed.

Theorem concrete_coinvariant_pivot row column :
  paper_coinvariant_coordinate (concrete_candidate column)
      (explicit_pivot row) =
    expected_raw_pivot_entry row column.
Proof.
have /forallP h := concrete_coinvariant_pivot_checkP.
have /forallP hr := h row.
exact/eqP: hr column.
Qed.

Definition concrete_coinvariant_pivot_matrix : 'M[rat]_6 :=
  \matrix_(row, column)
    paper_coinvariant_coordinate (concrete_candidate column)
      (explicit_pivot row).

Definition raw_pivot_diagonal_row : 'rV[rat]_6 :=
  \row_row tnth raw_pivot_diagonal row.

Theorem concrete_coinvariant_pivot_matrixE :
  concrete_coinvariant_pivot_matrix = diag_mx raw_pivot_diagonal_row.
Proof.
apply/matrixP=> row column.
rewrite /concrete_coinvariant_pivot_matrix
  /raw_pivot_diagonal_row !mxE concrete_coinvariant_pivot.
by rewrite /expected_raw_pivot_entry.
Qed.

Theorem concrete_coinvariant_pivot_det :
  \det concrete_coinvariant_pivot_matrix = 64.
Proof.
rewrite concrete_coinvariant_pivot_matrixE det_diag.
vm_compute.
Qed.

Theorem concrete_coinvariant_pivot_unit :
  concrete_coinvariant_pivot_matrix \in unitmx.
Proof. by rewrite unitmxE concrete_coinvariant_pivot_det unitfE; vm_compute. Qed.

(** * The Molien/Reynolds rank-six gate *)

Local Definition f20_card_neq0 :
    (#|[subg standard_F20]|%:R : rat) != 0 :=
  MC.f20_subgroup_card_rat_neq0.

Local Notation AbstractIndex :=
  (T2.lazard_theorem_two_index
    (F := rat) (H := standard_F20) f20_card_neq0).

Local Notation AbstractBasis :=
  (T2.lazard_subgroup_invariant_finite_free
    (F := rat) (H := standard_F20) f20_card_neq0).

(** The type [AbstractIndex] is the disjoint union of the images of the
    degree-block Reynolds projections.  Thus this is a direct finite
    cardinality check against the very blocks used by the unconditional
    Theorem-2 basis.  It does not derive that cardinality from the Molien
    numerator; the explicit candidate-degree equality below is the later
    formal link with the numerator calculation. *)
Definition f20_abstract_index_card_check : bool :=
  #|AbstractIndex| == 6%N.

Lemma f20_abstract_index_card_checkP : f20_abstract_index_card_check.
Proof. vm_compute. Qed.

Theorem f20_abstract_index_card : #|AbstractIndex| = 6%N.
Proof. exact/eqP: f20_abstract_index_card_checkP. Qed.

(** The coefficientwise numerator theorem and the finite Reynolds-rank
    calculation are exposed together.  The first conjunct is the actual
    denominator-times-Reynolds-rank-series identity, not merely equality
    with the unsimplified class sum.  The upstream sequence retains the
    legacy name [f20_invariant_hilbert_series], but no identification with an
    independently encoded graded invariant space is used here. *)
Theorem f20_molien_series_and_abstract_rank_six :
  (forall d,
    MN.polynomial_series_action MN.f20_symmetric_denominator_poly
        MC.f20_invariant_hilbert_series d =
      MN.f20_molien_numerator_poly`_d) /\
  #|AbstractIndex| = 6%N.
Proof.
split.
- exact: MN.f20_invariant_hilbert_series_mul_symmetric_denominator.
- exact: f20_abstract_index_card.
Qed.

(** A concrete reindexing of the abstract Reynolds basis by six ordinals. *)
Definition abstract_index (j : 'I_6) : AbstractIndex :=
  enum_val (cast_ord (esym f20_abstract_index_card) j).

Definition abstract_index_inverse (i : AbstractIndex) : 'I_6 :=
  cast_ord f20_abstract_index_card (enum_rank i).

Lemma abstract_indexK : cancel abstract_index abstract_index_inverse.
Proof.
move=> j; rewrite /abstract_index /abstract_index_inverse enum_valK.
exact: cast_ordKV.
Qed.

Lemma abstract_index_inverseK : cancel abstract_index_inverse abstract_index.
Proof.
move=> i; rewrite /abstract_index /abstract_index_inverse cast_ordK.
exact: enum_rankK.
Qed.

Lemma abstract_index_bijective : bijective abstract_index.
Proof.
exists abstract_index_inverse; split.
- exact: abstract_indexK.
- exact: abstract_index_inverseK.
Qed.

Definition abstract_basis (j : 'I_6) : Inv :=
  FF.ffd_basis AbstractBasis (abstract_index j).

Definition abstract_coefficient (p : Inv) (j : 'I_6) : Coeff :=
  FF.ffd_coeff AbstractBasis p (abstract_index j).

Lemma abstract_reindexed_reconstruct p :
  p = \sum_j (abstract_coefficient p j) *: abstract_basis j.
Proof.
rewrite (FF.ffd_reconstruct AbstractBasis p).
rewrite (reindex abstract_index
  (onW_bij predT abstract_index_bijective)) /=.
exact: erefl.
Qed.

(** * A unit change of basis *)

Definition invariant_paper_coordinate
    (p : Inv) (a : IM.artin_index 5) : Coeff :=
  DG.paper_artin_coordinate
    (SIM.lazard_subgroup_invariant_val p)
    (DG.reverse_index_of_artin a).

Lemma invariant_paper_coordinateD p q a :
  invariant_paper_coordinate (p + q) a =
    invariant_paper_coordinate p a + invariant_paper_coordinate q a.
Proof.
rewrite /invariant_paper_coordinate /DG.paper_artin_coordinate.
rewrite msymD FF.ffd_coeffD.
exact: erefl.
Qed.

Lemma invariant_paper_coordinateZ c p a :
  invariant_paper_coordinate (c *: p) a =
    c * invariant_paper_coordinate p a.
Proof.
rewrite /invariant_paper_coordinate /DG.paper_artin_coordinate.
rewrite SM.symmetric_scalarE msymM DG.msym_sym_eval.
change
  FF.ffd_coeff
      (@AS.lazard_reverse_artin_finite_free_decomposition rat 5)
      (c *:
        msym (DG.paper_reverse_perm^-1)%g
          (SIM.lazard_subgroup_invariant_val p))
      (DG.reverse_index_of_artin a) = _.
exact: FF.ffd_coeffZ.
Qed.

Fact invariant_paper_coordinate_is_linear a :
  linear (fun p : Inv => invariant_paper_coordinate p a).
Proof.
move=> c p q.
by rewrite invariant_paper_coordinateD invariant_paper_coordinateZ.
Qed.

Definition invariant_paper_coordinate_linear a : {linear Inv -> Coeff} :=
  let f := fun p : Inv => invariant_paper_coordinate p a in
  HB.pack f
    (GRing.isLinear.Build Coeff Inv Coeff *:%R f
      (invariant_paper_coordinate_is_linear a)).

Lemma invariant_paper_coordinate_linearE p a :
  invariant_paper_coordinate_linear a p = invariant_paper_coordinate p a.
Proof. by []. Qed.

Definition concrete_artin_matrix : 'M[Coeff]_6 :=
  \matrix_(row, column)
    invariant_paper_coordinate (concrete_invariant column)
      (explicit_pivot row).

(** The full coefficient matrix is triangular.  Its constant diagonal is
    the preceding coinvariant certificate, so its determinant is the unit
    [64], not merely a nonzero polynomial. *)
Definition concrete_artin_transpose_trig_check : bool :=
  is_trig_mx (concrete_artin_matrix^T).

Lemma concrete_artin_transpose_trig_checkP :
  concrete_artin_transpose_trig_check.
Proof. vm_compute. Qed.

Theorem concrete_artin_matrix_det :
  \det concrete_artin_matrix = ((64%:R : rat)%:MP : Coeff).
Proof.
rewrite -det_tr.
rewrite (det_trig concrete_artin_transpose_trig_checkP).
vm_compute.
Qed.

Theorem concrete_artin_matrix_unit : concrete_artin_matrix \in unitmx.
Proof.
rewrite unitmxE concrete_artin_matrix_det.
vm_compute.
Qed.

Definition abstract_selected_matrix : 'M[Coeff]_6 :=
  \matrix_(row, column)
    invariant_paper_coordinate (abstract_basis column)
      (explicit_pivot row).

(** Column [column] contains the coordinates of the corresponding concrete
    candidate in the reindexed abstract Theorem-2 basis. *)
Definition concrete_to_abstract_matrix : 'M[Coeff]_6 :=
  \matrix_(row, column)
    abstract_coefficient (concrete_invariant column) row.

Lemma invariant_paper_coordinate_abstract_expansion p a :
  invariant_paper_coordinate p a =
    \sum_j abstract_coefficient p j *
      invariant_paper_coordinate (abstract_basis j) a.
Proof.
have h := congr1 (invariant_paper_coordinate_linear a)
  (abstract_reindexed_reconstruct p).
rewrite linear_sum invariant_paper_coordinate_linearE in h.
under [RHS] eq_bigr => j _ do
  rewrite linearZ invariant_paper_coordinate_linearE.
exact: h.
Qed.

Theorem concrete_artin_matrix_factorization :
  concrete_artin_matrix =
    abstract_selected_matrix *m concrete_to_abstract_matrix.
Proof.
apply/matrixP=> row column.
rewrite /concrete_artin_matrix /abstract_selected_matrix
  /concrete_to_abstract_matrix !mxE mulmxE.
rewrite invariant_paper_coordinate_abstract_expansion.
apply: eq_bigr=> j _.
by rewrite mulrC.
Qed.

Theorem concrete_to_abstract_matrix_unit :
  concrete_to_abstract_matrix \in unitmx.
Proof.
have hproduct :
    abstract_selected_matrix *m concrete_to_abstract_matrix \in unitmx.
  by rewrite -concrete_artin_matrix_factorization;
    exact: concrete_artin_matrix_unit.
move: hproduct.
by rewrite unitmx_mul => /andP [_].
Qed.

Definition abstract_coefficient_row (p : Inv) : 'rV[Coeff]_6 :=
  \row_j abstract_coefficient p j.

Definition concrete_coefficient_row (p : Inv) : 'rV[Coeff]_6 :=
  abstract_coefficient_row p *m invmx (concrete_to_abstract_matrix^T).

Definition concrete_coefficient (p : Inv) (j : 'I_6) : Coeff :=
  concrete_coefficient_row p 0 j.

Lemma abstract_coefficient_concrete_combination
    (c : 'rV[Coeff]_6) i :
  abstract_coefficient
      (\sum_j (c 0 j) *: concrete_invariant j) i =
    (c *m concrete_to_abstract_matrix^T) 0 i.
Proof.
rewrite /abstract_coefficient FF.ffd_coeff_sum mulmxE.
apply: eq_bigr=> j _.
rewrite FF.ffd_coeffZ /concrete_to_abstract_matrix !mxE.
exact: erefl.
Qed.

Theorem concrete_coefficient_reconstruct p :
  p = \sum_j (concrete_coefficient p j) *: concrete_invariant j.
Proof.
apply: esym.
apply: FF.ffd_eq_of_coeff_eq=> i.
pose j := abstract_index_inverse i.
have hij : abstract_index j = i := abstract_index_inverseK i.
rewrite -hij -/abstract_coefficient.
rewrite abstract_coefficient_concrete_combination.
rewrite /concrete_coefficient /concrete_coefficient_row.
have hunitT : concrete_to_abstract_matrix^T \in unitmx.
  by rewrite unitmx_tr; exact: concrete_to_abstract_matrix_unit.
rewrite (mulmxKV hunitT).
by rewrite /abstract_coefficient_row mxE.
Qed.

Theorem concrete_coefficient_unique p (c : 'I_6 -> Coeff) :
  p = \sum_j (c j) *: concrete_invariant j ->
  forall j, c j = concrete_coefficient p j.
Proof.
move=> hp j.
pose rowc : 'rV[Coeff]_6 := \row_k c k.
have hrow : abstract_coefficient_row p =
    rowc *m concrete_to_abstract_matrix^T.
  apply/rowP=> i.
  rewrite /abstract_coefficient_row mxE hp.
  exact: abstract_coefficient_concrete_combination rowc i.
rewrite /concrete_coefficient /concrete_coefficient_row hrow.
have hunitT : concrete_to_abstract_matrix^T \in unitmx.
  by rewrite unitmx_tr; exact: concrete_to_abstract_matrix_unit.
rewrite (mulmxK hunitT).
by rewrite /rowc mxE.
Qed.

(** The promised concrete symmetric-module basis.  This is the same
    finite-free interface used by the Coq statement of Lazard's Theorem 2;
    its coordinate and uniqueness fields have just been proved above. *)
Definition concrete_invariant_finite_free :
    FF.finite_free_decomposition Coeff Inv :=
  {| FF.ffd_index := [finType of 'I_6];
     FF.ffd_basis := concrete_invariant;
     FF.ffd_coeff := concrete_coefficient;
     FF.ffd_reconstruct := concrete_coefficient_reconstruct;
     FF.ffd_unique := concrete_coefficient_unique |}.

(** The finite-free basis field is literally Lazard's displayed family,
    rather than an unnamed basis whose cardinality merely happens to be six. *)
Lemma concrete_invariant_finite_free_basisE j :
  FF.ffd_basis concrete_invariant_finite_free j = concrete_invariant j.
Proof. by []. Qed.

Definition concrete_degree_bound_check : bool :=
  [forall j : 'I_6,
    concrete_candidate_degree j <= IM.lazard_degree_bound 5].

Lemma concrete_degree_bound_checkP : concrete_degree_bound_check.
Proof. vm_compute. Qed.

Lemma concrete_candidate_degree_le j :
  concrete_candidate_degree j <= IM.lazard_degree_bound 5.
Proof.
have /forallP h := concrete_degree_bound_checkP.
exact: h j.
Qed.

Definition concrete_invariant_homogeneous_finite_free :
    @FF.homogeneous_finite_free_decomposition Coeff Inv
      (SIM.lazard_invariant_homogeneous
        (F := rat) (H := standard_F20))
      (IM.lazard_degree_bound 5) :=
  {| FF.hffd_free := concrete_invariant_finite_free;
     FF.hffd_degree := concrete_candidate_degree;
     FF.hffd_basis_homogeneous := concrete_invariant_homogeneous;
     FF.hffd_degree_le := concrete_candidate_degree_le |}.

(** The six displayed basis degrees themselves form Lazard's numerator.
    This is the explicit link that was absent when the Molien class-sum and
    the rank-six computation were merely paired as independent conjuncts. *)
Definition concrete_basis_degree_polynomial : {poly rat} :=
  \sum_(j < 6) ('X : {poly rat}) ^+ (concrete_candidate_degree j).

Lemma concrete_basis_degree_polynomial_eq_molien_numerator :
  concrete_basis_degree_polynomial = MN.f20_molien_numerator_poly.
Proof.
rewrite /concrete_basis_degree_polynomial /concrete_candidate_degree
  /concrete_candidate_degrees /MN.f20_molien_numerator_poly
  !big_ord_recr big_ord0 /= expr0 add0r.
reflexivity.
Qed.

(** Terminal Molien-to-basis endpoint.  Its coefficient identity has the
    actual six basis degrees on the right, so the rank-six homogeneous basis
    is connected to, rather than merely conjoined with, the numerator
    computation. *)
Theorem f20_molien_numerator_concrete_basis_complete :
  (forall d,
    MN.polynomial_series_action MN.f20_symmetric_denominator_poly
        MC.f20_invariant_hilbert_series d =
      concrete_basis_degree_polynomial`_d) /\
  #|AbstractIndex| = 6%N /\
  inhabited
    (@FF.homogeneous_finite_free_decomposition Coeff Inv
      (SIM.lazard_invariant_homogeneous
        (F := rat) (H := standard_F20))
      (IM.lazard_degree_bound 5)).
Proof.
split.
- move=> d.
  rewrite concrete_basis_degree_polynomial_eq_molien_numerator.
  exact: MN.f20_invariant_hilbert_series_mul_symmetric_denominator.
- split.
  + exact: f20_abstract_index_card.
  + exact: inhabits concrete_invariant_homogeneous_finite_free.
Qed.

(** A compact end theorem for audit files.  The first conjunct is the
    literal six-by-six coinvariant calculation; the second is the actual
    homogeneous module basis, with no certificate parameter. *)
Theorem lazard_f20_concrete_basis_complete :
  (forall row column,
    paper_coinvariant_coordinate (concrete_candidate column)
        (explicit_pivot row) =
      expected_raw_pivot_entry row column) /\
  inhabited
    (@FF.homogeneous_finite_free_decomposition Coeff Inv
      (SIM.lazard_invariant_homogeneous
        (F := rat) (H := standard_F20))
      (IM.lazard_degree_bound 5)).
Proof.
split.
- exact: concrete_coinvariant_pivot.
- exact: inhabits concrete_invariant_homogeneous_finite_free.
Qed.

End PolynomialFormulasLazardQuinticConcreteInvariantBasis.
