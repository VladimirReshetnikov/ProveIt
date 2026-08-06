(* ===================================================================== *)
(*  Semantics of the direct Mu-recursive sextic resolvent root tests.    *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util Require Import recomp.

From PolynomialFormulas Require Import
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecSparseEvaluator SexticMuRecCollisionEvaluator
  SexticMuRecCollisionSemantics SexticMuRecResolventRootEvaluator
  SexticRecursiveCore SexticSparsePolynomials SexticSparseResolvents
  SexticPowerSumSymmetric SexticNewtonPowerSums SexticComputedResolvents
  SexticResolventSymmetry SexticComputedResolventBridge
  SexticSeparatingSearch
  SexticRationalRootSearch SexticHomogeneousRootSearch
  SexticMuRecResolventCoefficients SexticCanonicalVieta
  SexticDescriptorGaloisCriterion SexticMuRecSeparatingInstance
  SexticMuRecIrreducibleAssembly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecResolventRootSemantics.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SP := PolynomialFormulasSexticSparsePolynomials.
Module SR := PolynomialFormulasSexticSparseResolvents.
Module PS := PolynomialFormulasSexticPowerSumSymmetric.
Module NPS := PolynomialFormulasSexticNewtonPowerSums.
Module CR := PolynomialFormulasSexticComputedResolvents.
Module SRS := PolynomialFormulasSexticResolventSymmetry.
Module CRB := PolynomialFormulasSexticComputedResolventBridge.
Module SS := PolynomialFormulasSexticSeparatingSearch.
Module SRR := PolynomialFormulasSexticRationalRootSearch.
Module SHR := PolynomialFormulasSexticHomogeneousRootSearch.
Module RC := PolynomialFormulasSexticMuRecResolventCoefficients.
Module CV := PolynomialFormulasSexticCanonicalVieta.
Module DGC := PolynomialFormulasSexticDescriptorGaloisCriterion.
Module SSI := PolynomialFormulasSexticMuRecSeparatingInstance.
Module IA := PolynomialFormulasSexticMuRecIrreducibleAssembly.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module SE := PolynomialFormulasSexticMuRecSparseEvaluator.
Module CE := PolynomialFormulasSexticMuRecCollisionEvaluator.
Module CS := PolynomialFormulasSexticMuRecCollisionSemantics.
Module RE := PolynomialFormulasSexticMuRecResolventRootEvaluator.

(* --------------------------------------------------------------------- *)
(* Sparse homogeneous products underlying the direct evaluators.         *)

Definition pair_sparse_homogeneous_product
    (u v : int) (x : SR.parameter) : SP.sparse_polynomial :=
  SP.sparse_product
    [seq SP.sparse_sub (SP.sparse_const u)
      (SP.sparse_mul (SP.sparse_const v)
        (SR.pair_sparse_descriptor_value x p))
    | p <- enum SR.pair_partition].

Definition triple_sparse_homogeneous_product
    (u v : int) (x : SR.parameter) : SP.sparse_polynomial :=
  SP.sparse_product
    [seq SP.sparse_sub (SP.sparse_const u)
      (SP.sparse_mul (SP.sparse_const v)
        (SR.triple_sparse_descriptor_value x p))
    | p <- enum SR.triple_partition].

Section SparseHomogeneousEvaluation.

Variable R : comPzRingType.

Lemma pair_sparse_homogeneous_product_eval
    (roots : 6.-tuple R) u v x :
  NPS.sparse_eval_ring roots (pair_sparse_homogeneous_product u v x) =
  \prod_(p : SR.pair_partition)
    ((u)%:~R - (v)%:~R *
      NPS.sparse_eval_ring roots (SR.pair_sparse_descriptor_value x p)).
Proof.
rewrite /pair_sparse_homogeneous_product NPS.sparse_eval_ring_product
  big_map big_enum.
apply: eq_bigr=> p _.
by rewrite NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_const
  NPS.sparse_eval_ring_mul NPS.sparse_eval_ring_const.
Qed.

Lemma triple_sparse_homogeneous_product_eval
    (roots : 6.-tuple R) u v x :
  NPS.sparse_eval_ring roots (triple_sparse_homogeneous_product u v x) =
  \prod_(p : SR.triple_partition)
    ((u)%:~R - (v)%:~R *
      NPS.sparse_eval_ring roots (SR.triple_sparse_descriptor_value x p)).
Proof.
rewrite /triple_sparse_homogeneous_product NPS.sparse_eval_ring_product
  big_map big_enum.
apply: eq_bigr=> p _.
by rewrite NPS.sparse_eval_ring_sub NPS.sparse_eval_ring_const
  NPS.sparse_eval_ring_mul NPS.sparse_eval_ring_const.
Qed.

End SparseHomogeneousEvaluation.

Section SparseHomogeneousSymmetry.

Variable R : comNzRingType.

Lemma pair_sparse_homogeneous_tperm
    (roots : 6.-tuple R) u v x j :
  NPS.sparse_eval_ring
      (NPS.assignment_values roots (finfun (tperm ord0 j)))
      (pair_sparse_homogeneous_product u v x) =
  NPS.sparse_eval_ring roots (pair_sparse_homogeneous_product u v x).
Proof.
rewrite !pair_sparse_homogeneous_product_eval.
under [LHS]eq_bigr=> p _ do rewrite SRS.pair_descriptor_tperm.
symmetry.
rewrite (reindex_inj (@SRS.pair_partition_map_injective j)).
done.
Qed.

Lemma triple_sparse_homogeneous_tperm
    (roots : 6.-tuple R) u v x j :
  NPS.sparse_eval_ring
      (NPS.assignment_values roots (finfun (tperm ord0 j)))
      (triple_sparse_homogeneous_product u v x) =
  NPS.sparse_eval_ring roots (triple_sparse_homogeneous_product u v x).
Proof.
rewrite !triple_sparse_homogeneous_product_eval.
under [LHS]eq_bigr=> p _ do rewrite SRS.triple_descriptor_tperm.
symmetry.
rewrite (reindex_inj (@SRS.triple_partition_map_injective j)).
done.
Qed.

Lemma pair_sparse_homogeneous_perm u v x g :
  @SRS.sparse_permutation_invariant R
    (pair_sparse_homogeneous_product u v x) g.
Proof.
apply: SRS.sparse_permutation_invariant_all=> j roots.
exact: pair_sparse_homogeneous_tperm.
Qed.

Lemma triple_sparse_homogeneous_perm u v x g :
  @SRS.sparse_permutation_invariant R
    (triple_sparse_homogeneous_product u v x) g.
Proof.
apply: SRS.sparse_permutation_invariant_all=> j roots.
exact: triple_sparse_homogeneous_tperm.
Qed.

Theorem pair_sparse_homogeneous_invariant
    (roots : 6.-tuple R) u v x :
  NPS.permutation_invariant_at roots
    (pair_sparse_homogeneous_product u v x).
Proof.
move=> a ha.
rewrite NPS.assignment_code_injectiveb in ha.
have hainj : injective a := elimT (@injectiveP _ _ a) ha.
pose g : {perm 'I_6} := perm hainj.
have havals : NPS.assignment_values roots a =
    NPS.assignment_values roots (finfun g).
  apply: eq_from_tnth=> k.
  by rewrite /NPS.assignment_values !tnth_mktuple !ffunE /g permE.
rewrite havals.
exact: pair_sparse_homogeneous_perm.
Qed.

Theorem triple_sparse_homogeneous_invariant
    (roots : 6.-tuple R) u v x :
  NPS.permutation_invariant_at roots
    (triple_sparse_homogeneous_product u v x).
Proof.
move=> a ha.
rewrite NPS.assignment_code_injectiveb in ha.
have hainj : injective a := elimT (@injectiveP _ _ a) ha.
pose g : {perm 'I_6} := perm hainj.
have havals : NPS.assignment_values roots a =
    NPS.assignment_values roots (finfun g).
  apply: eq_from_tnth=> k.
  by rewrite /NPS.assignment_values !tnth_mktuple !ffunE /g permE.
rewrite havals.
exact: triple_sparse_homogeneous_perm.
Qed.

End SparseHomogeneousSymmetry.

Definition pair_scaled_homogeneous_sparse_value
    (f : SRC.monic_sextic) (x : SR.parameter) (u v : int) : int :=
  CR.scaled_symmetric_value f (pair_sparse_homogeneous_product u v x).

Definition triple_scaled_homogeneous_sparse_value
    (f : SRC.monic_sextic) (x : SR.parameter) (u v : int) : int :=
  CR.scaled_symmetric_value f (triple_sparse_homogeneous_product u v x).

Section ScaledSparseHomogeneousCorrectness.

Variable R : comNzRingType.

Theorem pair_scaled_homogeneous_sparse_value_correct roots f x u v :
  @CR.cast_int_values R (CR.monic_elementary_values f) =
      NPS.elementary_values roots ->
  (pair_scaled_homogeneous_sparse_value f x u v)%:~R =
  720%:R * \prod_(p : SR.pair_partition)
    ((u)%:~R - (v)%:~R *
      NPS.sparse_eval_ring roots (SR.pair_sparse_descriptor_value x p)).
Proof.
move=> hvieta.
rewrite /pair_scaled_homogeneous_sparse_value.
rewrite (@CR.scaled_symmetric_value_correct R roots f
  (pair_sparse_homogeneous_product u v x) hvieta
  (pair_sparse_homogeneous_invariant roots u v x)).
by rewrite pair_sparse_homogeneous_product_eval.
Qed.

Theorem triple_scaled_homogeneous_sparse_value_correct roots f x u v :
  @CR.cast_int_values R (CR.monic_elementary_values f) =
      NPS.elementary_values roots ->
  (triple_scaled_homogeneous_sparse_value f x u v)%:~R =
  720%:R * \prod_(p : SR.triple_partition)
    ((u)%:~R - (v)%:~R *
      NPS.sparse_eval_ring roots (SR.triple_sparse_descriptor_value x p)).
Proof.
move=> hvieta.
rewrite /triple_scaled_homogeneous_sparse_value.
rewrite (@CR.scaled_symmetric_value_correct R roots f
  (triple_sparse_homogeneous_product u v x) hvieta
  (triple_sparse_homogeneous_invariant roots u v x)).
by rewrite triple_sparse_homogeneous_product_eval.
Qed.

End ScaledSparseHomogeneousCorrectness.

(* --------------------------------------------------------------------- *)
(* The sparse product is the homogeneous evaluation of the computed list. *)

Lemma homogeneous_eval_zero_fixed degree cs u :
  size cs = degree.+1 ->
  SRR.homogeneous_eval cs u 0 = u ^+ degree * nth 0 cs degree.
Proof.
elim: degree cs=> [|degree ih] [|a cs] //=.
- move=> hsize.
  case: cs hsize=> [|b cs] //= _.
  by rewrite !expr0 mulr1 mulr0 addr0 mul1r.
- move=> hsize.
  have htail : size cs = degree.+1 by lia.
  clear hsize.
  case: cs htail=> [|b cs] //= htail.
  rewrite exprS mul0r mulr0 add0r.
  change (u * SRR.homogeneous_eval (b :: cs) u 0 =
    u ^+ degree.+1 * nth 0 (b :: cs) degree).
  rewrite (ih (b :: cs) htail) exprS.
  by rewrite mulrA [u * u ^+ degree]mulrC.
Qed.

Section DenominatorClearing.

Variable F : fieldType.

Lemma product_div_clear degree (u v : F) (value : 'I_degree -> F) :
  v != 0 ->
  (\prod_(i : 'I_degree) (u / v - value i)) * v ^+ degree =
  \prod_(i : 'I_degree) (u - v * value i).
Proof.
move=> hv.
have hvprod : v ^+ degree = \prod_(i : 'I_degree) v.
  by rewrite prodr_const card_ord.
rewrite hvprod -big_split.
apply: eq_bigr=> i _.
change ((u / v - value i) * v = u - v * value i).
by rewrite mulrBl divfK // mulrC.
Qed.

End DenominatorClearing.

Local Notation ratrC := (@ratr algC).

Lemma cast_homogeneous_eval_nonzero cs u v :
  v != 0 ->
  ((SRR.homogeneous_eval cs u v)%:~R : algC) =
  (map_poly (intr : int -> algC) (SRR.coefficient_list_poly_int cs)).[
      (u%:~R : algC) / (v%:~R : algC)] *
    (v%:~R : algC) ^+ (size cs).-1.
Proof.
move=> hv.
have hrat := SHR.homogeneous_eval_ratE cs u hv.
rewrite -SRR.coefficient_list_eval_ratE in hrat.
have hcast := congr1 ratrC hrat.
have hp := CRB.int_poly_horner_ratr
  (SRR.coefficient_list_poly_int cs)
  ((u%:~R : rat) / (v%:~R : rat)).
move: hcast; rewrite rmorphM rmorphXn=> hcast.
change (ratrC ((SRR.homogeneous_eval cs u v)%:~R : rat) =
  ratrC ((map_poly (intr : int -> rat)
    (SRR.coefficient_list_poly_int cs)).[
      (u%:~R : rat) / (v%:~R : rat)]) *
  ratrC (v%:~R : rat) ^+ (size cs).-1) in hcast.
rewrite -hp in hcast.
rewrite !ratr_int rmorph_div in hcast.
- rewrite !rmorph_int in hcast.
  exact hcast.
- by rewrite unitfE intr_eq0.
Qed.

Lemma pair_computed_homogeneous_cast_nonzero roots f x u v :
  @CR.cast_int_values algC (CR.monic_elementary_values f) =
      NPS.elementary_values roots ->
  v != 0 ->
  ((SRR.homogeneous_eval (CR.pair_scaled_resolvent f x) u v)%:~R
      : algC) =
  720%:R * \prod_(p : SR.pair_partition)
    ((u)%:~R - (v)%:~R *
      NPS.sparse_eval_ring roots (SR.pair_sparse_descriptor_value x p)).
Proof.
move=> hvieta hv.
rewrite cast_homogeneous_eval_nonzero // CR.size_pair_scaled_resolvent.
rewrite (@CRB.pair_scaled_resolvent_poly_correct
  algC roots f x hvieta) hornerZ.
rewrite SRS.coefficient_list_poly_pair_resolvent horner_prod.
under eq_bigr=> p _ do rewrite hornerXsubC.
have hvC : (v%:~R : algC) != 0 by rewrite intr_eq0.
rewrite /SR.pair_partition.
rewrite /=.
rewrite -mulrA (@product_div_clear algC 15
  (u%:~R : algC) (v%:~R : algC)
  (fun p : SR.pair_partition =>
    NPS.sparse_eval_ring roots (SR.pair_sparse_descriptor_value x p))
  hvC).
reflexivity.
Qed.

Lemma triple_computed_homogeneous_cast_nonzero roots f x u v :
  @CR.cast_int_values algC (CR.monic_elementary_values f) =
      NPS.elementary_values roots ->
  v != 0 ->
  ((SRR.homogeneous_eval (CR.triple_scaled_resolvent f x) u v)%:~R
      : algC) =
  720%:R * \prod_(p : SR.triple_partition)
    ((u)%:~R - (v)%:~R *
      NPS.sparse_eval_ring roots (SR.triple_sparse_descriptor_value x p)).
Proof.
move=> hvieta hv.
rewrite cast_homogeneous_eval_nonzero // CR.size_triple_scaled_resolvent.
rewrite (@CRB.triple_scaled_resolvent_poly_correct
  algC roots f x hvieta) hornerZ.
rewrite SRS.coefficient_list_poly_triple_resolvent horner_prod.
under eq_bigr=> p _ do rewrite hornerXsubC.
have hvC : (v%:~R : algC) != 0 by rewrite intr_eq0.
rewrite /SR.triple_partition.
rewrite /=.
rewrite -mulrA (@product_div_clear algC 10
  (u%:~R : algC) (v%:~R : algC)
  (fun p : SR.triple_partition =>
    NPS.sparse_eval_ring roots (SR.triple_sparse_descriptor_value x p))
  hvC).
reflexivity.
Qed.

Definition canonical_roots (f : SRC.monic_sextic) : 6.-tuple algC :=
  @DGC.sextic_complex_root_tuple
    (CV.rational_monic_sextic f) (CV.size_rational_monic_sextic f).

Theorem pair_scaled_homogeneous_sparse_valueE f x u v :
  pair_scaled_homogeneous_sparse_value f x u v =
  SRR.homogeneous_eval (CR.pair_scaled_resolvent f x) u v.
Proof.
apply: (@intr_inj algC).
case hv: (v == 0).
- move/eqP: hv=> ->.
  rewrite (@homogeneous_eval_zero_fixed 15
    (CR.pair_scaled_resolvent f x) u
    (CR.size_pair_scaled_resolvent f x)) RC.pair_scaled_resolvent_last.
  rewrite (@pair_scaled_homogeneous_sparse_value_correct
    algC (canonical_roots f) f x u 0
    (CV.canonical_monic_sextic_vieta f)).
  under eq_bigr=> p _ do rewrite rmorph0 mul0r subr0.
  rewrite prodr_const card_ord rmorphM rmorphXn rmorph_nat.
  by rewrite mulrC.
- have hvnz : v != 0 by rewrite /negb hv.
  rewrite (@pair_scaled_homogeneous_sparse_value_correct
    algC (canonical_roots f) f x u v
    (CV.canonical_monic_sextic_vieta f)).
  symmetry.
  exact: (@pair_computed_homogeneous_cast_nonzero
    (canonical_roots f) f x u v
    (CV.canonical_monic_sextic_vieta f) hvnz).
Qed.

Theorem triple_scaled_homogeneous_sparse_valueE f x u v :
  triple_scaled_homogeneous_sparse_value f x u v =
  SRR.homogeneous_eval (CR.triple_scaled_resolvent f x) u v.
Proof.
apply: (@intr_inj algC).
case hv: (v == 0).
- move/eqP: hv=> ->.
  rewrite (@homogeneous_eval_zero_fixed 10
    (CR.triple_scaled_resolvent f x) u
    (CR.size_triple_scaled_resolvent f x))
    RC.triple_scaled_resolvent_last.
  rewrite (@triple_scaled_homogeneous_sparse_value_correct
    algC (canonical_roots f) f x u 0
    (CV.canonical_monic_sextic_vieta f)).
  under eq_bigr=> p _ do rewrite rmorph0 mul0r subr0.
  rewrite prodr_const card_ord rmorphM rmorphXn rmorph_nat.
  by rewrite mulrC.
- have hvnz : v != 0 by rewrite /negb hv.
  rewrite (@triple_scaled_homogeneous_sparse_value_correct
    algC (canonical_roots f) f x u v
    (CV.canonical_monic_sextic_vieta f)).
  symmetry.
  exact: (@triple_computed_homogeneous_cast_nonzero
    (canonical_roots f) f x u v
    (CV.canonical_monic_sextic_vieta f) hvnz).
Qed.

Print Assumptions pair_scaled_homogeneous_sparse_value_correct.
Print Assumptions triple_scaled_homogeneous_sparse_value_correct.
Print Assumptions pair_scaled_homogeneous_sparse_valueE.
Print Assumptions triple_scaled_homogeneous_sparse_valueE.

End PolynomialFormulasSexticMuRecResolventRootSemantics.
