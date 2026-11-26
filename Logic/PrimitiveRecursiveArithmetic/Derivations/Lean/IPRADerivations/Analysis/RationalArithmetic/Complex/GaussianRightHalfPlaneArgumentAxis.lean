import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRightHalfPlaneArgument
import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentExtensionAxis
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder
import IPRADerivations.Analysis.Names.ImaginaryParts.GaussianImaginaryNameConjugation

/-!
# Exact axis and real-axis value of the right half-plane argument

The right half-plane argument has exactly imaginary observations. On
the positive real axis it has the same observations as the zero name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentAxis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentExponentialPrefix (prefixValue prefix_zero at_pi_observation)
open GaussianArctangentExtensionAxis (prefix_axis_at)
open GaussianArctangentPartialQuadrature (mesh clearing)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianImaginaryNameConjugation (imaginarySamples)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalMetric (qnegative qsub)
open GaussianRightHalfPlaneArgument
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr multiply_congr negative_congr)
open RationalGaussianEmbedding (embed scalarZero scalar_zero_represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem zero_guard : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (scalarZero : PTm n) :=
  RationalNormalForm.normalize_well_formed _ _ (le_refl one)

private theorem add_zero_zero : Γ ⊢[PRAAx] add (scalarZero : PTm n) scalarZero ≐ scalarZero := by
  have e := RationalRepresentations.represents_add (Γ := Γ) scalarZero scalarZero _ _ one one
    (scalar_zero_represents one) (scalar_zero_represents one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.add_guard _ _) zero_guard e (scalar_zero_represents one)
    (GaussianRationalHorner.positive_product _ _ (le_refl one) (le_refl one)) (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,Q.mk_zero,map_zero]

private theorem mul_zero_right (r : PTm n) : Γ ⊢[PRAAx] multiply r scalarZero ≐ scalarZero := by
  let D := RationalSupMetric.denominatorOf r
  have hd := RationalArgmin.denominator_positive (Γ := Γ) r
  have e := RationalRepresentations.represents_multiply (Γ := Γ) r scalarZero _ _ D one
    (RationalRepresentations.represents_self r) (scalar_zero_represents one)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.multiply_guard _ _) zero_guard e (scalar_zero_represents one)
    (GaussianRationalHorner.positive_product _ _ hd (le_refl one)) (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_zero,map_zero]

private theorem mul_zero_left (r : PTm n) : Γ ⊢[PRAAx] multiply scalarZero r ≐ scalarZero :=
  (RationalAlgebra.multiply_commutative _ _).eqTrans (mul_zero_right r)

private theorem negative_zero : Γ ⊢[PRAAx] negative (scalarZero : PTm n) ≐ scalarZero :=
  (RationalAlgebra.negative_minus_multiply scalarZero).eqTrans (mul_zero_right _)

private theorem add_axis (q r : PTm n) (hq : Γ ⊢[PRAAx] fstT q ≐ scalarZero)
    (hr : Γ ⊢[PRAAx] fstT r ≐ scalarZero) : Γ ⊢[PRAAx] fstT (qadd q r) ≐ scalarZero :=
  (fst_pair _ _).eqTrans ((add_congr hq hr).eqTrans add_zero_zero)

private theorem neg_axis (q : PTm n) (hq : Γ ⊢[PRAAx] fstT q ≐ scalarZero) :
    Γ ⊢[PRAAx] fstT (qnegative q) ≐ scalarZero :=
  (fst_pair _ _).eqTrans ((negative_congr hq).eqTrans negative_zero)

private theorem conjugate_axis (q : PTm n) (hq : Γ ⊢[PRAAx] fstT q ≐ scalarZero) :
    Γ ⊢[PRAAx] fstT (GaussianRationalConjugation.point q) ≐ scalarZero :=
  add_axis qzero _ ((congrFst (prefix_zero zero zero)).eqSymm.eqTrans (prefix_axis_at zero zero zero))
    ((fst_pair _ _).eqTrans hq)

private theorem half_axis : Γ ⊢[PRAAx] sndT (GaussianRightHalfPlaneArgument.half : PTm n) ≐ scalarZero := by
  let w := ComplexLogarithmRemainder.oneCode (n := n)
  have h : Γ ⊢[PRAAx] ZT.eq (ComplexLogarithmRemainder.im w) (ZT.ofNat zero) := by
    apply ZT.derive
    simpa [w,ZT.toZ_ofNat,Q.mk_zero,map_zero] using (GaussianRootAlgebra.im_one (Γ := Γ))
  have d : Γ ⊢[PRAAx] le one two := le_succ_self one
  have e := GaussianRationalHorner.scalar_congr (.eqRefl _) h (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (Γ := Γ) w two d).andE₂
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (GaussianRationalHorner.ofGaussian_canonical w two d).andE₂.andE₂ zero_guard e
    (scalar_zero_represents one) d (le_refl one)
  apply ZT.derive
  simp [ZT.toZ_ofNat,ZT.toZ_mul,Q.mk_zero,map_zero]

theorem small_axis (p A B : PTm n) :
    Γ ⊢[PRAAx] fstT (ap2 smallF p (smallData A B)) ≐ scalarZero := by
  let atanF := GaussianArctangentPartialQuadrature.nameF
  let x := GaussianArctangentPartialQuadrature.data B A
  let j := GaussianBoundedConstantProductName.clock p one
  let M := A*mesh j
  let K := B*mesh j
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ) atanF p one GaussianRightHalfPlaneArgument.half x
  have h := (congrFst (GaussianArctangentPartialQuadrature.sample_at (Γ := Γ) j B A)).eqTrans
    (prefix_axis_at K M (clearing M))
  exact (congrFst e).eqTrans ((fst_pair _ _).eqTrans
    ((add_congr ((multiply_congr (.eqRefl _) h).eqTrans (mul_zero_right _))
      ((negative_congr ((multiply_congr half_axis (.eqRefl _)).eqTrans (mul_zero_left _))).eqTrans negative_zero)
      ).eqTrans add_zero_zero))

theorem large_axis (p A B : PTm n) :
    Γ ⊢[PRAAx] fstT (ap2 largeF p (largeData A B)) ≐ scalarZero := by
  let x := smallData B A
  let j := GaussianFastValueCut.exponent two p
  let k := GaussianFastValueCut.exponent (one+one) j
  let M := GaussianGammaHalfPiName.meshAt j
  let L := GaussianGammaHalfPiName.clearing j
  have quarter := (congrFst ((GaussianArctangentQuarterExponential.sample_at (Γ := Γ) j zero).eqTrans
    (at_pi_observation j zero).eqSymm)).eqTrans (prefix_axis_at M M L)
  have z := (congrFst (prefix_zero (Γ := Γ) zero zero)).eqSymm.eqTrans (prefix_axis_at zero zero zero)
  have sub := add_axis qzero (qnegative (ap2 smallF k x)) z (neg_axis _ (small_axis k B A))
  have e := (GaussianNameRingLaws.negative_at (Γ := Γ) smallF x j).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))
  have neg := (congrFst e).eqTrans sub
  exact (congrFst (GaussianExponentialReference.add_sample quarterF (negativeF smallF) zero (negativeData x) p)).eqTrans
    (add_axis _ _ quarter neg)

theorem unsigned_axis (p A B : PTm n) :
    Γ ⊢[PRAAx] fstT (ap2 unsignedF p (unsignedData A B)) ≐ scalarZero := by
  have e := GaussianNameBranch.sample_at (Γ := Γ) smallF largeF p
    (wide A B) (smallData A B) (largeData A B)
  refine .orE (lt_or_le A B) ?_ ?_
  · have branch := e.wk.eqTrans (RationalArithmetic.select_one _ _ _ (wide_one A B Prf.hyp0))
    exact (congrFst branch).eqTrans (large_axis p A B)
  · have branch := e.wk.eqTrans (RationalArithmetic.select_zero _ _ _ (wide_zero A B Prf.hyp0))
    exact (congrFst branch).eqTrans (small_axis p A B)

theorem phase_axis (p A B neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] fstT (ap2 nameF p (data A B neg)) ≐ scalarZero := by
  have e := GaussianNameBranch.sample_at (Γ := Γ) unsignedF (GaussianNameConjugation.nameF unsignedF) p neg
    (unsignedData A B) (unsignedData A B)
  refine .orE h ?_ ?_
  · have branch := e.wk.eqTrans (RationalArithmetic.select_zero _ _ _ Prf.hyp0)
    exact (congrFst branch).eqTrans (unsigned_axis p A B)
  · have branch := e.wk.eqTrans (RationalArithmetic.select_one _ _ _ Prf.hyp0)
    exact (congrFst (branch.eqTrans (GaussianNameConjugation.sample_at _ _ _))).eqTrans
      (conjugate_axis _ (unsigned_axis p A B))

theorem imaginary_samples (A B neg : PTm n) (h : Γ ⊢[PRAAx] source A neg) :
    Γ ⊢[PRAAx] imaginarySamples nameF (data A B neg) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift A) (Syn.shift neg) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [imaginarySamples, subst_data,Syn.shift] using
    phase_axis (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift neg) hs.andE₂

private theorem small_zero (p A : PTm n) : Γ ⊢[PRAAx] ap2 smallF p (smallData A zero) ≐ qzero := by
  let atanF := GaussianArctangentPartialQuadrature.nameF
  let x := GaussianArctangentPartialQuadrature.data zero A
  let j := GaussianBoundedConstantProductName.clock p one
  let M := A*mesh j
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ) atanF p one GaussianRightHalfPlaneArgument.half x
  have index : Γ ⊢[PRAAx] prefixValue (zero*mesh j) M (clearing M) ≐ prefixValue zero M (clearing M) := by
    simpa only [GaussianArctangentExponentialPrefix.subst_prefixValue,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (prefixValue (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![zero*mesh j,M,clearing M]) (σ' := ![zero,M,clearing M]) (fun i => by
          fin_cases i
          exact zero_mul _
          exact .eqRefl _
          exact .eqRefl _))
  have h := (GaussianArctangentPartialQuadrature.sample_at (Γ := Γ) j zero A).eqTrans
    (index.eqTrans (prefix_zero M (clearing M)))
  exact e.eqTrans ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) h).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _))

private theorem unsigned_zero (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] crossEquivalent unsignedF GaussianNameRingLaws.zeroF
      (unsignedData A zero) (unsignedData A zero) := by
  apply cross_trans _ _ _ _ _ _ (unsigned_small A zero hA (zero_le A))
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (small_regular _ _ hA (zero_le A)) (GaussianNameRingLaws.zero_fast _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,subst_smallData,subst_unsignedData,
    ConciseIPRA.PTm.subst_zero] using
    (small_zero (var 0) (Syn.shift A)).eqTrans
      (GaussianNameRingLaws.zero_at (var 0) (unsignedData (Syn.shift A) zero)).eqSymm

theorem zero_axis_cross (A neg : PTm n) (h : Γ ⊢[PRAAx] source A neg) :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianNameRingLaws.zeroF (data A zero neg) (unsignedData A zero) := by
  have u := unsigned_zero A h.andE₁
  refine .orE h.andE₂ ?_ ?_
  · exact cross_trans _ _ _ _ _ _ (positive_sign A zero neg h.andE₁.wk Prf.hyp0) u.wk
  · apply cross_trans _ _ _ _ _ _ (negative_sign A zero neg h.andE₁.wk Prf.hyp0)
    apply cross_trans _ _ _ _ _ _ (GaussianNameConjugation.conjugate_cross _ _ _ _ u.wk)
    apply GaussianNameConjugation.equal_samples_cross _ _ _ _
      (GaussianNameConjugation.regular _ _ (GaussianNameRingLaws.zero_fast _)) (GaussianNameRingLaws.zero_fast _)
    refine .allI ?_
    let x := Syn.shift (unsignedData A zero)
    let p : PTm (n+1) := var 0
    exact (GaussianNameConjugation.sample_at _ p x).eqTrans
      ((GaussianRationalConjugation.point_congr (GaussianNameRingLaws.zero_at p x)).eqTrans
        (GaussianRationalConjugation.point_zero.eqTrans (GaussianNameRingLaws.zero_at p x).eqSymm))

theorem actual_right_half_plane_argument_axes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 2) ⟶ imaginarySamples nameF (data (var 0) (var 1) (var 2)) ⋏
      crossEquivalent nameF GaussianNameRingLaws.zeroF (data (var 0) zero (var 2)) (unsignedData (var 0) zero)) :=
  closeUniv 3 (.impI (.andI (imaginary_samples _ _ _ Prf.hyp0) (zero_axis_cross _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentAxis
