import IPRADerivations.Analysis.Exponential.GaussianExponentialLinearRemainder
import IPRADerivations.Analysis.Exponential.GaussianPositiveExponentialTermBound
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# A rational nonnegative majorant for the Gaussian exponential

A positive real rational argument is a sharp Euclidean majorant for
the literal finite Taylor sums on its closed disk. The real radius
is retained as an arbitrary rational code throughout the proof.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalExponentialMagnitude

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianPositiveRealArithmetic (positive numerator natural_representation)
open GaussianRationalHorner (canonical qadd qmul scalar_congr positive_product)
open GaussianRationalMetric (bounded comparison_to_cleared qnegative)
open GaussianRationalReciprocal (power bound_congr bounded_product bounded_sum)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalPolynomialExponential (scalarSum inverseFactorial factorial_positive)
open RationalSupMetric (denominatorOf)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def majorized (q r : PTm n) : Fm PTm n := bounded q (numerator (fstT r)) (denominatorOf (fstT r))

@[simp] theorem subst_majorized {l : ℕ} (σ : Fin n → PTm l) (q r : PTm n) :
    (majorized q r).subst σ = majorized (Syn.subst σ q) (Syn.subst σ r) := by
  simp [majorized,numerator,RationalSupMetric.numeratorOf]

theorem congr {q q' r r' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ q') (hr : Γ ⊢[PRAAx] r ≐ r')
    (h : Γ ⊢[PRAAx] majorized q r) : Γ ⊢[PRAAx] majorized q' r' := by
  simpa only [subst_majorized,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqSubst (majorized (var 0) (var 1) : Fm PTm 2) ![q,r] ![q',r']
      (fun i => by fin_cases i; exact hq; exact hr) (by simpa only [subst_majorized,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h)

theorem of_representation (q r A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hr : Γ ⊢[PRAAx] positive r)
    (hRep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT r) (ZT.ofNat A) B)
    (h : Γ ⊢[PRAAx] bounded q A B) : Γ ⊢[PRAAx] majorized q r :=
  bounded_radius_mono _ _ _ _ _ hB (RationalArgmin.denominator_positive _) (le_congr (mul_comm _ _) (.eqRefl _)
    (comparison_to_cleared _ _ _ _ _ _ hRep (natural_representation _ hr.andE₂) (RationalArgmin.reflexive _))) h

/-- The usual Euclidean norm bound resulting from any upper rational
estimate on the actual positive majorant. -/
theorem bound_by (q r b C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] positive r) (h : Γ ⊢[PRAAx] majorized q r)
    (hRep : Γ ⊢[PRAAx] RationalArithmetic.represents b (ZT.ofNat C) D)
    (hLE : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT r) b) :
    Γ ⊢[PRAAx] bounded q C D :=
  bounded_radius_mono _ _ _ _ _ (RationalArgmin.denominator_positive _) hD
    (le_congr (mul_comm _ _) (.eqRefl _)
      (comparison_to_cleared _ _ _ _ _ _ (natural_representation _ hr.andE₂) hRep hLE)) h

theorem weaken (q r s : PTm n) (hr : Γ ⊢[PRAAx] positive r) (hs : Γ ⊢[PRAAx] positive s)
    (h : Γ ⊢[PRAAx] majorized q r)
    (hLE : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT r) (fstT s)) : Γ ⊢[PRAAx] majorized q s :=
  bound_by q r (fstT s) _ _ (RationalArgmin.denominator_positive _) hr h
    (natural_representation _ hs.andE₂) hLE

private theorem positive_representation (r : PTm n) (hr : Γ ⊢[PRAAx] positive r)
    (hc : Γ ⊢[PRAAx] canonical r) : Γ ⊢[PRAAx] GaussianRationalHorner.represents r
      (GaussianDominantPairAlgebra.radiusNumerator (numerator (fstT r))) (denominatorOf (fstT r)) := by
  have fixed : Γ ⊢[PRAAx] GaussianTranslatedNonconstant.recode r ≐ r :=
    GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianTranslatedNonconstant.recode_canonical _) hc
      (GaussianRationalL1.raw_den_positive _) (GaussianTranslatedNonconstant.recode_represents _) (GaussianRationalL1.raw_represents _)
  have eq := fixed.eqSymm.eqTrans (RationalGaussianEmbedding.axis_roundtrip r hr.andE₁)
  exact GaussianRationalHorner.represents_congr eq.eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (natural_representation _ hr.andE₂))

theorem positive_self (r : PTm n) (hr : Γ ⊢[PRAAx] positive r) (hc : Γ ⊢[PRAAx] canonical r) :
    Γ ⊢[PRAAx] majorized r r := by
  have hD := RationalArgmin.denominator_positive (Γ := Γ) (fstT r)
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hD hD (positive_representation r hr hc)
  exact le_congr ((congrMul (.eqRefl _) (GaussianDominantPairAlgebra.radius_numerator_norm _)).eqTrans (by ipra_ring)).eqSymm
    (.eqRefl _) (le_refl _)

theorem negative_majorized (q r : PTm n) (h : Γ ⊢[PRAAx] majorized q r) : Γ ⊢[PRAAx] majorized (qnegative q) r :=
  GaussianRationalReciprocal.bounded_negative _ _ _ (RationalArgmin.denominator_positive _) h

theorem bound_from_majorant_norm (q r C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] positive r) (hc : Γ ⊢[PRAAx] canonical r) (hq : Γ ⊢[PRAAx] majorized q r)
    (hR : Γ ⊢[PRAAx] bounded r C D) : Γ ⊢[PRAAx] bounded q C D := by
  have hB := RationalArgmin.denominator_positive (Γ := Γ) (fstT r)
  have clear := GaussianRationalMetric.bounded_to_cleared _ _ _ _ _ hB hD (positive_representation r hr hc) hR
  apply bounded_radius_mono _ _ _ _ _ hB hD _ hq
  apply DiophantineNumberTheory.Coprime.le_of_sq_le
  exact le_congr ((congrMul (.eqRefl _) (GaussianDominantPairAlgebra.radius_numerator_norm _)).eqTrans (by ipra_ring))
    (by ipra_ring) clear

theorem add (q r u v : PTm n) (hu : Γ ⊢[PRAAx] positive u) (hv : Γ ⊢[PRAAx] positive v)
    (hq : Γ ⊢[PRAAx] majorized q u) (hr : Γ ⊢[PRAAx] majorized r v) : Γ ⊢[PRAAx]
    majorized (qadd q r) (qadd u v) := by
  let a := fstT u
  let b := fstT v
  let A := numerator a
  let C := numerator b
  let B := denominatorOf a
  let D := denominatorOf b
  have bpos : Γ ⊢[PRAAx] le one B := RationalArgmin.denominator_positive a
  have dpos : Γ ⊢[PRAAx] le one D := RationalArgmin.denominator_positive b
  have repr := RationalRepresentations.represents_add a b _ _ B D
    (natural_representation a hu.andE₂) (natural_representation b hv.andE₂)
  have lifted := RationalGaussianEmbedding.scalar_recode_represents _ _ _ repr
  have read := (congrFst (RationalGaussianEmbedding.axis_add_representation u v hu.andE₁ hv.andE₁)).eqTrans (fst_pair _ _)
  apply of_representation _ _ (A*D+C*B) (B*D) (positive_product _ _ bpos dpos)
    (GaussianPositiveRealArithmetic.positive_add u v hu hv) _ (bounded_sum _ _ _ _ _ _ bpos dpos hq hr)
  apply scalar_congr read.eqSymm _ (.eqRefl _) lifted
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,Q.mk_mul,map_add,map_mul]
  ring

theorem multiply (q r u v : PTm n) (hu : Γ ⊢[PRAAx] positive u) (hv : Γ ⊢[PRAAx] positive v)
    (hq : Γ ⊢[PRAAx] majorized q u) (hr : Γ ⊢[PRAAx] majorized r v) : Γ ⊢[PRAAx]
    majorized (qmul q r) (qmul u v) := by
  let a := fstT u
  let b := fstT v
  let A := numerator a
  let C := numerator b
  let B := denominatorOf a
  let D := denominatorOf b
  have bpos : Γ ⊢[PRAAx] le one B := RationalArgmin.denominator_positive a
  have dpos : Γ ⊢[PRAAx] le one D := RationalArgmin.denominator_positive b
  have repr := RationalRepresentations.represents_multiply a b _ _ B D
    (natural_representation a hu.andE₂) (natural_representation b hv.andE₂)
  have lifted := RationalGaussianEmbedding.scalar_recode_represents _ _ _ repr
  have read := (congrFst (RationalGaussianEmbedding.axis_multiply_representation u v hu.andE₁ hv.andE₁)).eqTrans (fst_pair _ _)
  apply of_representation _ _ (A*C) (B*D) (positive_product _ _ bpos dpos)
    (GaussianPositiveRealArithmetic.positive_multiply u v hu hv) _ (bounded_product _ _ _ _ _ _ bpos dpos hq hr)
  apply scalar_congr read.eqSymm _ (.eqRefl _) lifted
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  rfl

theorem one_majorized : Γ ⊢[PRAAx] majorized (qone : PTm n) qone := by
  apply of_representation _ _ one one (le_refl _) GaussianPositiveRealArithmetic.positive_one _ GaussianRationalReciprocal.qone_bounded
  apply scalar_congr (.eqRefl _) _ (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents ComplexLogarithmRemainder.oneCode one (le_refl one)).andE₁
  apply ZT.derive
  simp only [GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem power_majorized (q r K : PTm n) (hr : Γ ⊢[PRAAx] positive r) (h : Γ ⊢[PRAAx] majorized q r) :
    Γ ⊢[PRAAx] majorized (power q K) (power r K) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift r) := by simpa [Fm.shift,Syn.shift] using hr.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] majorized (Syn.shift q) (Syn.shift r) := by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (majorized (power (Syn.shift q) (var 0)) (power (Syn.shift r) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_majorized,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        congr (GaussianRationalReciprocal.power_zero q).eqSymm (GaussianRationalReciprocal.power_zero r).eqSymm one_majorized
    · simp only [subst_majorized,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact congr (GaussianRationalReciprocal.power_succ _ _).eqSymm (GaussianRationalReciprocal.power_succ _ _).eqSymm
        (multiply _ _ _ _ (GaussianPositiveRealArithmetic.positive_power _ _ hs.wk) hs.wk Prf.hyp0 hm.wk)
  simpa only [subst_majorized,GaussianRationalReciprocal.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

theorem inverse_factorial_majorized (j : PTm n) : Γ ⊢[PRAAx] majorized (inverseFactorial j) (inverseFactorial j) := by
  have hj := factorial_positive (Γ := Γ) j
  have hB : Γ ⊢[PRAAx] bounded (inverseFactorial j) one (fact j) :=
    GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ hj
      (RationalArgmin.rationalLE_congr (GaussianFiniteExponentialWeightedNorm.inverse_factorial_norm _).eqSymm
        (.eqRefl _) (RationalArgmin.reflexive _))
  apply of_representation _ _ one (fact j) hj (GaussianPositiveRealArithmetic.positive_inverse_factorial j) _ hB
  apply scalar_congr (.eqRefl _) _ (.eqRefl _) (GaussianRationalPolynomialExponential.inverse_factorial_represents j).andE₁
  apply ZT.derive
  simp only [GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem scalar_sum_majorized (q r K : PTm n) (hr : Γ ⊢[PRAAx] positive r)
    (h : Γ ⊢[PRAAx] majorized q r) : Γ ⊢[PRAAx] majorized (scalarSum q K) (scalarSum r K) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift r) := by simpa [Fm.shift,Syn.shift] using hr.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] majorized (Syn.shift q) (Syn.shift r) := by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (majorized (scalarSum (Syn.shift q) (var 0)) (scalarSum (Syn.shift r) (var 0))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_majorized,GaussianRationalPolynomialExponential.subst_scalarSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        congr (GaussianRationalPolynomialExponential.scalar_sum_zero q).eqSymm
          (GaussianRationalPolynomialExponential.scalar_sum_zero r).eqSymm one_majorized
    · simp only [subst_majorized,GaussianRationalPolynomialExponential.subst_scalarSum,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let u := Syn.shift q
      let v := Syn.shift r
      let j : PTm (n+1) := var 0
      let Δ := majorized (scalarSum u j) (scalarSum v j) :: Γ.map Fm.shift
      have hv : Δ ⊢[PRAAx] positive v := hs.wk
      have hvu : Δ ⊢[PRAAx] majorized u v := hm.wk
      have p := GaussianPositiveExponentialTermBound.positive_prefix v (succ j) hv
      have pow := GaussianPositiveRealArithmetic.positive_power v (succ j) hv
      have inv := GaussianPositiveRealArithmetic.positive_inverse_factorial (Γ := Δ) (succ j)
      have mon := multiply _ _ _ _ inv pow (inverse_factorial_majorized (succ j))
        (power_majorized u v (succ j) hv hvu)
      exact congr (GaussianRationalPolynomialExponential.scalar_sum_succ u j).eqSymm
        (GaussianRationalPolynomialExponential.scalar_sum_succ v j).eqSymm
        (add _ _ _ _ p (GaussianPositiveRealArithmetic.positive_multiply _ _ inv pow) Prf.hyp0 mon)
  simpa only [subst_majorized,GaussianRationalPolynomialExponential.subst_scalarSum,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

end LeanProofs.IPRA.Analysis.GaussianRationalExponentialMagnitude
