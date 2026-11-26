import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorMass
import IPRADerivations.Analysis.Inequalities.WeightedComparison.GaussianWeightedErrorBudget
import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialDilation
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerExpansion
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# An order-independent weighted mass for the stored Barnes exponent

At radius one quarter the stored coefficients of degree (e \\geq 1)
are bounded in weighted L1 norm by a common cap divided by (2^e).
The descending prefix telescopes and the constant coefficient vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorWeightedMass

open_ipra
open GaussianBarnesCanonicalExponentTaylorBuffer
  (buffer coefficient descending_at coefficient_index_congr positive_degree_cases
    coefficient_zero coefficient_one coefficient_two coefficient_high)
open GaussianBarnesCanonicalExponentTaylorMass
  (linearCap squareCap stirlingCap halfCap quadraticCap linear_bound quadratic_bound higher_bound)
open GaussianBarnesCanonicalHigherRows (previous degree)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientL1 (prefixNorm prefix_zero prefix_succ qL1_congr)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalL1 (qL1)
open GaussianRationalMetric (bounded)
open GaussianRationalPolynomialDilation (dilated weightedNorm dilated_length dilated_lookup subst_dilated)
open GaussianRationalReciprocal (power bounded_power bounded_product bound_congr)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianRationalSyntheticDivision (qmul_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point : PTm n := radiusPoint one (num 4)
def massCap (R : PTm n) : PTm n := linearCap R+squareCap R+two

@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (point : PTm n) = (point : PTm m) := by simp [point]

@[simp] theorem subst_massCap {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (massCap R) = massCap (Syn.subst σ R) := by
  simp [massCap,linearCap,squareCap,stirlingCap,halfCap,quadraticCap,
    GaussianBarnesCanonicalPrefactor.negativeHalf,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,one,two]

private def majorant (C e : PTm n) : PTm n := fraction C (pw two e)

@[simp] private theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (C e : PTm n) :
    Syn.subst σ (majorant C e) = majorant (Syn.subst σ C) (Syn.subst σ e) := by simp [majorant]

private theorem two_positive : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
private theorem dyadic_positive (e : PTm n) : Γ ⊢[PRAAx] le one (pw two e) :=
  GaussianFactorBudget.power_positive _ _ two_positive
private theorem four_positive : Γ ⊢[PRAAx] le one (num 4 : PTm n) :=
  le_of_eq_add (d := num 3) (by ipra_ring)

private theorem four_power (e : PTm n) : Γ ⊢[PRAAx] pw (num 4) e ≐ pw two e*pw two e :=
  (congrAp2 powF (.eqRefl _) (show Γ ⊢[PRAAx] num 4 ≐ two*two by ipra_ring)).eqTrans
    (AnalyticNumberTheory.LocalFactor.pw_mul_base two two e)

private theorem scaled_entry (a A e C : PTm n) (ha : Γ ⊢[PRAAx] bounded a A one)
    (hc : Γ ⊢[PRAAx] le (two*A) (C*pw two e)) :
    Γ ⊢[PRAAx] rationalLE (qL1 (qmul a (power point e))) (majorant C e) := by
  let D := pw (num 4) e
  have hD : Γ ⊢[PRAAx] le one D := GaussianFactorBudget.power_positive _ _ four_positive
  have hw : Γ ⊢[PRAAx] bounded (power point e) one D :=
    bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power e) (.eqRefl _)
      (bounded_power _ _ _ _ four_positive (radius_bounded one (num 4) four_positive))
  have hs := bounded_product a (power point e) A one one D (le_refl one) hD ha hw
  have hq : Γ ⊢[PRAAx] bounded (qmul a (power point e)) A D :=
    bound_congr (.eqRefl _) (by ipra_ring) (one_mul D) hs
  have hqL := GaussianRationalL1Algebra.qL1_of_bounded _ _ _ hD hq
  have heq : Γ ⊢[PRAAx] (C*pw two e)*pw two e ≐ C*D :=
    (mul_assoc _ _ _).eqTrans (congrMul (.eqRefl C) (four_power e).eqSymm)
  have cmp : Γ ⊢[PRAAx] le (pw two e*(two*A)) (C*D) :=
    le_congr (mul_comm _ _) heq (mul_le_mul_right (pw two e) hc)
  exact RationalArgmin.transitive hqL (fraction_order _ _ _ _ hD (dyadic_positive e) cmp)

private theorem low_budget (A R e : PTm n) (he : Γ ⊢[PRAAx] le one e)
    (ha : Γ ⊢[PRAAx] le A (massCap R)) : Γ ⊢[PRAAx] le (two*A) (massCap R*pw two e) := by
  have ht : Γ ⊢[PRAAx] le two (pw two e) :=
    le_congr (pw_one two) (.eqRefl _) (GaussianFactorBudget.power_monotone_length two one e two_positive he)
  exact le_congr (mul_comm _ _) (.eqRefl _) (Common.mul_le_mul ha ht)

private theorem coefficient_bound (q z R B r e : PTm n) (hs : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le one e) :
    Γ ⊢[PRAAx] rationalLE (qL1 (qmul (coefficient q z R B r e) (power point e))) (majorant (massCap R) e) := by
  let c := coefficient q z R B r e
  let C := massCap R
  have l : Γ ⊢[PRAAx] le (linearCap R) C := le_trans (le_add_right _ _) (le_add_right _ _)
  have s : Γ ⊢[PRAAx] le (squareCap R) C := le_trans (le_add_left _ _) (le_add_right _ _)
  have t : Γ ⊢[PRAAx] le two C := le_add_left _ _
  refine positive_degree_cases e he ?_ ?_ ?_
  · have rd := (coefficient_index_congr (Γ := (e ≐ one) :: Γ) q z R B r Prf.hyp0).eqTrans
      (coefficient_one q z R B r)
    exact scaled_entry c (linearCap R) e C
      (bound_congr rd.eqSymm (.eqRefl _) (.eqRefl _) (linear_bound q z R B r hs.wk))
      (low_budget (linearCap R) R e he.wk l.wk)
  · have rd := (coefficient_index_congr (Γ := (e ≐ two) :: Γ) q z R B r Prf.hyp0).eqTrans
      (coefficient_two q z R B r)
    exact scaled_entry c (squareCap R) e C
      (bound_congr rd.eqSymm (.eqRefl _) (.eqRefl _) (quadratic_bound q z R B r hs.wk))
      (low_budget (squareCap R) R e he.wk s.wk)
  · let j := monus e (num 3)
    have eq : (e ≐ degree j) :: Γ ⊢[PRAAx] e ≐ degree j := Prf.hyp0
    have rd := (coefficient_index_congr q z R B r eq).eqTrans (coefficient_high q z R B r j)
    have p := congrAp2 powF eq.eqSymm (.eqRefl two)
    exact scaled_entry c (pw two e) e C
      (bound_congr rd.eqSymm p (.eqRefl _) (higher_bound z R B r j hs.wk))
      (mul_le_mul_right (pw two e) t.wk)

private theorem majorant_step (C e : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.add (majorant C (succ e)) (majorant C (succ e)) ≐ majorant C e := by
  let P := pw two e
  let Q := pw two (succ e)
  have hP := dyadic_positive (Γ := Γ) e
  have hQ := dyadic_positive (Γ := Γ) (succ e)
  have raw : Γ ⊢[PRAAx] RationalArithmetic.add (majorant C (succ e)) (majorant C (succ e)) ≐ fraction (C+C) Q :=
    GaussianWeightedErrorBudget.frac_add _ _ _ hQ
  refine raw.eqTrans ?_
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hQ) (RationalNormalForm.normalize_well_formed _ _ hP)
    (fraction_represents _ _ hQ) (fraction_represents _ _ hP) hQ hP
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [natEq (pw_succ (Γ := Γ) two e)]
  ipra_simps
  ring

private def entryLaw (C d A i : PTm n) : Fm PTm n :=
  lt i d ⟶ rationalLE (qL1 (entry C i)) (majorant A (monus d i))

@[simp] private theorem subst_entryLaw {m : ℕ} (σ : Fin n → PTm m) (C d A i : PTm n) :
    (entryLaw C d A i).subst σ = entryLaw (Syn.subst σ C) (Syn.subst σ d) (Syn.subst σ A) (Syn.subst σ i) := by
  simp [entryLaw]

private def prefixLaw (C d A i : PTm n) : Fm PTm n :=
  le i d ⟶ rationalLE (prefixNorm C i) (majorant A (monus d i))

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (C d A i : PTm n) :
    (prefixLaw C d A i).subst σ = prefixLaw (Syn.subst σ C) (Syn.subst σ d) (Syn.subst σ A) (Syn.subst σ i) := by
  simp [prefixLaw]

private theorem entry_at (C d A i : PTm n)
    (h : Γ ⊢[PRAAx] .all (entryLaw (Syn.shift C) (Syn.shift d) (Syn.shift A) (var 0))) :
    Γ ⊢[PRAAx] entryLaw C d A i := by
  simpa only [subst_entryLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

private theorem prefix_step (C d A i : PTm n) (hi : Γ ⊢[PRAAx] le (succ i) d)
    (h : Γ ⊢[PRAAx] entryLaw C d A i) (ih : Γ ⊢[PRAAx] prefixLaw C d A i) :
    Γ ⊢[PRAAx] rationalLE (prefixNorm C (succ i)) (majorant A (monus d (succ i))) := by
  have old := ih.impE (le_trans (le_succ_self i) hi)
  have leaf := h.impE hi
  have rem : Γ ⊢[PRAAx] monus d i ≐ succ (monus d (succ i)) :=
    (GaussianRationalPowerExpansion.remaining_succ d i).eqSymm.eqTrans
      (GaussianRationalPowerExpansion.remaining_before d (succ i) hi)
  have eq : Γ ⊢[PRAAx] majorant A (monus d i) ≐ majorant A (succ (monus d (succ i))) := by
    ipra_congr (majorant (var 0) (var 1) : PTm 2) with [.eqRefl A,rem]
  exact rationalLE_congr (prefix_succ C i).eqSymm
    ((RationalAlgebra.add_congr eq eq).eqTrans (majorant_step A (monus d (succ i))))
    (add_monotone _ _ _ _ old leaf)

private theorem prefix_bound (C d A : PTm n)
    (entries : Γ ⊢[PRAAx] .all (entryLaw (Syn.shift C) (Syn.shift d) (Syn.shift A) (var 0))) :
    Γ ⊢[PRAAx] rationalLE (prefixNorm C d) (fraction A one) := by
  have es : Γ.map Fm.shift ⊢[PRAAx] .all
      (entryLaw (Syn.shift (Syn.shift C)) (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift A)) (var 0)) := by
    have e := entries.shift
    simp only [Fm.shift,Fm.subst_all,subst_entryLaw,Syn.subst_var,
      AnalyticNumberTheory.Fermat.subst_up_shift',Syn.up_zero] at e
    simpa only [Syn.shift] using e
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift d) (Syn.shift A) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      refine .impI ?_
      exact rationalLE_congr ((prefix_zero C).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm).eqSymm
        (.eqRefl _)
        (fraction_order zero one A (pw two (monus d zero)) (le_refl _) (dyadic_positive _)
          (le_congr (mul_zero _).eqSymm (.eqRefl _) (zero_le (A*one))))
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact .impI (prefix_step _ _ _ _ Prf.hyp0 (entry_at _ _ _ _ es.wk.wk) Prf.hyp1)
  have atD : Γ ⊢[PRAAx] prefixLaw C d A d := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE d
  have eq : Γ ⊢[PRAAx] majorant A (monus d d) ≐ fraction A one :=
    RationalNonnegativePowers.fraction_congr (.eqRefl _)
      ((congrAp2 powF (monus_self d) (.eqRefl _)).eqTrans (pw_zero _))
  exact rationalLE_congr (.eqRefl _) eq (atD.impE (le_refl d))

private theorem stored_entry (q z R B r M i : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] entryLaw (dilated (buffer q z R B r M) (previous M) point) (previous M) (massCap R) i := by
  refine .impI ?_
  let d := previous M
  let e := monus d i
  have hi : (lt i d :: Γ) ⊢[PRAAx] le i d := le_trans (le_succ_self i) Prf.hyp0
  have he : (lt i d :: Γ) ⊢[PRAAx] le one e := by
    have eq := (GaussianRationalPowerExpansion.remaining_succ (Γ := lt i d :: Γ) d i).eqSymm.eqTrans
      (GaussianRationalPowerExpansion.remaining_before d (succ i) Prf.hyp0)
    exact le_congr (.eqRefl _) eq.eqSymm (zero_lt_succ _)
  have rd := (dilated_lookup (buffer q z R B r M) d point i hi).eqTrans
    (qmul_congr (descending_at q z R B r M i hi) (.eqRefl _))
  exact rationalLE_congr (qL1_congr rd).eqSymm (.eqRefl _) (coefficient_bound q z R B r e hs.wk he)

theorem mass (q z R B r M : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (buffer q z R B r M) (previous M) point) (fraction (massCap R) one) := by
  let D := previous M
  let C := buffer q z R B r M
  let W := dilated C D point
  let sh (u : PTm n) := Syn.shift u
  have entries : Γ ⊢[PRAAx] .all (entryLaw (sh W) (sh D) (sh (massCap R)) (var 0)) := by
    refine .allI ?_
    have hz : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
      simpa [Fm.shift,sh,Syn.shift] using hs.shift
    simpa only [sh,Syn.shift,W,C,D,subst_dilated,GaussianBarnesCanonicalExponentTaylorBuffer.subst_buffer,
      GaussianBarnesCanonicalHigherRows.subst_previous,subst_point,subst_massCap] using
      stored_entry (sh q) (sh z) (sh R) (sh B) (sh r) (sh M) (var 0) hz
  have coeffZero := (coefficient_index_congr (Γ := Γ) q z R B r (monus_self D)).eqTrans (coefficient_zero q z R B r)
  have qZero := (dilated_lookup C D point D (le_refl D)).eqTrans
    ((qmul_congr (descending_at q z R B r M D (le_refl D)) (.eqRefl _)).eqTrans
      ((qmul_congr coeffZero (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_left _)))
  have normZero := (qL1_congr qZero).eqTrans GaussianRationalLinearProduct.qzero_norm
  have drop : Γ ⊢[PRAAx] weightedNorm C D point ≐ prefixNorm W D :=
    (GaussianRationalLinearProduct.norm_length W _ (dilated_length C D point)).eqTrans
      ((prefix_succ W D).eqTrans ((RationalAlgebra.add_congr (.eqRefl _) normZero).eqTrans
        (GaussianRationalLinearProduct.scalar_add_zero _ (RationalFiniteSum.sum_well_formed _ _ _))))
  exact rationalLE_congr drop.eqSymm (.eqRefl _) (prefix_bound W D (massCap R) entries)

theorem actual_Barnes_exponent_Taylor_weighted_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) ⟶
      rationalLE (weightedNorm (buffer (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (previous (var 5)) point)
        (fraction (massCap (var 2)) one)) :=
  closeUniv 6 (.impI (mass _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorWeightedMass
