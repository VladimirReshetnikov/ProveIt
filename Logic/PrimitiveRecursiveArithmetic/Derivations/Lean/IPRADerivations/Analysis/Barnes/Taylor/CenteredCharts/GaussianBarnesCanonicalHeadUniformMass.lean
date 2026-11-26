import IPRADerivations.Analysis.Barnes.Logarithms.CofinalTails.GaussianBarnesCanonicalLogCofinal
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalCenteredHead
import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialPowerNormVariation
import IPRADerivations.Analysis.Polynomials.Products.GaussianRationalPolynomialProductTruncation

/-!
# Disk-uniform mass of the original centered Barnes head

Each original linear factor has coefficient mass at most 1 + 2(R + 1).
The actual retained product therefore has a mass budget determined by
its exact stored degree and the center disk radius. The numerical cap
does not use the numerator of the computed rational coefficient norm.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadUniformMass

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCenteredHead (linear factor polynomial polynomial_length polynomial_zero polynomial_succ factor_length)
open GaussianBarnesCanonicalFactor (base base_bound)
open GaussianBarnesCanonicalHeadPolynomial (degree degree_zero degree_succ subst_degree)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial subst_initial)
open GaussianCoefficientL1 (coefficientNorm prefix_monotone qL1_congr subst_coefficientNorm)
open GaussianCoefficientNormOrder (coefficientNorm_congr)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction_order)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianGammaLinearCoefficient (monomial monomial_length)
open GaussianPolynomialDeterminantStageNorm (singleton_norm)
open GaussianPolynomialNormBuffers (norm_added norm_append norm_padding)
open GaussianPositiveExponentialMajorant (natCode_congr)
open GaussianRationalL1 (qL1 qL1_guard qL1_nonnegative)
open GaussianRationalMonicReduction (singleton singleton_length)
open GaussianRationalPolynomialBuffers (leftPad pad_length)
open GaussianRationalPolynomialDilation (dilated dilated_length dilated_lookup subst_dilated weightedNorm)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticBounds (natCode natCode_add subst_natCode)
open GaussianRationalSyntheticDivision (qone)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open RationalArgmin (rationalLE rationalLE_congr subst_rationalLE)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def linearCap (R : PTm n) : PTm n := one+two*(R+one)
def cap (R N : PTm n) : PTm n := pw (linearCap R) (degree N)
def headCap (R : PTm n) : PTm n := cap R (initial R)

@[simp] theorem subst_cap {l : ℕ} (σ : Fin n → PTm l) (R N : PTm n) :
    Syn.subst σ (cap R N) = cap (Syn.subst σ R) (Syn.subst σ N) := by
  simp [cap,linearCap,pw,one,two]

@[simp] theorem subst_headCap {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (headCap R) = headCap (Syn.subst σ R) := by simp only [headCap,subst_cap,subst_initial]

theorem linear_mass (z R B i : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (linear z B i)) (natCode (linearCap R)) := by
  let a := reciprocalPoint i
  let b := base z B (succ i)
  let Q := leftPad (singleton b) one
  have len : Γ ⊢[PRAAx] length Q ≐ two :=
    (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (singleton_length b)).eqTrans (by ipra_ring))
  have aNorm : Γ ⊢[PRAAx] coefficientNorm (monomial a) ≐ qL1 a :=
    (norm_append (singleton a)).eqTrans (singleton_norm a)
  have bNorm : Γ ⊢[PRAAx] coefficientNorm Q ≐ qL1 b :=
    (norm_padding (singleton b) one).eqTrans (singleton_norm b)
  have aBound := rationalLE_congr aNorm.eqSymm (.eqRefl _) (GaussianGammaEulerFactorPolynomial.reciprocal_norm i)
  have bBound := rationalLE_congr bNorm.eqSymm (.eqRefl _)
    (GaussianRationalL1Algebra.qL1_of_bounded b (R+one) one (le_refl one)
      (base_bound z R B (succ i) (.andI hz.andE₁ (.andI (zero_lt_succ i) hz.andE₂))))
  have added := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ aBound bBound
  exact RationalArgmin.transitive (norm_added (monomial a) Q two (monomial_length a) len)
    (rationalLE_congr (.eqRefl _) (natCode_add one (two*(R+one))) added)

private theorem factor_mass (z R B i : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (factor z B i)) (natCode (pw (linearCap R) (succ i))) :=
  GaussianPolynomialPowerNormVariation.original_power_norm (linear z B i) one (succ i) (linearCap R) (succ i)
    (GaussianRationalPolynomialBuffers.added_length _ _ _) (linear_mass z R B i hz) (le_refl _)

private theorem mass_step (z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (ih : Γ ⊢[PRAAx] rationalLE (coefficientNorm (polynomial z B N)) (natCode (cap R N))) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (polynomial z B (succ N))) (natCode (cap R (succ N))) := by
  have product := GaussianRationalPolynomialProductTruncation.factor_mass (polynomial z B N) (factor z B N)
    (degree N) (succ N) (cap R N) (pw (linearCap R) (succ N))
    (polynomial_length z B N) (factor_length z B N) ih (factor_mass z R B N hz)
  have budget : Γ ⊢[PRAAx] cap R N*pw (linearCap R) (succ N) ≐ cap R (succ N) :=
    (pw_add (linearCap R) (degree N) (succ N)).eqSymm.eqTrans
      (congrAp2 powF (degree_succ N).eqSymm (.eqRefl _))
  exact rationalLE_congr (coefficientNorm_congr (polynomial_succ z B N).eqSymm) (natCode_congr budget) product

theorem mass (z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (polynomial z B N)) (natCode (cap R N)) := by
  let s (v : PTm n) := Syn.shift v
  have shift_source : Γ.map Fm.shift ⊢[PRAAx] source (s z) (s R) (s B) := by
    simpa [Fm.shift,Syn.shift,s] using hz.shift
  have all : Γ ⊢[PRAAx] .all (rationalLE
      (coefficientNorm (polynomial (s z) (s B) (var 0))) (natCode (cap (s R) (var 0)))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [s,subst_rationalLE,subst_coefficientNorm,GaussianBarnesCanonicalCenteredHead.subst_polynomial,
        subst_natCode,subst_cap,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      have norm := (coefficientNorm_congr (polynomial_zero (Γ := Γ) z B)).eqTrans
        ((singleton_norm qone).eqTrans GaussianRationalSyntheticBounds.qL1_qone)
      have cost : Γ ⊢[PRAAx] cap R zero ≐ one :=
        (congrAp2 powF degree_zero (.eqRefl (linearCap R))).eqTrans (pw_zero _)
      exact rationalLE_congr norm.eqSymm (natCode_congr cost).eqSymm (RationalArgmin.reflexive _)
    · simp only [s,subst_rationalLE,subst_coefficientNorm,GaussianBarnesCanonicalCenteredHead.subst_polynomial,
        subst_natCode,subst_cap,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact mass_step (s z) (s R) (s B) (var 0) shift_source.wk Prf.hyp0
  simpa only [s,subst_rationalLE,subst_coefficientNorm,GaussianBarnesCanonicalCenteredHead.subst_polynomial,
    subst_natCode,subst_cap,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem head_mass (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (polynomial z B (initial R))) (natCode (headCap R)) :=
  mass z R B (initial R) hz

theorem head_coefficient (z R B e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (polynomial z B (initial R)) (monus (degree (initial R)) e))) (natCode (headCap R)) := by
  have hi := GaussianRationalMonicReconstruction.monus_le_left (Γ := Γ) (degree (initial R)) e
  have span := lt_congr (.eqRefl _) (polynomial_length z B (initial R)).eqSymm ((succ_monus_succ _ _).eqTrans hi)
  exact RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ span) (head_mass z R B hz)

theorem padded_head_mass (z R B e : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (coefficientNorm (leftPad (polynomial z B (initial R)) e)) (natCode (headCap R)) :=
  rationalLE_congr (norm_padding _ _).eqSymm (.eqRefl _) (head_mass z R B hz)

theorem padded_head_coefficient (z R B e i : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    rationalLE (qL1 (entry (leftPad (polynomial z B (initial R)) e) (monus (e+degree (initial R)) i)))
      (natCode (headCap R)) := by
  let C := polynomial z B (initial R)
  let N := degree (initial R)
  have len : Γ ⊢[PRAAx] length (leftPad C e) ≐ succ (e+N) :=
    (pad_length C e).eqTrans ((congrAdd (.eqRefl _) (polynomial_length z B (initial R))).eqTrans (add_succ e N))
  have hi := GaussianRationalMonicReconstruction.monus_le_left (Γ := Γ) (e+N) i
  have span := lt_congr (.eqRefl _) len.eqSymm ((succ_monus_succ _ _).eqTrans hi)
  exact RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ span)
    (padded_head_mass z R B e hz)

private theorem reciprocal_power_mass (D e : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    rationalLE (qL1 (power (radiusPoint one D) e)) (natCode one) := by
  have pos := GaussianFactorBudget.power_positive (Γ := Γ) D e hD
  have code := (GaussianFiniteLogarithmWeightedNorm.radius_power_norm one D e hD).eqTrans
    (RationalNonnegativePowers.fraction_congr (GaussianPolynomialPerturbation.one_power e) (.eqRefl _))
  exact rationalLE_congr code.eqSymm (.eqRefl _)
    (fraction_order one (pw D e) one one pos (le_refl one)
      (le_congr (one_mul one).eqSymm (one_mul _).eqSymm pos))

private theorem reciprocal_weight_mass (C N D : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm C N (radiusPoint one D)) (coefficientNorm C) := by
  let P := dilated C N (radiusPoint one D)
  have cmp : Γ ⊢[PRAAx] rationalLE (GaussianCoefficientL1.prefixNorm P (succ N))
      (GaussianCoefficientL1.prefixNorm C (succ N)) := by
    refine prefix_monotone P C (succ N) (.allI (.impI ?_))
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (succ (s N)) :: Γ.map Fm.shift
    let q := entry (s C) (var 0)
    let u := power (radiusPoint one (s D)) (monus (s N) (var 0))
    have hd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hD.shift.wk
    have hi : Δ ⊢[PRAAx] le (var 0) (s N) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have bound := RationalArgmin.transitive (GaussianRationalL1Algebra.qL1_multiply q u)
      (RationalArithmetic.multiply_monotone (qL1 q) _ _ (qL1_nonnegative q) (reciprocal_power_mass _ _ hd))
    have row := rationalLE_congr (qL1_congr (dilated_lookup (s C) (s N) (radiusPoint one (s D)) (var 0) hi)).eqSymm
      (GaussianRationalLinearProduct.scalar_multiply_one (qL1 q) (qL1_guard q)) bound
    simpa only [P,Δ,s,q,Syn.shift,subst_dilated,GaussianDominantPairAlgebra.subst_radiusPoint,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using row
  exact rationalLE_congr (GaussianRationalLinearProduct.norm_length P (succ N) (dilated_length _ _ _)).eqSymm
    (GaussianRationalLinearProduct.norm_length C (succ N) hC).eqSymm cmp

theorem weighted_head_mass (z R B D : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (polynomial z B (initial R)) (degree (initial R)) (radiusPoint one D))
      (natCode (headCap R)) :=
  RationalArgmin.transitive (reciprocal_weight_mass _ _ _ (polynomial_length z B (initial R)) hD) (head_mass z R B hz)

theorem actual_Barnes_centered_head_uniform_mass_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶
      rationalLE (coefficientNorm (polynomial (var 0) (var 2) (initial (var 1)))) (natCode (headCap (var 1)))) :=
  closeUniv 3 (.impI (head_mass (var 0) (var 1) (var 2) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadUniformMass
