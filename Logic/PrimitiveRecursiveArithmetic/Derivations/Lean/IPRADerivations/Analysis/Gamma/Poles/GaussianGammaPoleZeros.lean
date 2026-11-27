import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Denominators.GaussianGammaEulerHeadLower
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaC7Name
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference

/-!
# Exact zeros of the original reciprocal Gamma program at the poles

A recorded pole index zeros the corresponding factor of the original
Euler head. Its numerical split contains that factor, so all subsequent
prefixes vanish. The literal C7 observation is then exactly zero at
every precision. This is the forward zero assertion at a rational input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleZeros

open_ipra
open GaussianRationalHorner (qzero qmul ofGaussian ofGaussian_represents canonical_unique represents_congr)
open GaussianRationalSyntheticDivision (qzero_canonical qmul_congr qmul_zero_left qmul_zero_right)
open GaussianGammaEulerHead (head factor head_zero head_succ head_split program_at)
open GaussianGammaEulerHeadLower (translated translated_zero factor_represents)
open ComplexLogarithmRemainder (zeroCode oneCode scale)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_neg im_neg re_zero im_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem factor_zero_at_pole (z B i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] equal (translated z B (succ i)) zeroCode) :
    Γ ⊢[PRAAx] factor i z B ≐ qzero := by
  let D := B*succ i
  exact canonical_unique _ _ zeroCode D (GaussianRationalHorner.qadd_canonical _ _) qzero_canonical
    (GaussianRationalHorner.positive_product _ _ hB (zero_lt_succ i))
    (represents_congr (.eqRefl _) h (.eqRefl _) (factor_represents i z B hB))
    (GaussianRationalHorner.zero_represents D)

theorem head_at_pole_index (z B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] equal (translated z B k) zeroCode) : Γ ⊢[PRAAx] head z B k ≐ qzero := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have e : (k ≐ zero) :: Γ ⊢[PRAAx] k ≐ zero := Prf.hyp0
    have ht : (k ≐ zero) :: Γ ⊢[PRAAx] translated z B k ≐ translated z B zero := by
      ipra_congr (translated (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl z, .eqRefl B, e] using [translated]
    have hz := GaussianRootAlgebra.equal_trans (GaussianRootAlgebra.equal_symm (translated_zero z B))
      (GaussianRootAlgebra.equal_trans (GaussianRootAlgebra.equal_symm (GaussianRootAlgebra.equal_of_code ht)) h.wk)
    have ez : (k ≐ zero) :: Γ ⊢[PRAAx] ofGaussian z B ≐ qzero :=
      canonical_unique _ _ zeroCode B (GaussianRationalHorner.ofGaussian_canonical _ _ hB.wk) qzero_canonical
        hB.wk (represents_congr (.eqRefl _) hz (.eqRefl _) (ofGaussian_represents _ _ hB.wk))
        (GaussianRationalHorner.zero_represents B)
    have headcong : (k ≐ zero) :: Γ ⊢[PRAAx] head z B k ≐ head z B zero := by
      ipra_congr (head (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl z, .eqRefl B, e]
    exact headcong.eqTrans ((head_zero z B hB.wk).eqTrans ez)
  · have e : (k ≐ succ (pred k)) :: Γ ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have ht : (k ≐ succ (pred k)) :: Γ ⊢[PRAAx] translated z B k ≐ translated z B (succ (pred k)) := by
      ipra_congr (translated (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl z, .eqRefl B, e]
    have hz := GaussianRootAlgebra.equal_trans (GaussianRootAlgebra.equal_symm (GaussianRootAlgebra.equal_of_code ht)) h.wk
    have headcong : (k ≐ succ (pred k)) :: Γ ⊢[PRAAx] head z B k ≐ head z B (succ (pred k)) := by
      ipra_congr (head (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl z, .eqRefl B, e]
    exact headcong.eqTrans ((head_succ z B (pred k)).eqTrans
      ((qmul_congr (.eqRefl _) (factor_zero_at_pole z B (pred k) hB.wk hz)).eqTrans (qmul_zero_right _)))

theorem head_zero_at_pole (z B k N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le k N)
    (h : Γ ⊢[PRAAx] equal (translated z B k) zeroCode) : Γ ⊢[PRAAx] head z B N ≐ qzero := by
  have hc : Γ ⊢[PRAAx] head z B N ≐ head z B (k+monus N k) := by
    ipra_congr (head (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl z, .eqRefl B, eq_add_of_le hk]
  exact hc.eqTrans ((head_split z B k (monus N k)).eqTrans
    ((qmul_congr (head_at_pole_index z B k hB h) (.eqRefl _)).eqTrans (qmul_zero_left _)))

theorem C7_sample_zero_at_pole (p z R B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le k (two*R)) (h : Γ ⊢[PRAAx] equal (translated z B k) zeroCode) :
    Γ ⊢[PRAAx] GaussianGammaC7Name.sample p z R B ≐ qzero := by
  have hh := (program_at z B (two*R)).eqTrans (head_zero_at_pole z B k (two*R) hB hk h)
  have eq := (qmul_congr hh (.eqRefl _)).eqTrans (qmul_zero_left
    (GaussianGammaCanonicalExponent.exponentialPoint (GaussianGammaC7Name.samplePrecision p z R B) z R B))
  exact (GaussianGammaC7Name.sample_at p z R B).eqTrans
    ((GaussianNameArithmetic.recode_congr eq).eqTrans (GaussianExponentialReference.recode_fixed _ qzero_canonical))

/-- The numerator at the negative-integer input `-k` with denominator `B`. -/
def poleNumerator (B k : PTm n) : PTm n := ComplexLogarithmRemainder.neg (scale (B*k) oneCode)

theorem translated_pole_numerator (B k : PTm n) : Γ ⊢[PRAAx] equal (translated (poleNumerator B k) B k) zeroCode := by
  apply equal_of_values <;> simp only [translated,poleNumerator,re_add,im_add,re_neg,im_neg,re_zero,im_zero] <;> ring

theorem C7_negative_integer_zero (p R B k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le k (two*R)) : Γ ⊢[PRAAx] GaussianGammaC7Name.sample p (poleNumerator B k) R B ≐ qzero :=
  C7_sample_zero_at_pole p (poleNumerator B k) R B k hB hk (translated_pole_numerator B k)

theorem actual_euler_head_zero_at_pole_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 2) (var 3) ⟶ equal (translated (var 0) (var 1) (var 2)) zeroCode ⟶
      head (var 0) (var 1) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (.impI (head_zero_at_pole _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_C7_sample_zero_at_pole_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ le (var 4) (two*var 2) ⟶ equal (translated (var 1) (var 3) (var 4)) zeroCode ⟶
      GaussianGammaC7Name.sample (var 0) (var 1) (var 2) (var 3) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (C7_sample_zero_at_pole _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_C7_negative_integer_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 3) (two*var 1) ⟶
      GaussianGammaC7Name.sample (var 0) (poleNumerator (var 2) (var 3)) (var 1) (var 2) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (C7_negative_integer_zero _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleZeros
