import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHead
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds

/-!
# The exact pole-separation lower bound of the original Euler polynomial

For the original input z/B and δ=a/d, the pole guard is the cleared
inequality (aB)²≤d²|z+Bk|² at every internal k≤N. A genuine guarded
QF induction on the original head recurrence proves

  |head(z/B,N)| ≥ (a/d)^(N+1)/N!.

The programmer's literal output inherits that exact rational constant.
No normalization/value law for a computed head is assumed. The proof
also covers N=0 and does not require the optional source restriction
δ≤1. For a,d≥1 the existing fractional apartness and actual reciprocal
algorithm are supplied with the corresponding exact certificates.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadLower

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaEulerHead (factor head run head_zero head_succ program_at)
open GaussianRationalHorner (represents positive_product)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation product_lower)
open ComplexLogarithmRemainder (normSq scale oneCode)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def translated (z B k : PTm n) : PTm n := ComplexLogarithmRemainder.add z (scale (B*k) oneCode)
def poleAt (z B a d k : PTm n) : Fm PTm n :=
  le ((a*B)*(a*B)) (d*d*normSq (translated z B k))
def poleGuard (z B a d N : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift N) ⟶ poleAt (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (var 0))
def prefixLower (z B a d N : PTm n) : Fm PTm n :=
  lower (head z B N) (pw a (succ N)) (pw d (succ N)*fact N)

ipra_subst translated
ipra_subst poleAt
ipra_subst poleGuard [Syn.subst_shift, Syn.shift_subst]
ipra_subst prefixLower [fact]

theorem pole_at (z B a d N k : PTm n) (h : Γ ⊢[PRAAx] poleGuard z B a d N)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] poleAt z B a d k := by
  have e : Γ ⊢[PRAAx] le k N ⟶ poleAt z B a d k := by simpa [poleGuard] using h.allE k
  exact .impE e hk

theorem translated_zero (z B : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (translated z B zero) z := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring

/-- The old factor 1+(z/B)/(i+1) retains its exact original numerator and denominator. -/
theorem factor_represents (i z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (factor i z B) (translated z B (succ i)) (B*succ i) := by
  have pos := positive_product (Γ := Γ) _ _ hB (zero_lt_succ i)
  have sum := GaussianRationalHorner.qadd_represents _ _ _ _ _ pos
    (GaussianRationalReciprocal.qone_represents_scaled (B*succ i)) (GaussianRationalHorner.ofGaussian_represents z _ pos)
  apply GaussianRationalHorner.represents_congr (.eqRefl _) _ (.eqRefl _) sum
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring

theorem factor_lower (i z B a d : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] poleAt z B a d (succ i)) : Γ ⊢[PRAAx] lower (factor i z B) a (d*succ i) := by
  apply lower_from_representation _ _ _ _ _ (positive_product _ _ hB (zero_lt_succ i))
    (positive_product _ _ hd (zero_lt_succ i)) (factor_represents i z B hB)
  exact le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl (succ i*succ i)) h)

theorem prefix_denominator_positive (d N : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] le one (pw d (succ N)*fact N) :=
  positive_product _ _ (GaussianFactorBudget.power_positive d (succ N) hd)
    (GaussianRationalPolynomialExponential.factorial_positive N)

theorem prefix_lower_zero (z B a d : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] poleAt z B a d zero) : Γ ⊢[PRAAx] prefixLower z B a d zero := by
  have first : Γ ⊢[PRAAx] lower (GaussianRationalHorner.ofGaussian z B) a d := by
    apply lower_from_representation _ _ _ _ _ hB hd (GaussianRationalHorner.ofGaussian_represents z B hB)
    exact le_congr (by ipra_ring) (congrMul (.eqRefl _) (GaussianRootAlgebra.normSq_equal (translated_zero z B))) h
  have den : Γ ⊢[PRAAx] pw d one*fact zero ≐ d :=
    (congrMul (pw_one d) (fact_zero zero)).eqTrans (by ipra_ring)
  exact lower_congr (head_zero z B hB).eqSymm (pw_one a).eqSymm den.eqSymm first

theorem prefix_lower_step (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] poleAt z B a d (succ N)) (ih : Γ ⊢[PRAAx] prefixLower z B a d N) :
    Γ ⊢[PRAAx] prefixLower z B a d (succ N) := by
  have joined := product_lower _ _ _ _ _ _ (prefix_denominator_positive d N hd) (positive_product _ _ hd (zero_lt_succ N))
    ih (factor_lower N z B a d hB hd h)
  have den : Γ ⊢[PRAAx] (pw d (succ N)*fact N)*(d*succ N) ≐ pw d (succ (succ N))*fact (succ N) := by
    have p := natEq (pw_succ (Γ := Γ) d (succ N))
    have f := natEq (fact_succ (Γ := Γ) N zero)
    apply deriveNat; ipra_simps; rw [p,f]; ring
  exact lower_congr (head_succ z B N).eqSymm (pw_succ a (succ N)).eqSymm den joined

/-- Genuine bounded QF induction on the original finite head, with all pole indices internal. -/
theorem prefix_lower (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] poleGuard z B a d N) : Γ ⊢[PRAAx] prefixLower z B a d N := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] poleGuard (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      prefixLower (Syn.shift z) (Syn.shift B) (Syn.shift a) (Syn.shift d) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_le, subst_prefixLower]
    · exact .impI (prefix_lower_zero z B a d hB.wk hd.wk (pole_at z B a d N zero h.wk (zero_le N)))
    · exact .impI (prefix_lower_step _ _ _ _ _ bs.wk.wk ds.wk.wk (pole_at _ _ _ _ _ _ hs.wk.wk Prf.hyp0)
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have last : Γ ⊢[PRAAx] le N N ⟶ prefixLower z B a d N := by
    simpa only [Fm.subst_imp,subst_le,subst_prefixLower,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE last (le_refl N)

theorem returned_head_lower (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] poleGuard z B a d N) : Γ ⊢[PRAAx]
    lower (run z B N) (pw a (succ N)) (pw d (succ N)*fact N) :=
  lower_congr (program_at z B N).eqSymm (.eqRefl _) (.eqRefl _) (prefix_lower z B a d N hB hd h)

theorem returned_fractional_apartness (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] poleGuard z B a d N) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.lower (run z B N) (pw d (succ N)*fact N) :=
  GaussianRationalLowerBounds.name_lower _ _ _ (GaussianFactorBudget.power_positive a (succ N) ha)
    (prefix_denominator_positive d N hd) (returned_head_lower z B a d N hB hd h)

theorem returned_inverse_bound (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] poleGuard z B a d N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (GaussianRationalReciprocal.reciprocal (run z B N)) (pw d (succ N)*fact N) (pw a (succ N)) :=
  GaussianRationalLowerBounds.inverse_bound _ _ _ (GaussianFactorBudget.power_positive a (succ N) ha)
    (prefix_denominator_positive d N hd) (returned_head_lower z B a d N hB hd h)

theorem returned_inverse_identity (z B a d N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] poleGuard z B a d N) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (run z B N) (GaussianRationalReciprocal.reciprocal (run z B N)) ≐ GaussianRationalSyntheticDivision.qone :=
  GaussianRationalReciprocal.reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ _
    (prefix_denominator_positive d N hd) (returned_fractional_apartness z B a d N hB ha hd h))

theorem original_finite_euler_head_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ poleGuard (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      lower (run (var 0) (var 1) (var 4)) (pw (var 2) (succ (var 4))) (pw (var 3) (succ (var 4))*fact (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (returned_head_lower _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_C7_euler_head_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ poleGuard (var 0) (var 1) (var 2) (var 3) (two*var 4) ⟶
      lower (run (var 0) (var 1) (two*var 4)) (pw (var 2) (succ (two*var 4)))
        (pw (var 3) (succ (two*var 4))*fact (two*var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (returned_head_lower _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem actual_separated_euler_head_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶ poleGuard (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianRationalHorner.qmul (run (var 0) (var 1) (var 4)) (GaussianRationalReciprocal.reciprocal (run (var 0) (var 1) (var 4))) ≐
        GaussianRationalSyntheticDivision.qone ⋏
      GaussianRationalMetric.bounded (GaussianRationalReciprocal.reciprocal (run (var 0) (var 1) (var 4)))
        (pw (var 3) (succ (var 4))*fact (var 4)) (pw (var 2) (succ (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.andI
    (returned_inverse_identity _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)
    (returned_inverse_bound _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadLower
