import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderPowerGap
import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexFiniteModulus

/-!
# Reflected mesh weights for the signed Stirling remainder

The weight at a grid point is the actual rational inverse power
of the numerator of that point, scaled by the grid denominator.
The reflected pair decreases on the first half of the grid with
an explicitly represented positive gap for distinct interior pairs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedWeight

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianRationalHorner (positive_product scalar_cancel scalar_congr)
open GaussianRationalMetric (comparison_of_cleared)
open GaussianStirlingAllOrderPowerGap (low base gap cleared_weight_gap)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (add represents)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def weight (q M a : PTm n) : PTm n := fraction (pw M (succ q)) (pw a (succ q))
def gapNumerator (q M a d h : PTm n) : PTm n := pw M (succ q)*gap q a (a+h) d h
def gapDenominator (q a d h : PTm n) : PTm n :=
  pw ((a*(a+d))*((a+h)*(a+h+d))) (succ q)
def gapFraction (q M a d h : PTm n) : PTm n :=
  fraction (gapNumerator q M a d h) (gapDenominator q a d h)
def pairWeight (q M A u : PTm n) : PTm n := add (weight q M (A+u)) (weight q M (A+monus M u))
def pairGap (q M A u v : PTm n) : PTm n := gapFraction q M (A+u) (monus v u) (monus M (u+v))

@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (q M a : PTm n) :
    Syn.subst σ (weight q M a) = weight (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ a) :=
  by simp [weight,fraction,pw]
@[simp] theorem subst_gapNumerator {m : ℕ} (σ : Fin n → PTm m) (q M a d h : PTm n) :
    Syn.subst σ (gapNumerator q M a d h) =
      gapNumerator (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ h) :=
  by simp [gapNumerator,pw]
@[simp] theorem subst_gapDenominator {m : ℕ} (σ : Fin n → PTm m) (q a d h : PTm n) :
    Syn.subst σ (gapDenominator q a d h) =
      gapDenominator (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ h) :=
  by simp [gapDenominator,pw]
@[simp] theorem subst_pairWeight {m : ℕ} (σ : Fin n → PTm m) (q M A u : PTm n) :
    Syn.subst σ (pairWeight q M A u) = pairWeight (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ u) :=
  by simp [pairWeight]
@[simp] theorem subst_pairGap {m : ℕ} (σ : Fin n → PTm m) (q M A u v : PTm n) :
    Syn.subst σ (pairGap q M A u v) =
      pairGap (Syn.subst σ q) (Syn.subst σ M) (Syn.subst σ A) (Syn.subst σ u) (Syn.subst σ v) :=
  by simp [pairGap,gapFraction,fraction]

private theorem weight_congr (q M : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] weight q M a ≐ weight q M b :=
  RationalNonnegativePowers.fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) h)

theorem gap_denominator_positive (q a d h : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (gapDenominator q a d h) := by
  have hb := le_trans ha (le_add_right a h)
  exact GaussianFactorBudget.power_positive _ _
    (positive_product _ _ (positive_product _ _ ha (le_trans ha (le_add_right a d)))
      (positive_product _ _ hb (le_trans hb (le_add_right (a+h) d))))

private theorem weight_rep (q M a c D : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (e : Γ ⊢[PRAAx] a*c ≐ D) :
    Γ ⊢[PRAAx] represents (weight q M a) (ZT.ofNat (pw M (succ q)*pw c (succ q))) (pw D (succ q)) :=
  RationalConvexFiniteModulus.rescale_natural _ _ _ _ _
    (fraction_represents _ _ (GaussianFactorBudget.power_positive _ _ ha))
    ((pw_mul_base a c (succ q)).eqSymm.eqTrans (congrAp2 powF (.eqRefl _) e))

private theorem add_rep (x y U V D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hx : Γ ⊢[PRAAx] represents x (ZT.ofNat U) D) (hy : Γ ⊢[PRAAx] represents y (ZT.ofNat V) D) :
    Γ ⊢[PRAAx] represents (add x y) (ZT.ofNat (U+V)) D := by
  apply scalar_cancel _ _ _ D hD
  apply scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := RationalRepresentations.represents_add _ _ _ _ _ _ hx hy)
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

set_option maxHeartbeats 900000 in
theorem weight_gap (q M a d h : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] rationalLE (add (add (weight q M (a+d)) (weight q M (a+h))) (gapFraction q M a d h))
      (add (weight q M a) (weight q M (a+h+d))) := by
  let k := succ q
  let b := a+h
  let X := a*(a+d)
  let Y := b*(b+d)
  let T := X*Y
  let D := gapDenominator q a d h
  let P := pw M k
  let c₀ := (a+d)*Y
  let c₁ := a*Y
  let c₂ := (b+d)*X
  let c₃ := b*X
  have hb := le_trans ha (le_add_right a h)
  have h₁ := le_trans ha (le_add_right a d)
  have h₃ := le_trans hb (le_add_right b d)
  have hD := gap_denominator_positive q a d h ha
  have r₀ := weight_rep q M a c₀ T ha (by dsimp [c₀,T,X]; ipra_ring)
  have r₁ := weight_rep q M (a+d) c₁ T h₁ (by dsimp [c₁,T,X]; ipra_ring)
  have r₂ := weight_rep q M b c₂ T hb (by dsimp [c₂,T,Y]; ipra_ring)
  have r₃ := weight_rep q M (b+d) c₃ T h₃ (by dsimp [c₃,T,Y]; ipra_ring)
  have g := fraction_represents (gapNumerator q M a d h) D hD
  have l := add_rep _ _ _ _ D hD (add_rep _ _ _ _ D hD r₁ r₂) g
  have r := add_rep _ _ _ _ D hD r₀ r₃
  apply comparison_of_cleared _ _ _ _ _ _ hD hD l r
  have cle := cleared_weight_gap (Γ := Γ) q a d h
  change Γ ⊢[PRAAx] le (D*(P*pw c₁ k+P*pw c₂ k+P*gap q a b d h)) ((P*pw c₀ k+P*pw c₃ k)*D)
  have core : Γ ⊢[PRAAx] le (pw c₂ k+pw c₁ k+gap q a b d h) (pw c₀ k+pw c₃ k) := cle
  exact le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right D (mul_le_mul_right P core))

theorem pair_gap (q M A u v : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (huv : Γ ⊢[PRAAx] le u v) (hM : Γ ⊢[PRAAx] le (two*v) M) :
    Γ ⊢[PRAAx] rationalLE (add (pairWeight q M A v) (pairGap q M A u v)) (pairWeight q M A u) := by
  let a := A+u
  let d := monus v u
  let h := monus M (u+v)
  have hv := eq_add_of_le huv
  have hsum : Γ ⊢[PRAAx] le (u+v) M := by ipra_le sl huv+sl hM
  have hm := eq_add_of_le hsum
  have e₁ : Γ ⊢[PRAAx] a+d ≐ A+v :=
    (by dsimp only [a]; ipra_ring : Γ ⊢[PRAAx] a+d ≐ A+(u+d)).eqTrans (congrAdd (.eqRefl _) hv.eqSymm)
  have e₂ : Γ ⊢[PRAAx] a+h ≐ A+monus M v := by
    have e : Γ ⊢[PRAAx] monus M v ≐ u+h :=
      (congrMonus hm (.eqRefl _)).eqTrans
        ((congrMonus (by ipra_ring : Γ ⊢[PRAAx] u+v+h ≐ u+h+v) (.eqRefl _)).eqTrans (add_monus _ _))
    exact (by dsimp [a]; ipra_ring : Γ ⊢[PRAAx] a+h ≐ A+(u+h)).eqTrans (congrAdd (.eqRefl _) e.eqSymm)
  have e₃ : Γ ⊢[PRAAx] a+h+d ≐ A+monus M u := by
    have e : Γ ⊢[PRAAx] monus M u ≐ v+h :=
      (congrMonus hm (.eqRefl _)).eqTrans
        ((congrMonus (by ipra_ring : Γ ⊢[PRAAx] u+v+h ≐ v+h+u) (.eqRefl _)).eqTrans (add_monus _ _))
    exact (by dsimp [a]; ipra_ring : Γ ⊢[PRAAx] a+h+d ≐ A+(u+d)+h).eqTrans
      ((congrAdd (congrAdd (.eqRefl _) hv.eqSymm) (.eqRefl _)).eqTrans
        ((by ipra_ring : Γ ⊢[PRAAx] A+v+h ≐ A+(v+h)).eqTrans (congrAdd (.eqRefl _) e.eqSymm)))
  exact rationalLE_congr
    (RationalAlgebra.add_congr (RationalAlgebra.add_congr (weight_congr q M e₁) (weight_congr q M e₂)) (.eqRefl _))
    (RationalAlgebra.add_congr (.eqRefl _) (weight_congr q M e₃)) (weight_gap q M a d h (le_trans hA (le_add_right A u)))

theorem gap_numerator_positive (q M a d h : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d) (hh : Γ ⊢[PRAAx] le one h) :
    Γ ⊢[PRAAx] le one (gapNumerator q M a d h) := by
  let b := a+h
  have hb := le_trans ha (le_add_right a h)
  have hL : Γ ⊢[PRAAx] le one (low a b d) :=
    positive_product _ _ hb (positive_product _ _ ha (le_trans ha (le_add_right a d)))
  have hB : Γ ⊢[PRAAx] le one (base a b d h) :=
    le_trans (le_trans hL (le_add_right _ _)) (le_add_right _ _)
  have he : Γ ⊢[PRAAx] le one (a+b+d) :=
    le_trans (le_trans ha (le_add_right a b)) (le_add_right _ _)
  exact positive_product _ _ (GaussianFactorBudget.power_positive _ _ hM)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hd hh) he)
      (GaussianFactorBudget.power_positive _ _ hB))

private theorem one_le_difference (a b : PTm n) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] le one (monus b a) := by
  let c := monus b (succ a)
  have e : Γ ⊢[PRAAx] b ≐ succ c+a := (eq_add_of_le h).eqTrans (by ipra_ring)
  exact le_congr (.eqRefl _) ((congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)).eqSymm (zero_lt_succ c)

theorem strict_pair_gap (q M A u v : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hM₀ : Γ ⊢[PRAAx] le one M) (huv : Γ ⊢[PRAAx] lt u v) (hM : Γ ⊢[PRAAx] le (two*v) M) :
    Γ ⊢[PRAAx] le one (gapNumerator q M (A+u) (monus v u) (monus M (u+v))) := by
  have hsum : Γ ⊢[PRAAx] lt (u+v) M := by
    change Γ ⊢[PRAAx] le (succ (u+v)) M
    ipra_le sl huv+sl hM
  exact gap_numerator_positive _ _ _ _ _ hM₀ (le_trans hA (le_add_right A u))
    (one_le_difference u v huv) (one_le_difference (u+v) M hsum)

theorem actual_Stirling_reflected_weight_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 2) ⋏ (le (var 3) (var 4) ⋏ le (two*var 4) (var 1))) ⟶
      rationalLE (add (pairWeight (var 0) (var 1) (var 2) (var 4))
        (pairGap (var 0) (var 1) (var 2) (var 3) (var 4))) (pairWeight (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (pair_gap _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPairedWeight
