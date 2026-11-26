import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderPowerIntegralPrefix

/-!
# The effective pure reciprocal-power integral

For any positive precision denominator D, a cutoff and mesh at least
D give distance at most (B^e+1)/D from the actual finite mass to the
exact primitive at A/B. The terminal primitive has the independent
bound 1/L at every positive cutoff L.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralCofinal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.Foundations.NumeralPrimes (num_le)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianFactorBudget (power_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderFirstPanelReadback (upper_of_add_order)
open GaussianStirlingAllOrderPanelPartsOuterFold (massPrefix)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderPowerIntegralPrefix (corrected_prefix_bounds)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open RationalAlgebra (add_commutative positive_product)
open RationalArithmetic (add)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalGaussianEmbedding (embed)
open RationalGaussianNameEmbedding (distance_from_radius)
open RationalReciprocalPowerTail (add_zero_right)
open RationalValueBounds (radius_of_upper)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem terminal_primitive_bounds (e : ℕ) (he : 2≤e) (A B L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (primitive e (A+B*L) B) ⋏
      rationalLE (primitive e (A+B*L) B) (fraction one L) := by
  let U := A+B*L
  let q : PTm n := num (e-1)
  let P := pw U q
  let C := pw B q
  have hq : Γ ⊢[PRAAx] le one q := num_le (by omega : 1≤e-1)
  have hU : Γ ⊢[PRAAx] le one U := le_trans hA (le_add_right _ _)
  have hP := power_positive U q hU
  have hD := positive_product hq hP
  have id : succ (num (e-2) : PTm n) = q := by
    change num ((e-2)+1) = num (e-1)
    congr 1
    omega
  have self : Γ ⊢[PRAAx] le L (pw L q) := by
    rw [← id]
    exact le_congr (one_mul _) (pw_succ _ _).eqSymm
      (mul_le_mul_right L (power_positive L (num (e-2)) hL))
  have hB : Γ ⊢[PRAAx] le (B*L) U :=
    le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _)
  have prod : Γ ⊢[PRAAx] le (C*pw L q) P :=
    le_congr (pw_mul_base _ _ _) (.eqRefl _) (pw_le_pw q hB)
  have first : Γ ⊢[PRAAx] le (L*C) (C*pw L q) :=
    le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right C self)
  have last : Γ ⊢[PRAAx] le P (one*(q*P)) :=
    le_congr (one_mul _) (by ipra_ring) (mul_le_mul_right P hq)
  exact .andI (fraction_order zero one C (q*P) (le_refl one) hD (by ipra_le 𝔞(C)))
    (fraction_order C (q*P) one L hD hL (le_trans first (le_trans prod last)))

theorem cofinal_mass_distance (e : ℕ) (he : 2≤e) (A B M L D : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (hDM : Γ ⊢[PRAAx] le D M) (hDL : Γ ⊢[PRAAx] le D L) :
    Γ ⊢[PRAAx] distanceBounded (embed (massPrefix e A B M L)) (embed (primitive e A B))
      (power e B+one) D := by
  let x := massPrefix e A B M L
  let y := primitive e A B
  let t := primitive e (A+B*L) B
  let C := power e B
  let budget := fraction (C+one) D
  have hM := le_trans hD hDM
  have hL := le_trans hD hDL
  have m := corrected_prefix_bounds e he A B M L hA hM
  have tail := terminal_primitive_bounds e he A B L hA hL
  have g : Γ ⊢[PRAAx] rationalLE (fraction C M) budget :=
    fraction_order _ _ _ _ hM hD (by ipra_le 𝔞(C)*sl hDM+𝔞(M))
  have f : Γ ⊢[PRAAx] rationalLE (fraction one L) budget :=
    fraction_order _ _ _ _ hL hD (by ipra_le sl hDL+𝔞(C)*𝔞(L))
  have monotone := add_monotone x x _ _ (reflexive x) tail.andE₁
  have nonneg : Γ ⊢[PRAAx] rationalLE x (add x t) :=
    rationalLE_congr (add_zero_right _ (RationalFiniteSum.sum_well_formed _ _ _)) (.eqRefl _) monotone
  have hi : Γ ⊢[PRAAx] rationalLE x (add y budget) :=
    transitive nonneg (transitive m.andE₂ (add_monotone _ _ _ _ (reflexive y) g))
  have lo : Γ ⊢[PRAAx] rationalLE y (add x budget) :=
    transitive m.andE₁ (add_monotone _ _ _ _ (reflexive x) (transitive tail.andE₂ f))
  exact distance_from_radius _ _ _ _ hD
    (radius_of_upper _ _ _ _ (upper_of_add_order _ _ _ _ hD hi) (upper_of_add_order _ _ _ _ hD lo))

theorem actual_original_reciprocal_mass_integral_cofinal_closed (e : ℕ) (he : 2≤e) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 0) ⟶ le one (var 4) ⟶ le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶
        distanceBounded (embed (massPrefix e (var 0) (var 1) (var 2) (var 3))) (embed (primitive e (var 0) (var 1)))
          (power e (var 1)+one) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (cofinal_mass_distance e he _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPowerIntegralCofinal
