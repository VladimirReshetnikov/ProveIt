import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactRiemannName
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactZeroWidth

/-!
# Independent positive uniform grids on the same actual compact panel

The two original quadratures have unrelated positive counts and
independent observation queries. Their product grid at query p+q
supplies two genuine refinement comparisons. The curvature error is
L*(C/E)^2*(1/N+1/H), and the observation error is at most
2*(C/E)*(eps_p+eps_q). The panel width may be zero. The original
quadrature at zero count is also proved to be literal zero for all data.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactUniformGridComparison

open_ipra
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def sharedPrecision (p q : PTm n) : PTm n := p+q
def common (F : PR 3) (p q N H a C E x : PTm n) : PTm n := quadrature F (sharedPrecision p q) (N*H) a C E x
def numerator (p q N H C E L : PTm n) : PTm n :=
  L*C*C*(N+H)*unit p*unit q+two*C*E*N*H*(unit p+unit q)
def denominator (p q N H E : PTm n) : PTm n := E*E*N*H*unit p*unit q

def leftNumerator (p q N H C E L : PTm n) : PTm n := L*C*C*H*unit p*unit q+two*C*E*N*H*unit q
def rightNumerator (p q N H C E L : PTm n) : PTm n := L*C*C*N*unit p*unit q+two*C*E*N*H*unit p

ipra_subst sharedPrecision
ipra_subst common
ipra_subst numerator
ipra_subst denominator

theorem denominator_positive (p q N H E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx] le one (denominator p q N H E) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hE hE) hN) hH)
    (unit_positive p)) (unit_positive q)

theorem common_left (F : PR 3) (p q N H a C E L x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (hH : Γ ⊢[PRAAx] le one H) (hMod : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    distanceBounded (common F p q N H a C E x) (quadrature F p N a C E x)
      (leftNumerator p q N H C E L) (denominator p q N H E) := by
  let r := sharedPrecision p q
  have grow : Γ ⊢[PRAAx] le (unit p) (unit r) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have raw := GaussianCompactRiemannName.quadrature_refinement F r p N H a C E L x ha hE hN hH hMod
  have oldDen : Γ ⊢[PRAAx] le one (E*rateDenominator (E*N) r p) :=
    positive_product _ _ hE (GaussianNamedInverseRate.denominator_positive _ r p (positive_product _ _ hE hN))
  exact distance_radius_mono _ _ _ _ _ _ oldDen (denominator_positive p q N H E hE hN hH)
    (by dsimp only [leftNumerator,denominator,rateNumerator,rateDenominator]
        ipra_le (𝔞 C*𝔞 E^3*𝔞 N^2*𝔞 H*𝔞(unit p)*𝔞(unit q))*sl grow)
    (distance_congr (GaussianCompactRiemannName.quadrature_index_congr F r (H*N) (N*H) a C E x (by ipra_ring))
      (.eqRefl _) (.eqRefl _) (.eqRefl _) raw)

theorem common_right (F : PR 3) (p q N H a C E L x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (hH : Γ ⊢[PRAAx] le one H) (hMod : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    distanceBounded (common F p q N H a C E x) (quadrature F q H a C E x)
      (rightNumerator p q N H C E L) (denominator p q N H E) := by
  let r := sharedPrecision p q
  have grow : Γ ⊢[PRAAx] le (unit q) (unit r) := GaussianExponentialReference.unit_monotone (le_add_left _ _)
  have raw := GaussianCompactRiemannName.quadrature_refinement F r q H N a C E L x ha hE hH hN hMod
  have oldDen : Γ ⊢[PRAAx] le one (E*rateDenominator (E*H) r q) :=
    positive_product _ _ hE (GaussianNamedInverseRate.denominator_positive _ r q (positive_product _ _ hE hH))
  exact distance_radius_mono _ _ _ _ _ _ oldDen (denominator_positive p q N H E hE hN hH)
    (by dsimp only [rightNumerator,denominator,rateNumerator,rateDenominator]
        ipra_le (𝔞 C*𝔞 E^3*𝔞 H^2*𝔞 N*𝔞(unit p)*𝔞(unit q))*sl grow) raw

/-- Unrelated positive counts, independent original queries, and C=0. -/
theorem original_comparison (F : PR 3) (p q N H a C E L x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (hH : Γ ⊢[PRAAx] le one H) (hMod : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F p N a C E x) (quadrature F q H a C E x)
      (numerator p q N H C E L) (denominator p q N H E) := by
  have hd := denominator_positive (Γ := Γ) p q N H E hE hN hH
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold leftNumerator rightNumerator numerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd
      (distance_symmetric _ _ _ _ hd (common_left F p q N H a C E L x ha hE hN hH hMod))
      (common_right F p q N H a C E L x ha hE hN hH hMod))

/-- The actual empty finite sum makes the original count-zero
quadrature zero even for an arbitrary original scalar weight. -/
theorem empty_quadrature (F : PR 3) (p a C E x : PTm n) : Γ ⊢[PRAAx] quadrature F p zero a C E x ≐ qzero :=
  (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianRationalFiniteSum.sum_zero _ _)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem zero_width_any_count (F : PR 3) (p N a E x : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    quadrature F p N a zero E x ≐ qzero := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact (GaussianCompactRiemannName.quadrature_index_congr F p N zero a zero E x Prf.hyp0).eqTrans (empty_quadrature F p a zero E x)
  · have positive : (N ≐ succ (LeanProofs.IPRA.PTm.pred N))::Γ ⊢[PRAAx] le one N :=
      Order.zero_lt_of_eq_succ Prf.hyp0
    exact GaussianCompactZeroWidth.quadrature_zero F p N a E x hE.wk positive

theorem actual_same_panel_independent_uniform_grid_comparison_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((le one (var 4) ⋏ (le one (var 6) ⋏ (le one (var 2) ⋏ (le one (var 3) ⋏ sampledModulus F
      (var 4) (var 5) (var 6) (var 7) (var 8))))) ⟶
      distanceBounded (quadrature F (var 0) (var 2) (var 4) (var 5) (var 6) (var 8))
        (quadrature F (var 1) (var 3) (var 4) (var 5) (var 6) (var 8))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 7))
        (denominator (var 0) (var 1) (var 2) (var 3) (var 6))) :=
  closeUniv 9 (.impI (original_comparison F _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

theorem actual_original_count_zero_quadrature_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (quadrature F (var 0) zero (var 1) (var 2) (var 3) (var 4) ≐ qzero) := closeUniv 5 (empty_quadrature F _ _ _ _ _)

theorem actual_original_zero_width_all_counts_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ quadrature F (var 0) (var 1) (var 2) zero (var 3) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (zero_width_any_count F _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactUniformGridComparison
