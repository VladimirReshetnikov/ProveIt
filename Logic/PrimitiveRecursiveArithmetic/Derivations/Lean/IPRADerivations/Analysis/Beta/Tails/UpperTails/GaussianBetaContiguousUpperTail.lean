import IPRADerivations.Analysis.Beta.Tails.ZeroExtension.GaussianBetaZeroUpperDifferenceGrid
import IPRADerivations.Analysis.Inequalities.WeightedComparison.GaussianWeightedHalfDecayEndpoint
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpPartition

/-!
# One D_R quarter-degree endpoint for the contiguous original upper tail

The beta degree N and the requested decay observation q are arbitrary.
Integrate the literal zero extension and Euler evaluator on one shared
grid from N/2 to T>=N. The actual old decay sample at N/4 appears once,
with explicit mesh, row and endpoint observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaContiguousUpperTail

open_ipra
open GaussianBetaSharpPartition (halfPoint halfDen even_denominator half_boundary_order half_point_decay_sample)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianWeightedHalfDecayEndpoint (coefficient)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianCompactRiemannName (quadrature)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def start (k A R N : PTm n) : PTm n := halfPoint k A R N
def width (k A R N T : PTm n) : PTm n := monus (etaDen k A R*T) (start k A R N)
def count (k A R N T S : PTm n) : PTm n := width k A R N T*S
def quarterSample (q N : PTm n) : PTm n := ap2 decayF q (decayData N (num 4))
def sampleNumerator (q N : PTm n) : PTm n := GaussianL1.norm1 (rawGaussian (quarterSample q N))
def sampleDenominator (q N : PTm n) : PTm n := rawDen (quarterSample q N)
def numerator (p q k A R N T S U V : PTm n) : PTm n :=
  (width k A R N T*GaussianBetaEulerTailDifferencePointwise.referenceError R)*
      GaussianWeightedHalfDecayEndpoint.denominator p q (count k A R N T S) (etaDen k A R) V+
    GaussianWeightedHalfDecayEndpoint.numerator p q (count k A R N T S) (width k A R N T) (etaDen k A R) R U V*(etaDen k A R*unit p)
def denominator (p q k A R N T S V : PTm n) : PTm n :=
  (etaDen k A R*unit p)*GaussianWeightedHalfDecayEndpoint.denominator p q (count k A R N T S) (etaDen k A R) V
def beta (p k A S z R B N T : PTm n) : PTm n := quadrature GaussianBetaZeroExtension.evaluatorF p (count k A R N T S)
  (start k A R N) (width k A R N T) (etaDen k A R) (GaussianBetaKernelGridComparison.sampleDataBeta z B N)
def euler (p k A S z R B N T : PTm n) : PTm n := quadrature GaussianEulerIntegrandName.evaluatorF p (count k A R N T S)
  (start k A R N) (width k A R N T) (etaDen k A R) (GaussianEulerIntegrandName.fixedData z B)
def source (z R B A N T S : PTm n) : Fm PTm n := GaussianEulerUpperPowerCoefficients.source z R B ⋏
  (le one A ⋏ (le two N ⋏ (le N T ⋏ le one S)))

theorem geometry (k A R N T : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hN : Γ ⊢[PRAAx] le two N)
    (hT : Γ ⊢[PRAAx] le N T) : Γ ⊢[PRAAx]
    le one (width k A R N T) ⋏ (le one (start k A R N) ⋏
      (le (etaDen k A R) (start k A R N) ⋏ start k A R N+width k A R N T ≐ etaDen k A R*T)) := by
  have bounds := half_boundary_order k A R N hA hN
  have ha := le_trans (eta_den_positive k A R) bounds.andE₁
  have twice : Γ ⊢[PRAAx] start k A R N+start k A R N ≐ etaDen k A R*N := by
    apply deriveNat
    have eq := natEq (even_denominator (Γ := Γ) k A R hA)
    dsimp only [start,halfPoint]
    ipra_simps
    rw [eq]
    ring
  have large : Γ ⊢[PRAAx] le (start k A R N+start k A R N) (etaDen k A R*T) :=
    le_congr twice.eqSymm (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (etaDen k A R)) hT)
  have within := le_trans bounds.andE₂ (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (etaDen k A R)) hT)
  have endpoint : Γ ⊢[PRAAx] start k A R N+width k A R N T ≐ etaDen k A R*T := (eq_add_of_le within).eqSymm
  have order : Γ ⊢[PRAAx] le (start k A R N+start k A R N) (start k A R N+width k A R N T) :=
    le_congr (.eqRefl _) endpoint.eqSymm large
  have grow : Γ ⊢[PRAAx] le (start k A R N) (width k A R N T) := by
    apply le_of_eq_add (d := monus (start k A R N+width k A R N T) (start k A R N+start k A R N))
    have eq := natEq (eq_add_of_le order)
    apply deriveNat
    ipra_simps
    linear_combination eq
  exact .andI (le_trans ha grow) (.andI ha (.andI bounds.andE₁ endpoint))

/-- The actual original N/4 observation is the only analytic input to
this generic weighted-endpoint transfer; its precision q is independent. -/
theorem original_grid_from_quarter_decay_bound (p q k A S z R B N T U V : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N T S) (hV : Γ ⊢[PRAAx] le one V)
    (hStart : Γ ⊢[PRAAx] bounded (qmul (radiusPoint (coefficient R) one) (quarterSample q N)) U V) : Γ ⊢[PRAAx]
    distanceBounded (beta p k A S z R B N T) (euler p k A S z R B N T)
      (numerator p q k A R N T S U V) (denominator p q k A R N T S V) := by
  have hA := h.andE₂.andE₁
  have hN := h.andE₂.andE₂.andE₁
  have hT := h.andE₂.andE₂.andE₂.andE₁
  have hS := h.andE₂.andE₂.andE₂.andE₂
  have geo := geometry k A R N T hA hN hT
  have he := eta_den_positive (Γ := Γ) k A R
  have hm : Γ ⊢[PRAAx] le one (count k A R N T S) := positive_product _ _ geo.andE₁ hS
  have step : Γ ⊢[PRAAx] le (width k A R N T) ((two*etaDen k A R)*count k A R N T S) :=
    le_congr (one_mul _) (by unfold count; ipra_ring)
      (mul_le_mul_right (width k A R N T) (positive_product _ _ (positive_product _ _ (le_succ_self one) he) hS))
  have startBound := bound_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (radiusPoint (coefficient R) one))
      (half_point_decay_sample q k A R N hA)).eqSymm (.eqRefl _) (.eqRefl _) hStart
  have half := GaussianWeightedHalfDecayEndpoint.original_scaled_half_decay_bound p q (count k A R N T S) (start k A R N)
    (width k A R N T) (etaDen k A R) R U V geo.andE₂.andE₁ hm geo.andE₁ he step hV startBound
  have hd := GaussianWeightedHalfDecayEndpoint.mesh_denominator_positive p q (count k A R N T S) (etaDen k A R) hm he
  exact GaussianBetaZeroUpperDifferenceGrid.original_grid_bound_from_scaled_half p (count k A R N T S) (start k A R N)
    (width k A R N T) (etaDen k A R) z R B N _ _ hm he geo.andE₂.andE₂.andE₁ h.andE₁
    (le_trans (le_succ_self one) hN) (positive_product _ _ hd (positive_product _ _ hV (unit_positive q))) half

theorem actual_quarter_sample_bound (q N : PTm n) : Γ ⊢[PRAAx]
    bounded (quarterSample q N) (sampleNumerator q N) (sampleDenominator q N) :=
  GaussianRationalMetric.bounded_of_same_denominator (raw_den_positive _) (raw_represents _)
    (GaussianL1.normSq_le_norm1_square (rawGaussian (quarterSample q N)))

/-- Source only, retaining the decoded magnitude of the SAME actual
original decay sample at N/4. Its coefficient is exactly one D_R. -/
theorem original_grid (p q k A S z R B N T : PTm n) (h : Γ ⊢[PRAAx] source z R B A N T S) : Γ ⊢[PRAAx]
    distanceBounded (beta p k A S z R B N T) (euler p k A S z R B N T)
      (numerator p q k A R N T S (coefficient R*sampleNumerator q N) (sampleDenominator q N))
      (denominator p q k A R N T S (sampleDenominator q N)) :=
  original_grid_from_quarter_decay_bound p q k A S z R B N T _ _ h (raw_den_positive _)
    (GaussianRationalReciprocal.bounded_product_one_left (raw_den_positive _)
      (radius_bounded (coefficient R) one (le_refl one)) (actual_quarter_sample_bound q N))

theorem original_contiguous_upper_tail_one_quarter_degree_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 5) (var 6) (var 7) (var 3) (var 8) (var 9) (var 4) ⟶
      distanceBounded (beta (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (euler (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 6) (var 8) (var 9) (var 4)
          (coefficient (var 6)*sampleNumerator (var 1) (var 8)) (sampleDenominator (var 1) (var 8)))
        (denominator (var 0) (var 1) (var 2) (var 3) (var 6) (var 8) (var 9) (var 4) (sampleDenominator (var 1) (var 8)))) :=
  closeUniv 10 (.impI (original_grid _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaContiguousUpperTail
