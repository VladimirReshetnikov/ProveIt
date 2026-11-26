import IPRADerivations.Analysis.Beta.GaussianBetaSharpFiniteBinding
import IPRADerivations.Analysis.Beta.GaussianBetaMiddleDyadicBudget
import IPRADerivations.Analysis.Beta.GaussianBetaLowDyadicBudget
import IPRADerivations.Analysis.Beta.GaussianBetaContiguousUpperTailBudget

/-!
# Explicit common-cutoff schedules for the sharp finite Euler comparison

The original cutoff is chosen before the common mesh multiplier. The
evaluation precision then uses the actual resulting support count. Each
threshold may be exceeded independently. Tail and middle reference
queries have separate computed lower bounds; the beta degree is fixed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpCofinalSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianBetaFiniteEulerComparison (supportWidth)
open GaussianBetaSharpPartition (lowWidth middleWidth)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev source (z R B A N : PTm n) : Fm PTm n := GaussianBetaFiniteEulerComparison.source z R B A N
def cutoff (t A N : PTm n) : PTm n := t+N+GaussianBetaFiniteEulerAtCutoff.minimumCutoff t A
def factor (t H A R N : PTm n) : PTm n :=
  GaussianBetaSharpFiniteBinding.multiplier H (cutoff t A N) A R
def supportCount (t H A R N : PTm n) : PTm n :=
  supportWidth (etaDen (cutoff t A N) A R) N*factor t H A R N
def minimumH (t z R B A N : PTm n) : PTm n :=
  one+GaussianBetaFiniteEulerAtCutoff.minimumCells t (cutoff t A N) z R B A N+
    GaussianBetaMiddleDyadicBudget.minimumMesh t (middleWidth (cutoff t A N) A R N) R+
    GaussianBetaContiguousUpperTailBudget.minimumMesh t R (top (cutoff t A N) A R)
def minimumPrecision (t H z R B A N : PTm n) : PTm n :=
  GaussianBetaLowDyadicBudget.minimumPrecision t+
    GaussianBetaFiniteEulerAtCutoff.minimumPrecision t (cutoff t A N) z R B A N (supportCount t H A R N)+
    GaussianBetaRefinedFixedCompactComparison.referencePrecision (cutoff t A N+num 4) (cutoff t A N) A R+
    GaussianBetaContiguousUpperTailBudget.minimumPrecision t R (top (cutoff t A N) A R)+
    GaussianFastValueCut.exponent (num 4*top (cutoff t A N) A R) t
def minimumTailQuery (t R : PTm n) : PTm n := GaussianBetaContiguousUpperTailBudget.minimumQuery t R
def minimumMiddleQuery (t A R N : PTm n) : PTm n :=
  GaussianBetaMiddleDyadicBudget.minimumAuxiliary t (middleWidth (cutoff t A N) A R N) N R

theorem cutoff_bounds (t A R N : PTm n) : Γ ⊢[PRAAx]
    le t (cutoff t A N) ⋏ (le (GaussianBetaFiniteEulerAtCutoff.minimumCutoff t A) (cutoff t A N) ⋏
      le N (top (cutoff t A N) A R)) := by
  have ht : Γ ⊢[PRAAx] le t (cutoff t A N) :=
    le_of_eq_add (d := N+GaussianBetaFiniteEulerAtCutoff.minimumCutoff t A) (by unfold cutoff; ipra_ring)
  have hk : Γ ⊢[PRAAx] le (GaussianBetaFiniteEulerAtCutoff.minimumCutoff t A) (cutoff t A N) :=
    le_of_eq_add (d := t+N) (by unfold cutoff; ipra_ring)
  have hn : Γ ⊢[PRAAx] le N (cutoff t A N) :=
    le_of_eq_add (d := t+GaussianBetaFiniteEulerAtCutoff.minimumCutoff t A) (by unfold cutoff; ipra_ring)
  have upper : Γ ⊢[PRAAx] le (cutoff t A N) (top (cutoff t A N) A R) := by
    dsimp only [top,GaussianGammaIntegralCutoffs.height]
    ipra_le 𝔞(cutoff t A N)+2*𝔞 A+2*𝔞(GaussianGammaIntegralCutoffs.tailCoefficient R)+20
  exact .andI ht (.andI hk (le_trans hn upper))

theorem degree_two (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx] le two N :=
  le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two h.andE₂.andE₁)) h.andE₂.andE₂

theorem original_partition (t z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    GaussianBetaSharpPartition.source (cutoff t A N) A R N :=
  .andI h.andE₁.andE₁ (.andI (degree_two z R B A N h) (cutoff_bounds t A R N).andE₂.andE₂)

theorem factor_growth (t H A R N : PTm n) : Γ ⊢[PRAAx] le H (factor t H A R N) := by
  have cells : Γ ⊢[PRAAx] le one (GaussianGammaEulerCompactQuadrature.conservativeCells (cutoff t A N+num 4) (cutoff t A N) A R) :=
    GaussianCompactRiemannName.mesh_positive _ _ _
  exact le_congr (by ipra_ring) (by dsimp only [factor,GaussianBetaSharpFiniteBinding.multiplier]; ipra_ring)
    (mul_le_mul_right H cells)

theorem mesh_budgets (t H z R B A N : PTm n)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    le one H ⋏
      (le (GaussianBetaFiniteEulerAtCutoff.minimumCells t (cutoff t A N) z R B A N) (factor t H A R N) ⋏
        (le (GaussianBetaMiddleDyadicBudget.minimumMesh t (middleWidth (cutoff t A N) A R N) R) (factor t H A R N) ⋏
          le (GaussianBetaContiguousUpperTailBudget.minimumMesh t R (top (cutoff t A N) A R)) (factor t H A R N))) := by
  let U := GaussianBetaFiniteEulerAtCutoff.minimumCells t (cutoff t A N) z R B A N
  let V := GaussianBetaMiddleDyadicBudget.minimumMesh t (middleWidth (cutoff t A N) A R N) R
  let W := GaussianBetaContiguousUpperTailBudget.minimumMesh t R (top (cutoff t A N) A R)
  have oneBound : Γ ⊢[PRAAx] le one (minimumH t z R B A N) :=
    le_of_eq_add (d := U+V+W) (by dsimp only [minimumH,U,V,W]; ipra_ring)
  have u : Γ ⊢[PRAAx] le U (minimumH t z R B A N) :=
    le_of_eq_add (d := one+V+W) (by dsimp only [minimumH,U,V,W]; ipra_ring)
  have v : Γ ⊢[PRAAx] le V (minimumH t z R B A N) :=
    le_of_eq_add (d := one+U+W) (by dsimp only [minimumH,U,V,W]; ipra_ring)
  have w : Γ ⊢[PRAAx] le W (minimumH t z R B A N) :=
    le_of_eq_add (d := one+U+V) (by dsimp only [minimumH,U,V,W]; ipra_ring)
  have grow := factor_growth (Γ := Γ) t H A R N
  exact .andI (le_trans oneBound hH) (.andI (le_trans (le_trans u hH) grow)
    (.andI (le_trans (le_trans v hH) grow) (le_trans (le_trans w hH) grow)))

theorem factor_positive (t H z R B A N : PTm n)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx] le one (factor t H A R N) :=
  le_trans (mesh_budgets t H z R B A N hH).andE₁ (factor_growth t H A R N)

theorem support_width_positive (E N : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le two N) : Γ ⊢[PRAAx]
    le one (supportWidth E N) := by
  have hn := le_trans (le_succ_self one) hN
  have bound : Γ ⊢[PRAAx] le two (E*N) := le_trans hN
    (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N hE))
  have endpoint := GaussianBetaFiniteEulerComparison.support_width_endpoint E N hE hn
  have eq := natEq endpoint
  ipra_simps
  ipra_le sl bound using
    linear_combination eq

theorem support_cells (t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    le (GaussianBetaFiniteEulerAtCutoff.minimumCells t (cutoff t A N) z R B A N) (supportCount t H A R N) := by
  have positive := support_width_positive (etaDen (cutoff t A N) A R) N
    (GaussianGammaIntegralCutoffs.eta_den_positive _ _ _) (degree_two z R B A N h)
  have grow : Γ ⊢[PRAAx] le (factor t H A R N) (supportCount t H A R N) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (factor t H A R N) positive)
  exact le_trans (mesh_budgets t H z R B A N hH).andE₂.andE₁ grow

theorem low_count_positive (t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    le one (lowWidth (cutoff t A N) A R*factor t H A R N) := by
  let k := cutoff t A N
  have even := GaussianBetaSharpPartition.even_denominator (Γ := Γ) k A R h.andE₁.andE₁
  have twoBound : Γ ⊢[PRAAx] le two (etaDen k A R) :=
    le_congr (one_mul two) ((mul_comm _ _).eqTrans even.eqSymm)
      (mul_le_mul_right two (unit_positive (LeanProofs.IPRA.PTm.monus (A*GaussianGammaIntegralCutoffs.height k A R) one)))
  have endpoint := (GaussianBetaSharpPartition.exact_partition k A R N (original_partition t z R B A N h)).andE₁
  have widthPos : Γ ⊢[PRAAx] le one (lowWidth k A R) := by
    have eq := natEq endpoint
    ipra_simps
    ipra_le sl twoBound using
      linear_combination eq
  exact positive_product _ _ widthPos (factor_positive t H z R B A N hH)

theorem precision_budgets (p t H z R B A N : PTm n)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t H z R B A N) p) : Γ ⊢[PRAAx]
    le (GaussianBetaLowDyadicBudget.minimumPrecision t) p ⋏
      (le (GaussianBetaFiniteEulerAtCutoff.minimumPrecision t (cutoff t A N) z R B A N (supportCount t H A R N)) p ⋏
        (le (GaussianBetaRefinedFixedCompactComparison.referencePrecision (cutoff t A N+num 4) (cutoff t A N) A R) p ⋏
          (le (GaussianBetaContiguousUpperTailBudget.minimumPrecision t R (top (cutoff t A N) A R)) p ⋏
            le (num 4*top (cutoff t A N) A R*unit t) (unit p)))) := by
  let L := GaussianBetaLowDyadicBudget.minimumPrecision t
  let F := GaussianBetaFiniteEulerAtCutoff.minimumPrecision t (cutoff t A N) z R B A N (supportCount t H A R N)
  let I := GaussianBetaRefinedFixedCompactComparison.referencePrecision (cutoff t A N+num 4) (cutoff t A N) A R
  let T := GaussianBetaContiguousUpperTailBudget.minimumPrecision t R (top (cutoff t A N) A R)
  let Q := GaussianFastValueCut.exponent (num 4*top (cutoff t A N) A R) t
  have l : Γ ⊢[PRAAx] le L (minimumPrecision t H z R B A N) :=
    le_of_eq_add (d := F+I+T+Q) (by dsimp only [L,F,I,T,Q,minimumPrecision]; ipra_ring)
  have f : Γ ⊢[PRAAx] le F (minimumPrecision t H z R B A N) :=
    le_of_eq_add (d := L+I+T+Q) (by dsimp only [L,F,I,T,Q,minimumPrecision]; ipra_ring)
  have i : Γ ⊢[PRAAx] le I (minimumPrecision t H z R B A N) :=
    le_of_eq_add (d := L+F+T+Q) (by dsimp only [L,F,I,T,Q,minimumPrecision]; ipra_ring)
  have tBound : Γ ⊢[PRAAx] le T (minimumPrecision t H z R B A N) :=
    le_of_eq_add (d := L+F+I+Q) (by dsimp only [L,F,I,T,Q,minimumPrecision]; ipra_ring)
  have q : Γ ⊢[PRAAx] le Q (minimumPrecision t H z R B A N) :=
    le_of_eq_add (d := L+F+I+T) (by dsimp only [L,F,I,T,Q,minimumPrecision]; ipra_ring)
  exact .andI (le_trans l hp) (.andI (le_trans f hp) (.andI (le_trans i hp)
    (.andI (le_trans tBound hp) (le_trans (GaussianFastValueCut.query_budget _ _)
      (GaussianExponentialReference.unit_monotone (le_trans q hp))))))

theorem finite_binding_time_budget (p t H z R B A N : PTm n)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t H z R B A N) p) : Γ ⊢[PRAAx]
    le (two*top (cutoff t A N) A R*unit t) (unit p) :=
  le_trans (le_of_eq_add (d := two*top (cutoff t A N) A R*unit t) (by ipra_ring))
    (precision_budgets p t H z R B A N hp).andE₂.andE₂.andE₂.andE₂

theorem split_time_budget (p t H z R B A N : PTm n)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t H z R B A N) p) : Γ ⊢[PRAAx]
    le (num 4*GaussianGammaCompactQuadratureBoundary.width (cutoff t A N) A R*unit t)
      (etaDen (cutoff t A N) A R*unit p) := by
  have clock := (precision_budgets p t H z R B A N hp).andE₂.andE₂.andE₂.andE₂
  have width := GaussianGammaCompactQuadratureBoundary.width_bound (Γ := Γ) (cutoff t A N) A R
  ipra_le (𝔞(etaDen (cutoff t A N) A R))*sl clock+(4*𝔞(unit t))*sl width

theorem middle_time_budget (p t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t H z R B A N) p) : Γ ⊢[PRAAx]
    le (two*middleWidth (cutoff t A N) A R N*unit t) (etaDen (cutoff t A N) A R*unit p) := by
  let k := cutoff t A N
  let C := middleWidth k A R N
  let E := etaDen k A R
  have part := original_partition t z R B A N h
  have endpoint := (GaussianBetaSharpPartition.exact_partition k A R N part).andE₂.andE₁
  have halfBound := (GaussianBetaSharpPartition.half_boundary_order k A R N part.andE₁ part.andE₂.andE₁).andE₂
  have right : Γ ⊢[PRAAx] le (E*N) (E*top k A R) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right E part.andE₂.andE₂)
  have width : Γ ⊢[PRAAx] le C (E*top k A R) := le_trans (le_add_left C E)
    (le_trans (le_congr endpoint.eqSymm (.eqRefl _) halfBound) right)
  have clock := finite_binding_time_budget p t H z R B A N hp
  ipra_le (𝔞 E)*sl clock+(2*𝔞(unit t))*sl width

theorem tail_source (t H z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N)
    (hH : Γ ⊢[PRAAx] le (minimumH t z R B A N) H) : Γ ⊢[PRAAx]
    GaussianBetaContiguousUpperTail.source z R B A N (top (cutoff t A N) A R) (factor t H A R N) :=
  .andI h.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁ (.andI (degree_two z R B A N h)
    (.andI (cutoff_bounds t A R N).andE₂.andE₂ (factor_positive t H z R B A N hH))))

theorem actual_sharp_cutoff_dominates_fixed_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (cutoff (var 0) (var 1) (var 3)) ⋏
      (le (GaussianBetaFiniteEulerAtCutoff.minimumCutoff (var 0) (var 1)) (cutoff (var 0) (var 1) (var 3)) ⋏
        le (var 3) (top (cutoff (var 0) (var 1) (var 3)) (var 1) (var 2)))) :=
  closeUniv 4 (cutoff_bounds _ _ _ _)

theorem actual_sharp_source_only_support_mesh_schedule_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      ((source (var 2) (var 3) (var 4) (var 5) (var 6) ⋏
        le (minimumH (var 0) (var 2) (var 3) (var 4) (var 5) (var 6)) (var 1)) ⟶
        (le (GaussianBetaFiniteEulerAtCutoff.minimumCells (var 0) (cutoff (var 0) (var 5) (var 6))
            (var 2) (var 3) (var 4) (var 5) (var 6)) (supportCount (var 0) (var 1) (var 5) (var 3) (var 6)) ⋏
          (le one (lowWidth (cutoff (var 0) (var 5) (var 6)) (var 5) (var 3)*factor (var 0) (var 1) (var 5) (var 3) (var 6)) ⋏
            GaussianBetaSharpPartition.source (cutoff (var 0) (var 5) (var 6)) (var 5) (var 3) (var 6)))) :=
  closeUniv 7 (.impI (.andI (support_cells _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (.andI (low_count_positive _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
      (original_partition _ _ _ _ _ _ Prf.hyp0.andE₁))))

theorem actual_sharp_evaluator_clock_spends_original_split_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (le (minimumPrecision (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 0) ⟶
        le (num 4*GaussianGammaCompactQuadratureBoundary.width (cutoff (var 1) (var 6) (var 7)) (var 6) (var 4)*unit (var 1))
          (etaDen (cutoff (var 1) (var 6) (var 7)) (var 6) (var 4)*unit (var 0))) :=
  closeUniv 8 (.impI (split_time_budget _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpCofinalSchedule
