import IPRADerivations.Analysis.Beta.GaussianBetaPrimitiveCompactGrid

/-!
# Computed mesh and precision for the original beta quadrature

For any requested dyadic error, choose the positive mesh count from
the actual compact curvature and the native small-step guard. Choose
the common evaluation precision to absorb the sum of the observation
errors. The original affine mesh, beta rows and endpoint programs are
used at these explicit parameters.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveCompactGridAccuracy

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaPrimitiveCompactGrid (K Z)
open GaussianBetaPrimitiveGridTelescope (gridEndpoint quadratureScaled cellNumerator globalDenominator)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A a C E T N : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    (le one E ⋏ le one N ⋏ le one a ⋏ le (a+C) (E*T) ⋏ le (a+C) (E*N))

def meshBase (z R B C E T N : PTm n) : PTm n := K z R B E T N*C*C+(R+one)*C+one
def cells (t z R B C E T N : PTm n) : PTm n := meshBase z R B C E T N*unit (succ t)
def precisionAt (t z B N M : PTm n) : PTm n := GaussianFastValueCut.exponent (num 6*Z z B N*M) (succ t)
def precision (t z R B C E T N : PTm n) : PTm n :=
  precisionAt t z B N (cells t z R B C E T N)

theorem mesh_positive (t z R B C E T N : PTm n) : Γ ⊢[PRAAx] le one (cells t z R B C E T N) := by
  have base : Γ ⊢[PRAAx] le one (meshBase z R B C E T N) :=
    le_congr (.eqRefl _) (by unfold meshBase; ipra_ring)
      (le_add_right one (K z R B E T N*C*C+(R+one)*C))
  exact positive_product _ _ base (unit_positive (succ t))

theorem small_step (t z R B a C E T N : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx]
    le ((R+one)*C) (a*cells t z R B C E T N) := by
  let d := meshBase z R B C E T N
  let M := cells t z R B C E T N
  have first : Γ ⊢[PRAAx] le ((R+one)*C) d :=
    le_congr (.eqRefl _) (by dsimp only [d,meshBase]; ipra_ring) (le_add_right ((R+one)*C) (K z R B E T N*C*C+one))
  have second : Γ ⊢[PRAAx] le d M :=
    le_congr (one_mul d) (by dsimp only [M,cells]; ipra_ring) (mul_le_mul_right d (unit_positive (succ t)))
  have third : Γ ⊢[PRAAx] le M (a*M) := le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right M ha)
  exact le_trans first (le_trans second third)

theorem radius_budget (t p z R B C E T M N : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hm : Γ ⊢[PRAAx] le (cells t z R B C E T N) M) (hp : Γ ⊢[PRAAx] le (precisionAt t z B N M) p) :
    Γ ⊢[PRAAx] le (cellNumerator p C E M (K z R B E T N) (Z z B N)*unit (succ t)) (two*globalDenominator p E M) := by
  let L := K z R B E T N*C*C
  let d := meshBase z R B C E T N
  let W := unit (succ t)
  let P := unit p
  have base : Γ ⊢[PRAAx] le L d :=
    le_congr (.eqRefl _) (by dsimp only [d,meshBase,L]; ipra_ring) (le_add_right L ((R+one)*C+one))
  have e2 := positive_product _ _ hE hE
  have first : Γ ⊢[PRAAx] le (L*W) (E*E*M) :=
    le_trans (mul_le_mul_right W base)
      (le_trans hm (le_congr (one_mul M) (.eqRefl _) (mul_le_mul_right M e2)))
  have second : Γ ⊢[PRAAx] le (num 6*Z z B N*M*W) P :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone hp)
  have add := add_le_add₂ (mul_le_mul_right P first) (mul_le_mul_right (E*E*M) second)
  change Γ ⊢[PRAAx] le (cellNumerator p C E M (K z R B E T N) (Z z B N)*W) (two*globalDenominator p E M)
  exact le_congr (by dsimp only [cellNumerator,L]; ipra_ring) (by dsimp only [globalDenominator,P]; ipra_ring) add

/-- Preserve the same computed error at any sufficiently fine mesh and
any observation at or above its computed precision. -/
theorem original_grid_dyadic_accuracy_at (t p z R B A a C E T M N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a C E T N) (hm : Γ ⊢[PRAAx] le (cells t z R B C E T N) M)
    (hp : Γ ⊢[PRAAx] le (precisionAt t z B N M) p) : Γ ⊢[PRAAx]
    distanceBounded (qsub (gridEndpoint M p z B a C E M N) (gridEndpoint zero p z B a C E M N))
      (quadratureScaled p z B a C E M N) one (unit t) := by
  have hE := h.andE₂.andE₁
  have hM := le_trans (mesh_positive t z R B C E T N) hm
  have width : Γ ⊢[PRAAx] le ((R+one)*C) (a*M) :=
    le_trans (small_step t z R B a C E T N h.andE₂.andE₂.andE₂.andE₁)
      (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right a hm))
  have guard : Γ ⊢[PRAAx] GaussianBetaPrimitiveCompactGrid.source z R B A a C E T M N :=
    .andI h.andE₁ (.andI (.andI hE (.andI hM h.andE₂.andE₂.andE₁))
      (.andI h.andE₂.andE₂.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₂.andE₂.andE₁
        (.andI h.andE₂.andE₂.andE₂.andE₂.andE₂ width))))
  have actual := GaussianBetaPrimitiveCompactGrid.original_compact_grid p z R B A a C E T M N guard
  have d : Γ ⊢[PRAAx] le one (globalDenominator p E M) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ hE hE) hM) (unit_positive p)
  have pair := distance_radius_mono _ _ _ _ _ _ d (unit_positive (succ t)) (radius_budget t p z R B C E T M N hE hm hp) actual
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive (succ t)) (unit_positive t)
    (le_of_eq_add (d := zero) ((congrMul (.eqRefl one) (pw_succ two t)).eqTrans (by unfold unit; ipra_ring))) pair

theorem original_grid_dyadic_accuracy (t z R B A a C E T N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A a C E T N) : Γ ⊢[PRAAx]
    let M := cells t z R B C E T N
    let p := precision t z R B C E T N
    distanceBounded (qsub (gridEndpoint M p z B a C E M N) (gridEndpoint zero p z B a C E M N))
      (quadratureScaled p z B a C E M N) one (unit t) :=
  original_grid_dyadic_accuracy_at _ _ _ _ _ _ _ _ _ _ _ _ h (le_refl _) (le_refl _)

theorem original_Beta_primitive_grid_finer_accuracy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 11) ⋏
      le (cells (var 0) (var 2) (var 3) (var 4) (var 7) (var 8) (var 9) (var 11)) (var 10) ⋏
      le (precisionAt (var 0) (var 2) (var 4) (var 11) (var 10)) (var 1)) ⟶
      distanceBounded
        (qsub (gridEndpoint (var 10) (var 1) (var 2) (var 4) (var 6) (var 7) (var 8) (var 10) (var 11))
          (gridEndpoint zero (var 1) (var 2) (var 4) (var 6) (var 7) (var 8) (var 10) (var 11)))
        (quadratureScaled (var 1) (var 2) (var 4) (var 6) (var 7) (var 8) (var 10) (var 11)) one (unit (var 0))) :=
  closeUniv 12 (.impI (original_grid_dyadic_accuracy_at _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem original_Beta_primitive_grid_computed_accuracy_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      let M := cells (var 0) (var 1) (var 2) (var 3) (var 6) (var 7) (var 8) (var 9)
      let p := precision (var 0) (var 1) (var 2) (var 3) (var 6) (var 7) (var 8) (var 9)
      distanceBounded
        (qsub (gridEndpoint M p (var 1) (var 3) (var 5) (var 6) (var 7) M (var 9))
          (gridEndpoint zero p (var 1) (var 3) (var 5) (var 6) (var 7) M (var 9)))
        (quadratureScaled p (var 1) (var 3) (var 5) (var 6) (var 7) M (var 9)) one (unit (var 0))) :=
  closeUniv 10 (.impI (original_grid_dyadic_accuracy _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveCompactGridAccuracy
