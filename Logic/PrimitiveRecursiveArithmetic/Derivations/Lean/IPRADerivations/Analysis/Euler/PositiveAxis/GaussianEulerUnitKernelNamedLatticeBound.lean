import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionIndependentQuadrature

/-!
# The actual compact unit name versus an independent literal lattice

Specialize the genuine independent-grid comparison to the original
compact sampler's actual mesh and evaluator precision. Native panel
guards supply K<=M. The exact safe-count arithmetic gives L/M plus
three requested compact dyadics and four lattice dyadics. A source
mesh/precision threshold yields eight compact dyadics, including K=0.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNamedLatticeBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitKernelCompactName (source lipschitz nameF data)
open GaussianCompactRiemannName (mesh precision)
open GaussianCompactSafeGridComparison (safeCount)
open GaussianEulerUnitSubstitutionIndependentQuadrature (gridNumerator gridDenominator)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numerator (s q L M : PTm n) : PTm n := L*unit s*unit q+num 3*M*unit q+num 4*M*unit s
def denominator (s q M : PTm n) : PTm n := M*unit s*unit q
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (s q L M : PTm n) :
    Syn.subst σ (numerator s q L M) = numerator (Syn.subst σ s) (Syn.subst σ q) (Syn.subst σ L) (Syn.subst σ M) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (s q M : PTm n) :
    Syn.subst σ (denominator s q M) = denominator (Syn.subst σ s) (Syn.subst σ q) (Syn.subst σ M) := by simp [denominator]

theorem denominator_positive (s q M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx] le one (denominator s q M) :=
  positive_product _ _ (positive_product _ _ hM (unit_positive s)) (unit_positive q)

theorem count_le_safe (K : PTm n) : Γ ⊢[PRAAx] le K (safeCount K) := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le (safeCount K))
  · exact le_congr (.eqRefl _) Prf.hyp0 (le_refl K)

/-- Native exact coarsening of the genuine safe-grid comparison. -/
theorem grid_budget (s q r K H M L : PTm n) (hK : Γ ⊢[PRAAx] le K M)
    (hH : Γ ⊢[PRAAx] le (L*unit s) H) (hr : Γ ⊢[PRAAx] le (unit s) (unit r)) : Γ ⊢[PRAAx]
    le (gridNumerator q r K H M L*denominator s q M)
      (numerator s q L M*gridDenominator q r K H M) := by
  have square := sq_le_sq hK
  have mixed := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hK (count_le_safe (Γ := Γ) K)
  unfold gridNumerator gridDenominator GaussianCompactSafeGridComparison.numerator GaussianCompactSafeGridComparison.denominator
    GaussianCompactUniformGridComparison.numerator GaussianCompactUniformGridComparison.denominator numerator denominator
  ipra_le (𝔞 L*𝔞 M*𝔞(unit s)*𝔞 H*𝔞(unit q)^2*𝔞(unit r))*sl mixed+
    (𝔞 L*𝔞 M*𝔞(safeCount K)*𝔞(unit s)*𝔞(unit q)^2*𝔞(unit r))*sl square+
    (𝔞 M^3*𝔞(safeCount K)*𝔞(unit q)^2*𝔞(unit r))*sl hH+
    (2*𝔞 M^2*𝔞(safeCount K)*𝔞 H*𝔞(unit s)*𝔞(unit q)^2)*sl hK+
    (2*𝔞 M^3*𝔞(safeCount K)*𝔞 H*𝔞(unit q)^2)*sl hr+
    (4*𝔞 M^2*𝔞(safeCount K)*𝔞 H*𝔞(unit s)*𝔞(unit q)*𝔞(unit r))*sl hK

theorem original_mesh_budget (s L : PTm n) : Γ ⊢[PRAAx] le (L*unit s) (mesh s L one) := by
  have grow := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) s (s+num 6) (le_add_right _ _)
  have first : Γ ⊢[PRAAx] le (L*unit s) (unit (s+num 6)*L*one*one) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right L grow)
  exact le_trans first (GaussianCompactRiemannName.mesh_cost s L one)

/-- Original name_s versus the literal lattice_q, with no count guard. -/
theorem original_bound (s q z R B a K M G : PTm n) (h : Γ ⊢[PRAAx] source z R B a K M G) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF s (data z R B a K M G)) (GaussianEulerUnitKernelLatticeSum.lattice q K z B a M)
      (numerator s q (lipschitz R G) M) (denominator s q M) := by
  let L := lipschitz R G
  let H := mesh s L one
  let r := precision s one
  have hM := h.andE₂.andE₁
  have hH := GaussianCompactRiemannName.mesh_positive (Γ := Γ) s L one
  have hK : Γ ⊢[PRAAx] le K M := le_trans (le_add_left K a) (GaussianEulerUnitKernelCompactName.right_endpoint_le_one z R B a K M G h)
  have later : Γ ⊢[PRAAx] le s r := le_of_eq_add (d := one+num 6) (by dsimp only [r,precision]; ipra_ring)
  have old := GaussianEulerUnitSubstitutionIndependentQuadrature.original_lattice_grid q r z R B a K M G H h hH
  have coarsened := distance_radius_mono _ _ _ _ (numerator s q L M) (denominator s q M)
    (GaussianCompactSafeGridComparison.denominator_positive q r K H M hM hH) (denominator_positive s q M hM)
    (grid_budget s q r K H M L hK (original_mesh_budget s L) (GaussianExponentialReference.unit_monotone later)) old
  exact distance_congr (GaussianEulerUnitKernelCompactName.name_at s z R B a K M G).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ (denominator_positive s q M hM) coarsened)

/-- A computed lattice denominator and any later lattice query pay the
entire original comparison with eight requested compact dyadics. -/
theorem original_dyadic_bound (s q z R B a K M G : PTm n) (h : Γ ⊢[PRAAx] source z R B a K M G)
    (hM : Γ ⊢[PRAAx] le (lipschitz R G*unit s) M) (hq : Γ ⊢[PRAAx] le s q) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF s (data z R B a K M G)) (GaussianEulerUnitKernelLatticeSum.lattice q K z B a M)
      (num 8) (unit s) := by
  have grow := GaussianExponentialReference.unit_monotone hq
  apply distance_radius_mono _ _ _ _ _ _ (denominator_positive s q M h.andE₂.andE₁) (unit_positive s) _
    (original_bound s q z R B a K M G h)
  unfold numerator denominator
  ipra_le (𝔞(unit s)*𝔞(unit q))*sl hM+(4*𝔞 M*𝔞(unit s))*sl grow

theorem actual_original_compact_unit_name_lattice_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (GaussianEulerUnitKernelLatticeSum.lattice (var 1) (var 6) (var 2) (var 4) (var 5) (var 7))
        (numerator (var 0) (var 1) (lipschitz (var 3) (var 8)) (var 7)) (denominator (var 0) (var 1) (var 7))) :=
  closeUniv 9 (.impI (original_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_compact_unit_name_lattice_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
      (le (lipschitz (var 3) (var 8)*unit (var 0)) (var 7) ⋏ le (var 0) (var 1))) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (GaussianEulerUnitKernelLatticeSum.lattice (var 1) (var 6) (var 2) (var 4) (var 5) (var 7)) (num 8) (unit (var 0))) :=
  closeUniv 9 (.impI (original_dyadic_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelNamedLatticeBound
