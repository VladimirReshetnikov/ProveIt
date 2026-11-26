import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionLatticeComparison
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelLatticeComparison
import IPRADerivations.Analysis.Integration.GaussianCompactSafeGridComparison

/-!
# An independently chosen ordinary unit quadrature versus the original density

The actual floor-cut interval is retained. Its original lattice at query
q is compared with an ordinary quadrature of any positive count H and
independent query r. The intermediate actual count may be zero: the
proved safe-count identity handles it without an additional source guard.
Combining the genuine lattice/density estimate preserves the original
coarse decay clock and the two independent unit-kernel query precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionIndependentQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionLatticeGeometry (source start count disk)
open GaussianEulerUnitKernelCompactName (evaluatorF fixedData)
open GaussianCompactRiemannName (quadrature)
open GaussianCompactSafeGridComparison (safeCount)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def ordinary (r H k N z B a C E T M : PTm n) : PTm n := quadrature evaluatorF r H
  (start k N a C E T M) (count k N a C E T M) M (fixedData z B)
def gridNumerator (q r K H M L : PTm n) : PTm n :=
  GaussianCompactSafeGridComparison.numerator q r K H M L+two*K*M*safeCount K*H*unit r
def gridDenominator (q r K H M : PTm n) : PTm n := GaussianCompactSafeGridComparison.denominator q r K H M

def numerator (k q r N H R a C E T M : PTm n) : PTm n :=
  gridNumerator q r (count k N a C E T M) H M (GaussianEulerUnitKernelCompactName.lipschitz R (disk E T))*
    GaussianEulerUnitSubstitutionLatticeComparison.denominator k q N E T M+
  GaussianEulerUnitSubstitutionLatticeComparison.numerator k q N R C E T M*gridDenominator q r (count k N a C E T M) H M

def denominator (k q r N H a C E T M : PTm n) : PTm n :=
  gridDenominator q r (count k N a C E T M) H M*GaussianEulerUnitSubstitutionLatticeComparison.denominator k q N E T M

@[simp] theorem subst_ordinary {m : ℕ} (σ : Fin n → PTm m) (r H k N z B a C E T M : PTm n) :
    Syn.subst σ (ordinary r H k N z B a C E T M) = ordinary (Syn.subst σ r) (Syn.subst σ H) (Syn.subst σ k)
      (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by simp [ordinary]
@[simp] theorem subst_gridNumerator {m : ℕ} (σ : Fin n → PTm m) (q r K H M L : PTm n) :
    Syn.subst σ (gridNumerator q r K H M L) = gridNumerator (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ K)
      (Syn.subst σ H) (Syn.subst σ M) (Syn.subst σ L) := by simp [gridNumerator]
@[simp] theorem subst_gridDenominator {m : ℕ} (σ : Fin n → PTm m) (q r K H M : PTm n) :
    Syn.subst σ (gridDenominator q r K H M) = gridDenominator (Syn.subst σ q) (Syn.subst σ r) (Syn.subst σ K)
      (Syn.subst σ H) (Syn.subst σ M) := by simp [gridDenominator]

/-- The lattice query q and the ordinary quadrature query r are unrelated.
The actual lattice count K may be zero. -/
theorem original_lattice_grid (q r z R B a K M G H : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactName.source z R B a K M G)
    (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerUnitKernelLatticeSum.lattice q K z B a M)
      (quadrature evaluatorF r H a K M (fixedData z B))
      (gridNumerator q r K H M (GaussianEulerUnitKernelCompactName.lipschitz R G)) (gridDenominator q r K H M) := by
  let L := GaussianEulerUnitKernelCompactName.lipschitz R G
  let D := gridDenominator q r K H M
  let A := two*K*M*safeCount K*H*unit r
  have hM := h.andE₂.andE₁
  have hd : Γ ⊢[PRAAx] le one D := GaussianCompactSafeGridComparison.denominator_positive q r K H M hM hH
  have hn := unit_positive (Γ := Γ) q
  have oldDen : Γ ⊢[PRAAx] le one (M*unit q*unit q) := positive_product _ _ (positive_product _ _ hM hn) hn
  have old := GaussianEulerUnitKernelLatticeComparison.original_comparison q q z R B a K M G h
  have lattice := distance_radius_mono _ _ _ _ A D oldDen hd
    (le_of_eq_add (d := zero) (by dsimp only [A,D,gridDenominator,GaussianCompactSafeGridComparison.denominator,
        GaussianCompactUniformGridComparison.denominator,GaussianEulerUnitKernelLatticeComparison.numerator,
        GaussianEulerUnitKernelLatticeComparison.denominator]; ipra_ring)) old
  have grids := GaussianCompactSafeGridComparison.original_comparison evaluatorF q r K H a M L (fixedData z B)
    (GaussianEulerUnitKernelCompactName.start_positive z R B a K M G h) hM hH
    (GaussianEulerUnitKernelCompactName.sampled_modulus z R B a K M G h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [A,gridNumerator]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd lattice grids)

theorem original_denominator_positive (k q r N H z R B a C E T M : PTm n)
    (h : Γ ⊢[PRAAx] source k N z R B a C E T M) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le one (denominator k q r N H a C E T M) :=
  positive_product _ _
    (GaussianCompactSafeGridComparison.denominator_positive q r _ H M (GaussianEulerUnitSubstitutionLatticeGeometry.denominator_positive _ _ _ _ _ _ _ _ _ _ h) hH)
    (positive_product _ _ (GaussianEulerUnitSubstitutionLatticeRows.anchor_denominator_positive k q N z R B a C E T M h)
      (GaussianEulerUnitSubstitutionLatticeComparison.width_denominator_positive k N z R B a C E T M h))

/-- Any independently chosen positive ordinary unit-grid count H on the
actual floor interval has an explicit bound to the unchanged density. -/
theorem original_comparison (k q r N H z R B a C E T M : PTm n)
    (h : Γ ⊢[PRAAx] source k N z R B a C E T M) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    distanceBounded (ordinary r H k N z B a C E T M)
      (GaussianEulerUnitSubstitutionDensity.density (GaussianEulerUnitDecayInput.clock k E T) N z B a C E)
      (numerator k q r N H R a C E T M) (denominator k q r N H a C E T M) := by
  let K := count k N a C E T M
  let L := GaussianEulerUnitKernelCompactName.lipschitz R (disk E T)
  have hM := GaussianEulerUnitSubstitutionLatticeGeometry.denominator_positive _ _ _ _ _ _ _ _ _ _ h
  have hd := GaussianCompactSafeGridComparison.denominator_positive q r K H M hM hH
  have hb := positive_product _ _ (GaussianEulerUnitSubstitutionLatticeRows.anchor_denominator_positive k q N z R B a C E T M h)
    (GaussianEulerUnitSubstitutionLatticeComparison.width_denominator_positive k N z R B a C E T M h)
  have grid := original_lattice_grid q r z R B (start k N a C E T M) K M (disk E T) H
    (GaussianEulerUnitSubstitutionLatticeGeometry.compact_interval_source k N z R B a C E T M h) hH
  exact GaussianEulerUnitSubstitutionLatticeComparison.add_errors _ _ _ _ _ _ _ hd hb
    (distance_symmetric _ _ _ _ hd grid)
    (GaussianEulerUnitSubstitutionLatticeComparison.original_finite_bound k q N z R B a C E T M h)

theorem actual_independently_chosen_unit_quadrature_density_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((source (var 0) (var 3) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏ le one (var 4)) ⟶
      distanceBounded (ordinary (var 2) (var 4) (var 0) (var 3) (var 5) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (GaussianEulerUnitSubstitutionDensity.density (GaussianEulerUnitDecayInput.clock (var 0) (var 10) (var 11))
          (var 3) (var 5) (var 7) (var 8) (var 9) (var 10))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 6) (var 8) (var 9) (var 10) (var 11) (var 12))
        (denominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 8) (var 9) (var 10) (var 11) (var 12))) :=
  closeUniv 13 (.impI (original_comparison _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionIndependentQuadrature
