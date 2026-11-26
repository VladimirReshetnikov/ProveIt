import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionLatticeRate

/-!
# Independent effective choices for the original unit-lattice comparison

Choose the original time-grid count first. Then the chart read query,
lattice denominator and kernel query have separate explicit lower bounds.
Their native budgets imply all genuine original cut-domain guards and
make each of the four separated finite errors at most the chosen dyadic.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionLatticeRate (meshCoefficient queryCoefficient latticeCoefficient)
open GaussianEulerUnitSubstitutionLatticeGeometry (disk start count)
open GaussianEulerUnitDecayInput (clock compactDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def minimumCount (s R C E T : PTm n) : PTm n := meshCoefficient R C E T*unit s
def minimumChart (s N R E T : PTm n) : PTm n := GaussianFastValueCut.exponent (queryCoefficient N R E T+num 4*N) s
def minimumLattice (s N R E T : PTm n) : PTm n := (latticeCoefficient N R E T+disk E T)*unit s
def source (s k q N z R B a C E T M : PTm n) : Fm PTm n :=
  GaussianEulerUnitSubstitutionDensity.source z R B a C E T N ⋏
    (le (minimumCount s R C E T) N ⋏ (le (minimumChart s N R E T) k ⋏
      (le (minimumLattice s N R E T) M ⋏ le s q)))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (s k q N z R B a C E T M : PTm n) :
    (source s k q N z R B a C E T M).subst σ = source (Syn.subst σ s) (Syn.subst σ k) (Syn.subst σ q)
      (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a)
      (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by
  simp [source,minimumCount,minimumChart,minimumLattice]

theorem chart_budget (s k N R E T : PTm n) (h : Γ ⊢[PRAAx] le (minimumChart s N R E T) k) : Γ ⊢[PRAAx]
    le ((queryCoefficient N R E T+num 4*N)*unit s) (unit k) :=
  le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone h)

theorem original_source (s k q N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source s k q N z R B a C E T M) :
    Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionLatticeGeometry.source k N z R B a C E T M := by
  let G := compactDenominator E T
  let Q := queryCoefficient N R E T+num 4*N
  have kb : Γ ⊢[PRAAx] le (Q*unit s) (unit k) := chart_budget s k N R E T h.andE₂.andE₂.andE₁
  have lower : Γ ⊢[PRAAx] le ((two*two)*G*N) (G*Q*unit s) := by
    dsimp only [Q]
    ipra_le 4*𝔞 (G*N)*sl (unit_positive (Γ := Γ) s)+𝔞 (G*queryCoefficient N R E T*unit s)
  have lifted : Γ ⊢[PRAAx] le (G*Q*unit s) (G*unit k) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right G kb)
  have chart : Γ ⊢[PRAAx] le ((two*two)*G*N) (unit (clock k E T)) :=
    le_trans lower (le_trans lifted (GaussianFastValueCut.query_budget G k))
  have ml : Γ ⊢[PRAAx] le (disk E T) (minimumLattice s N R E T) := by
    unfold minimumLattice
    ipra_le 𝔞 (disk E T)*sl (unit_positive (Γ := Γ) s)+𝔞 (latticeCoefficient N R E T*unit s)
  exact .andI h.andE₁ (.andI chart (le_trans ml h.andE₂.andE₂.andE₂.andE₁))

private theorem four_terms_budget (X U M W A B C S : PTm n)
    (h₁ : Γ ⊢[PRAAx] le (A*S) X) (h₂ : Γ ⊢[PRAAx] le (B*S) U)
    (h₃ : Γ ⊢[PRAAx] le (C*S) M) (h₄ : Γ ⊢[PRAAx] le S W) : Γ ⊢[PRAAx]
    le ((A*U*M*W+B*X*M*W+C*X*U*W+X*U*M)*S) (num 4*(X*U*M*W)) := by
  ipra_le 𝔞 (U*M*W)*sl h₁+𝔞 (X*M*W)*sl h₂+𝔞 (X*U*W)*sl h₃+𝔞 (X*U*M)*sl h₄

theorem normalized_budget (s k q N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source s k q N z R B a C E T M) : Γ ⊢[PRAAx]
    le (GaussianEulerUnitSubstitutionLatticeRate.numerator k q N R C E T M*unit s)
      (num 4*GaussianEulerUnitSubstitutionLatticeRate.denominator k q N E M) := by
  have hs := original_source s k q N z R B a C E T M h
  have hE := hs.andE₁.andE₁.andE₁.andE₂.andE₁
  have ne : Γ ⊢[PRAAx] le N (E*N) := le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right N hE)
  have h₁ : Γ ⊢[PRAAx] le (meshCoefficient R C E T*unit s) (E*N) := le_trans h.andE₂.andE₁ ne
  have h₂ : Γ ⊢[PRAAx] le (queryCoefficient N R E T*unit s) (unit k) :=
    le_trans (le_of_eq_add (d := num 4*N*unit s) (by ipra_ring)) (chart_budget s k N R E T h.andE₂.andE₂.andE₁)
  have h₃ : Γ ⊢[PRAAx] le (latticeCoefficient N R E T*unit s) M :=
    le_trans (le_of_eq_add (d := disk E T*unit s) (by unfold minimumLattice; ipra_ring)) h.andE₂.andE₂.andE₂.andE₁
  have h₄ := GaussianExponentialReference.unit_monotone h.andE₂.andE₂.andE₂.andE₂
  simpa only [GaussianEulerUnitSubstitutionLatticeRate.numerator,GaussianEulerUnitSubstitutionLatticeRate.denominator] using
    four_terms_budget (E*N) (unit k) M (unit q) (meshCoefficient R C E T) (queryCoefficient N R E T)
      (latticeCoefficient N R E T) (unit s) h₁ h₂ h₃ h₄

theorem original_scheduled_bound (s k q N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source s k q N z R B a C E T M) :
    Γ ⊢[PRAAx] distanceBounded
      (GaussianEulerUnitKernelLatticeSum.lattice q (count k N a C E T M) z B (start k N a C E T M) M)
      (GaussianEulerUnitSubstitutionDensity.density (clock k E T) N z B a C E) (num 4) (unit s) := by
  have hs := original_source s k q N z R B a C E T M h
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (GaussianEulerUnitSubstitutionLatticeRate.rate_denominator_positive k q N z R B a C E T M hs)
    (unit_positive s) (normalized_budget s k q N z R B a C E T M h)
    (GaussianEulerUnitSubstitutionLatticeRate.original_finite_bound k q N z R B a C E T M hs)

theorem actual_original_unit_lattice_effective_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⟶
      distanceBounded (GaussianEulerUnitKernelLatticeSum.lattice (var 2)
        (count (var 1) (var 3) (var 7) (var 8) (var 9) (var 10) (var 11))
        (var 4) (var 6) (start (var 1) (var 3) (var 7) (var 8) (var 9) (var 10) (var 11)) (var 11))
      (GaussianEulerUnitSubstitutionDensity.density (clock (var 1) (var 9) (var 10)) (var 3) (var 4) (var 6) (var 7) (var 8) (var 9))
      (num 4) (unit (var 0))) :=
  closeUniv 12 (.impI (original_scheduled_bound _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeSchedule
