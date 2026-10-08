import GowersSzemeredi.Proofs16PolynomialVarietyOscillation
import GowersSzemeredi.Proofs16PolynomialRecurrenceProfile

/-! Power-width good cells for multilinear variety phases.

Integer rounding turns the minimum-width oscillation partition into a
power-width profile. The threshold depends only on the radius and number
of conditions, with fixed existential dimension constants. Mixed phases
must be multilinear on the given parent; local Freiman linearity alone
is not assumed to imply this.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16PolynomialVarietyExponent (p q : Nat) : Real :=
  ((2 * (p * (q + 1) ^ 8) : Nat) : Real)⁻¹

def section16PolynomialVarietyThreshold (C p q : Nat) (rho : Real) : Nat :=
  (max (C * (q + 1)) (Nat.ceil (8 / rho))) ^ (2 * (p * (q + 1) ^ 8))

theorem section16PolynomialVarietyExponent_pos {p : Nat} (hp : 0 < p) (q : Nat) :
    0 < section16PolynomialVarietyExponent p q := by
  unfold section16PolynomialVarietyExponent
  positivity

/-- Large parents admit good cells of a reciprocal-polynomial width power,
provided each mixed variety phase is multilinear on that parent. -/
theorem exists_polynomial_variety_good_partition :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N : Nat) [NeZero N] (Gamma Psi : Finset (ZMod N)) (r : Nat)
    (L : Fin r → ZMod N → ZMod N) (rho : Real), 0 < rho →
    ∀ P : Box N 2, P.IsProper →
      (∀ i, MultilinearOn P.carrier (fun x : Point N 2 => L i (x 1) * x 0)) →
      section16PolynomialVarietyThreshold C p (Gamma.card + Psi.card + r) rho ≤ P.width →
      ∃ M : Nat, ∃ Q : Fin M → Box N 2,
        IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, (P.width : Real) ^ section16PolynomialVarietyExponent p
          (Gamma.card + Psi.card + r) ≤ (Q j).width) ∧
        ∀ j, CellGood (bilinearBohrVariety Gamma Psi L (rho / 2))
          (bilinearBohrVariety Gamma Psi L rho) (Q j) := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_polynomial_variety_oscillation_partition
  let C := Nat.ceil K
  have hKC : K ≤ (C : Real) := Nat.le_ceil K
  have hC : 2 ≤ C := by exact_mod_cast hK.trans hKC
  refine ⟨C, p, hC, hp, ?_⟩
  intro N _ Gamma Psi r L rho hrho P hP hL hlarge
  let q := Gamma.card + Psi.card + r
  let E := p * (q + 1) ^ 8
  let B := max (C * (q + 1)) (Nat.ceil (8 / rho))
  have hE : 0 < E := Nat.mul_pos hp (by positivity)
  have hB : 2 ≤ B := (hC.trans (Nat.le_mul_of_pos_right C (by omega))).trans (le_max_left _ _)
  obtain ⟨H, hH, hBH, hbudget, hroot⟩ := exists_rounded_power_scale B E P.width hB hE hlarge
  have hscale : K * ((q : Real) + 1) ≤ H := by
    calc
      _ ≤ (C : Real) * ((q : Real) + 1) := mul_le_mul_of_nonneg_right hKC (by positivity)
      _ ≤ H := by exact_mod_cast (le_max_left (C * (q + 1)) (Nat.ceil (8 / rho))).trans hBH
  have hrad : 8 ≤ rho * (H : Real) := by
    have h : 8 / rho ≤ (H : Real) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right (C * (q + 1)) (Nat.ceil (8 / rho))).trans hBH)
    have hh := (div_le_iff₀ hrho).mp h
    simpa only [mul_comm] using hh
  obtain ⟨M, Q, hpart, hproper, hw, hosc⟩ :=
    hpartition N Gamma Psi r L P hP hL H hH hscale hbudget
  exact ⟨M, Q, hpart, hproper, fun j => hroot.trans (hw j),
    fun j => cellGood_of_polynomial_oscillation hH hrad (Q j) (hosc j)⟩

end LeanProofs.GowersSzemeredi
