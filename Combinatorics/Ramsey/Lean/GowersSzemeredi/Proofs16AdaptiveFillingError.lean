import GowersSzemeredi.Proofs16AdaptiveDenseGraph
import GowersSzemeredi.Proofs16RobustPatternRepresentations

/-! A state-dependent graph error pays for the robust seven-operator
row-filling budget at the same retained-density state. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def adaptiveFillingError (alpha : Real) (Q H m d : Nat) : Real :=
  let b := (1 / ((4 * H : Nat) : Real)^m) / 2
  min (b / 2) ((b^3 * ((alpha / (Q : Real)^d)^4 / 4))^2 /
    (12 * (4 : Real)^(m + 1) * ((4 * H : Nat) : Real)^m))

/-- The row-filling schedule is admissible for adaptive graph refinement. -/
theorem adaptiveFillingError_pos_le {alpha : Real} (ha : 0 < alpha)
    (Q H m d : Nat) [NeZero Q] [NeZero H] :
    0 < adaptiveFillingError alpha Q H m d ∧
      adaptiveFillingError alpha Q H m d ≤ (1 / ((4 * H : Nat) : Real)^m) / 2 := by
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hH : (0 : Real) < H := by exact_mod_cast NeZero.pos H
  have h4H : (0 : Real) < ((4 * H : Nat) : Real) := by push_cast; positivity
  constructor
  · unfold adaptiveFillingError; positivity
  · apply (min_le_left _ _).trans
    have h : (0 : Real) ≤ 1 / ((4 * H : Nat) : Real)^m := by positivity
    linarith

/-- The schedule pays the complete scalar budget for any graph and witness
densities above their uniform lower bounds. -/
theorem adaptiveFillingError_budget {alpha delta tau : Real} (ha : 0 < alpha)
    (Q H m d : Nat) [NeZero Q] [NeZero H]
    (hd : (1 / ((4 * H : Nat) : Real)^m) / 2 ≤ delta)
    (ht : (alpha / (Q : Real)^d)^4 / 4 ≤ tau) :
    (4 : Real)^(m + 1) * (12 * adaptiveFillingError alpha Q H m d) *
      ((4 * H : Nat) : Real)^m ≤ (delta^3 * tau)^2 := by
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hH : (0 : Real) < H := by exact_mod_cast NeZero.pos H
  have h4H : (0 : Real) < ((4 * H : Nat) : Real) := by push_cast; positivity
  let b := (1 / ((4 * H : Nat) : Real)^m) / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hdelta : 0 < delta := hb.trans_le hd
  have hden : 0 < 12 * (4 : Real)^(m + 1) * ((4 * H : Nat) : Real)^m := by positivity
  have hsmall : adaptiveFillingError alpha Q H m d ≤
      (b^3 * ((alpha / (Q : Real)^d)^4 / 4))^2 /
        (12 * (4 : Real)^(m + 1) * ((4 * H : Nat) : Real)^m) := min_le_right _ _
  have hpaid := (le_div_iff₀ hden).mp hsmall
  have hprod : b^3 * ((alpha / (Q : Real)^d)^4 / 4) ≤ delta^3 * tau :=
    mul_le_mul (pow_le_pow_left₀ hb.le hd 3) ht (by positivity) (by positivity)
  have hsq := pow_le_pow_left₀ (by positivity) hprod 2
  nlinarith only [hpaid, hsq]

/-- Robust witness density is bounded below by a fourth power of any
ambient-density lower bound; no parameter-domain size occurs in this bound. -/
theorem robustRepresentationDensity_lower {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (hC : C.Nonempty) {alpha gamma : Real}
    (hg : 0 ≤ gamma) (hga : gamma ≤ alpha) :
    gamma^4 / 4 ≤ robustRepresentationDensity alpha C := by
  have hp := pow_le_pow_left₀ hg hga 4
  exact (div_le_div_of_nonneg_right hp (by norm_num : (0 : Real) ≤ 4)).trans
    (robustRepresentationDensity_ge alpha C hC)

/-- Specialization to the witness density used by robust row filling. -/
theorem adaptiveFillingError_robust_budget {N : Nat} [NeZero N]
    (C : Finset (ZMod N)) (hC : C.Nonempty) {alpha alpha' delta : Real}
    (ha : 0 < alpha) (Q H m d : Nat) [NeZero Q] [NeZero H]
    (hactual : alpha / (Q : Real)^d ≤ alpha')
    (hd : (1 / ((4 * H : Nat) : Real)^m) / 2 ≤ delta) :
    (4 : Real)^(m + 1) * (12 * adaptiveFillingError alpha Q H m d) *
      ((4 * H : Nat) : Real)^m ≤ (delta^3 * robustRepresentationDensity alpha' C)^2 := by
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  exact adaptiveFillingError_budget ha Q H m d hd
    (robustRepresentationDensity_lower C hC (by positivity) hactual)

end LeanProofs.GowersSzemeredi
