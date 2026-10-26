import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Source-body elaboration fixture. The three upstream source lemmas are
explicit theorem parameters; this is not a full project rebuild. There are
no axioms and no placeholders. The target proof body is byte-identical to
the proposed repository proof body. -/

namespace DiophantineProofIdeas.RankSourceFixture

def nativeRank (x : Fin 31 → ℕ) : ℤ := (x 19 : ℤ) * x 8 - x 26

def nativeTarget (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ) : ℤ :=
  let q := 1 + (x 0 : ℤ) * ports 0
  ((q - 1) * (q - x 1) + x 2) * (q ^ 2 - 1) +
    (ports 2 + ports 3 * q) * x 0

section
variable (sourceRows : (Fin 4 → ℤ) → (Fin 31 → ℤ) → Fin 22 → ℤ)
variable (source_transport_positive : ∀ (ports : Fin 4 → ℤ),
  0 < ports 0 → 0 ≤ ports 1 → ∀ (x : Fin 31 → ℕ),
  (∀ i, 0 < x i) → (∀ k, sourceRows ports (fun i => (x i : ℤ)) k = 0) →
  0 < 1 + (x 0 : ℤ) * ports 0 - x 1 - x 2)
variable (source_rank_eq_target : ∀ (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ),
  (∀ k, sourceRows ports (fun i => (x i : ℤ)) k = 0) →
  nativeRank x = nativeTarget ports x)
variable (source_scale_eq : ∀ (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ),
  (∀ i, 0 < x i) → (∀ k, sourceRows ports (fun i => (x i : ℤ)) k = 0) →
  (x 17 : ℤ) = (1 + (x 0 : ℤ) * ports 0) ^ 4 * (x 10 * x 9))

include source_transport_positive source_rank_eq_target source_scale_eq

theorem source_window_bound (ports : Fin 4 → ℤ)
    (hβ : 0 < ports 0) (hK : 0 ≤ ports 1)
    (hMCβ : ports 2 < ports 0) (hMFβ : ports 3 < 2 * ports 0)
    (x : Fin 31 → ℕ) (hx : ∀ i, 0 < x i)
    (hs : ∀ k, sourceRows ports (fun i => (x i : ℤ)) k = 0) :
    nativeRank x + 1 < (x 17 : ℤ) := by
  let q : ℤ := 1 + (x 0 : ℤ) * ports 0
  have hC : 0 < q - x 1 - x 2 := source_transport_positive ports hβ hK x hx hs
  have hF : (0 : ℤ) < x 1 := by exact_mod_cast hx 1
  have hα : (0 : ℤ) < x 2 := by exact_mod_cast hx 2
  have hJ : (0 : ℤ) < x 0 := by exact_mod_cast hx 0
  have hq3 : 3 ≤ q := by omega
  have hL : 0 ≤ q ^ 2 - 1 := by nlinarith
  have hF1 : 0 ≤ (x 1 : ℤ) - 1 := by omega
  have hC1 : 0 ≤ q - x 1 - x 2 - 1 := by omega
  have hJ1 : 0 ≤ (x 0 : ℤ) - 1 := by omega
  have hM : 0 ≤ ports 0 - ports 2 - 1 := by omega
  have hH : 0 ≤ 2 * ports 0 - ports 3 - 1 := by omega
  have hgap := add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg (show 0 ≤ q by omega) hL) hF1) (mul_nonneg hL hC1))
    (mul_nonneg (show 0 ≤ q + 1 by omega) hJ1))
    (mul_nonneg hJ.le (add_nonneg hM (mul_nonneg (show 0 ≤ q by omega) hH)))
  have he : q ^ 4 - q ^ 3 - q - 1 - nativeRank x =
      q * (q ^ 2 - 1) * ((x 1 : ℤ) - 1) + (q ^ 2 - 1) * (q - x 1 - x 2 - 1) +
      (q + 1) * ((x 0 : ℤ) - 1) +
      (x 0 : ℤ) * ((ports 0 - ports 2 - 1) + q * (2 * ports 0 - ports 3 - 1)) := by
    rw [source_rank_eq_target ports x hs]
    dsimp [nativeTarget, q]
    ring
  rw [← he] at hgap
  have hEbound : q ^ 4 ≤ (x 17 : ℤ) := by
    rw [source_scale_eq ports x hx hs]
    exact le_mul_of_one_le_right (pow_nonneg (show 0 ≤ q by omega) 4)
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hx 10) (by exact_mod_cast hx 9))
  have hcube : 0 < q ^ 3 := pow_pos (by omega) _
  omega

#print axioms source_window_bound

end
end DiophantineProofIdeas.RankSourceFixture
