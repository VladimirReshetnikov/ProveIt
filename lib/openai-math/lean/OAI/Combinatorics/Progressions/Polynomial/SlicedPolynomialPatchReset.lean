import OAI.Combinatorics.Progressions.Dynamics.PatchIterationBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem patch_reset_log_loss_eq {P : ℕ} (hP : 0 < P) (d a : ℕ) :
    Real.log (2 * (P * (d + 1) ^ a : ℕ)) =
      Real.log (2 * (P : ℝ)) + (a : ℝ) * Real.log ((d : ℝ) + 1) := by
  push_cast
  rw [show 2 * ((P : ℝ) * ((d : ℝ) + 1) ^ a) =
    (2 * P) * ((d : ℝ) + 1) ^ a by ring, Real.log_mul (by positivity) (by positivity),
    Real.log_pow]

theorem logarithmic_polynomial_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N : ℕ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        let Q := P * (d + 1) ^ (2 * s * s)
        2 * (Q : ℝ) * Real.log (2 * C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) / σ)
          ≤ Real.log N →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.exp (Real.log N / (2 * Q)) ≤ len ∧
          Real.log (Real.log N) -
            (Real.log (2 * (P : ℝ)) + (2 * s * s : ℕ) * Real.log ((d : ℝ) + 1)) ≤
              Real.log (Real.log len) ∧
          b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := quantitative_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N A f hf b σ hb hσ Q hsize hscore
  have hQ : 0 < Q := Nat.mul_pos hP (pow_pos (by omega) _)
  let cost := C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1)
  have hcost : 1 ≤ cost := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
    (by have := A.kernel.lip.coe_nonneg; linarith)
  have hσ1 := hscore.trans (polynomial_patch_score_le_one A f hf hb)
  have hB : 1 ≤ cost / σ := (le_div_iff₀ hσ).mpr (by linarith)
  have hsize' : 2 * (Q : ℝ) * Real.log (2 * (cost / σ)) ≤ Real.log N := by
    convert hsize using 1
    congr 2
    dsimp [cost]
    ring
  obtain ⟨hN, T, _, hBT, hTN, hroot⟩ := exists_reset_scale_of_log_bound hQ hB hsize'
  have hscale : C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) ≤ σ * T := by
    have h := (div_le_iff₀ hσ).mp hBT
    change cost ≤ σ * T
    simpa only [mul_comm] using h
  obtain ⟨q, a, len, hq, hlen, hin, hdense⟩ := hreset d N T A f hf b σ hb hσ hscale hTN hscore
  have hroot' : Real.exp (Real.log N / (2 * Q)) ≤ len :=
    hroot.trans (by exact_mod_cast hlen)
  obtain ⟨hlen1, hloss⟩ := log_log_length_loss hN (by positivity : (0 : ℝ) < 2 * Q) hroot'
  refine ⟨q, a, len, hq, hlen1, hin, hroot', ?_, hdense⟩
  simpa only [Q, patch_reset_log_loss_eq hP] using hloss

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sliced_polynomial_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N M a₀ q₀ : ℕ) (U : ℝ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        ∀ b : ℝ, b ∈ Set.Icc (0 : ℝ) 1 →
        let Q := P * (d + 1) ^ (2 * s * s)
        4 * (Q : ℝ) * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log N →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.exp (Real.log N / (4 * Q)) ≤ len ∧
          Real.log (Real.log N) -
            (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * Real.log ((d : ℝ) + 1)) ≤
              Real.log (Real.log len) ∧
          b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := logarithmic_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N M a₀ q₀ U A f hq₀ hslice hf hU hlogM hLip b hb Q hsize hscore
  have hQ : 0 < Q := Nat.mul_pos hP (pow_pos (by omega) _)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨hN, hhalf, hroom⟩ := slice_reset_log_room hQ1 hC hU hlogM hsize
  have hcost := log_patch_reset_cost_le (by linarith : 0 < C) A.kernel.lip.coe_nonneg
    (Real.exp_pos (-U)) hLip le_rfl d
  have hresetSize : 2 * (Q : ℝ) *
      Real.log (2 * C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) / Real.exp (-U)) ≤
        Real.log M :=
    (mul_le_mul_of_nonneg_left hcost (by positivity)).trans hroom
  obtain ⟨q, a, len, hq, hlen, hin, hroot, _, hdense⟩ := hreset d M A
    (fun n => f (a₀ + q₀ * n)) (fun n hn => hf _ (hslice n hn)) b (Real.exp (-U))
    hb (Real.exp_pos (-U)) hresetSize hscore
  have hrootParent : Real.exp (Real.log N / (4 * Q)) ≤ len := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hroot
    calc
      _ = (Real.log N / 2) / (2 * Q) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hhalf (by positivity)
  obtain ⟨_, hloss⟩ := log_log_length_loss hN (by positivity : (0 : ℝ) < 4 * Q) hrootParent
  have hfactor : Real.log (4 * (Q : ℝ)) =
      Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * Real.log ((d : ℝ) + 1) := by
    dsimp [Q]
    push_cast
    rw [show 4 * ((P : ℝ) * ((d : ℝ) + 1) ^ (2 * s * s)) =
      (4 * P) * ((d : ℝ) + 1) ^ (2 * s * s) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    rfl
  rw [hfactor] at hloss
  refine ⟨q₀ * q, a₀ + q₀ * a, len, Nat.mul_pos hq₀ hq, hlen, ?_, hrootParent, hloss, ?_⟩
  · intro n hn
    convert hslice (a + q * n) (hin n hn) using 1
    ring
  · convert hdense using 1
    congr 1
    funext n
    congr 1
    ring

end Erdos3

end

end OAI
