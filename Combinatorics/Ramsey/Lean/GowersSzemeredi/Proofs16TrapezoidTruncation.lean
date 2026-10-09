import GowersSzemeredi.Proofs16TrapezoidFourier

/-! Inversion and tails: bricks C and D of [49]'s Proposition 26.

* `fourier_inversion`: `f(t) = N⁻¹ Σ_ξ e(ξt) f̂(ξ)` on `ℤ/N`
  (`ZMod.dft.symm_apply_apply`, `ZMod.invDFT_apply`).
* `inv_sq_tail_le`: `Σ_{M < m ≤ U} 1/m² ≤ 1/M`, by telescoping against
  `1/(m−1) − 1/m`.
* `centeredAbs_fibre_card_le`: at most two residues share a centered value.
* `residue_inv_sq_tail_le`: `Σ_{|ξ| > M} 1/|ξ|² ≤ 2/M` over `ℤ/N`.

With `fourier_trapezoid_le` this bounds the error of truncating the
trapezoid's Fourier series to `|ξ| ≤ M` by `N/(2|I_c|M)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **Fourier inversion on `ℤ/N`.** -/
theorem fourier_inversion {N : Nat} [NeZero N] (f : ZMod N → Complex) (t : ZMod N) :
    f t = (N : Complex)⁻¹ * ∑ ξ : ZMod N, exponential (ξ * t) * fourier f ξ := by
  have h := congrFun (ZMod.dft.symm_apply_apply f) t
  rw [ZMod.invDFT_apply] at h
  rw [← h]
  simp only [smul_eq_mul, fourier, exponential]

/-- **Telescoping tail of `1/m²`.** -/
theorem inv_sq_tail_le {M : Nat} (hM : 1 ≤ M) (U : Nat) :
    ∑ m ∈ Finset.Ioc M U, (1 : Real) / (m : Real) ^ 2 ≤ 1 / M - 1 / max M U := by
  induction U with
  | zero =>
    have : Finset.Ioc M 0 = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [this, Finset.sum_empty, Nat.max_zero]
    simp
  | succ U ih =>
    by_cases hU : U + 1 ≤ M
    · have : Finset.Ioc M (U + 1) = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [this, Finset.sum_empty, max_eq_left hU]
      simp
    · push Not at hU
      have hMU : M ≤ U := by omega
      rw [Finset.sum_Ioc_succ_top (by omega), max_eq_right hU.le]
      rw [max_eq_right hMU] at ih
      have hU1 : (1 : Real) ≤ U := by exact_mod_cast (show 1 ≤ U by omega)
      have hstep : (1 : Real) / ((U + 1 : Nat) : Real) ^ 2 ≤ 1 / (U : Real) - 1 / ((U + 1 : Nat) : Real) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast at hstep ⊢
      linarith

/-- At most two residues share a centered value. -/
theorem centeredAbs_fibre_card_le {N : Nat} [NeZero N] (m : Nat) :
    (Finset.univ.filter fun ξ : ZMod N => centeredAbs ξ = m).card ≤ 2 := by
  have hsub : (Finset.univ.filter fun ξ : ZMod N => centeredAbs ξ = m) ⊆
      ({((m : Int) : ZMod N), ((-(m : Int)) : ZMod N)} : Finset (ZMod N)) := by
    intro ξ hξ
    have h := (Finset.mem_filter.mp hξ).2
    unfold centeredAbs at h
    rcases Int.natAbs_eq ξ.valMinAbs with h1 | h1
    · rw [h] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      left
      rw [← h1, ZMod.coe_valMinAbs]
    · rw [h] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      right
      have hc := ZMod.coe_valMinAbs ξ
      rw [h1] at hc
      rw [← hc]
      push_cast
      ring
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))

/-- **The residue tail.** `Σ_{|ξ| > M} 1/|ξ|² ≤ 2/M`. -/
theorem residue_inv_sq_tail_le {N : Nat} [NeZero N] {M : Nat} (hM : 1 ≤ M) :
    ∑ ξ ∈ Finset.univ.filter (fun ξ : ZMod N => M < centeredAbs ξ),
      (1 : Real) / (centeredAbs ξ : Real) ^ 2 ≤ 2 / M := by
  -- group by the centered value
  rw [← Finset.sum_fiberwise_of_maps_to (g := centeredAbs) (t := Finset.Ioc M N)
    (fun ξ hξ => Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp hξ).2, by
      have := ZMod.natAbs_valMinAbs_le ξ
      unfold centeredAbs; omega⟩)]
  calc ∑ m ∈ Finset.Ioc M N, ∑ ξ ∈ (Finset.univ.filter fun ξ : ZMod N => M < centeredAbs ξ).filter
          (fun ξ => centeredAbs ξ = m), (1 : Real) / (centeredAbs ξ : Real) ^ 2
      ≤ ∑ m ∈ Finset.Ioc M N, 2 * ((1 : Real) / (m : Real) ^ 2) := by
        apply Finset.sum_le_sum
        intro m _
        rw [Finset.sum_congr rfl fun ξ hξ => by rw [(Finset.mem_filter.mp hξ).2]]
        rw [Finset.sum_const, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : ((Finset.univ.filter fun ξ : ZMod N => M < centeredAbs ξ).filter
            (fun ξ => centeredAbs ξ = m)).card ≤ 2 := by
          refine (Finset.card_le_card ?_).trans (centeredAbs_fibre_card_le m)
          intro ξ hξ
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hξ).2⟩
        exact_mod_cast this
    _ = 2 * ∑ m ∈ Finset.Ioc M N, (1 : Real) / (m : Real) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 / M) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have := inv_sq_tail_le hM N
        have h2 : (0 : Real) ≤ 1 / (max M N : Nat) := by positivity
        push_cast at this h2
        linarith
    _ = 2 / M := by ring

end LeanProofs.GowersSzemeredi
