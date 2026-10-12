import GowersSzemeredi.Sections01_03

/-! The quantitative headline is an eventual-in-N statement. Its literal
finite reading without that qualification is false, for ordinary intervals. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem no_natAP_longer_than_interval (N : Nat) :
    ¬ HasNatAP (Finset.Icc 1 N) (N + 1) := by
  rintro ⟨a, d, hd, hAP⟩
  have h0 : 1 ≤ a := by
    simpa only [Nat.zero_mul, Nat.add_zero] using (Finset.mem_Icc.mp (hAP 0 (by omega))).1
  have hlast : a + N * d ≤ N := (Finset.mem_Icc.mp (hAP N (by omega))).2
  have hstep : 1 ≤ d := by omega
  have hm : N ≤ N * d := by simpa using Nat.mul_le_mul_left N hstep
  omega

/-- The unqualified reading of the printed quantitative headline. This
predicate is refuted below and is never counted as a positive companion. -/
def theorem_1_3_without_eventual_scale : Prop :=
  ∀ k : Nat, 0 < k → ∀ N : Nat, 0 < N →
    ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N →
      (N : Real) * (Real.log (Real.log N)) ^ (-theorem_1_3_constant k) ≤ A.card →
      HasNatAP A k

/-- A full interval above the logarithm threshold meets the displayed
size bound, but cannot contain a progression longer than the interval. -/
theorem theorem_1_3_without_eventual_scale_counterexample :
    ¬ theorem_1_3_without_eventual_scale := by
  intro h
  let N : Nat := ⌈Real.exp (Real.exp (1 : Real))⌉₊ + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hthreshold : Real.exp (Real.exp (1 : Real)) ≤ N := by
    exact (Nat.le_ceil _).trans (by dsimp [N]; exact_mod_cast Nat.le_succ _)
  have hlog : Real.exp (1 : Real) ≤ Real.log N :=
    (Real.le_log_iff_exp_le hNreal).mpr hthreshold
  have hlogpos : 0 < Real.log N := (Real.exp_pos _).trans_le hlog
  have hloglog : (1 : Real) ≤ Real.log (Real.log N) :=
    (Real.le_log_iff_exp_le hlogpos).mpr hlog
  have hcoef : (Real.log (Real.log N)) ^ (-theorem_1_3_constant (N + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hloglog (by
      apply neg_nonpos.mpr
      unfold theorem_1_3_constant
      positivity)
  have hcard : (Finset.Icc 1 N).card = N := by simp
  have hsize : (N : Real) * (Real.log (Real.log N)) ^
      (-theorem_1_3_constant (N + 1)) ≤ (Finset.Icc 1 N).card := by
    rw [hcard]
    simpa using mul_le_mul_of_nonneg_left hcoef hNreal.le
  exact no_natAP_longer_than_interval N
    (h (N + 1) (by omega) N hN (Finset.Icc 1 N) (Finset.Subset.refl _) hsize)

end LeanProofs.GowersSzemeredi
