import Mathlib.LinearAlgebra.Quotient.Basic
import OAI.Combinatorics.Progressions.Linear.RationalKernelBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in

theorem kernel_equations_of_transpose_kernel (A : Matrix ι κ ℚ)
    (v : Fin (Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin)) → (ι → ℚ))
    (hli : LinearIndependent ℚ v)
    (hspan : Submodule.span ℚ (Set.range v) = LinearMap.ker Aᵀ.mulVecLin) :
    Function.Surjective (Matrix.mulVec v) ∧
      LinearMap.ker (Matrix.mulVecLin v) = LinearMap.range A.mulVecLin := by
  let D : Matrix (Fin (Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin))) ι ℚ := v
  have hrows : LinearIndependent ℚ D.row := hli
  have hDA : D * A = 0 := by
    ext i j
    have hi : v i ∈ LinearMap.ker Aᵀ.mulVecLin := by
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hj := congrFun hi j
    change (∑ k, A k j * v i k) = 0 at hj
    change (∑ k, v i k * A k j) = 0
    simpa only [mul_comm] using hj
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.ker D.mulVecLin := by
    rintro y ⟨x, rfl⟩
    change D *ᵥ (A *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hDA, Matrix.zero_mulVec]
  have hdimD := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have hdimA := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  change D.rank + Module.finrank ℚ (LinearMap.ker D.mulVecLin) =
    Module.finrank ℚ (ι → ℚ) at hdimD
  change Aᵀ.rank + Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin) =
    Module.finrank ℚ (ι → ℚ) at hdimA
  rw [hrows.rank_matrix, Fintype.card_fin] at hdimD
  rw [Matrix.rank_transpose] at hdimA
  have heq : Module.finrank ℚ (LinearMap.range A.mulVecLin) =
      Module.finrank ℚ (LinearMap.ker D.mulVecLin) := by
    change A.rank = _
    omega
  exact ⟨mulVec_surjective_of_independent_rows D hrows,
    (Submodule.eq_of_le_of_finrank_eq hle heq).symm⟩

theorem exists_bounded_image_equations (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, Function.Surjective D.mulVec ∧
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧
        ∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H) := by
  obtain ⟨t, ht, v, hli, hspan, hv⟩ := exists_bounded_rational_kernel_family Aᵀ hH
    (fun i j => hA j i)
  have hD := kernel_equations_of_transpose_kernel A v hli hspan
  refine ⟨t, ht, Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin), ?_, v, hD.1, hD.2, hv⟩
  simpa only [Module.finrank_pi] using (LinearMap.ker Aᵀ.mulVecLin).finrank_le

theorem rationalKernelHeight_pos (t : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < rationalKernelHeight t H := by
  have hsolve := rationalSolveHeight_pos t hH
  have hHpos : 0 < H := Nat.zero_lt_one.trans_le hH
  unfold rationalKernelHeight
  positivity

theorem exists_bounded_quotient_presentation (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H)) := by
  obtain ⟨t, ht, d, hd, D, hsurj, hker, hD⟩ := exists_bounded_image_equations A hH hA
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section D hsurj
    (rationalKernelHeight_pos t hH) hD
  exact ⟨t, ht, d, hd, D, S, hker, hS, hD, by simpa only [Fintype.card_fin] using hSH⟩

section Coordinates

variable [DecidableEq κ]

noncomputable def rationalQuotientEquiv (D : Matrix ι κ ℚ)
    (K : Submodule ℚ (κ → ℚ)) (hker : LinearMap.ker D.mulVecLin = K)
    (hsurj : Function.Surjective D.mulVec) :
    ((κ → ℚ) ⧸ K) ≃ₗ[ℚ] (ι → ℚ) :=
  (Submodule.quotEquivOfEq K (LinearMap.ker D.mulVecLin) hker.symm).trans
    (D.mulVecLin.quotKerEquivOfSurjective hsurj)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem rationalQuotientEquiv_apply_mk (D : Matrix ι κ ℚ)
    (K : Submodule ℚ (κ → ℚ)) (hker : LinearMap.ker D.mulVecLin = K)
    (hsurj : Function.Surjective D.mulVec) (x : κ → ℚ) :
    rationalQuotientEquiv D K hker hsurj (Submodule.Quotient.mk x) = D *ᵥ x := by
  simp only [rationalQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact D.mulVecLin.quotKerEquivOfSurjective_apply_mk hsurj x

omit [DecidableEq κ] in

theorem rationalQuotientEquiv_symm_apply (D : Matrix ι κ ℚ)
    (K : Submodule ℚ (κ → ℚ)) (hker : LinearMap.ker D.mulVecLin = K)
    (hsurj : Function.Surjective D.mulVec) (S : Matrix κ ι ℚ) (hS : D * S = 1)
    (y : ι → ℚ) : (rationalQuotientEquiv D K hker hsurj).symm y =
      Submodule.Quotient.mk (S *ᵥ y) := by
  apply (rationalQuotientEquiv D K hker hsurj).injective
  rw [LinearEquiv.apply_symm_apply, rationalQuotientEquiv_apply_mk,
    Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

end Coordinates

end Erdos3

end

section

namespace Erdos3

theorem rationalSolveHeight_mono {r s H : ℕ} (hH : 1 ≤ H) (hrs : r ≤ s) :
    rationalSolveHeight r H ≤ rationalSolveHeight s H := by
  unfold rationalSolveHeight
  apply Nat.mul_le_mul (Nat.factorial_le hrs)
  have he : r * r + r ≤ s * s + s := Nat.add_le_add (Nat.mul_le_mul hrs hrs) hrs
  have hbase := pow_le_pow_right₀ hH he
  calc
    _ ≤ (H ^ (s * s + s)) ^ r := pow_le_pow_left₀ (Nat.zero_le _) hbase r
    _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ hH) hrs

theorem rationalKernelHeight_mono {r s H : ℕ} (hH : 1 ≤ H) (hrs : r ≤ s) :
    rationalKernelHeight r H ≤ rationalKernelHeight s H := by
  unfold rationalKernelHeight
  apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hrs))
  have hbase := Nat.mul_le_mul_right H (rationalSolveHeight_mono hH hrs)
  have hpos : 1 ≤ rationalSolveHeight s H * H :=
    Nat.mul_pos (rationalSolveHeight_pos s hH) (Nat.zero_lt_one.trans_le hH)
  calc
    _ ≤ (rationalSolveHeight s H * H) ^ r := pow_le_pow_left₀ (Nat.zero_le _) hbase r
    _ ≤ _ := pow_le_pow_right₀ hpos hrs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

theorem exists_bounded_image_intersection_basis (A : ∀ i, Matrix κ (ρ i) ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H) :
    ∃ r : ℕ, r ≤ Fintype.card η * Fintype.card κ ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ
          (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
        ℚ (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ)),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j)
          (rationalKernelHeight r (rationalKernelHeight (∑ i, Fintype.card (ρ i)) H)) := by
  classical
  choose t ht d hd D hsurj hker hD using
    (fun i => exists_bounded_image_equations (A i) hH (hA i))
  let M := ∑ i, Fintype.card (ρ i)
  let K := rationalKernelHeight M H
  have htM : ∀ i, t i ≤ M := by
    intro i
    exact (ht i).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (Fintype.card (ρ j)))
      (Finset.mem_univ i))
  have hDK : ∀ i j k, RationalHeightLE (D i j k) K := by
    intro i j k
    exact (hD i j k).mono (rationalKernelHeight_mono hH (htM i))
  have hsub : (⨅ i, LinearMap.ker (D i).mulVecLin : Submodule ℚ (κ → ℚ)) =
      ⨅ i, LinearMap.range (A i).mulVecLin := iInf_congr hker
  rw [← hsub]
  obtain ⟨r, hr, b, hb⟩ := exists_bounded_rational_intersection_basis D
    (rationalKernelHeight_pos M hH) hDK
  refine ⟨r, ?_, b, hb⟩
  calc
    r ≤ ∑ i, d i := by simpa only [Fintype.card_fin] using hr
    _ ≤ ∑ _ : η, Fintype.card κ := Finset.sum_le_sum fun i _ => hd i
    _ = _ := by simp

theorem exists_image_intersection_basis_exp_height (A : ∀ i, Matrix κ (ρ i) ℚ)
    {H : ℕ} (hHpos : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hcount : (Fintype.card η : ℝ) ≤ p)
    (hdim : (Fintype.card κ : ℝ) ≤ p)
    (hcols : ((∑ i, Fintype.card (ρ i) : ℕ) : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ
        (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
      ℚ (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ)), ∀ i j,
        ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤ Real.exp ((p + 2) ^ 63) ∧
        ((((b i : κ → ℚ) j).den) : ℝ) ≤ Real.exp ((p + 2) ^ 63) := by
  obtain ⟨r, hr, b, hb⟩ := exists_bounded_image_intersection_basis A hHpos hA
  let M := ∑ i, Fintype.card (ρ i)
  have hK := rationalKernelHeight_le_budget M H hp hcols hH
  have hrp : (r : ℝ) ≤ (p + 2) ^ 7 := by
    calc
      (r : ℝ) ≤ (Fintype.card η : ℝ) * Fintype.card κ := by exact_mod_cast hr
      _ ≤ (p + 2) ^ 2 := by nlinarith [mul_le_mul hcount hdim (Nat.cast_nonneg _) hp]
      _ ≤ (p + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by decide)
  have hbudget : (rationalKernelHeight r (rationalKernelHeight M H) : ℝ) ≤
      Real.exp ((p + 2) ^ 63) := by
    have h := rationalKernelHeight_le_budget r (rationalKernelHeight M H)
      (by positivity : 0 ≤ (p + 2) ^ 7) hrp hK
    exact exponential_budget_comp hp (by positivity) 7 7 le_rfl h
  refine ⟨b, fun i j => ?_⟩
  constructor
  · exact (show ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤
      rationalKernelHeight r (rationalKernelHeight M H) from
      by exact_mod_cast (hb i j).1).trans hbudget
  · exact (show ((((b i : κ → ℚ) j).den) : ℝ) ≤
      rationalKernelHeight r (rationalKernelHeight M H) from
      by exact_mod_cast (hb i j).2).trans hbudget

end Erdos3

end

end OAI
