import GRHArticle.SingularModuli.ConjugateDisks
import GRHArticle.SingularModuli.DepthOne

/-!
# Near-maximal minimum support from a depth-one disk of conjugates

Count the distinct conjugates in one disk in terms of the actual minimum
support. If all conjugates occur there, the support deficit is bounded
explicitly by a logarithm of the degree.
-/

namespace GRHArticle.SingularModuli

open Polynomial

variable {p : ℕ} [Fact p.Prime] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [Algebra K ℂ_[p]]

/-- For any odd prime, distinct conjugates in one closed depth-one disk
satisfy both the linear and the logarithmic estimates for the minimum
number of terms in an annihilator over the base field. -/
theorem conjugate_count_le_minimumSupport_depth_one {x : L} (hx : IsIntegral K x)
    (hp : 3 ≤ p) {m : ℕ} (a : ℂ_[p]) (ha : a ≠ 0) (σ : Fin m → L →ₐ[K] ℂ_[p])
    (hdistinct : Function.Injective fun i ↦ σ i x)
    (hdisk : ∀ i, ‖σ i x/a-1‖ ≤ (p:ℝ)⁻¹) :
    let t : ℝ := minimumSupport hx
    let C := ((p:ℝ)-1)/(p-2)
    (m:ℝ) ≤ C*(t-1) ∧ (m:ℝ) ≤ t-1+C*(1+Real.logb p t) := by
  let t := minimumSupport hx
  have ht : 0 < t := minimumSupport_pos hx
  have hp' : (3:ℚ) ≤ p := by exact_mod_cast hp
  have hr : 1/((p:ℚ)-1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hm : m ≤ sparseDiskRootBound p t 1 ht hr := by
    by_contra! h
    exact not_hasSparseAnnihilator_of_padic_conjugates ht hr x a ha σ hdistinct
      (by simpa [Real.rpow_neg_one] using hdisk) h (hasSparseAnnihilator_minimumSupport hx)
  obtain ⟨hlin,hlog⟩ := sparseDiskRootBound_one_le (p := p) ht hp (hr := hr)
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  have htR : (1:ℝ) ≤ t := by exact_mod_cast ht
  let C := ((p:ℝ)-1)/(p-2)
  have hC : 0 ≤ C := div_nonneg (by linarith) (by linarith)
  have hL : 0 ≤ Real.logb p t := Real.logb_nonneg (by linarith) htR
  have h₁ : 0 ≤ C*((t:ℝ)-1) := mul_nonneg hC (by linarith)
  have h₂ : 0 ≤ (t:ℝ)-1+C*(1+Real.logb p t) :=
    add_nonneg (by linarith) (mul_nonneg hC (by linarith))
  exact ⟨(Nat.le_floor_iff h₁).mp (hm.trans hlin), (Nat.le_floor_iff h₂).mp (hm.trans hlog)⟩

/-- When the disk contains a full set of conjugates, the loss from maximal
support is logarithmic in the degree. The statement gives an explicit
constant over every eligible base field. -/
theorem minimumSupport_deficit_le_log_degree_of_depth_one {x : L} (hx : IsIntegral K x)
    (hp : 3 ≤ p) (a : ℂ_[p]) (ha : a ≠ 0)
    (σ : Fin (minpoly K x).natDegree → L →ₐ[K] ℂ_[p])
    (hdistinct : Function.Injective fun i ↦ σ i x)
    (hdisk : ∀ i, ‖σ i x/a-1‖ ≤ (p:ℝ)⁻¹) :
    let h : ℝ := (minpoly K x).natDegree
    h+1-minimumSupport hx ≤ ((p:ℝ)-1)/(p-2)*(1+Real.logb p (h+1)) := by
  have h := (conjugate_count_le_minimumSupport_depth_one hx hp a ha σ hdistinct hdisk).2
  have hup : (minimumSupport hx : ℝ) ≤ (minpoly K x).natDegree+1 := by
    exact_mod_cast minimumSupport_le_natDegree_add_one hx
  have hpR : (3:ℝ) ≤ p := by exact_mod_cast hp
  have hlog := Real.logb_le_logb_of_le (by linarith : (1:ℝ) < p)
    (by exact_mod_cast minimumSupport_pos hx) hup
  have hb := mul_le_mul_of_nonneg_left (add_le_add_left hlog 1)
    (div_nonneg (by linarith : 0 ≤ (p:ℝ)-1) (by linarith : 0 ≤ (p:ℝ)-2))
  dsimp only
  linarith only [h,hb]

end GRHArticle.SingularModuli
