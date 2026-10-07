import GowersSzemeredi.Proofs13EndpointFiniteError

/-! Over a finite field, a table L(h,k)=a(k)h is close to a scalar bilinear
map whenever it is nearly symmetric. A pivot argument loses no constant:
distance to some chk is at most the symmetry disagreement. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpoint_symmetric_rank_one {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a : F → F) :
    ∃ c : F, endpointError (fun p : F × F => a p.2 * p.1) (fun p => c * p.1 * p.2) ≤
      endpointError (fun p : F × F => a p.2 * p.1) (fun p => a p.1 * p.2) := by
  let L : F × F → F := fun p => a p.2 * p.1
  let B (c : F) : F × F → F := fun p => c * p.1 * p.2
  let row (h : F) : Real := endpointError (fun k => a k * h) (fun k => a h * k)
  let q : Real := 𝔼 h : F, if h = 0 then 0 else 1
  have hq : 0 < q := by
    dsimp [q]
    rw [Fintype.expect_eq_sum_div_card]
    apply div_pos
    · apply Finset.sum_pos'
      · intro h _
        split_ifs <;> norm_num
      · exact ⟨1, Finset.mem_univ _, by simp⟩
    · exact_mod_cast Fintype.card_pos
  have hpivot (h : F) (hh : h ≠ 0) : endpointError L (B (a h / h)) = q * row h := by
    have he (h' k : F) :
        (if L (h', k) = B (a h / h) (h', k) then (0 : Real) else 1) =
          (if h' = 0 then 0 else 1) * (if a k * h = a h * k then 0 else 1) := by
      by_cases hh' : h' = 0
      · simp [L, B, hh']
      · have hid : a k * h' - a h / h * h' * k = (h' / h) * (a k * h - a h * k) := by
          field_simp
        have heq : L (h', k) = B (a h / h) (h', k) ↔ a k * h = a h * k := by
          change a k * h' = a h / h * h' * k ↔ _
          rw [← sub_eq_zero, hid, mul_eq_zero]
          simp only [div_ne_zero hh' hh, false_or, sub_eq_zero]
        simp only [heq, if_neg hh', one_mul]
    unfold endpointError
    rw [endpoint_expect_prod]
    simp_rw [he, ← Finset.mul_expect]
    rw [← Finset.expect_mul]
    rfl
  obtain ⟨c, _, hc⟩ := Finset.exists_min_image Finset.univ (fun c => endpointError L (B c)) Finset.univ_nonempty
  have hmin (h : F) :
      (if h = 0 then (0 : Real) else 1) * endpointError L (B c) ≤ q * row h := by
    by_cases hh : h = 0
    · simp only [if_pos hh, zero_mul]
      exact mul_nonneg hq.le (endpointError_nonneg _ _)
    · simp only [if_neg hh, one_mul]
      exact (hc _ (Finset.mem_univ (a h / h))).trans_eq (hpivot h hh)
  have ht := Finset.expect_le_expect (fun h (_ : h ∈ (Finset.univ : Finset F)) => hmin h)
  rw [← Finset.expect_mul, ← Finset.mul_expect] at ht
  have hrow : (𝔼 h : F, row h) = endpointError L (fun p => a p.1 * p.2) := by
    unfold endpointError
    rw [endpoint_expect_prod]
    rfl
  rw [hrow] at ht
  exact ⟨c, (mul_le_mul_iff_right₀ hq).mp ht⟩

end LeanProofs.GowersSzemeredi
