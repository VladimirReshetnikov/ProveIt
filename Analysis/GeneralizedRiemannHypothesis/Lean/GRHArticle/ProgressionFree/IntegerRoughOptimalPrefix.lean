import GRHArticle.ProgressionFree.IntegerSmoothFactorization
import Mathlib.Data.Nat.Squarefree

/-!
# Assigning smooth optimizers to rough factors in a finite prefix
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical

/-- A finite set realizing the smooth prefix maximum. -/
theorem exists_integerSmoothPrefixMaximum (integral : Bool) (Y k : ℕ) :
    ∃ A : Finset ℕ, A ⊆ integerPrefixSlice (Nat.smoothNumbers (Y+1)) k ∧
      IntegerPrefixAdmissible integral (A : Set ℕ) ∧
      A.card = integerSmoothPrefixMaximum integral Y k := by
  let C := ((integerPrefixSlice (Nat.smoothNumbers (Y+1)) k).powerset.filter
    fun A : Finset ℕ ↦ IntegerPrefixAdmissible integral (A : Set ℕ))
  have hC : C.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),
    by simp [IntegerPrefixAdmissible]⟩⟩
  obtain ⟨A, hA, heq⟩ := exists_mem_eq_sup C hC Finset.card
  obtain ⟨hsub, hadm⟩ := mem_filter.mp hA
  exact ⟨A, mem_powerset.mp hsub, hadm, heq.symm⟩

/-- A maximizing template is chosen once for each smooth cutoff. -/
noncomputable def integerSmoothPrefixOptimizer (integral : Bool) (Y k : ℕ) : Finset ℕ :=
  (exists_integerSmoothPrefixMaximum integral Y k).choose

theorem integerSmoothPrefixOptimizer_spec (integral : Bool) (Y k : ℕ) :
    integerSmoothPrefixOptimizer integral Y k ⊆ integerPrefixSlice (Nat.smoothNumbers (Y+1)) k ∧
      IntegerPrefixAdmissible integral (integerSmoothPrefixOptimizer integral Y k : Set ℕ) ∧
      (integerSmoothPrefixOptimizer integral Y k).card = integerSmoothPrefixMaximum integral Y k :=
  (exists_integerSmoothPrefixMaximum integral Y k).choose_spec

theorem mem_smooth_of_mem_integerSmoothPrefixOptimizer {integral : Bool} {Y k h : ℕ}
    (hh : h ∈ integerSmoothPrefixOptimizer integral Y k) :
    (0 < h ∧ h ≤ k) ∧ h ∈ Nat.smoothNumbers (Y+1) := by
  have h := (integerSmoothPrefixOptimizer_spec integral Y k).1 hh
  simp only [integerPrefixSlice, mem_filter, integerPrefix, mem_Icc] at h
  exact h

/-- The locally optimal set obtained by choosing separately within each
rough class of the given prefix. -/
noncomputable def integerRoughOptimalPrefix (integral : Bool) (Y : ℕ) (Q : Set ℕ) (N : ℕ) : Set ℕ :=
  {a | ∃ r s : ℕ, r ∈ Q ∧ s ∈ integerSmoothPrefixOptimizer integral Y (N / r) ∧ a = r*s}

private theorem factorization_rough_small {Y r p : ℕ} (hr : r ∈ integerRoughNumbers Y)
    (hp : p.Prime) (hY : p ≤ Y) : r.factorization p = 0 := by
  rw [integerRoughNumbers_eq_valuationCylinder] at hr
  exact hr.2 p (Nat.mem_primesLE.mpr ⟨hY, hp⟩)

private theorem factorization_mul_smooth_large {Y r s p : ℕ} (hr : r ≠ 0)
    (hs : s ∈ Nat.smoothNumbers (Y+1)) (hp : p.Prime) (hY : Y < p) :
    (r*s).factorization p = r.factorization p := by
  have hzero := Nat.factorization_eq_zero_of_not_dvd (n := s) (p := p) (fun h ↦ by
    have := Nat.mem_smoothNumbers'.mp hs p hp h
    omega)
  rw [Nat.factorization_mul hr (Nat.ne_zero_of_mem_smoothNumbers hs), Finsupp.add_apply, hzero, add_zero]

/-- One admissible smooth template may be chosen independently for each
squarefree rough part. A progression cannot use two different rough parts. -/
theorem integerRoughTemplate_admissible (integral : Bool) (Y : ℕ) (Q : Set ℕ)
    (T : ℕ → Set ℕ) (hrough : Q ⊆ integerRoughNumbers Y)
    (hsquarefree : ∀ r ∈ Q, Squarefree r)
    (hT : ∀ r ∈ Q, T r ⊆ Nat.smoothNumbers (Y+1))
    (hA : ∀ r ∈ Q, IntegerPrefixAdmissible integral (T r)) :
    IntegerPrefixAdmissible integral {a | ∃ r s : ℕ, r ∈ Q ∧ s ∈ T r ∧ a = r*s} := by
  intro a b c ha hb hc hab hbc he hd
  obtain ⟨r, a', hr, ha', rfl⟩ := ha
  obtain ⟨s, b', hs, hb', rfl⟩ := hb
  obtain ⟨t, c', ht, hc', rfl⟩ := hc
  have hr₀ := (hsquarefree r hr).ne_zero
  have hs₀ := (hsquarefree s hs).ne_zero
  have ht₀ := (hsquarefree t ht).ne_zero
  have haS := hT r hr ha'
  have hbS := hT s hs hb'
  have hcS := hT t ht hc'
  have hfac (p : ℕ) : r.factorization p = s.factorization p ∧ s.factorization p = t.factorization p := by
    by_cases hp : p.Prime
    · by_cases hY : p ≤ Y
      · rw [factorization_rough_small (hrough hr) hp hY,
          factorization_rough_small (hrough hs) hp hY, factorization_rough_small (hrough ht) hp hY]
        exact ⟨rfl, rfl⟩
      · have hpY := Nat.lt_of_not_ge hY
        have h := congrArg (fun z : ℕ ↦ z.factorization p) he
        simp only [Nat.factorization_mul (mul_ne_zero hr₀ (Nat.ne_zero_of_mem_smoothNumbers haS))
          (mul_ne_zero ht₀ (Nat.ne_zero_of_mem_smoothNumbers hcS)),
          Nat.factorization_mul (mul_ne_zero hs₀ (Nat.ne_zero_of_mem_smoothNumbers hbS))
            (mul_ne_zero hs₀ (Nat.ne_zero_of_mem_smoothNumbers hbS)), Finsupp.add_apply,
          factorization_mul_smooth_large hr₀ haS hp hpY, factorization_mul_smooth_large hs₀ hbS hp hpY,
          factorization_mul_smooth_large ht₀ hcS hp hpY] at h
        have hR := (hsquarefree r hr).natFactorization_le_one p
        have hS := (hsquarefree s hs).natFactorization_le_one p
        have hT := (hsquarefree t ht).natFactorization_le_one p
        omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hrs := Nat.eq_of_factorization_eq hr₀ hs₀ (fun p ↦ (hfac p).1)
  have hst := Nat.eq_of_factorization_eq hs₀ ht₀ (fun p ↦ (hfac p).2)
  subst s
  subst t
  have hpos := Nat.pos_of_ne_zero hr₀
  have he' : a'*c' = b'*b' := by
    apply Nat.mul_left_cancel (Nat.mul_pos hpos hpos)
    calc
      _ = (r*a')*(r*c') := by ring
      _ = (r*b')*(r*b') := he
      _ = _ := by ring
  refine hA r hr ha' hb' hc'
    (Nat.lt_of_mul_lt_mul_left hab) (Nat.lt_of_mul_lt_mul_left hbc) he' ?_
  intro hi
  obtain ⟨q, hq⟩ := hd hi
  exact ⟨q, Nat.mul_left_cancel hpos (by simpa only [mul_assoc] using hq)⟩

/-- In a cutoff prefix, the smooth template of rough part `r` can be an
optimizer for the budget `N/r`. -/
theorem integerRoughOptimalPrefix_admissible (integral : Bool) (Y N : ℕ) (Q : Set ℕ)
    (hrough : Q ⊆ integerRoughNumbers Y)
    (hsquarefree : ∀ r ∈ Q, Squarefree r) :
    IntegerPrefixAdmissible integral (integerRoughOptimalPrefix integral Y Q N) :=
  integerRoughTemplate_admissible integral Y Q
    (fun r ↦ (integerSmoothPrefixOptimizer integral Y (N/r) : Set ℕ)) hrough hsquarefree
    (fun _ _ _ hs ↦ (mem_smooth_of_mem_integerSmoothPrefixOptimizer hs).2)
    (fun r _ ↦ (integerSmoothPrefixOptimizer_spec integral Y (N/r)).2.1)

end GRHArticle.ProgressionFree
