import GRHArticle.ProgressionFree.Rankin

/-!
# A shared deletion for progressions of arbitrary length

A marker coordinate distinguishes the inserted exponent vectors. The
remaining coordinates take a common value except for the one associated
with the inserted vector.
-/

namespace GRHArticle.ProgressionFree

/-- Every affine string of length `k` in the set has zero integral step. -/
def KTermAPFree (k : ℕ) (G : Set ℕ) : Prop :=
  ∀ (x : Fin k → ℕ) (u d : ℤ), (∀ i, x i ∈ G) →
    (∀ i, (x i : ℤ) = u + (i.val : ℤ)*d) → d = 0

/-- The old vectors remaining after both shared-deletion tests. -/
def sharedDeletionOld {ι : Type*} (b : ℕ) (G : Set ℕ) : Set (Option ι → ℕ) :=
  {v | (∀ p, v p ∈ G) ∧
    (¬ ∀ q : ι, v (some q) = b) ∧
    ∀ q : ι, (∀ r, r ≠ q → v (some r) = b) → v (some q) < b+2}

/-- The new vector with marker and satellite `q` set to `b+1`. -/
def sharedDeletionVector {ι : Type*} [DecidableEq ι] (b : ℕ) (q : ι) : Option ι → ℕ
  | none => b+1
  | some r => if r = q then b+1 else b

/-- The edited joint exponent rule of the article's shared-deletion argument. -/
def sharedDeletionRule {ι : Type*} [DecidableEq ι] (b : ℕ) (G : Set ℕ) :
    Set (Option ι → ℕ) :=
  sharedDeletionOld b G ∪ Set.range (sharedDeletionVector b)

private theorem step_zero_of_repeat {k : ℕ} {x : Fin k → ℕ} {u d : ℤ}
    (hx : ∀ i, (x i : ℤ) = u + (i.val : ℤ)*d)
    {i j : Fin k} (hij : i ≠ j) (he : x i = x j) : d = 0 := by
  have hcast : ((i.val : ℤ) - (j.val : ℤ)) ≠ 0 := by
    refine sub_ne_zero.mpr fun h ↦ hij (Fin.ext ?_)
    exact_mod_cast h
  have hm : ((i.val : ℤ) - (j.val : ℤ))*d = 0 := by
    rw [sub_mul]
    have h := hx i
    rw [he, hx j] at h
    linarith
  exact (mul_eq_zero.mp hm).resolve_left hcast

private theorem step_zero_of_two_values {k b : ℕ} (hk : 3 ≤ k) {x : Fin k → ℕ}
    {u d : ℤ} (hx : ∀ i, (x i : ℤ) = u + (i.val : ℤ)*d)
    (hval : ∀ i, b ≤ x i ∧ x i ≤ b+1) : d = 0 := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨2, by omega⟩
  have hi : (x i : ℤ) = u := by simpa [i] using hx i
  have hj : (x j : ℤ) = u + 2*d := by simpa [j] using hx j
  have hlo (l : Fin k) : (b : ℤ) ≤ x l := by exact_mod_cast (hval l).1
  have hhi (l : Fin k) : (x l : ℤ) ≤ b+1 := by exact_mod_cast (hval l).2
  have low_i := hlo i
  have high_i := hhi i
  have low_j := hlo j
  have high_j := hhi j
  omega

private theorem step_zero_of_short_interval_missing {k : ℕ} (hk : 3 ≤ k)
    {x : Fin k → ℕ} {u d : ℤ}
    (hx : ∀ i, (x i : ℤ) = u + (i.val : ℤ)*d)
    (hval : ∀ i, x i ≤ k-1) (hmiss : ∀ i, x i ≠ k-2) : d = 0 := by
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨k-1, by omega⟩
  let L : ℤ := (k-1 : ℕ)
  have hL : 0 < L := by dsimp [L]; exact_mod_cast (show 0 < k-1 by omega)
  have hi : (x i : ℤ) = u := by simpa [i] using hx i
  have hj : (x j : ℤ) = u + L*d := hx j
  have hlo (l : Fin k) : 0 ≤ (x l : ℤ) := Nat.cast_nonneg _
  have hhi (l : Fin k) : (x l : ℤ) ≤ L := by dsimp [L]; exact_mod_cast hval l
  have hmin : L*(-1) ≤ L*d := by
    rw [mul_neg, mul_one]
    linarith [hlo j, hhi i]
  have hmax : L*d ≤ L*1 := by
    rw [mul_one]
    linarith [hlo i, hhi j]
  have hmin' : -1 ≤ d := (mul_le_mul_iff_of_pos_left hL).mp hmin
  have hmax' : d ≤ 1 := (mul_le_mul_iff_of_pos_left hL).mp hmax
  rcases (show d = -1 ∨ d = 0 ∨ d = 1 by omega) with hd | hd | hd
  · exfalso
    rw [hd, mul_neg, mul_one] at hj
    have hu : u = L := by linarith [hlo j, hhi i]
    let l : Fin k := ⟨1, by omega⟩
    have hh : (x l : ℤ) = L-1 := by simpa [l, hu, hd, sub_eq_add_neg] using hx l
    exact hmiss l (by dsimp [L] at hh; omega)
  · exact hd
  · exfalso
    rw [hd, mul_one] at hj
    have hu : u = 0 := by linarith [hlo i, hhi j]
    let l : Fin k := ⟨k-2, by omega⟩
    have hh : (x l : ℤ) = ((k-2 : ℕ) : ℤ) := by simpa [l, hu, hd, sub_eq_add_neg] using hx l
    exact hmiss l (by exact_mod_cast hh)

/-- The shared-deletion rule contains no nonconstant affine (k)-term
progression of exponent vectors, with either sign permitted in each step
coordinate. This is the article's `gpi:lem:kavoid`. -/
theorem sharedDeletionRule_step_zero {ι : Type*} [DecidableEq ι] {k : ℕ} (hk : 3 ≤ k)
    {G : Set ℕ} (hG : KTermAPFree k G)
    (hb : k-2 ∈ G) (hnext : k-2+1 ∉ G)
    {x : Fin k → Option ι → ℕ} (hmem : ∀ i, x i ∈ sharedDeletionRule (k-2) G)
    {u d : Option ι → ℤ} (hx : ∀ i p, (x i p : ℤ) = u p + (i.val : ℤ)*d p) :
    ∀ p, d p = 0 := by
  classical
  let b := k-2
  have hold {i : Fin k} (hi : x i none ≠ b+1) : x i ∈ sharedDeletionOld b G := by
    rcases hmem i with h | ⟨q,hq⟩
    · exact h
    · exact (hi (congrFun hq.symm none)).elim
  have hnew {i : Fin k} (hi : x i none = b+1) : ∃ q, sharedDeletionVector b q = x i := by
    rcases hmem i with h | h
    · exact (hnext (hi ▸ h.1 none)).elim
    · exact h
  by_cases hnone : ∀ i, x i none ≠ b+1
  · exact fun p ↦ hG (fun i ↦ x i p) (u p) (d p) (fun i ↦ (hold (hnone i)).1 p) (fun i ↦ hx i p)
  push Not at hnone
  obtain ⟨i, hi⟩ := hnone
  by_cases htwo : ∃ j : Fin k, j ≠ i ∧ x j none = b+1
  · obtain ⟨j,hji,hj⟩ := htwo
    have hd : d none = 0 := step_zero_of_repeat (fun t ↦ hx t none) hji (hj.trans hi.symm)
    have hmark (j : Fin k) : x j none = b+1 := by
      have h1 := hx i none
      have h2 := hx j none
      rw [hd] at h1 h2
      exact_mod_cast (by linarith only [h1, h2,
        (show (x i none : ℤ) = ((b+1 : ℕ) : ℤ) by exact_mod_cast hi)] :
        (x j none : ℤ) = ((b+1 : ℕ) : ℤ))
    intro p
    apply step_zero_of_two_values (b := b) hk (fun t ↦ hx t p)
    intro j
    obtain ⟨q, hq⟩ := hnew (hmark j)
    rw [← hq]
    cases p with
    | none => exact ⟨Nat.le_succ _, le_rfl⟩
    | some r =>
      by_cases he : r = q <;> simp [sharedDeletionVector, he]
  · obtain ⟨q,hq⟩ := hnew hi
    have hOld (j : Fin k) (hj : j ≠ i) : x j ∈ sharedDeletionOld b G :=
      hold (fun hm ↦ htwo ⟨j,hj,hm⟩)
    have hbase (r : ι) (hr : r ≠ q) : ∀ j, x j (some r) = b := by
      have hxi : x i (some r) = b := by simpa [sharedDeletionVector, hr] using congrFun hq.symm (some r)
      have hG' (j : Fin k) : x j (some r) ∈ G := by
        by_cases hj : j = i
        · simpa only [hj,hxi] using hb
        · exact (hOld j hj).1 (some r)
      have h := hG _ _ _ hG' (fun j ↦ hx j (some r))
      intro j
      have h1 := hx i (some r)
      have h2 := hx j (some r)
      rw [h,hxi] at h1
      rw [h] at h2
      exact_mod_cast (by linarith only [h1,h2] : (x j (some r) : ℤ) = b)
    have hqNew : x i (some q) = b+1 := by simpa [sharedDeletionVector] using congrFun hq.symm (some q)
    have hqOld (j : Fin k) (hj : j ≠ i) : x j (some q) < b := by
      have hothers : ∀ r, r ≠ q → x j (some r) = b := fun r hr ↦ hbase r hr j
      have h := hOld j hj
      have hne : x j (some q) ≠ b := fun he ↦ h.2.1 (fun r ↦ by
        by_cases hr : r = q
        · simpa only [hr] using he
        · exact hothers r hr)
      have hne' : x j (some q) ≠ b+1 := fun he ↦ hnext (he ▸ h.1 (some q))
      have hlt := h.2.2 q hothers
      omega
    have hdq : d (some q) = 0 := by
      apply step_zero_of_short_interval_missing hk (fun j ↦ hx j (some q))
      · intro j
        by_cases hj : j = i
        · simpa only [hj, hqNew] using (show b+1 ≤ k-1 by dsimp [b]; omega)
        · have h := hqOld j hj
          dsimp [b] at h
          omega
      · intro j
        by_cases hj : j = i
        · rw [hj,hqNew]
          dsimp [b]
          omega
        · have h := hqOld j hj
          dsimp [b] at h
          omega
    have hAnother : ∃ j : Fin k, j ≠ i := by
      let j : Fin k := ⟨0, by omega⟩
      let l : Fin k := ⟨1, by omega⟩
      by_cases hji : j = i
      · refine ⟨l, fun hli ↦ ?_⟩
        have he := congrArg Fin.val (hli.trans hji.symm)
        simp [j,l] at he
      · exact ⟨j,hji⟩
    obtain ⟨j,hji⟩ := hAnother
    have h1 := hx i (some q)
    have h2 := hx j (some q)
    rw [hdq,hqNew] at h1
    rw [hdq] at h2
    have hlt := hqOld j hji
    exfalso
    omega

end GRHArticle.ProgressionFree
