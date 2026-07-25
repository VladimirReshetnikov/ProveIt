import PresburgerArithmetic.Syntax

namespace PresburgerArithmetic

/-! The arithmetic heart of Cooper elimination.

`periodic_interval` is the finite-residue lemma used when eliminating one
integer variable.  It is deliberately stated independently of syntax: every
conjunction of divisibility atoms gives such a periodic predicate.
-/

theorem periodic_shift_of_mod
    {P : Int → Prop} {m : Nat}
    (hper : ∀ x, P (x + m) ↔ P x) :
    ∀ x k : Int, P (x + k * m) ↔ P x := by
  have hplus : ∀ n : Nat, ∀ x : Int, P (x + n * m) ↔ P x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have heq : x + (Nat.succ n : Int) * (m : Int) =
            (x + (n : Int) * m) + m := by
          push_cast
          ring
        rw [heq]
        exact (hper (x + n * m)).trans (ih x)
  have hminus : ∀ n : Nat, ∀ x : Int, P (x - n * m) ↔ P x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have heq : x - (Nat.succ n : Int) * (m : Int) + m =
            x - (n : Int) * m := by
          push_cast
          ring
        have hp := (hper (x - (Nat.succ n : Int) * m)).symm
        rw [heq] at hp
        exact hp.trans (ih x)
  intro x k
  cases k with
  | ofNat n => exact hplus n x
  | negSucc n =>
      have heq : x + Int.negSucc n * (m : Int) =
          x - ((n + 1 : Nat) : Int) * m := by
        rw [Int.negSucc_eq]
        push_cast
        ring
      rw [heq]
      exact hminus (n + 1) x

theorem periodic_interval
    {P : Int → Prop} {m : Nat} (hm : 0 < m)
    (hper : ∀ x, P (x + m) ↔ P x) (lo hi : Int) :
    (∃ x, lo ≤ x ∧ x ≤ hi ∧ P x) ↔
      ∃ k : Nat, k < m ∧ lo + k ≤ hi ∧ P (lo + k) := by
  constructor
  · rintro ⟨x, hlo, hhi, hx⟩
    let k : Nat := Int.toNat ((x - lo) % m)
    have hmz : (m : Int) ≠ 0 := by omega
    have hnonneg : 0 ≤ (x - lo) % (m : Int) := Int.emod_nonneg _ hmz
    have hlt : (x - lo) % (m : Int) < m := Int.emod_lt_of_pos _ (by omega)
    have hkcast : (k : Int) = (x - lo) % (m : Int) := by
      simp [k, Int.toNat_of_nonneg hnonneg]
    refine ⟨k, by omega, ?_, ?_⟩
    · have hqnonneg : 0 ≤ (x - lo) / (m : Int) :=
        Int.ediv_nonneg (by omega) (by omega)
      have hmulnonneg : 0 ≤ (x - lo) / (m : Int) * (m : Int) :=
        Int.mul_nonneg hqnonneg (by omega)
      have hdecomp := Int.ediv_mul_add_emod (x - lo) (m : Int)
      rw [hkcast]
      omega
    · let q := (x - lo) / (m : Int)
      have hdecomp := Int.ediv_mul_add_emod (x - lo) (m : Int)
      have heq : lo + (k : Int) + q * m = x := by
        rw [hkcast]
        dsimp [q]
        omega
      have hp := periodic_shift_of_mod hper (lo + k) q
      rw [heq] at hp
      exact hp.mp hx
  · rintro ⟨k, hk, hhi, hp⟩
    exact ⟨lo + k, by omega, hhi, hp⟩

theorem periodic_has_residue
    {P : Int → Prop} {m : Nat} (hm : 0 < m)
    (hper : ∀ x, P (x + m) ↔ P x) :
    (∃ x, P x) ↔ ∃ k : Nat, k < m ∧ P k := by
  constructor
  · rintro ⟨x, hx⟩
    let k : Nat := Int.toNat (x % m)
    have hmz : (m : Int) ≠ 0 := by omega
    have hnonneg : 0 ≤ x % (m : Int) := Int.emod_nonneg _ hmz
    have hlt : x % (m : Int) < m := Int.emod_lt_of_pos _ (by omega)
    have hkcast : (k : Int) = x % (m : Int) := by
      simp [k, Int.toNat_of_nonneg hnonneg]
    refine ⟨k, by omega, ?_⟩
    let q := x / (m : Int)
    have hdecomp := Int.ediv_mul_add_emod x (m : Int)
    have heq : (k : Int) + q * m = x := by
      rw [hkcast]
      dsimp [q]
      omega
    have hp := periodic_shift_of_mod hper (k : Int) q
    rw [heq] at hp
    exact hp.mp hx
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk⟩

def maxFrom (x : Int) : List Int → Int
  | [] => x
  | y :: ys => maxFrom (max x y) ys

def minFrom (x : Int) : List Int → Int
  | [] => x
  | y :: ys => minFrom (min x y) ys

theorem le_maxFrom_left (x : Int) (xs : List Int) : x ≤ maxFrom x xs := by
  induction xs generalizing x with
  | nil => simp [maxFrom]
  | cons y ys ih => exact le_trans (le_max_left _ _) (ih _)

theorem le_maxFrom_of_mem {x y : Int} {xs : List Int} (hy : y ∈ xs) :
    y ≤ maxFrom x xs := by
  induction xs generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
      simp only [List.mem_cons] at hy
      simp only [maxFrom]
      rcases hy with rfl | hy
      · exact le_trans (le_max_right _ _) (le_maxFrom_left _ _)
      · exact ih hy

theorem maxFrom_mem (x : Int) (xs : List Int) : maxFrom x xs ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [maxFrom]
  | cons y ys ih =>
      simp only [maxFrom]
      have h := ih (max x y)
      rcases List.mem_cons.mp h with h | h
      · by_cases hxy : x ≤ y
        · have hmax : max x y = y := max_eq_right hxy
          exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl (h.trans hmax))))
        · have hmax : max x y = x := max_eq_left (le_of_not_ge hxy)
          exact List.mem_cons.mpr (.inl (h.trans hmax))
      · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr h)))

theorem minFrom_le_left (x : Int) (xs : List Int) : minFrom x xs ≤ x := by
  induction xs generalizing x with
  | nil => simp [minFrom]
  | cons y ys ih => exact le_trans (ih _) (min_le_left _ _)

theorem minFrom_le_of_mem {x y : Int} {xs : List Int} (hy : y ∈ xs) :
    minFrom x xs ≤ y := by
  induction xs generalizing x with
  | nil => simp at hy
  | cons z zs ih =>
      simp only [List.mem_cons] at hy
      simp only [minFrom]
      rcases hy with rfl | hy
      · exact le_trans (minFrom_le_left _ _) (min_le_right _ _)
      · exact ih hy

theorem minFrom_mem (x : Int) (xs : List Int) : minFrom x xs ∈ x :: xs := by
  induction xs generalizing x with
  | nil => simp [minFrom]
  | cons y ys ih =>
      simp only [minFrom]
      have h := ih (min x y)
      rcases List.mem_cons.mp h with h | h
      · by_cases hxy : x ≤ y
        · have hmin : min x y = x := min_eq_left hxy
          exact List.mem_cons.mpr (.inl (h.trans hmin))
        · have hmin : min x y = y := min_eq_right (le_of_not_ge hxy)
          exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl (h.trans hmin))))
      · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr h)))

theorem periodic_unbounded_above
    {P : Int → Prop} {m : Nat} (hm : 0 < m)
    (hper : ∀ x, P (x + m) ↔ P x) (los : List Int) :
    (∃ x, (∀ l ∈ los, l ≤ x) ∧ P x) ↔ ∃ k : Nat, k < m ∧ P k := by
  constructor
  · rintro ⟨x, _, hx⟩
    exact periodic_has_residue hm hper |>.mp ⟨x, hx⟩
  · rintro ⟨k, hk, hp⟩
    cases los with
    | nil => exact ⟨k, by simp, hp⟩
    | cons l ls =>
        let q : Nat := Int.natAbs (maxFrom l ls - k) + 1
        let x : Int := k + q * m
        have hxP : P x := by
          simpa [x, Int.ofNat_eq_natCast] using
            (periodic_shift_of_mod hper (k : Int) q).mpr hp
        refine ⟨x, ?_, hxP⟩
        intro z hz
        have hzmax : z ≤ maxFrom l ls := by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact le_maxFrom_left _ _
          · exact le_maxFrom_of_mem hz
        have hq : maxFrom l ls ≤ x := by
          have habs : maxFrom l ls - k ≤ Int.natAbs (maxFrom l ls - k) :=
            Int.le_natAbs
          have hqm : (q : Int) ≤ q * (m : Int) := by
            calc
              (q : Int) = q * 1 := by ring
              _ ≤ q * (m : Int) :=
                Int.mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg q)
          calc
            maxFrom l ls = (k : Int) + (maxFrom l ls - k) := by ring
            _ ≤ k + Int.natAbs (maxFrom l ls - k) :=
              Int.add_le_add_left habs _
            _ ≤ k + (q : Int) := by dsimp [q]; norm_num
            _ ≤ k + q * (m : Int) := Int.add_le_add_left hqm _
            _ = x := rfl
        exact hzmax.trans hq

theorem periodic_unbounded_below
    {P : Int → Prop} {m : Nat} (hm : 0 < m)
    (hper : ∀ x, P (x + m) ↔ P x) (his : List Int) :
    (∃ x, (∀ h ∈ his, x ≤ h) ∧ P x) ↔ ∃ k : Nat, k < m ∧ P k := by
  constructor
  · rintro ⟨x, _, hx⟩
    exact periodic_has_residue hm hper |>.mp ⟨x, hx⟩
  · rintro ⟨k, hk, hp⟩
    cases his with
    | nil => exact ⟨k, by simp, hp⟩
    | cons h hs =>
        let q : Nat := Int.natAbs (k - minFrom h hs) + 1
        let x : Int := k - q * m
        have hxP : P x := by
          convert (periodic_shift_of_mod hper (k : Int) (-(q : Int))).mpr hp using 1
          simp [x]; ring
        refine ⟨x, ?_, hxP⟩
        intro z hz
        have hminz : minFrom h hs ≤ z := by
          rcases List.mem_cons.mp hz with rfl | hz
          · exact minFrom_le_left _ _
          · exact minFrom_le_of_mem hz
        have hxmin : x ≤ minFrom h hs := by
          have habs : k - minFrom h hs ≤ Int.natAbs (k - minFrom h hs) :=
            Int.le_natAbs
          have hqm : (q : Int) ≤ q * (m : Int) := by
            calc
              (q : Int) = q * 1 := by ring
              _ ≤ q * (m : Int) :=
                Int.mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg q)
          calc
            x = (k : Int) - q * (m : Int) := rfl
            _ ≤ k - (q : Int) := Int.sub_le_sub_left hqm _
            _ ≤ k - Int.natAbs (k - minFrom h hs) := by
              dsimp [q]
              norm_num
              omega
            _ ≤ minFrom h hs := by omega
        exact hxmin.trans hminz

theorem cooper_finite_criterion
    {P : Int → Prop} {m : Nat} (hm : 0 < m)
    (hper : ∀ x, P (x + m) ↔ P x) (los his : List Int) :
    (∃ x, (∀ l ∈ los, l ≤ x) ∧ (∀ h ∈ his, x ≤ h) ∧ P x) ↔
      if los.isEmpty || his.isEmpty then
        ∃ k : Nat, k < m ∧ P k
      else
        ∀ l ∈ los, ∀ h ∈ his,
          ∃ k : Nat, k < m ∧ l + k ≤ h ∧ P (l + k) := by
  cases los with
  | nil =>
      simp only [List.isEmpty_nil, Bool.true_or, if_true, List.not_mem_nil]
      simpa [and_assoc] using periodic_unbounded_below hm hper his
  | cons l ls =>
      cases his with
      | nil =>
          simp only [List.isEmpty_cons, List.isEmpty_nil, Bool.or_true, if_true,
            List.not_mem_nil]
          simpa [and_assoc] using periodic_unbounded_above hm hper (l :: ls)
      | cons h hs =>
          simp only [List.isEmpty_cons, Bool.false_or]
          constructor
          · rintro ⟨x, hlo, hhi, hp⟩ lo hloMem hi hhiMem
            apply periodic_interval hm hper lo hi |>.mp
            exact ⟨x, hlo lo hloMem, hhi hi hhiMem, hp⟩
          · intro hall
            let lo := maxFrom l ls
            let hi := minFrom h hs
            have hloMem : lo ∈ l :: ls := maxFrom_mem l ls
            have hhiMem : hi ∈ h :: hs := minFrom_mem h hs
            rcases hall lo hloMem hi hhiMem with ⟨k, hk, hbound, hp⟩
            refine ⟨lo + k, ?_, ?_, hp⟩
            · intro z hz
              have hzlo : z ≤ lo := by
                dsimp [lo]
                rcases List.mem_cons.mp hz with hzl | hz
                · rw [hzl]; exact le_maxFrom_left l ls
                · exact le_maxFrom_of_mem (x := l) (xs := ls) hz
              exact hzlo.trans (by omega)
            · intro z hz
              have hhiz : hi ≤ z := by
                dsimp [hi]
                rcases List.mem_cons.mp hz with hzh | hz
                · rw [hzh]; exact minFrom_le_left h hs
                · exact minFrom_le_of_mem (x := h) (xs := hs) hz
              exact hbound.trans hhiz

end PresburgerArithmetic
