import Prefix

namespace BudgetAnalysis.Prefix

def candidates (qs : List Nat) : List Nat := 0 :: (qs ++ qs.map Nat.succ)

def startOfGap (j : Nat) : List Nat → Nat
  | [] => 0
  | q::qs => if q < j then max (q+1) (startOfGap j qs) else startOfGap j qs

theorem gap_le (j : Nat) (qs : List Nat) : startOfGap j qs ≤ j := by
  induction qs with
  | nil => exact Nat.zero_le _
  | cons q qs ih =>
    by_cases h : q < j <;> simp [startOfGap, h, Nat.max_le, ih] <;> omega

theorem gap_gt (j i : Nat) (qs : List Nat) (mem : i ∈ qs) (below : i < j) :
    i < startOfGap j qs := by
  induction qs with
  | nil => contradiction
  | cons q qs ih =>
    by_cases h : q < j
    · simp only [startOfGap, if_pos h]
      rcases List.mem_cons.mp mem with rfl | m
      · exact Nat.le_max_left .. 
      · exact Nat.le_trans (ih m) (Nat.le_max_right ..)
    · have ne : i ≠ q := by omega
      exact (if_neg h ▸ (ih ((List.mem_cons.mp mem).resolve_left ne)) :
        i < (if q < j then max (q+1) (startOfGap j qs) else startOfGap j qs))

theorem gap_source (j : Nat) (qs : List Nat) : startOfGap j qs = 0 ∨
    ∃ i ∈ qs, startOfGap j qs = i+1 := by
  induction qs with
  | nil => exact Or.inl rfl
  | cons q qs ih =>
    by_cases h : q < j ∧ startOfGap j qs ≤ q+1
    · exact Or.inr ⟨q, by simp, by simp [startOfGap, h.1, Nat.max_eq_left h.2]⟩
    · have eq : startOfGap j (q::qs) = startOfGap j qs := by
        by_cases b : q < j
        · simp [startOfGap, b, Nat.max_eq_right (by omega : q+1 ≤ startOfGap j qs)]
        · simp [startOfGap, b]
      rw [eq]
      rcases ih with zero | ⟨i,mem,ei⟩
      · exact Or.inl zero
      · exact Or.inr ⟨i, by simp [mem], ei⟩

/-- Bits before, at, and after the carry use different constraints. -/
def phase (i j : Nat) : Ordering :=
  if i < j then .lt else if i = j then .eq else .gt

theorem representative (qs : List Nat) (j : Nat) :
    ∃ r ∈ candidates qs, ∀ i ∈ qs, phase i r = phase i j := by
  by_cases mem : j ∈ qs
  · exact ⟨j, by simp [candidates, mem], by simp⟩
  · let r := startOfGap j qs
    have rin : r ∈ candidates qs := by
      rcases gap_source j qs with z | ⟨i,hi,eq⟩
      · simp [r, z, candidates]
      · simp only [r, eq, candidates, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inr ⟨i,hi,rfl⟩)
    refine ⟨r, rin, ?_⟩
    intro i hi
    by_cases h : i < j
    · have hr : i < r := gap_gt j i qs hi h
      simp [phase, h, hr]
    · have ne : i ≠ j := fun eq => mem (eq ▸ hi)
      have le : r ≤ j := gap_le j qs
      have gt : r < i := by omega
      simp [phase, h, ne, Nat.not_lt_of_ge (Nat.le_of_lt gt), Nat.ne_of_gt gt]

def permits : Option Bool → Bool → Bool
  | none, _ => true
  | some b, c => b == c

def carryOK (u v : Option Bool) : Ordering → Bool
  | .lt => pairOK u v
  | .eq => permits u false && permits v true
  | .gt => permits u true && permits v false

def keys (u v : Sparse) : List Nat := u.map Prod.fst ++ v.map Prod.fst

def atCarry (u v : Sparse) (j : Nat) : Bool :=
  (keys u v).all (fun i => carryOK (lookup u i) (lookup v i) (phase i j))

def hasCarry (u v : Sparse) : Bool :=
  (candidates (keys u v)).any (atCarry u v)

theorem sparse_carry_iff (u v : Sparse) :
    hasCarry u v = true ↔ ∃ j, atCarry u v j = true := by
  simp only [hasCarry, List.any_eq_true]
  constructor
  · rintro ⟨j,_,pass⟩
    exact ⟨j,pass⟩
  · rintro ⟨j,pass⟩
    obtain ⟨r,hr,rep⟩ := representative (keys u v) j
    refine ⟨r, hr, ?_⟩
    simp only [atCarry, List.all_eq_true] at pass ⊢
    intro i hi
    rw [rep i hi]
    exact pass i hi

/-- The pair's digits at a single address, for the two expansions of a dyadic. -/
def required : Ordering → Bool → Bool → Prop
  | .lt, x, y => x = y
  | .eq, x, y => x = false ∧ y = true
  | .gt, x, y => x = true ∧ y = false

def witnessDigits (a b : Option Bool) : Ordering → Bool × Bool
  | .lt =>
    let bit := a.getD (b.getD false)
    (bit,bit)
  | .eq => (false,true)
  | .gt => (true,false)

theorem local_sound (a b : Option Bool) (ph : Ordering) (ok : carryOK a b ph = true) :
    let w := witnessDigits a b ph
    permits a w.1 = true ∧ permits b w.2 = true ∧ required ph w.1 w.2 := by
  cases ph <;> cases a <;> cases b <;>
    simp_all [carryOK, pairOK, permits, required, witnessDigits]

theorem local_complete (a b : Option Bool) (ph : Ordering) (x y : Bool)
    (hx : permits a x = true) (hy : permits b y = true) (hxy : required ph x y) :
    carryOK a b ph = true := by
  cases ph <;> cases a <;> cases b <;> simp_all [carryOK, pairOK, permits, required]

theorem fixed_carry_realizable (u v : Sparse) (j : Nat) :
    atCarry u v j = true ↔ ∃ x y : BitIntegral.Oracle, Extends x (lookup u) ∧
      Extends y (lookup v) ∧ (∀ i, required (phase i j) (x i) (y i)) := by
  simp only [atCarry, List.all_eq_true]
  constructor
  · intro checks
    have ok (i : Nat) : carryOK (lookup u i) (lookup v i) (phase i j) = true := by
      by_cases hi : i ∈ keys u v
      · exact checks i hi
      · have absent (xs : Sparse) (sub : ∀ a ∈ xs.map Prod.fst, a ∈ keys u v) :
            lookup xs i = none := by
          cases val : lookup xs i with
          | none => rfl
          | some b => exact False.elim (hi (sub i (mem_keys xs i b val)))
        have hu := absent u (fun a ha => List.mem_append_left _ ha)
        have hv := absent v (fun a ha => List.mem_append_right _ ha)
        cases phase i j <;> simp [hu, hv, carryOK, pairOK, permits]
    let w (i : Nat) := witnessDigits (lookup u i) (lookup v i) (phase i j)
    refine ⟨fun i => (w i).1, fun i => (w i).2, ?_, ?_, ?_⟩
    · intro i b assigned
      have good : permits (lookup u i) (w i).1 = true := (local_sound _ _ _ (ok i)).1
      exact ((by simpa [assigned, permits] using good) : b = _).symm
    · intro i b assigned
      have good : permits (lookup v i) (w i).2 = true := (local_sound _ _ _ (ok i)).2.1
      exact ((by simpa [assigned, permits] using good) : b = _).symm
    · exact fun i => (local_sound _ _ _ (ok i)).2.2
  · rintro ⟨x,y,ex,ey,rule⟩ i _
    have permit (xs : Sparse) (z : BitIntegral.Oracle) (ez : Extends z (lookup xs)) :
        permits (lookup xs i) (z i) = true := by
      cases h : lookup xs i with
      | none => rfl
      | some b => simp [permits, ez i b h]
    exact local_complete _ _ _ _ _ (permit _ _ ex) (permit _ _ ey) (rule i)

/-- Executing the sparse test is equivalent to existence of two total compatible
streams with exactly the common-prefix, carry-bit and constant-tail shapes. -/
theorem finite_carry_iff (u v : Sparse) :
    hasCarry u v = true ↔ ∃ j, ∃ x y : BitIntegral.Oracle, Extends x (lookup u) ∧
      Extends y (lookup v) ∧ (∀ i, required (phase i j) (x i) (y i)) := by
  rw [sparse_carry_iff]
  apply exists_congr
  intro j
  exact fixed_carry_realizable u v j

end BudgetAnalysis.Prefix
