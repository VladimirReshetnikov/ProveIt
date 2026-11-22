import Std

/-! Finite kernels of the closed-box nerve construction.
Coordinates of boxes have been put over a common positive denominator and
translated by a common origin. A vector of coordinates is read only below d.
All names and theorems below live in the host theory. -/
namespace PresentedTopology

structure Box where
  low : Nat → Nat
  high : Nat → Nat

def Box.Mem (b : Box) (d : Nat) (x : Nat → Nat) : Prop :=
  ∀ j, j < d → b.low j ≤ x j ∧ x j ≤ b.high j

def Box.cap (a b : Box) : Box :=
  ⟨fun j => max (a.low j) (b.low j), fun j => min (a.high j) (b.high j)⟩

theorem cap_mem (a b : Box) (d : Nat) (x : Nat → Nat) :
    (a.cap b).Mem d x ↔ a.Mem d x ∧ b.Mem d x := by
  constructor
  · intro h
    constructor
    · intro j hj
      obtain ⟨hl, hu⟩ := h j hj
      change max (a.low j) (b.low j) ≤ x j at hl
      change x j ≤ min (a.high j) (b.high j) at hu
      exact ⟨(Nat.max_le.mp hl).1, (Nat.le_min.mp hu).1⟩
    · intro j hj
      obtain ⟨hl, hu⟩ := h j hj
      change max (a.low j) (b.low j) ≤ x j at hl
      change x j ≤ min (a.high j) (b.high j) at hu
      exact ⟨(Nat.max_le.mp hl).2, (Nat.le_min.mp hu).2⟩
  · rintro ⟨ha, hb⟩ j hj
    exact ⟨Nat.max_le.mpr ⟨(ha j hj).1, (hb j hj).1⟩,
           Nat.le_min.mpr ⟨(ha j hj).2, (hb j hj).2⟩⟩

def meetAll (b : Box) : List Box → Box
  | [] => b
  | c :: cs => (meetAll b cs).cap c

theorem meetAll_mem (b : Box) (cs : List Box) (d : Nat) (x : Nat → Nat) :
    (meetAll b cs).Mem d x ↔ b.Mem d x ∧ ∀ c ∈ cs, c.Mem d x := by
  induction cs with
  | nil => simp [meetAll]
  | cons c cs ih =>
    simp only [meetAll, cap_mem, ih, List.mem_cons]
    constructor
    · rintro ⟨⟨hb, hs⟩, hc⟩
      refine ⟨hb, ?_⟩
      rintro k (rfl | h)
      · exact hc
      · exact hs k h
    · rintro ⟨hb, h⟩
      exact ⟨⟨hb, fun k hk => h k (Or.inr hk)⟩, h c (Or.inl rfl)⟩

/-- The lower corner of a nonempty intersection is a distinguished witness. -/
theorem lowerCornerCriterion (b : Box) (d : Nat) :
    (∃ x, b.Mem d x) ↔ b.Mem d b.low := by
  constructor
  · rintro ⟨x, h⟩ j hj
    exact ⟨Nat.le_refl _, Nat.le_trans (h j hj).1 (h j hj).2⟩
  · intro h
    exact ⟨b.low, h⟩

/-- Weighted sum of one coordinate, all integer denominators cleared. -/
def weighted (w a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => weighted w a n + w n * a n

def prefixSum (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => prefixSum a n + a n

theorem weighted_lower (m D n : Nat) (w a : Nat → Nat)
    (h : ∀ j, j < n → D ≤ m * a j) :
    D * prefixSum w n ≤ m * weighted w a n := by
  induction n with
  | zero => simp [weighted, prefixSum]
  | succ n ih =>
    have hi := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have ha := Nat.mul_le_mul_left (w n) (h n (Nat.lt_succ_self n))
    rw [prefixSum, weighted, Nat.mul_add, Nat.mul_add]
    have hb : D * w n ≤ m * (w n * a n) := by
      simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ha
    exact Nat.add_le_add hi hb

theorem term_le_sum (n i : Nat) (a : Nat → Nat) (hi : i < n) :
    a i ≤ prefixSum a n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [prefixSum]
    by_cases heq : i = n
    · subst i; omega
    · have hlt : i < n := by omega
      have h := ih hlt
      omega

def overlap (x v : Nat → Nat) (i : Nat) : Nat := min (x i) (v i)

theorem overlap_support (x v : Nat → Nat) (i : Nat) :
    0 < overlap x v i ↔ 0 < x i ∧ 0 < v i := by
  unfold overlap
  omega

/-- For x and v encoded over D, one common heavy coordinate bounds the
denominator of the normalized minimum away from zero by 1/m. -/
theorem overlap_mass (n i m D : Nat) (x v : Nat → Nat) (hi : i < n)
    (hx : D ≤ m * x i) (hv : D ≤ m * v i) :
    D ≤ m * prefixSum (overlap x v) n := by
  have hw : D ≤ m * overlap x v i := by
    by_cases h : x i ≤ v i
    · simpa [overlap, Nat.min_eq_left h] using hx
    · simpa [overlap, Nat.min_eq_right (by omega : v i ≤ x i)] using hv
  exact Nat.le_trans hw (Nat.mul_le_mul_left m (term_le_sum n i (overlap x v) hi))

/-- Arithmetic membership in a fixed simplex. Only the first n coordinates count. -/
def Supported (n : Nat) (J : Nat → Bool) (x : Nat → Nat) : Prop :=
  ∀ i, i < n → J i = false → x i = 0

/-- A weighted sum of two rational vectors x/D and y/E, at time b/(a+b).
The new denominator is (a+b)*D*E. -/
def blendNum (D E a b : Nat) (x y : Nat → Nat) (i : Nat) : Nat :=
  (a * E) * x i + (b * D) * y i

private theorem prefix_linear (n u v : Nat) (x y : Nat → Nat) :
    prefixSum (fun i => u * x i + v * y i) n =
    u * prefixSum x n + v * prefixSum y n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    simp only [prefixSum, ih, Nat.mul_add]
    omega

theorem blend_total (n D E a b : Nat) (x y : Nat → Nat)
    (hx : prefixSum x n = D) (hy : prefixSum y n = E) :
    prefixSum (blendNum D E a b x y) n = (a+b)*D*E := by
  unfold blendNum
  rw [prefix_linear, hx, hy]
  simp only [Nat.add_mul]
  ac_rfl

private theorem blend_supported (n D E a b : Nat) (J : Nat → Bool) (x y : Nat → Nat)
    (hx : Supported n J x) (hy : Supported n J y) :
    Supported n J (blendNum D E a b x y) := by
  intro i hi hJ
  simp [blendNum, hx i hi hJ, hy i hi hJ]

/-- Two rational segments join x/D to v/D through their normalized minimum.
Each segment has the asserted total and stays in the corresponding simplex.
For any a+b>0 these vectors have positive denominator. -/
theorem overlap_segments (n i m D a b : Nat) (x v : Nat → Nat) (J K : Nat → Bool)
    (hi : i < n) (hD : 0 < D) (hx : D ≤ m * x i) (hv : D ≤ m * v i)
    (tx : prefixSum x n = D) (tv : prefixSum v n = D)
    (jx : Supported n J x) (kv : Supported n K v) :
    let z := overlap x v
    let S := prefixSum z n
    0 < S ∧ Supported n J (blendNum D S a b x z) ∧
      Supported n K (blendNum S D a b z v) ∧
      prefixSum (blendNum D S a b x z) n = (a+b)*D*S ∧
      prefixSum (blendNum S D a b z v) n = (a+b)*S*D := by
  dsimp only
  have hp : 0 < prefixSum (overlap x v) n := by
    have hm := overlap_mass n i m D x v hi hx hv
    by_cases he : prefixSum (overlap x v) n = 0
    · rw [he, Nat.mul_zero] at hm
      omega
    · omega
  have jz : Supported n J (overlap x v) := by
    intro k hk hJ
    simp [overlap, jx k hk hJ]
  have kz : Supported n K (overlap x v) := by
    intro k hk hK
    simp [overlap, kv k hk hK]
  exact ⟨hp, blend_supported _ _ _ _ _ _ _ _ jx jz,
    blend_supported _ _ _ _ _ _ _ _ kz kv,
    blend_total _ _ _ _ _ _ _ tx rfl, blend_total _ _ _ _ _ _ _ rfl tv⟩

#print axioms overlap_segments
end PresentedTopology
