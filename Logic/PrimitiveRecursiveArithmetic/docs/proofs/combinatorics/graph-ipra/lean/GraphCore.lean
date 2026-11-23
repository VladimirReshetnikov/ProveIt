import Std

/-! Finite tables and graph identities. All indices are natural numbers.
    A table is inspected only on its displayed finite range. -/
namespace GraphIPRA

def sumB (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumB f n + f n

theorem sumB_add (f g : Nat → Nat) (n : Nat) :
    sumB (fun i => f i + g i) n = sumB f n + sumB g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumB, ih]; omega

theorem sumB_congr {f g : Nat → Nat} (n : Nat)
    (h : ∀ i, i < n → f i = g i) : sumB f n = sumB g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumB]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumB_zero (n : Nat) : sumB (fun _ => 0) n = 0 := by
  induction n <;> simp_all [sumB]

def singleton (a v : Nat) := if a = v then 1 else 0

theorem sumB_singleton (a n : Nat) :
    sumB (singleton a) n = if a < n then 1 else 0 := by
  induction n with
  | zero => simp [sumB]
  | succ n ih =>
    simp only [sumB, ih, singleton]
    split <;> split <;> split <;> omega

structure Edges where
  n : Nat
  m : Nat
  tail : Nat → Nat
  head : Nat → Nat
  tail_lt : ∀ i, i < m → tail i < n
  head_lt : ∀ i, i < m → head i < n

def hits (endpoint : Nat → Nat) (k v : Nat) :=
  sumB (fun i => singleton (endpoint i) v) k

theorem hits_total (endpoint : Nat → Nat) (k n : Nat)
    (valid : ∀ i, i < k → endpoint i < n) :
    sumB (hits endpoint k) n = k := by
  induction k with
  | zero => exact sumB_zero n
  | succ k ih =>
    change sumB (fun v => hits endpoint k v + singleton (endpoint k) v) n = k + 1
    rw [sumB_add, ih (fun i hi => valid i (by omega)), sumB_singleton,
      if_pos (valid k (by omega))]

def outDegree (g : Edges) := hits g.tail g.m
def inDegree (g : Edges) := hits g.head g.m
def degree (g : Edges) (v : Nat) := outDegree g v + inDegree g v

theorem sum_out (g : Edges) : sumB (outDegree g) g.n = g.m :=
  hits_total _ _ _ g.tail_lt

theorem sum_in (g : Edges) : sumB (inDegree g) g.n = g.m :=
  hits_total _ _ _ g.head_lt

theorem handshaking (g : Edges) : sumB (degree g) g.n = 2 * g.m := by
  unfold degree
  rw [sumB_add, sum_out, sum_in]
  omega

def anyB (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => anyB p n || p n

theorem anyB_iff (p : Nat → Bool) (n : Nat) :
    anyB p n = true ↔ ∃ i, i < n ∧ p i = true := by
  induction n with
  | zero => simp [anyB]
  | succ n ih =>
    simp only [anyB, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, hp⟩ | hp)
      · exact ⟨i, by omega, hp⟩
      · exact ⟨n, by omega, hp⟩
    · rintro ⟨i, hi, hp⟩
      by_cases h : i = n
      · exact Or.inr (h ▸ hp)
      · exact Or.inl ⟨i, by omega, hp⟩

theorem sumB_pos (f : Nat → Nat) (n : Nat) :
    0 < sumB f n ↔ ∃ i, i < n ∧ 0 < f i := by
  induction n with
  | zero => simp [sumB]
  | succ n ih =>
    simp only [sumB]
    constructor
    · intro hp
      by_cases h : 0 < f n
      · exact ⟨n, by omega, h⟩
      · obtain ⟨i, hi, hf⟩ := ih.mp (by omega)
        exact ⟨i, by omega, hf⟩
    · rintro ⟨i, hi, hf⟩
      by_cases h : i = n
      · subst i; omega
      · have := ih.mpr ⟨i, by omega, hf⟩
        omega

/-- Digit at i in base b; graph bits use the full square encoding. -/
def digit (b data i : Nat) := (data / b ^ i) % b

def arc (n code u v : Nat) : Bool :=
  decide (u < n ∧ v < n ∧ digit 2 code (u*n+v) = 1)

/-- All intermediate and final vertices of nonempty walks are checked. -/
inductive Walk (edge : Nat → Nat → Bool) (n s : Nat) : Nat → Nat → Prop
  | nil (hs : s < n) : Walk edge n s 0 s
  | snoc {k u v} (p : Walk edge n s k u) (hv : v < n) (e : edge u v = true) :
      Walk edge n s (k + 1) v

theorem Walk.end_lt {edge n s k v} (p : Walk edge n s k v) : v < n := by
  cases p with
  | nil hs => exact hs
  | snoc _ hv _ => exact hv

/-- The length-k adjacency-power entry. This is the simple digraph version. -/
def walks (edge : Nat → Nat → Bool) (n s : Nat) : Nat → Nat → Nat
  | 0, v => if s = v ∧ v < n then 1 else 0
  | k+1, v => sumB (fun u => if v < n ∧ edge u v = true then walks edge n s k u else 0) n

theorem walks_pos (edge : Nat → Nat → Bool) (n s k v : Nat) :
    0 < walks edge n s k v ↔ Walk edge n s k v := by
  induction k generalizing v with
  | zero =>
    constructor
    · intro h
      have hv : s = v ∧ v < n := by
        by_cases hp : s = v ∧ v < n
        · exact hp
        · simp [walks, hp] at h
      obtain ⟨rfl, hs⟩ := hv
      exact .nil hs
    · intro h
      cases h with
      | nil hs => simp [walks, hs]
  | succ k ih =>
    rw [walks, sumB_pos]
    constructor
    · rintro ⟨u, _, hp⟩
      split at hp
      next h => exact .snoc ((ih u).mp hp) h.1 h.2
      next => exact False.elim ((Nat.lt_irrefl 0) hp)
    · intro h
      cases h with
      | @snoc _ u _ p hv e =>
        exact ⟨u, p.end_lt, by simpa [hv, e] using (ih u).mpr p⟩

def reachableBy (edge : Nat → Nat → Bool) (n s k v : Nat) : Bool :=
  anyB (fun j => decide (0 < walks edge n s j v)) (k+1)

theorem reachableBy_iff (edge : Nat → Nat → Bool) (n s k v : Nat) :
    reachableBy edge n s k v = true ↔ ∃ j, j ≤ k ∧ Walk edge n s j v := by
  rw [reachableBy, anyB_iff]
  simp [Nat.lt_succ_iff, walks_pos]

end GraphIPRA
