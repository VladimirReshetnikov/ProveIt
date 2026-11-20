import IPRAComplexity.Bounded

namespace IPRAComplexity

/-- An independently defined relational walk with an exact edge count. -/
inductive Walk (R : Nat → Nat → Prop) : Nat → Nat → Nat → Prop where
  | nil (u) : Walk R 0 u u
  | cons {n u w v} : R u w → Walk R n w v → Walk R (n + 1) u v

theorem Walk.append {R : Nat → Nat → Prop} {m n u v w : Nat}
    (p : Walk R m u v) (q : Walk R n v w) : Walk R (m + n) u w := by
  induction p with
  | nil => simpa using q
  | @cons m u z v h p ih =>
    have hh := Walk.cons h (ih q)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem Walk.split {R : Nat → Nat → Prop} (m n u v : Nat)
    (p : Walk R (m + n) u v) : ∃ w, Walk R m u w ∧ Walk R n w v := by
  induction m generalizing u with
  | zero => exact ⟨u, Walk.nil u, by simpa using p⟩
  | succ m ih =>
    have p' : Walk R ((m + n) + 1) u v := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using p
    cases p' with
    | @cons _ _ z _ h q =>
      obtain ⟨w, h₁, h₂⟩ := ih z q
      exact ⟨w, Walk.cons h h₁, h₂⟩

theorem Walk.map {R S : Nat → Nat → Prop} {n u v : Nat}
    (h : ∀ a b, R a b → S a b) (p : Walk R n u v) : Walk S n u v := by
  induction p with
  | nil u => exact Walk.nil u
  | cons hp _ ih => exact Walk.cons (h _ _ hp) ih

theorem Walk.stay {R : Nat → Nat → Prop} (n v : Nat) (h : R v v) :
    Walk R n v v := by
  induction n with
  | zero => exact Walk.nil v
  | succ n ih => exact Walk.cons h ih

/-- All vertices are coded in `[0,B)`; self-loops pad paths to an exact length. -/
def BoundedStep (B : Nat) (edge : Nat → Nat → Bool) (u v : Nat) : Prop :=
  u < B ∧ v < B ∧ (u = v ∨ edge u v = true)

def DirectedStep (B : Nat) (edge : Nat → Nat → Bool) (u v : Nat) : Prop :=
  u < B ∧ v < B ∧ edge u v = true

theorem Walk.source_bound {B : Nat} {edge : Nat → Nat → Bool}
    {n u v : Nat} (p : Walk (BoundedStep B edge) n u v) (hn : 0 < n) : u < B := by
  cases p with
  | nil => omega
  | cons h _ => exact h.1

theorem Walk.target_bound {B : Nat} {edge : Nat → Nat → Bool}
    {n u v : Nat} (p : Walk (BoundedStep B edge) n u v) (hn : 0 < n) : v < B := by
  induction p with
  | nil => omega
  | @cons n u w v h p ih =>
    cases n with
    | zero => cases p; exact h.2.1
    | succ n => exact ih (by omega)

theorem Walk.erase_stutters {B : Nat} {edge : Nat → Nat → Bool}
    {n u v : Nat} (p : Walk (BoundedStep B edge) n u v) :
    ∃ m, m ≤ n ∧ Walk (DirectedStep B edge) m u v := by
  induction p with
  | nil u => exact ⟨0, by omega, Walk.nil u⟩
  | @cons n u w v h p ih =>
    obtain ⟨m, hm, q⟩ := ih
    rcases h.2.2 with he | he
    · subst w
      exact ⟨m, by omega, q⟩
    · exact ⟨m + 1, by omega, Walk.cons ⟨h.1, h.2.1, he⟩ q⟩

/-- Divide-and-conquer reachability: at level k search paths of length at most 2^k.
The implementation is finite and primitive recursive after arithmetic coding.
-/
def reach (B : Nat) (edge : Nat → Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, u, v => decide (u < B) && decide (v < B) && ((u == v) || edge u v)
  | k + 1, u, v => bany (fun w => reach B edge k u w && reach B edge k w v) B

theorem reach_correct (B : Nat) (edge : Nat → Nat → Bool) (k u v : Nat) :
    reach B edge k u v = true ↔ Walk (BoundedStep B edge) (2 ^ k) u v := by
  induction k generalizing u v with
  | zero =>
    simp only [reach, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
      beq_iff_eq, Nat.pow_zero]
    constructor
    · rintro ⟨⟨hu, hv⟩, he⟩
      exact Walk.cons ⟨hu, hv, he⟩ (Walk.nil v)
    · intro p
      cases p with
      | cons h q => cases q; exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  | succ k ih =>
    simp only [reach, bany_correct, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨w, _, p, q⟩
      have h := p.append q
      simpa [Nat.pow_succ, Nat.mul_two] using h
    · intro p
      have p' : Walk (BoundedStep B edge) (2 ^ k + 2 ^ k) u v := by
        simpa [Nat.pow_succ, Nat.mul_two] using p
      obtain ⟨w, p₁, p₂⟩ := Walk.split (2 ^ k) (2 ^ k) u v p'
      have hk : 0 < 2 ^ k := Nat.two_pow_pos k
      exact ⟨w, p₁.target_bound hk, p₁, p₂⟩

/-- Full graph meaning: bounded reachability is equivalent to a directed walk
of length at most `2^k`, with valid source and target codes. -/
theorem reach_iff_short_walk (B : Nat) (edge : Nat → Nat → Bool) (k u v : Nat) :
    reach B edge k u v = true ↔
      u < B ∧ v < B ∧ ∃ n, n ≤ 2 ^ k ∧ Walk (DirectedStep B edge) n u v := by
  rw [reach_correct]
  constructor
  · intro p
    exact ⟨p.source_bound (Nat.two_pow_pos k), p.target_bound (Nat.two_pow_pos k),
      p.erase_stutters⟩
  · rintro ⟨_, hv, n, hn, p⟩
    have p' : Walk (BoundedStep B edge) n u v :=
      p.map (fun _ _ h => ⟨h.1, h.2.1, Or.inr h.2.2⟩)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hn
    rw [hd]
    exact p'.append (Walk.stay d v ⟨hv, hv, Or.inl rfl⟩)

end IPRAComplexity
