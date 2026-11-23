import OrdinalCore

/-! Computable local order facts for finite hereditary Cantor normal forms.
The successor and fundamental-sequence comparison theorems below even hold
before imposing canonicality. -/
namespace OrdinalPacket
open T

private theorem cmp_nil_ne_lt (x : T) : cmp x nil ≠ .lt := by
  cases x <;> simp [cmp]

/-- Appending a zero exponent is immediate successor in lexicographic order. -/
theorem immediate_succ (x y : T) :
    cmp x y = .lt ↔ cmp (succ x) y ≠ .gt := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => decide
    | cons c d =>
      cases c with
      | nil => cases d <;> simp [succ, append, one, principal, cmp]
      | cons => simp [succ, append, one, principal, cmp]
  | cons a b _ hb =>
    cases y with
    | nil => simp [cmp, succ, append]
    | cons c d =>
      cases h : cmp a c <;> simp [cmp, succ, append, h] <;> exact hb d

/-- Every term lies strictly below a term with that term as its first exponent. -/
theorem lt_cons_self (x t : T) : cmp x (cons x t) = .lt := by
  induction x generalizing t with
  | nil => rfl
  | cons a b ha _ => simp [cmp, ha b]

theorem lt_principal (x : T) : cmp x (principal x) = .lt :=
  lt_cons_self x nil

def tower : Nat → T
  | 0 => one
  | n+1 => principal (tower n)

theorem tower_step (n : Nat) : cmp (tower n) (tower (n+1)) = .lt :=
  lt_principal _

/-- On a canonical tree the leftmost branch has maximal depth. -/
def leftHeight : T → Nat
  | nil => 0
  | cons a _ => leftHeight a + 1

private theorem cons_lt_principal_iff (a b t : T) :
    cmp (cons a b) (principal t) = .lt ↔ cmp a t = .lt := by
  cases h : cmp a t <;> simp [principal, cmp, h, cmp_nil_ne_lt]

theorem tower_level (x : T) (n : Nat) :
    cmp x (tower n) = .lt ↔ leftHeight x ≤ n := by
  induction n generalizing x with
  | zero =>
    cases x with
    | nil => decide
    | cons a b => simp [tower, one, cons_lt_principal_iff, cmp_nil_ne_lt, leftHeight]
  | succ n ih =>
    cases x with
    | nil => simp [tower, principal, cmp, leftHeight]
    | cons a b => simp [tower, cons_lt_principal_iff, ih, leftHeight]

theorem tower_cofinal (x : T) : cmp x (tower (leftHeight x)) = .lt :=
  (tower_level x _).mpr (Nat.le_refl _)

/-- Passing n selects the n-th fundamental-sequence value in the limit case. -/
inductive LocalStep where
  | zero
  | successor (pred : T)
  | limit (value : T)
deriving DecidableEq, Repr

def localStep (n : Nat) : T → LocalStep
  | nil => .zero
  | cons a nil =>
    match localStep n a with
    | .zero => .successor nil
    | .successor p => .limit (copies p (n+1))
    | .limit u => .limit (principal u)
  | cons a (cons b t) =>
    match localStep n (cons b t) with
    | .zero => .zero
    | .successor p => .successor (cons a p)
    | .limit u => .limit (cons a u)

/-- The totalized function uses zero on zero and successor inputs. -/
def fundamental (x : T) (n : Nat) : T :=
  match localStep n x with
  | .limit u => u
  | _ => nil

private theorem cmp_copies_step (x : T) (n : Nat) :
    cmp (copies x n) (copies x (n+1)) = .lt := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [copies, cmp] using ih

/-- The tag is stable; successive approximants increase strictly and stay below x. -/
theorem localStep_spec (n : Nat) (x : T) :
    match localStep n x, localStep (n+1) x with
    | .zero, .zero => x = nil
    | .successor p, .successor q => q = p ∧ succ p = x
    | .limit u, .limit v => cmp u v = .lt ∧ cmp v x = .lt
    | _, _ => False := by
  induction x with
  | nil => rfl
  | cons a b ha hb =>
    cases b with
    | nil =>
      cases h : localStep n a <;> cases k : localStep (n+1) a <;>
        simp only [h, k] at ha <;> try contradiction
      case zero.zero =>
        subst a
        exact ⟨rfl, rfl⟩
      case successor.successor p q =>
        obtain ⟨rfl, rfl⟩ := ha
        simp only [localStep, h, k]
        exact ⟨cmp_copies_step _ _, by simp [copies, cmp, succ_gt]⟩
      case limit.limit u v =>
        simp only [localStep, h, k]
        exact ⟨by simpa [principal_cmp] using ha.1,
          by simp [principal, cmp, ha.2]⟩
    | cons b t =>
      cases h : localStep n (cons b t) <;> cases k : localStep (n+1) (cons b t) <;>
        simp only [h, k] at hb <;> try contradiction
      case successor.successor p q =>
        obtain ⟨rfl, he⟩ := hb
        simp only [localStep, h, k]
        exact ⟨trivial, congrArg (cons a) he⟩
      case limit.limit u v =>
        simp only [localStep, h, k, cmp, cmp_self]
        exact hb

theorem fundamental_increases (n : Nat) (x u : T) (h : localStep n x = .limit u) :
    cmp u (fundamental x (n+1)) = .lt ∧ cmp (fundamental x (n+1)) x = .lt := by
  have hs := localStep_spec n x
  cases k : localStep (n+1) x <;> simp [h, k, fundamental] at hs ⊢
  exact hs

theorem fundamental_lt (n : Nat) (x u : T) (h : localStep n x = .limit u) :
    cmp u x = .lt := by
  have hu := fundamental_increases n x u h
  exact cmp_trans _ _ _ hu.1 hu.2

example (n : Nat) : fundamental omega n = fin (n+1) := rfl
example (n : Nat) : fundamental (principal (fin 2)) n = copies one (n+1) := rfl
example (n : Nat) : fundamental (principal omega) n = principal (fin (n+1)) := rfl

/-- Ordinary rooted-tree node count. The list tail includes the same list root. -/
def nodes : T → Nat
  | nil => 1
  | cons a b => nodes a + nodes b

private theorem nodes_positive (x : T) : 0 < nodes x := by
  induction x with
  | nil => decide
  | cons a b ha hb => simp only [nodes]; omega

private theorem ok_children {a t : T} (h : ok (cons a t) = true) :
    ok a = true ∧ ok t = true := by
  simp only [ok, Bool.and_eq_true] at h
  exact h.1

private theorem ok_adjacent {a b t : T} (h : ok (cons a (cons b t)) = true) :
    cmp b a ≠ .gt := by
  have he : cmp a b ≠ .lt := by
    simp only [ok, Bool.and_eq_true, bne_iff_ne] at h
    exact h.2
  rw [cmp_swap]
  cases hc : cmp a b <;> simp_all

private theorem below_succ {a p : T} (h : cmp a (succ p) = .lt) :
    cmp a p ≠ .gt := by
  intro hc
  have l : cmp p a = .lt := by rw [cmp_swap, hc]; rfl
  apply (immediate_succ p a).mp l
  rw [cmp_swap, h]
  rfl

private theorem short_below_copies (y p : T) (n : Nat)
    (hy : ok y = true) (headBound : cmp (degree y) p ≠ .gt)
    (lengthBound : nodes y ≤ n) : cmp y (copies p (n+1)) = .lt := by
  induction y generalizing n with
  | nil => rfl
  | cons a t _ ht =>
    change cmp a p ≠ .gt at headBound
    cases h : cmp a p with
    | gt => exact False.elim (headBound h)
    | lt => simp [copies, cmp, h]
    | eq =>
      obtain rfl := (cmp_eq_iff a p).mp h
      cases n with
      | zero =>
        have hn := nodes_positive (cons a t)
        omega
      | succ n =>
        simp only [copies, cmp, cmp_self]
        have htail : cmp (degree t) a ≠ .gt := by
          cases t with
          | nil => cases a <;> simp [degree, cmp]
          | cons => exact ok_adjacent hy
        apply ht n (ok_children hy).2 htail
        simp only [nodes] at lengthBound
        have hn := nodes_positive a
        omega

private theorem step_pred {n : Nat} {a p : T} (h : localStep n a = .successor p) :
    succ p = a := by
  have hs := localStep_spec n a
  cases k : localStep (n+1) a <;> simp [h, k] at hs
  exact hs.2

/-- A comparator's node count is a uniform cofinality modulus. -/
theorem fundamental_cofinal (x : T) (n : Nat) (y u : T)
    (hl : localStep n x = .limit u) (hy : ok y = true)
    (h : cmp y x = .lt) (hb : nodes y ≤ n) : cmp y u = .lt := by
  induction x generalizing y u with
  | nil => simp [localStep] at hl
  | cons a t ha ht =>
    cases t with
    | nil =>
      cases hs : localStep n a with
      | zero => simp [localStep, hs] at hl
      | successor p =>
        simp only [localStep, hs, LocalStep.limit.injEq] at hl
        subst u
        cases y with
        | nil => rfl
        | cons d r =>
          have hd := (cons_lt_principal_iff d r a).mp h
          rw [← step_pred hs] at hd
          exact short_below_copies _ _ _ hy (below_succ hd) hb
      | limit v =>
        simp only [localStep, hs, LocalStep.limit.injEq] at hl
        subst u
        cases y with
        | nil => rfl
        | cons d r =>
          apply (cons_lt_principal_iff d r v).mpr
          apply ha d v hs (ok_children hy).1 ((cons_lt_principal_iff d r a).mp h)
          simp only [nodes] at hb
          omega
    | cons b t =>
      cases hs : localStep n (cons b t) with
      | zero => simp [localStep, hs] at hl
      | successor p => simp [localStep, hs] at hl
      | limit v =>
        simp only [localStep, hs, LocalStep.limit.injEq] at hl
        subst u
        cases y with
        | nil => rfl
        | cons d r =>
          apply (cons_lt_iff ..).mpr
          rcases (cons_lt_iff ..).mp h with hd | ⟨he, hr⟩
          · exact Or.inl hd
          · refine Or.inr ⟨he, ht r v hs (ok_children hy).2 hr ?_⟩
            simp only [nodes] at hb
            omega

private theorem ok_first_ge {a b t : T} (h : ok (cons a (cons b t)) = true) :
    cmp a b ≠ .lt := by
  simp only [ok, Bool.and_eq_true, bne_iff_ne] at h
  exact h.2

private theorem ok_cons_of (a b : T) (ha : ok a = true) (hb : ok b = true)
    (he : match b with | nil => True | cons c _ => cmp a c ≠ .lt) :
    ok (cons a b) = true := by
  cases b with
  | nil => simp [ok, ha]
  | cons c t => simpa only [ok, ha, Bool.true_and, Bool.and_eq_true, bne_iff_ne]
                  using And.intro hb he

private theorem ok_of_succ (p : T) (h : ok (succ p) = true) : ok p = true := by
  induction p with
  | nil => rfl
  | cons a t _ ht =>
    change ok (cons a (succ t)) = true at h
    apply ok_cons_of _ _ (ok_children h).1 (ht (ok_children h).2)
    cases t with
    | nil => trivial
    | cons b t => exact ok_first_ge h

theorem copies_ok (p : T) (hp : ok p = true) (n : Nat) : ok (copies p n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply ok_cons_of _ _ hp ih
    cases n with
    | zero => trivial
    | succ n => simp [copies, cmp_self]

theorem fundamental_ok (x : T) (n : Nat) (u : T)
    (hx : ok x = true) (h : localStep n x = .limit u) : ok u = true := by
  induction x generalizing u with
  | nil => simp [localStep] at h
  | cons a t ha ht =>
    cases t with
    | nil =>
      cases hs : localStep n a with
      | zero => simp [localStep, hs] at h
      | successor p =>
        simp only [localStep, hs, LocalStep.limit.injEq] at h
        subst u
        have hv := (ok_children hx).1
        rw [← step_pred hs] at hv
        exact copies_ok _ (ok_of_succ _ hv) _
      | limit v =>
        simp only [localStep, hs, LocalStep.limit.injEq] at h
        subst u
        exact ok_cons_of _ _ (ha v (ok_children hx).1 hs) rfl trivial
    | cons b t =>
      cases hs : localStep n (cons b t) with
      | zero => simp [localStep, hs] at h
      | successor p => simp [localStep, hs] at h
      | limit v =>
        simp only [localStep, hs, LocalStep.limit.injEq] at h
        subst u
        apply ok_cons_of _ _ (ok_children hx).1 (ht v (ok_children hx).2 hs)
        cases v with
        | nil => trivial
        | cons c r =>
          intro hac
          apply ok_first_ge hx
          rcases (cons_lt_iff ..).mp (fundamental_lt _ _ _ hs) with hcb | ⟨he, _⟩
          · exact cmp_trans _ _ _ hac hcb
          · exact he ▸ hac

private theorem leftHeight_mono (a b : T) (h : cmp a b ≠ .gt) :
    leftHeight a ≤ leftHeight b := by
  apply (tower_level _ _).mp
  cases e : cmp a b with
  | gt => exact False.elim (h e)
  | eq => rw [(cmp_eq_iff _ _).mp e]; exact tower_cofinal _
  | lt => exact cmp_trans _ _ _ e (tower_cofinal _)

/-- Height of the ordinary rooted tree (maximum over all branches). -/
def treeHeight : T → Nat
  | nil => 0
  | cons a t => max (treeHeight a + 1) (treeHeight t)

theorem canonical_height (x : T) (hx : ok x = true) : treeHeight x = leftHeight x := by
  induction x with
  | nil => rfl
  | cons a t ha ht =>
    simp only [treeHeight, leftHeight, ha (ok_children hx).1, ht (ok_children hx).2]
    apply Nat.max_eq_left
    cases t with
    | nil => exact Nat.zero_le _
    | cons b t => exact Nat.succ_le_succ (leftHeight_mono b a (ok_adjacent hx))

theorem canonical_tower_level (x : T) (n : Nat) (h : ok x = true) :
    cmp x (tower n) = .lt ↔ treeHeight x ≤ n := by
  rw [canonical_height x h, tower_level]

/-- A nonzero last exponent tests for a limit. -/
def endsPositive : T → Bool
  | nil => false
  | cons a nil => decide (a ≠ nil)
  | cons _ (cons b t) => endsPositive (cons b t)

def LocalStep.isLimit : LocalStep → Bool
  | .limit _ => true
  | _ => false

private theorem step_zero_iff (n : Nat) (x : T) : localStep n x = .zero ↔ x = nil := by
  constructor
  · intro h
    have hs := localStep_spec n x
    cases k : localStep (n+1) x <;> simp [h, k] at hs
    exact hs
  · rintro rfl
    rfl

theorem localStep_isLimit (x : T) (n : Nat) : (localStep n x).isLimit = endsPositive x := by
  induction x with
  | nil => rfl
  | cons a t _ ht =>
    cases t with
    | nil =>
      cases h : localStep n a with
      | zero =>
        obtain rfl := (step_zero_iff _ _).mp h
        rfl
      | successor p =>
        have hn : a ≠ nil := by rintro rfl; contradiction
        simp [localStep, h, endsPositive, LocalStep.isLimit, hn]
      | limit u =>
        have hn : a ≠ nil := by rintro rfl; contradiction
        simp [localStep, h, endsPositive, LocalStep.isLimit, hn]
    | cons b t =>
      cases h : localStep n (cons b t) <;>
        simpa [localStep, endsPositive, h, LocalStep.isLimit] using ht

theorem localStep_value (x : T) (n : Nat) (hl : endsPositive x = true) :
    localStep n x = .limit (fundamental x n) := by
  have hc := localStep_isLimit x n
  cases h : localStep n x <;> simp [h, LocalStep.isLimit, hl, fundamental] at hc ⊢

theorem fundamental_sequence (x : T) (n : Nat) (hx : ok x = true) (hl : endsPositive x = true) :
    ok (fundamental x n) = true ∧
    cmp (fundamental x n) (fundamental x (n+1)) = .lt ∧
    cmp (fundamental x (n+1)) x = .lt := by
  have h := localStep_value x n hl
  exact ⟨fundamental_ok _ _ _ hx h, fundamental_increases _ _ _ h⟩

theorem cofinal_modulus (x y : T) (n : Nat) (hl : endsPositive x = true)
    (hy : ok y = true) (h : cmp y x = .lt) (hb : nodes y ≤ n) :
    cmp y (fundamental x n) = .lt :=
  fundamental_cofinal _ _ _ _ (localStep_value x n hl) hy h hb

end OrdinalPacket
