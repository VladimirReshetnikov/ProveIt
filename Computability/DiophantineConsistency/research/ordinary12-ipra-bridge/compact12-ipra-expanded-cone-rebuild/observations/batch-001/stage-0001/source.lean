import BusyBeaver.ZFC.ArithmeticMachineGraphPerm252

set_option autoImplicit false

/-!
# Internal offset segment bisimulation of numbered control programs

Two numbered control interpreters over a nine-register file are compared in
every model of `IΣ₁`. A finite external *certificate* pairs control numbers
`a` of machine `A` with control numbers `b` of machine `B`, together with two
standard offset vectors `α`, `β`: the pair relates an `A`-file `x + α` to the
`B`-file `x + β` for an arbitrary internal base file `x`.

From a related pair each side runs its straight-line segment (increments and
pure control steps) up to its next register test or halt, then executes the
test. Related tests read the same register, on which both accumulated offsets
agree; the certificate names the related successor entry of each branch. Each
such segment costs at least one instruction on both sides (the test itself),
so one `Σ₁` induction transports halting in both directions (`halts_iff`).

`checkFrom`/`entryOK` are external Boolean computations, evaluated by the
kernel on concrete catalogues. Their soundness (`entry_step`) is proved once for
arbitrary internal register values. Concrete machines enter only through the
abstract step equations `spec`, so this module fixes no catalogue and no file
encoding.

The method follows the segment bisimulation of `RMBisim` (after upstream
`Bisim.v` by Mira-Cult and Jeff Ketchersid), extended by register offsets so
that transfer-plus-one loop rotations are covered as well.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! ## External certificate data -/

/-- One numbered instruction: opcode 1 increments `reg` and continues at
`next0`; opcode 2 tests `reg`, continuing at `next0` on zero and decrementing
and continuing at `next1` otherwise; opcode 3 is a pure control step to
`next0`; opcode 4 halts. -/
structure Row where
  op : Nat
  reg : Fin 9
  next0 : Nat
  next1 : Nat
  deriving DecidableEq, Repr

/-- An offset vector, read with default zero. -/
abbrev Vec := List Nat

/-- Structural read (kernel-fast; no typeclass indexing). -/
def vget : Vec → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: u, p+1 => vget u p

def bump : Vec → Nat → Vec
  | [], 0 => [1]
  | [], p+1 => 0 :: bump [] p
  | x :: u, 0 => (x+1) :: u
  | x :: u, p+1 => x :: bump u p

theorem vget_nil (p : Nat) : vget [] p = 0 := by cases p <;> rfl

theorem vget_bump (u : Vec) (r p : Nat) :
    vget (bump u r) p = vget u p + if p = r then 1 else 0 := by
  induction u generalizing r p with
  | nil =>
    induction r generalizing p with
    | zero => cases p <;> simp [bump, vget]
    | succ r ih =>
      cases p with
      | zero => simp [bump, vget]
      | succ p => simpa [bump, vget, vget_nil] using ih p
  | cons x u ih =>
    cases r with
    | zero => cases p <;> simp [bump, vget]
    | succ r =>
      cases p with
      | zero => simp [bump, vget]
      | succ p => simpa [bump, vget] using ih r p

def vhead : Vec → Nat
  | [] => 0
  | x :: _ => x

def vtail : Vec → Vec
  | [] => []
  | _ :: u => u

/-- Offset left over after moving the pointwise minimum into the base (first `n`
registers). -/
def vnormN : Nat → Vec → Vec → Vec
  | 0, _, _ => []
  | n+1, u, v => (vhead u - min (vhead u) (vhead v)) :: vnormN n (vtail u) (vtail v)

def vnorm (u v : Vec) : Vec := vnormN 9 u v

theorem vget_vnormN (n : Nat) (u v : Vec) (p : Nat) (hp : p < n) :
    vget (vnormN n u v) p = vget u p - min (vget u p) (vget v p) := by
  induction n generalizing u v p with
  | zero => omega
  | succ n ih =>
    cases p with
    | zero => cases u <;> cases v <;> simp [vnormN, vget, vhead]
    | succ p =>
      have h := ih (vtail u) (vtail v) p (by omega)
      cases u <;> cases v <;> simp_all [vnormN, vget, vtail, vget_nil]

theorem vget_vnorm (u v : Vec) (p : Fin 9) :
    vget (vnorm u v) p = vget u p - min (vget u p) (vget v p) :=
  vget_vnormN 9 u v p p.isLt

/-- One certificate entry: related controls, their offsets, and the indices of
the successor entries for the zero and the positive branch. -/
structure Entry where
  a : Nat
  b : Nat
  α : Vec
  β : Vec
  s0 : Nat
  s1 : Nat
  deriving DecidableEq, Repr

/-- Straight-line segment from control `c` with accumulated offset `u`: follows
increments and pure control steps to the next test or halt. -/
def segment (rows : Nat → Option Row) : Nat → Nat → Vec → Option (Nat × Vec)
  | 0, _, _ => none
  | fuel+1, c, u =>
    match rows c with
    | none => none
    | some row =>
      if row.op = 2 ∨ row.op = 4 then some (c, u)
      else if row.op = 1 then segment rows fuel row.next0 (bump u row.reg)
      else if row.op = 3 then segment rows fuel row.next0 u
      else none

def entryIs (e : Entry) (a b : Nat) (α β : Vec) : Bool :=
  e.a == a && e.b == b && e.α == α && e.β == β

theorem entryIs_eq {e : Entry} {a b : Nat} {α β : Vec} (h : entryIs e a b α β = true) :
    e.a = a ∧ e.b = b ∧ e.α = α ∧ e.β = β := by
  simp only [entryIs, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The local check of one entry against the two catalogues. -/
def checkEntry (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel : Nat) (e : Entry) : Bool :=
  match segment rowsA fuel e.a e.α, segment rowsB fuel e.b e.β with
  | some (ta, ua), some (tb, ub) =>
    match rowsA ta, rowsB tb with
    | some ra, some rb =>
      if ra.op = 4 ∧ rb.op = 4 then true
      else if ra.op = 2 ∧ rb.op = 2 ∧ ra.reg = rb.reg ∧
          vget ua ra.reg = vget ub ra.reg then
        (match cert e.s0 with
          | some e0 => entryIs e0 ra.next0 rb.next0 (vnorm ua ub) (vnorm ub ua)
          | none => false) &&
        (match cert e.s1 with
          | some e1 => entryIs e1 ra.next1 rb.next1 (vnorm ua ub) (vnorm ub ua)
          | none => false)
      else false
    | _, _ => false
  | _, _ => false

/-- What a passing entry check guarantees, in a form usable without unfolding. -/
theorem checkEntry_spec (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel : Nat) (e : Entry) (h : checkEntry rowsA rowsB cert fuel e = true) :
    ∃ ta ua tb ub ra rb,
      segment rowsA fuel e.a e.α = some (ta, ua) ∧
      segment rowsB fuel e.b e.β = some (tb, ub) ∧
      rowsA ta = some ra ∧ rowsB tb = some rb ∧
      ((ra.op = 4 ∧ rb.op = 4) ∨
       (ra.op = 2 ∧ rb.op = 2 ∧ ra.reg = rb.reg ∧ vget ua ra.reg = vget ub ra.reg ∧
        (∃ e0, cert e.s0 = some e0 ∧
          entryIs e0 ra.next0 rb.next0 (vnorm ua ub) (vnorm ub ua) = true) ∧
        (∃ e1, cert e.s1 = some e1 ∧
          entryIs e1 ra.next1 rb.next1 (vnorm ua ub) (vnorm ub ua) = true))) := by
  unfold checkEntry at h
  split at h
  next ta ua tb ub hsa hsb =>
    split at h
    next ra rb hra hrb =>
      refine ⟨ta, ua, tb, ub, ra, rb, hsa, hsb, hra, hrb, ?_⟩
      by_cases hh : ra.op = 4 ∧ rb.op = 4
      · exact .inl hh
      rw [if_neg hh] at h
      by_cases ht : ra.op = 2 ∧ rb.op = 2 ∧ ra.reg = rb.reg ∧
          vget ua ra.reg = vget ub ra.reg
      · rw [if_pos ht, Bool.and_eq_true] at h
        obtain ⟨h0, h1⟩ := h
        refine .inr ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2, ?_, ?_⟩
        · split at h0
          next e0 he0 => exact ⟨e0, he0, h0⟩
          next => cases h0
        · split at h1
          next e1 he1 => exact ⟨e1, he1, h1⟩
          next => cases h1
      · rw [if_neg ht] at h
        cases h
    next => cases h
  next => cases h

/-- One entry exists, passes the local check, and names successors below `bound`. -/
def entryOK (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound i : Nat) : Bool :=
  match cert i with
  | some e => checkEntry rowsA rowsB cert fuel e && decide (e.s0 < bound) &&
      decide (e.s1 < bound) && decide (0 < e.a)
  | none => false

/-- Entries `i, …, i+k-1` pass `entryOK`; the entry check is evaluated first so
that the recursive call is in tail position for the kernel. -/
def checkFrom (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | i, k+1 => entryOK rowsA rowsB cert fuel bound i && checkFrom rowsA rowsB cert fuel bound (i+1) k

theorem checkFrom_entry (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound i k : Nat) (h : checkFrom rowsA rowsB cert fuel bound i k = true)
    (j : Nat) (hj : i ≤ j) (hjk : j < i + k) : entryOK rowsA rowsB cert fuel bound j = true := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact h.1
    · exact ih (i+1) h.2 (by omega) (by omega)

theorem entryOK_spec (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound i : Nat) (h : entryOK rowsA rowsB cert fuel bound i = true) :
    ∃ e, cert i = some e ∧ checkEntry rowsA rowsB cert fuel e = true ∧
      e.s0 < bound ∧ e.s1 < bound ∧ 0 < e.a := by
  unfold entryOK at h
  revert h
  cases cert i with
  | none => simp
  | some e =>
    intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨e, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ## A generic two-sided positive transport -/

section Transport

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (runA runB : V → V → V) (R : V → V → Prop)
  [𝚺₁-Function₂[V] runA] [𝚺₁-Function₂[V] runB] [𝚺₁-Relation[V] R]
  (runA_zero : ∀ x, runA 0 x = x) (runB_zero : ∀ x, runB 0 x = x)
  (runA_add : ∀ t u x, runA (t+u) x = runA u (runA t x))
  (runB_add : ∀ t u x, runB (t+u) x = runB u (runB t x))
  (runA_halted : ∀ t, runA t 0 = 0) (runB_halted : ∀ t, runB t 0 = 0)
  (rel_live : ∀ a b, R a b → a ≠ 0 ∧ b ≠ 0)
  (rel_step : ∀ a b, R a b → ∃ ka kb, 1 ≤ ka ∧ 1 ≤ kb ∧
    ((runA ka a = 0 ∧ runB kb b = 0) ∨ R (runA ka a) (runB kb b)))

include runA_zero runB_zero runA_add runB_add runA_halted runB_halted rel_step in
/-- Both clocks pass any internal bound while staying related or jointly halted. -/
theorem clocks (a0 b0 : V) (h0 : R a0 b0) (n : V) :
    ∃ ta tb, n ≤ ta ∧ n ≤ tb ∧
      ((runA ta a0 = 0 ∧ runB tb b0 = 0) ∨ R (runA ta a0) (runB tb b0)) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, 0, le_rfl, le_rfl, .inr (by simpa only [runA_zero, runB_zero] using h0)⟩
  case succ n ih =>
    obtain ⟨ta, tb, hta, htb, hq⟩ := ih
    rcases hq with ⟨hza, hzb⟩ | hr
    · refine ⟨ta+1, tb+1, add_le_add hta le_rfl, add_le_add htb le_rfl, .inl ⟨?_, ?_⟩⟩
      · rw [runA_add, hza, runA_halted]
      · rw [runB_add, hzb, runB_halted]
    · obtain ⟨ka, kb, hka, hkb, hs⟩ := rel_step _ _ hr
      refine ⟨ta+ka, tb+kb, add_le_add hta hka, add_le_add htb hkb, ?_⟩
      rw [runA_add, runB_add]
      exact hs

include runA_zero runB_zero runA_add runB_add runA_halted runB_halted rel_live rel_step in
/-- Related starts halt together. All clocks and register values are internal. -/
theorem halts_iff (a0 b0 : V) (h0 : R a0 b0) :
    (∃ t, runA t a0 = 0) ↔ (∃ t, runB t b0 = 0) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨ta, tb, hta, _, hq⟩ := clocks runA runB R runA_zero runB_zero runA_add runB_add
      runA_halted runB_halted rel_step a0 b0 h0 t
    have hz : runA ta a0 = 0 := by
      rw [← add_tsub_cancel_of_le hta, runA_add, ht, runA_halted]
    rcases hq with ⟨_, hzb⟩ | hr
    · exact ⟨tb, hzb⟩
    · exact absurd hz (rel_live _ _ hr).1
  · rintro ⟨t, ht⟩
    obtain ⟨ta, tb, _, htb, hq⟩ := clocks runA runB R runA_zero runB_zero runA_add runB_add
      runA_halted runB_halted rel_step a0 b0 h0 t
    have hz : runB tb b0 = 0 := by
      rw [← add_tsub_cancel_of_le htb, runB_add, ht, runB_halted]
    rcases hq with ⟨hza, _⟩ | hr
    · exact ⟨ta, hza⟩
    · exact absurd hz (rel_live _ _ hr).2

end Transport

/-! ## Arithmetic semantics of a catalogue -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### The register-file algebra -/

variable (reg : V → Fin 9 → V) (write : Fin 9 → V → V → V) (live : V → V → V)

/-- `y` is the base file `x` shifted by the standard offset `u`. -/
def Shifted (x : V) (u : Vec) (y : V) : Prop := ∀ p : Fin 9, reg y p = reg x p + (vget u p : V)

/-- Expected one-step result of a catalogue row at file `x`. -/
noncomputable def sem (row : Row) (x : V) : V :=
  if row.op = 1 then live (row.next0 : V) (write row.reg (reg x row.reg + 1) x)
  else if row.op = 2 then
    if reg x row.reg = 0 then live (row.next0 : V) x
    else live (row.next1 : V) (write row.reg (reg x row.reg - 1) x)
  else if row.op = 3 then live (row.next0 : V) x
  else 0

variable {reg write live}

section Laws

variable
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)

include reg_write_same reg_write_other

theorem shifted_bump (x y : V) (u : Vec) (r : Fin 9) (h : Shifted reg x u y) :
    Shifted reg x (bump u r) (write r (reg y r + 1) y) := by
  intro p
  by_cases hp : r = p
  · subst hp
    rw [reg_write_same, h r, vget_bump]
    simp only [if_true, Nat.cast_add, Nat.cast_one, add_assoc]
  · rw [reg_write_other _ _ _ _ hp, h p, vget_bump]
    have hp' : (p : Nat) ≠ r := fun he => hp (Fin.ext he.symm)
    simp only [hp', if_false, add_zero]

/-- Decrementing a register on which the offset vanishes moves the base. -/
theorem shifted_decrement (x y : V) (u : Vec) (r : Fin 9) (h : Shifted reg x u y)
    (hu : vget u r = 0) :
    Shifted reg (write r (reg x r - 1) x) u (write r (reg y r - 1) y) := by
  intro p
  by_cases hp : r = p
  · subst hp
    rw [reg_write_same, reg_write_same, h r, hu]
    simp
  · rw [reg_write_other _ _ _ _ hp, reg_write_other _ _ _ _ hp, h p]

end Laws

/-- Moving the common part of two offsets into the base. -/
theorem shifted_norm (x ya yb : V) (ua ub : Vec)
    (ha : Shifted reg x ua ya) (hb : Shifted reg x ub yb)
    (x' : V) (hx' : ∀ p : Fin 9, reg x' p = reg x p + ((min (vget ua p) (vget ub p) : Nat) : V)) :
    Shifted reg x' (vnorm ua ub) ya ∧ Shifted reg x' (vnorm ub ua) yb := by
  constructor
  · intro p
    rw [ha p, hx' p, vget_vnorm, add_assoc, ← Nat.cast_add]
    congr 2
    omega
  · intro p
    rw [hb p, hx' p, vget_vnorm, add_assoc, ← Nat.cast_add]
    congr 2
    omega

/-! ### A machine described by a catalogue -/

section Segment

variable (step : V → V) (run : V → V → V) (rows : Nat → Option Row)
  (run_zero : ∀ x, run 0 x = x)
  (run_add : ∀ t u x, run (t+u) x = run u (run t x))
  (run_one : ∀ x, run 1 x = step x)
  (spec : ∀ (c : Nat) (row : Row) (x : V), rows c = some row →
    step (live (c : V) x) = sem reg write live row x)
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)

include run_zero run_add run_one spec reg_write_same reg_write_other

/-- Soundness of the straight-line segment walk, by external induction on its
standard fuel. The base file and all register values are internal. -/
theorem segment_sound (fuel c : Nat) (u : Vec) (t : Nat) (u' : Vec)
    (hs : segment rows fuel c u = some (t, u')) (x y : V) (hy : Shifted reg x u y) :
    ∃ k y', run k (live (c : V) y) = live (t : V) y' ∧ Shifted reg x u' y' := by
  induction fuel generalizing c u y with
  | zero => simp [segment] at hs
  | succ fuel ih =>
    rcases hr : rows c with _ | row
    · simp [segment, hr] at hs
    · simp only [segment, hr] at hs
      by_cases hstop : row.op = 2 ∨ row.op = 4
      · rw [if_pos hstop] at hs
        cases hs
        exact ⟨0, y, run_zero _, hy⟩
      rw [if_neg hstop] at hs
      have h2 : row.op ≠ 2 := fun h => hstop (.inl h)
      by_cases h1 : row.op = 1
      · rw [if_pos h1] at hs
        obtain ⟨k, y', hk, hy'⟩ := ih row.next0 (bump u row.reg) hs
          (write row.reg (reg y row.reg + 1) y)
          (shifted_bump reg_write_same reg_write_other x y u row.reg hy)
        refine ⟨1+k, y', ?_, hy'⟩
        rw [run_add, run_one, spec c row y hr, sem, if_pos h1, hk]
      · rw [if_neg h1] at hs
        by_cases h3 : row.op = 3
        · rw [if_pos h3] at hs
          obtain ⟨k, y', hk, hy'⟩ := ih row.next0 u hs y hy
          refine ⟨1+k, y', ?_, hy'⟩
          rw [run_add, run_one, spec c row y hr, sem, if_neg h1, if_neg h2, if_pos h3, hk]
        · rw [if_neg h3] at hs
          cases hs

end Segment

/-! ### One certified segment on both sides -/

section Entry

variable (fileOf : (Fin 9 → V) → V) (reg_fileOf : ∀ g p, reg (fileOf g) p = g p)
  (stepA stepB : V → V) (runA runB : V → V → V) (rowsA rowsB : Nat → Option Row)
  (cert : Nat → Option Entry) (fuel : Nat)
  (runA_zero : ∀ x, runA 0 x = x) (runB_zero : ∀ x, runB 0 x = x)
  (runA_add : ∀ t u x, runA (t+u) x = runA u (runA t x))
  (runB_add : ∀ t u x, runB (t+u) x = runB u (runB t x))
  (runA_one : ∀ x, runA 1 x = stepA x) (runB_one : ∀ x, runB 1 x = stepB x)
  (specA : ∀ (c : Nat) (row : Row) (x : V), rowsA c = some row →
    stepA (live (c : V) x) = sem reg write live row x)
  (specB : ∀ (c : Nat) (row : Row) (x : V), rowsB c = some row →
    stepB (live (c : V) x) = sem reg write live row x)
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)

/-- The successor pair of a certified entry: both runs are again related by
the named successor entry, over a new internal base file. -/
def Next (e' : Entry) (a b : V) : Prop :=
  ∃ x' ya' yb', a = live (e'.a : V) ya' ∧ b = live (e'.b : V) yb' ∧
    Shifted reg x' e'.α ya' ∧ Shifted reg x' e'.β yb'

include reg_fileOf runA_zero runB_zero runA_add runB_add runA_one runB_one specA specB
  reg_write_same reg_write_other in
theorem entry_step (e : Entry) (hc : checkEntry rowsA rowsB cert fuel e = true)
    (x ya yb : V) (ha : Shifted reg x e.α ya) (hb : Shifted reg x e.β yb) :
    ∃ ka kb, 1 ≤ ka ∧ 1 ≤ kb ∧
      ((runA ka (live (e.a : V) ya) = 0 ∧ runB kb (live (e.b : V) yb) = 0) ∨
       ∃ s e', (s = e.s0 ∨ s = e.s1) ∧ cert s = some e' ∧
         Next (reg := reg) (live := live) e' (runA ka (live (e.a : V) ya))
           (runB kb (live (e.b : V) yb))) := by
  obtain ⟨ta, ua, tb, ub, ra, rb, hsa, hsb, hra, hrb, hcase⟩ :=
    checkEntry_spec rowsA rowsB cert fuel e hc
  obtain ⟨k1, ya1, hk1, hya1⟩ := segment_sound stepA runA rowsA runA_zero runA_add runA_one
    specA reg_write_same reg_write_other fuel e.a e.α ta ua hsa x ya ha
  obtain ⟨k2, yb1, hk2, hyb1⟩ := segment_sound stepB runB rowsB runB_zero runB_add runB_one
    specB reg_write_same reg_write_other fuel e.b e.β tb ub hsb x yb hb
  have hA : ∀ t, runA (k1+t) (live (e.a : V) ya) = runA t (live (ta : V) ya1) := by
    intro t; rw [runA_add, hk1]
  have hB : ∀ t, runB (k2+t) (live (e.b : V) yb) = runB t (live (tb : V) yb1) := by
    intro t; rw [runB_add, hk2]
  have hpos : ∀ k : V, 1 ≤ k + 1 := fun k => le_add_self
  rcases hcase with ⟨ha4, hb4⟩ | ⟨ha2, hb2, hreg, hoff, ⟨e0, he0, hm0⟩, ⟨e1, he1, hm1⟩⟩
  · refine ⟨k1+1, k2+1, hpos _, hpos _, .inl ⟨?_, ?_⟩⟩
    · rw [hA, runA_one, specA ta ra ya1 hra, sem]
      simp [ha4]
    · rw [hB, runB_one, specB tb rb yb1 hrb, sem]
      simp [hb4]
  -- the common part of the accumulated offsets moves into the base
  set x' := fileOf (fun p => reg x p + ((min (vget ua p) (vget ub p) : Nat) : V)) with hx'
  have hx'p : ∀ p : Fin 9, reg x' p = reg x p + ((min (vget ua p) (vget ub p) : Nat) : V) :=
    fun p => by rw [hx', reg_fileOf]
  obtain ⟨hsa', hsb'⟩ := shifted_norm x ya1 yb1 ua ub hya1 hyb1 x' hx'p
  set r := ra.reg
  have hra0 : vget (vnorm ua ub) r = 0 := by
    rw [vget_vnorm]; omega
  have hrb0 : vget (vnorm ub ua) r = 0 := by
    rw [vget_vnorm]; omega
  have hva : reg ya1 r = reg x' r := by rw [hsa' r, hra0]; simp
  have hvb : reg yb1 r = reg x' r := by rw [hsb' r, hrb0]; simp
  have hvb' : reg yb1 rb.reg = reg x' r := by rw [← hreg]; exact hvb
  obtain ⟨h0a, h0b, h0α, h0β⟩ := entryIs_eq hm0
  obtain ⟨h1a, h1b, h1α, h1β⟩ := entryIs_eq hm1
  have ha1 : ra.op ≠ 1 := by omega
  have hb1 : rb.op ≠ 1 := by omega
  refine ⟨k1+1, k2+1, hpos _, hpos _, .inr ?_⟩
  by_cases hz : reg x' r = 0
  · refine ⟨e.s0, e0, .inl rfl, he0, x', ya1, yb1, ?_, ?_, ?_, ?_⟩
    · rw [hA, runA_one, specA ta ra ya1 hra, sem, if_neg ha1, if_pos ha2, if_pos (hva.trans hz),
        h0a]
    · rw [hB, runB_one, specB tb rb yb1 hrb, sem, if_neg hb1, if_pos hb2,
        if_pos (hvb'.trans hz), h0b]
    · rw [h0α]; exact hsa'
    · rw [h0β]; exact hsb'
  · refine ⟨e.s1, e1, .inr rfl, he1, write r (reg x' r - 1) x',
      write r (reg ya1 r - 1) ya1, write r (reg yb1 r - 1) yb1, ?_, ?_, ?_, ?_⟩
    · rw [hA, runA_one, specA ta ra ya1 hra, sem, if_neg ha1, if_pos ha2,
        if_neg (fun h => hz (hva ▸ h)), h1a]
    · rw [hB, runB_one, specB tb rb yb1 hrb, sem, if_neg hb1, if_pos hb2,
        if_neg (fun h => hz (hvb' ▸ h)), h1b, ← hreg]
    · rw [h1α]
      exact shifted_decrement reg_write_same reg_write_other x' ya1 _ r hsa' hra0
    · rw [h1β]
      exact shifted_decrement reg_write_same reg_write_other x' yb1 _ r hsb' hrb0

end Entry

end Model

/-! ## The certificate relation as a fixed `Σ₁` formula -/

section Lookup

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

open ArithmeticMachineGraphPerm252 (lookupValue lookupNat)

/-- The lookup at the `i`-th key, for an external index `i`. -/
theorem lookup_at (rows : List (Nat × Nat)) (first i : Nat) (hi : i < rows.length) (s : V) :
    lookupValue rows first ((first+i+1 : Nat) : V) s =
      if s = 0 then ((rows[i]'hi).1 : V) else ((rows[i]'hi).2 : V) := by
  induction rows generalizing first i with
  | nil => simp at hi
  | cons row rows ih =>
    classical
    cases i with
    | zero =>
      simp only [Nat.add_zero, lookupValue, numeral_eq_natCast, if_true, List.getElem_cons_zero]
    | succ i =>
      have hlt : ((first+1 : Nat) : V) < ((first+(i+1)+1 : Nat) : V) :=
        (Nat.cast_lt (α := V)).mpr (by omega)
      have hne : ((first+(i+1)+1 : Nat) : V) ≠ ((first+1 : Nat) : V) := ne_of_gt hlt
      simp only [lookupValue, numeral_eq_natCast, if_neg hne, List.getElem_cons_succ]
      have hi' : i < rows.length := Nat.lt_of_succ_lt_succ (by
        simpa only [List.length_cons] using hi)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (first+1) i hi'

/-- A nonzero lookup result classifies an arbitrary internal key as one of the
finitely many external keys; the key need not be assumed standard. -/
theorem lookup_supported (rows : List (Nat × Nat)) (first : Nat) (q s : V)
    (hn : lookupValue rows first q s ≠ 0) :
    ∃ i, i < rows.length ∧ q = ((first+i+1 : Nat) : V) := by
  induction rows generalizing first with
  | nil => simp [lookupValue] at hn
  | cons row rows ih =>
    classical
    by_cases hq : q = ORingStructure.numeral (first+1)
    · exact ⟨0, by simp, by simpa only [Nat.add_zero, numeral_eq_natCast] using hq⟩
    · obtain ⟨i, hi, he⟩ := ih (first+1) (by simpa only [lookupValue, if_neg hq] using hn)
      exact ⟨i+1, by simpa using hi, by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he⟩

end Lookup

section Relation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open ArithmeticMachineGraphPerm252 (lookupValue lookup_defined)

variable (reg : V → Fin 9 → V) (live : V → V → V) (cert : Nat → Option Entry) (N : Nat)

/-- External tables of the certificate, keyed by entry index plus one. -/
def ctlRows : List (Nat × Nat) :=
  (List.range N).map fun i => match cert i with
    | some e => (e.a, e.b)
    | none => (0, 0)

def offRows (p : Nat) : List (Nat × Nat) :=
  (List.range N).map fun i => match cert i with
    | some e => (vget e.α p, vget e.β p)
    | none => (0, 0)

/-- Related control of entry `k` on side `s` (zero: machine A, one: machine B). -/
noncomputable def ctl (k s : V) : V := lookupValue (ctlRows cert N) 0 (k+1) s

/-- Offset of entry `k` on side `s` at register `p`. -/
noncomputable def off (p : Fin 9) (k s : V) : V := lookupValue (offRows cert N p) 0 (k+1) s

/-- One register of `ShiftK`. -/
def ShiftP (p : Fin 9) (k s x y : V) : Prop := reg y p = reg x p + off cert N p k s

/-- Register-wise shift by the offsets of entry `k`, side `s`. -/
def ShiftK (k s x y : V) : Prop :=
  ShiftP reg cert N 0 k s x y ∧ ShiftP reg cert N 1 k s x y ∧ ShiftP reg cert N 2 k s x y ∧
  ShiftP reg cert N 3 k s x y ∧ ShiftP reg cert N 4 k s x y ∧ ShiftP reg cert N 5 k s x y ∧
  ShiftP reg cert N 6 k s x y ∧ ShiftP reg cert N 7 k s x y ∧ ShiftP reg cert N 8 k s x y

/-- The certified relation between machine states. -/
def Rel (a b : V) : Prop :=
  ∃ k x ya yb, ctl cert N k 0 ≠ 0 ∧ a = live (ctl cert N k 0) ya ∧
    b = live (ctl cert N k 1) yb ∧ ShiftK reg cert N k 0 x ya ∧ ShiftK reg cert N k 1 x yb

open ArithmeticMachineGraphPerm252 (lookupDef) in
def ctlDef : 𝚺₁.Semisentence 3 := .mkSigma
  “c k s. !(lookupDef (ctlRows cert N) 0) c (k+1) s”

open ArithmeticMachineGraphPerm252 (lookupDef) in
def offDef (p : Fin 9) : 𝚺₁.Semisentence 3 := .mkSigma
  “o k s. !(lookupDef (offRows cert N p) 0) o (k+1) s”

instance ctl_defined : 𝚺₁-Function₂[V] (ctl cert N) via ctlDef cert N :=
  .mk fun e => by simp [ctlDef, ctl, (lookup_defined (V := V) (ctlRows cert N) 0).iff]

instance off_defined (p : Fin 9) : 𝚺₁-Function₂[V] (off cert N p) via offDef cert N p :=
  .mk fun e => by simp [offDef, off, (lookup_defined (V := V) (offRows cert N p) 0).iff]

variable (liveDef : 𝚺₁.Semisentence 3) (regDef : Fin 9 → 𝚺₁.Semisentence 2)

def shiftPDef (p : Fin 9) : 𝚺₁.Semisentence 4 := .mkSigma
  “k s x y. ∃ ry, !(regDef p) ry y ∧ ∃ rx, !(regDef p) rx x ∧
    ∃ o, !(offDef cert N p) o k s ∧ ry = rx + o”

def shiftKDef : 𝚺₁.Semisentence 4 := .mkSigma
  “k s x y. !(shiftPDef cert N regDef 0) k s x y ∧ !(shiftPDef cert N regDef 1) k s x y ∧
    !(shiftPDef cert N regDef 2) k s x y ∧ !(shiftPDef cert N regDef 3) k s x y ∧
    !(shiftPDef cert N regDef 4) k s x y ∧ !(shiftPDef cert N regDef 5) k s x y ∧
    !(shiftPDef cert N regDef 6) k s x y ∧ !(shiftPDef cert N regDef 7) k s x y ∧
    !(shiftPDef cert N regDef 8) k s x y”

def relDef : 𝚺₁.Semisentence 2 := .mkSigma
  “a b. ∃ k, ∃ x, ∃ ya, ∃ yb, ∃ c0, !(ctlDef cert N) c0 k 0 ∧ c0 ≠ 0 ∧
    ∃ c1, !(ctlDef cert N) c1 k 1 ∧ !liveDef a c0 ya ∧ !liveDef b c1 yb ∧
    !(shiftKDef cert N regDef) k 0 x ya ∧ !(shiftKDef cert N regDef) k 1 x yb”

variable [hlive : 𝚺₁-Function₂[V] live via liveDef]
  [hreg : ∀ p, 𝚺₁-Function₁[V] (fun x => reg x p) via regDef p]

theorem shiftP_defined (p : Fin 9) :
    𝚺₁-Relation₄[V] (ShiftP reg cert N p) via shiftPDef cert N regDef p :=
  .mk fun e => by simp [shiftPDef, ShiftP, (hreg p).iff, (off_defined (V := V) cert N p).iff]

theorem shiftK_defined :
    𝚺₁-Relation₄[V] (ShiftK reg cert N) via shiftKDef cert N regDef :=
  .mk fun e => by
    simp only [shiftKDef, ShiftK, HierarchySymbol.Semiformula.val_mkSigma]
    simp [(shiftP_defined reg cert N regDef _).iff]

theorem rel_defined :
    𝚺₁-Relation[V] (Rel reg live cert N) via relDef cert N liveDef regDef :=
  .mk fun e => by
    simp [relDef, Rel, (ctl_defined (V := V) cert N).iff, hlive.iff,
      (shiftK_defined reg cert N regDef).iff]

variable {reg live cert N}

theorem ctl_at (i : Nat) (hi : i < N) (e : Entry) (he : cert i = some e) :
    ctl cert N (i : V) 0 = (e.a : V) ∧ ctl cert N (i : V) 1 = (e.b : V) := by
  have hl : i < (ctlRows cert N).length := by simpa [ctlRows] using hi
  have h := fun s : V => lookup_at (ctlRows cert N) 0 i hl s
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one] at h
  have hg : List.get (ctlRows cert N) ⟨i, hl⟩ = (e.a, e.b) := by simp [ctlRows, he]
  rw [_root_.List.get_eq_getElem] at hg
  refine ⟨?_, ?_⟩
  · rw [ctl, h 0, if_pos rfl, hg]
  · rw [ctl, h 1, if_neg _root_.one_ne_zero, hg]

theorem off_at (p : Fin 9) (i : Nat) (hi : i < N) (e : Entry) (he : cert i = some e) :
    off cert N p (i : V) 0 = (vget e.α p : V) ∧ off cert N p (i : V) 1 = (vget e.β p : V) := by
  have hl : i < (offRows cert N p).length := by simpa [offRows] using hi
  have h := fun s : V => lookup_at (offRows cert N p) 0 i hl s
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one] at h
  have hg : List.get (offRows cert N p) ⟨i, hl⟩ = (vget e.α p, vget e.β p) := by
    simp [offRows, he]
  rw [_root_.List.get_eq_getElem] at hg
  refine ⟨?_, ?_⟩
  · rw [off, h 0, if_pos rfl, hg]
  · rw [off, h 1, if_neg _root_.one_ne_zero, hg]

theorem shiftK_iff (s : V) (u : Vec) (k x y : V)
    (hoff : ∀ p : Fin 9, off cert N p k s = (vget u p : V)) :
    ShiftK reg cert N k s x y ↔ Shifted reg x u y := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ ⟨p, hp⟩
    rw [← hoff ⟨p, hp⟩]
    match p, hp with
    | 0, _ => exact h0 | 1, _ => exact h1 | 2, _ => exact h2 | 3, _ => exact h3
    | 4, _ => exact h4 | 5, _ => exact h5 | 6, _ => exact h6 | 7, _ => exact h7
    | 8, _ => exact h8
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [ShiftP, hoff]; exact h _)

/-- Every certified related pair arises from one external entry. -/
theorem rel_entry (a b : V) (h : Rel reg live cert N a b) :
    ∃ i, i < N ∧ ∃ e, cert i = some e ∧ ∃ x ya yb,
      a = live (e.a : V) ya ∧ b = live (e.b : V) yb ∧
      Shifted reg x e.α ya ∧ Shifted reg x e.β yb := by
  obtain ⟨k, x, ya, yb, hk, ha, hb, hsa, hsb⟩ := h
  obtain ⟨i, hi, hki⟩ := lookup_supported (ctlRows cert N) 0 (k+1) 0 hk
  have hiN : i < N := by simpa [ctlRows] using hi
  have hk' : k = (i : V) := by
    simpa only [Nat.zero_add, Nat.cast_add, Nat.cast_one, add_left_inj] using hki
  subst hk'
  cases he : cert i with
  | none =>
    exfalso
    apply hk
    have hl : i < (ctlRows cert N).length := hi
    have h := lookup_at (ctlRows cert N) 0 i hl (0 : V)
    simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one] at h
    rw [ctl, h]
    simp [ctlRows, he]
  | some e =>
    obtain ⟨hca, hcb⟩ := ctl_at (V := V) i hiN e he
    refine ⟨i, hiN, e, he, x, ya, yb, by rw [ha, hca], by rw [hb, hcb], ?_, ?_⟩
    · exact (shiftK_iff 0 e.α _ x ya (fun p => (off_at p i hiN e he).1)).mp hsa
    · exact (shiftK_iff 1 e.β _ x yb (fun p => (off_at p i hiN e he).2)).mp hsb

/-- Conversely an entry with a positive `A`-control yields related states. -/
theorem rel_of_entry (i : Nat) (hi : i < N) (e : Entry) (he : cert i = some e)
    (hpos : 0 < e.a) (x ya yb : V) (hsa : Shifted reg x e.α ya) (hsb : Shifted reg x e.β yb) :
    Rel reg live cert N (live (e.a : V) ya) (live (e.b : V) yb) := by
  obtain ⟨hca, hcb⟩ := ctl_at (V := V) i hi e he
  refine ⟨(i : V), x, ya, yb, ?_, by rw [hca], by rw [hcb], ?_, ?_⟩
  · rw [hca]
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  · exact (shiftK_iff 0 e.α _ x ya (fun p => (off_at p i hi e he).1)).mpr hsa
  · exact (shiftK_iff 1 e.β _ x yb (fun p => (off_at p i hi e he).2)).mpr hsb

end Relation

/-! ## The certified halting equivalence -/

section Main

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable {reg : V → Fin 9 → V} {write : Fin 9 → V → V → V} {live : V → V → V}
  (fileOf : (Fin 9 → V) → V) (reg_fileOf : ∀ g p, reg (fileOf g) p = g p)
  (live_ne : ∀ c x, live c x ≠ 0)
  (liveDef : 𝚺₁.Semisentence 3) (regDef : Fin 9 → 𝚺₁.Semisentence 2)
  [hlive : 𝚺₁-Function₂[V] live via liveDef]
  [hreg : ∀ p, 𝚺₁-Function₁[V] (fun x => reg x p) via regDef p]
  (stepA stepB : V → V) (runA runB : V → V → V)
  [𝚺₁-Function₂[V] runA] [𝚺₁-Function₂[V] runB]
  (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry) (fuel N : Nat)
  (runA_zero : ∀ x, runA 0 x = x) (runB_zero : ∀ x, runB 0 x = x)
  (runA_add : ∀ t u x, runA (t+u) x = runA u (runA t x))
  (runB_add : ∀ t u x, runB (t+u) x = runB u (runB t x))
  (runA_one : ∀ x, runA 1 x = stepA x) (runB_one : ∀ x, runB 1 x = stepB x)
  (runA_halted : ∀ t, runA t 0 = 0) (runB_halted : ∀ t, runB t 0 = 0)
  (specA : ∀ (c : Nat) (row : Row) (x : V), rowsA c = some row →
    stepA (live (c : V) x) = sem reg write live row x)
  (specB : ∀ (c : Nat) (row : Row) (x : V), rowsB c = some row →
    stepB (live (c : V) x) = sem reg write live row x)
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)
  (hcheck : ∀ i, i < N → entryOK rowsA rowsB cert fuel N i = true)

include reg_fileOf live_ne runA_zero runB_zero runA_add runB_add runA_one runB_one
  runA_halted runB_halted specA specB reg_write_same reg_write_other hcheck hlive hreg

/-- **Certified halting equivalence.** If entry `0` relates controls `a`, `b`
with zero offsets, then from every internal register file the two control
interpreters halt together. -/
theorem halts_iff_of_check (e : Entry) (he : cert 0 = some e) (hN : 0 < N)
    (hα : ∀ p : Fin 9, vget e.α p = 0) (hβ : ∀ p : Fin 9, vget e.β p = 0) (x : V) :
    (∃ t, runA t (live (e.a : V) x) = 0) ↔ (∃ t, runB t (live (e.b : V) x) = 0) := by
  haveI : 𝚺₁-Relation[V] (Rel reg live cert N) :=
    (rel_defined reg live cert N liveDef regDef).to_definable
  refine halts_iff runA runB (Rel reg live cert N) runA_zero runB_zero runA_add runB_add
    runA_halted runB_halted ?_ ?_ _ _ ?_
  · intro a b h
    obtain ⟨_, _, _, _, _, _, _, ha, hb, _, _⟩ := rel_entry a b h
    exact ⟨ha ▸ live_ne _ _, hb ▸ live_ne _ _⟩
  · intro a b h
    obtain ⟨i, hi, e, he, x, ya, yb, ha, hb, hsa, hsb⟩ := rel_entry a b h
    obtain ⟨_, he', hc, hs0, hs1, _⟩ := entryOK_spec rowsA rowsB cert fuel N i (hcheck i hi)
    rw [he] at he'
    cases he'
    obtain ⟨ka, kb, hka, hkb, hq⟩ := entry_step fileOf reg_fileOf stepA stepB runA runB rowsA
      rowsB cert fuel runA_zero runB_zero runA_add runB_add runA_one runB_one specA specB
      reg_write_same reg_write_other e hc x ya yb hsa hsb
    refine ⟨ka, kb, hka, hkb, ?_⟩
    rw [ha, hb]
    rcases hq with hz | ⟨s, e', hs, hes, x', ya', yb', ha', hb', hsa', hsb'⟩
    · exact .inl hz
    · have hsN : s < N := by rcases hs with rfl | rfl <;> assumption
      refine .inr ?_
      rw [ha', hb']
      obtain ⟨e'', he'', _, _, _, hpos⟩ := entryOK_spec rowsA rowsB cert fuel N s (hcheck s hsN)
      rw [hes] at he''
      cases he''
      exact rel_of_entry s hsN e' hes hpos x' ya' yb' hsa' hsb'
  · obtain ⟨e', he', _, _, _, hpos⟩ := entryOK_spec rowsA rowsB cert fuel N 0 (hcheck 0 hN)
    rw [he] at he'
    cases he'
    exact rel_of_entry 0 hN e he hpos x x x
      (fun p => by rw [hα p]; simp) (fun p => by rw [hβ p]; simp)

end Main

end SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim
