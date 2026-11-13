import BusyBeaver.ZFC.ArithmeticControlTable
import BusyBeaver.ZFC.RMDag

set_option autoImplicit false

/-!
# Internal structured semantics of DAG register programs

The structured big-step semantics `RMDag.Run` of a DAG program, represented
over a numbered control interpreter in every model of `IΣ₁`.

In the path program of a DAG every occurrence of an edge is a contiguous block
of controls whose rows depend only on the edge, except for the targets of the
block's exits. `Occ fuel e c E` says that edge `e` occurs as the block starting
at control number `c` with exit map `E : Exit → ℕ`; for a node it unfolds to the
occurrences of its car and cdr, with the exit maps prescribed by the car/cdr
rules of `RMDag.Run`. `IRun e x y X y'` says: from every occurrence, the run
started at file `x` reaches the exit `X` with file `y'` (for `halt`: reaches the
absorbing zero). Each constructor of `RMDag.Run` becomes a composition lemma
(`run_inc` … `run_restart`), so subroutine proofs carry over constructor by
constructor; loops use internal `Σ₁` induction (`while_loop`). Only the root
occurrence is ever checked against the concrete catalogue.

Registers are logical: logical register `r` is the physical field `physOf r`.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagRun

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticControlFile (regValue liveValue live_ne_zero)
open ArithmeticControlBisim (Row sem)
open ArithmeticControlTable (write reg_write_same reg_write_other)
open RMDag (Prog Exit)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! ## Blocks of a DAG program -/

/-- The physical field of a logical register. -/
def phys (r : Nat) : Fin 9 := ⟨Permutation252Frame.physOf r, ArithmeticControlTable.physOf_lt r⟩

/-- Number of leaves (controls) of an edge's block, with decoder fuel. -/
def size (p : Prog) : Nat → RMDag.Edge → Nat
  | 0, _ => 0
  | f+1, .node n => size p f (p.nodes n).1 + size p f (p.nodes n).2
  | _+1, _ => 1

/-- The catalogue row of a leaf edge under exit map `E`. -/
def leafRow (e : RMDag.Edge) (E : Exit → Nat) : Option Row :=
  match e with
  | .inc r => some ⟨1, phys r, E .normal, E .normal⟩
  | .decnz r => some ⟨2, phys r, E (.brk 1), E .normal⟩
  | .brk 0 => some ⟨3, 0, E .normal, E .normal⟩
  | .brk (k+1) => some ⟨3, 0, E (.brk (k+1)), E (.brk (k+1))⟩
  | .cont (k+1) => some ⟨3, 0, E (.cont (k+1)), E (.cont (k+1))⟩
  | .halt => some ⟨4, 0, 0, 0⟩
  | _ => none

/-- Exit map of the car of a node occurrence at `c` with car size `ncar`. -/
def carExit (c ncar : Nat) (E : Exit → Nat) : Exit → Nat
  | .normal => c + ncar
  | .brk 1 => E .normal
  | .brk (k+2) => E (.brk (k+1))
  | .brk 0 => E .normal
  | .cont k => E (.cont k)
  | .halt => 0

/-- Exit map of the cdr of a node occurrence at `c`. -/
def cdrExit (c : Nat) (E : Exit → Nat) : Exit → Nat
  | .normal => E .normal
  | .brk k => E (.brk k)
  | .cont 1 => c
  | .cont (k+2) => E (.cont (k+1))
  | .cont 0 => E (.cont 0)
  | .halt => 0

variable (p : Prog) (rows : Nat → Option Row)

/-- Edge `e` occurs as the control block starting at `c` with exit map `E`. -/
def Occ : Nat → RMDag.Edge → Nat → (Exit → Nat) → Prop
  | 0, _, _, _ => False
  | f+1, .node n, c, E =>
      Occ f (p.nodes n).1 c (carExit c (size p f (p.nodes n).1) E) ∧
      Occ f (p.nodes n).2 (c + size p f (p.nodes n).1) (cdrExit c E)
  | _+1, e, c, E => leafRow e E ≠ none ∧ rows c = leafRow e E

/-- Boolean version for the one concrete root check. -/
def occB : Nat → RMDag.Edge → Nat → (Exit → Nat) → Bool
  | 0, _, _, _ => false
  | f+1, .node n, c, E =>
      occB f (p.nodes n).1 c (carExit c (size p f (p.nodes n).1) E) &&
      occB f (p.nodes n).2 (c + size p f (p.nodes n).1) (cdrExit c E)
  | _+1, e, c, E => (leafRow e E).isSome && rows c == leafRow e E

theorem occ_of_occB : ∀ (f : Nat) (e : RMDag.Edge) (c : Nat) (E : Exit → Nat),
    occB p rows f e c E = true → Occ p rows f e c E
  | 0, _, _, _, h => by simp [occB] at h
  | f+1, .node n, c, E, h => by
    simp only [occB, Bool.and_eq_true] at h
    exact ⟨occ_of_occB f _ _ _ h.1, occ_of_occB f _ _ _ h.2⟩
  | f+1, .inc r, c, E, h => by
    simp only [occB, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_ne_none] at h
    exact h
  | f+1, .decnz r, c, E, h => by
    simp only [occB, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_ne_none] at h
    exact h
  | f+1, .brk k, c, E, h => by
    simp only [occB, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_ne_none] at h
    exact h
  | f+1, .cont k, c, E, h => by
    simp only [occB, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_ne_none] at h
    exact h
  | f+1, .halt, c, E, h => by
    simp only [occB, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_ne_none] at h
    exact h

/-! ## The internal structured run -/

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (step : V → V) (run : V → V → V)

/-- Reaching the exit `X` of an occurrence (`halt`: the absorbing zero). -/
def Reach (c : Nat) (E : Exit → Nat) (x : V) (X : Exit) (y : V) : Prop :=
  match X with
  | .halt => ∃ t, run t (liveValue (c : V) x) = 0
  | X => ∃ t, run t (liveValue (c : V) x) = liveValue ((E X : Nat) : V) y

/-- Structured run of edge `e` from file `x` to exit `X` with file `y`. -/
def IRun (e : RMDag.Edge) (x : V) (X : Exit) (y : V) : Prop :=
  ∀ f c E, Occ p rows f e c E → Reach run c E x X y

/-- Logical register read and write. -/
noncomputable def lreg (x : V) (r : Nat) : V := regValue x (phys r)
noncomputable def lupd (x : V) (r : Nat) (v : V) : V := write (phys r) v x

variable {p rows step run}
variable (run_zero : ∀ x, run 0 x = x)
  (run_add : ∀ t u x, run (t+u) x = run u (run t x))
  (run_one : ∀ x, run 1 x = step x)
  (spec : ∀ (c : Nat) (row : Row) (x : V), rows c = some row →
    step (liveValue (c : V) x) = sem regValue write liveValue row x)

include run_add run_one spec

omit run_add in
/-- One instruction step of a leaf occurrence. -/
theorem leaf_step (e : RMDag.Edge) (c : Nat) (E : Exit → Nat) (row : Row)
    (hrow : leafRow e E = some row) (hc : rows c = leafRow e E) (x : V) :
    run 1 (liveValue (c : V) x) = sem regValue write liveValue row x := by
  rw [run_one, spec c row x (hc.trans hrow)]

omit run_add in
theorem run_inc (r : Nat) (x : V) :
    IRun p rows run (.inc r) x .normal (lupd x r (lreg x r + 1)) := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    refine ⟨1, ?_⟩
    rw [leaf_step run_one spec (.inc r) c E _ rfl hc]
    simp [sem, lupd, lreg]

omit run_add in
theorem run_decPos (r : Nat) (x v : V) (hv : lreg x r = v + 1) :
    IRun p rows run (.decnz r) x .normal (lupd x r v) := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    refine ⟨1, ?_⟩
    rw [leaf_step run_one spec (.decnz r) c E _ rfl hc]
    have hne : regValue x (phys r) ≠ 0 := by
      change lreg x r ≠ 0; rw [hv]; exact Arithmetic.succ_ne_zero v
    simp only [sem, show (2 : Nat) ≠ 1 by decide, if_false, if_true, hne]
    simp only [lupd, lreg] at hv ⊢
    rw [hv, add_tsub_cancel_right]

omit run_add in
theorem run_decZero (r : Nat) (x : V) (hz : lreg x r = 0) :
    IRun p rows run (.decnz r) x (.brk 1) x := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    refine ⟨1, ?_⟩
    rw [leaf_step run_one spec (.decnz r) c E _ rfl hc]
    have hz' : regValue x (phys r) = 0 := hz
    simp [sem, hz']

omit run_add in
theorem run_brk0 (x : V) : IRun p rows run (.brk 0) x .normal x := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, by rw [leaf_step run_one spec (.brk 0) c E _ rfl hc]; simp [sem]⟩

omit run_add in
theorem run_brkS (k : Nat) (x : V) : IRun p rows run (.brk (k+1)) x (.brk (k+1)) x := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, by rw [leaf_step run_one spec (.brk (k+1)) c E _ rfl hc]; simp [sem]⟩

omit run_add in
theorem run_contS (k : Nat) (x : V) : IRun p rows run (.cont (k+1)) x (.cont (k+1)) x := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, by rw [leaf_step run_one spec (.cont (k+1)) c E _ rfl hc]; simp [sem]⟩

omit run_add in
theorem run_halt (x : V) : IRun p rows run .halt x .halt x := by
  intro f c E h
  cases f with
  | zero => exact h.elim
  | succ f =>
    obtain ⟨_, hc⟩ := h
    exact ⟨1, by rw [leaf_step run_one spec .halt c E _ rfl hc]; simp [sem]⟩

omit run_one spec in
/-- Composition of reaches through an intermediate control. -/
theorem reach_trans {c₁ c₂ : Nat} {x y : V} {t₁ : V}
    (h₁ : run t₁ (liveValue (c₁ : V) x) = liveValue (c₂ : V) y) {E : Exit → Nat} {X : Exit} {z : V}
    (h₂ : Reach run c₂ E y X z) : Reach run c₁ E x X z := by
  cases X with
  | halt => obtain ⟨t, ht⟩ := h₂; exact ⟨t₁ + t, by rw [run_add, h₁, ht]⟩
  | normal => obtain ⟨t, ht⟩ := h₂; exact ⟨t₁ + t, by rw [run_add, h₁, ht]⟩
  | brk k => obtain ⟨t, ht⟩ := h₂; exact ⟨t₁ + t, by rw [run_add, h₁, ht]⟩
  | cont k => obtain ⟨t, ht⟩ := h₂; exact ⟨t₁ + t, by rw [run_add, h₁, ht]⟩

omit run_add run_one spec in
/-- The occurrence of a node splits into car and cdr occurrences. -/
theorem occ_node {f : Nat} {n c : Nat} {E : Exit → Nat} (h : Occ p rows f (.node n) c E) :
    ∃ f', f = f'+1 ∧ Occ p rows f' (p.nodes n).1 c (carExit c (size p f' (p.nodes n).1) E) ∧
      Occ p rows f' (p.nodes n).2 (c + size p f' (p.nodes n).1) (cdrExit c E) := by
  cases f with
  | zero => exact h.elim
  | succ f => exact ⟨f, rfl, h⟩

omit run_one spec in
/-- Sequencing: both halves finish normally. -/
theorem run_seq {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z : V}
    (ha : IRun p rows run a x .normal y) (hb : IRun p rows run b y .normal z) :
    IRun p rows run (.node n) x .normal z := by
  intro f c E h
  obtain ⟨f', rfl, hca, hcd⟩ := occ_node h
  simp only [hn] at hca hcd
  obtain ⟨t₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
  exact reach_trans run_add (c₂ := c + size p f' a) h₁
    (hb f' (c + size p f' a) (cdrExit c E) hcd)

omit run_add run_one spec in
/-- A car that breaks one level skips the cdr. -/
theorem run_skip {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y : V}
    (ha : IRun p rows run a x (.brk 1) y) : IRun p rows run (.node n) x .normal y := by
  intro f c E h
  obtain ⟨f', rfl, hca, _⟩ := occ_node h
  simp only [hn] at hca
  exact ha f' c (carExit c (size p f' a) E) hca

omit run_add run_one spec in
/-- Halting in the car. -/
theorem run_halt_car {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y : V}
    (ha : IRun p rows run a x .halt y) : IRun p rows run (.node n) x .halt y := by
  intro f c E h
  obtain ⟨f', rfl, hca, _⟩ := occ_node h
  simp only [hn] at hca
  exact ha f' c (carExit c (size p f' a) E) hca

omit run_one spec in
/-- Halting in the cdr. -/
theorem run_halt_cdr {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z : V}
    (ha : IRun p rows run a x .normal y) (hb : IRun p rows run b y .halt z) :
    IRun p rows run (.node n) x .halt z := by
  intro f c E h
  obtain ⟨f', rfl, hca, hcd⟩ := occ_node h
  simp only [hn] at hca hcd
  obtain ⟨t₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
  exact reach_trans run_add (c₂ := c + size p f' a) h₁
    (hb f' (c + size p f' a) (cdrExit c E) hcd)

omit run_one spec in
/-- A cdr breaking `k+1` levels breaks the node `k+1` levels. -/
theorem run_brk_cdr {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z : V}
    (ha : IRun p rows run a x .normal y) (hb : IRun p rows run b y (.brk (k+1)) z) :
    IRun p rows run (.node n) x (.brk (k+1)) z := by
  intro f c E h
  obtain ⟨f', rfl, hca, hcd⟩ := occ_node h
  simp only [hn] at hca hcd
  obtain ⟨t₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
  exact reach_trans run_add (c₂ := c + size p f' a) h₁
    (hb f' (c + size p f' a) (cdrExit c E) hcd)

omit run_add run_one spec in
/-- A car breaking `k+2` levels breaks the node `k+1` levels. -/
theorem run_brk_car {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y : V}
    (ha : IRun p rows run a x (.brk (k+2)) y) : IRun p rows run (.node n) x (.brk (k+1)) y := by
  intro f c E h
  obtain ⟨f', rfl, hca, _⟩ := occ_node h
  simp only [hn] at hca
  exact ha f' c (carExit c (size p f' a) E) hca

omit run_add run_one spec in
/-- A car continuing propagates the continue. -/
theorem run_cont_car {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y : V}
    (ha : IRun p rows run a x (.cont (k+1)) y) : IRun p rows run (.node n) x (.cont (k+1)) y := by
  intro f c E h
  obtain ⟨f', rfl, hca, _⟩ := occ_node h
  simp only [hn] at hca
  exact ha f' c (carExit c (size p f' a) E) hca

omit run_one spec in
/-- A cdr continuing `k+2` levels continues the node `k+1` levels. -/
theorem run_cont_cdr {n k : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z : V}
    (ha : IRun p rows run a x .normal y) (hb : IRun p rows run b y (.cont (k+2)) z) :
    IRun p rows run (.node n) x (.cont (k+1)) z := by
  intro f c E h
  obtain ⟨f', rfl, hca, hcd⟩ := occ_node h
  simp only [hn] at hca hcd
  obtain ⟨t₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
  exact reach_trans run_add (c₂ := c + size p f' a) h₁
    (hb f' (c + size p f' a) (cdrExit c E) hcd)

omit run_one spec in
/-- A cdr continuing one level restarts the node. -/
theorem run_restart {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b)) {x y z w : V}
    {X : Exit} (ha : IRun p rows run a x .normal y) (hb : IRun p rows run b y (.cont 1) z)
    (hrest : IRun p rows run (.node n) z X w) : IRun p rows run (.node n) x X w := by
  intro f c E h
  obtain ⟨f', hf, hca, hcd⟩ := occ_node h
  have h' := h
  subst hf
  simp only [hn] at hca hcd
  obtain ⟨t₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
  obtain ⟨t₂, h₂⟩ := hb f' (c + size p f' a) (cdrExit c E) hcd
  have h₁' : run t₁ (liveValue (c : V) x) = liveValue ((c + size p f' a : Nat) : V) y := h₁
  have h₂' : run t₂ (liveValue ((c + size p f' a : Nat) : V) y) = liveValue (c : V) z := h₂
  exact reach_trans run_add (t₁ := t₁ + t₂) (by rw [run_add, h₁', h₂']) (hrest (f'+1) c E h')

section Iterate

variable [𝚺₁-Function₂[V] run]

omit run_one spec in
include run_zero in
/-- Repeated passes through a node whose cdr restarts it: `G t` is the file
before the `t`-th pass and `H t` the file between car and cdr. All iteration
indices are internal; the induction runs at one fixed occurrence, so its
predicate is `Σ₁`. The last state continues by `hfin`. -/
theorem run_iterate {n : Nat} {a b : RMDag.Edge} (hn : p.nodes n = (a, b))
    (G H : V → V) [𝚺₁-Function₁[V] G] (N : V)
    (hpass : ∀ t, t < N → IRun p rows run a (G t) .normal (H t) ∧
      IRun p rows run b (H t) (.cont 1) (G (t+1)))
    {X : Exit} {y : V} (hfin : IRun p rows run (.node n) (G N) X y) :
    IRun p rows run (.node n) (G 0) X y := by
  intro f c E h
  have hlive : 𝚺₁-Function₂[V] liveValue := ArithmeticControlFile.live_defined.to_definable
  have key : ∀ t, t ≤ N → ∃ s, run s (liveValue (c : V) (G 0)) = liveValue (c : V) (G t) := by
    intro t
    induction t using ISigma1.sigma1_succ_induction
    · definability
    case zero => intro _; exact ⟨0, run_zero _⟩
    case succ t ih =>
      intro ht
      have htN : t < N := lt_of_lt_of_le (lt_add_one t) ht
      obtain ⟨s, hs⟩ := ih (le_of_lt htN)
      obtain ⟨ha, hb⟩ := hpass t htN
      obtain ⟨f', hf, hca, hcd⟩ := occ_node h
      subst hf
      simp only [hn] at hca hcd
      obtain ⟨t₁, h₁⟩ := ha f' c (carExit c (size p f' a) E) hca
      obtain ⟨t₂, h₂⟩ := hb f' (c + size p f' a) (cdrExit c E) hcd
      have h₁' : run t₁ (liveValue (c : V) (G t)) =
          liveValue ((c + size p f' a : Nat) : V) (H t) := h₁
      have h₂' : run t₂ (liveValue ((c + size p f' a : Nat) : V) (H t)) =
          liveValue (c : V) (G (t+1)) := h₂
      exact ⟨s + t₁ + t₂, by rw [run_add, run_add, hs, h₁', h₂']⟩
  obtain ⟨s, hs⟩ := key N le_rfl
  exact reach_trans run_add hs (hfin f c E h)

end Iterate

end Model

end SetTheory.BusyBeaver.ZFC.ArithmeticDagRun
