import BusyBeaver.ZFC.RMEquiv

/-!
Halting equivalence of two path programs from a checked segment certificate.

Between two register tests a path program only increments, breaks and
continues; none of these reads a register. A run therefore splits into
*segments*: from a test site, follow the leaves on the instruction pointer
alone, collecting the increments, up to the next `decnz` or `halt` leaf
(`seg`). A *segment bisimulation* (`Bisim`) is a relation `S` between test
sites of two programs such that related sites are both `halt` leaves, or both
`decnz r` leaves on the same register whose two outcomes lead, by segments
with equal increment counts, to related sites again; the segments from the
empty pointer start related. `Bisim.halts` shows that a segment bisimulation
transfers halting from the empty pointer, for every register file; since the
definition is symmetric (`Bisim.symm`), one relation gives both directions.

`check` is a Boolean test of a certificate: a tree of entries
`(P₁, P₂, j, k)` (pointers coded as numbers, the successor entries of the two
outcomes given by index). The relation is *defined* as the set of pairs the
lookup can return, so the soundness proof needs no invariant of the tree.
For kernel evaluation the programs are first converted into explicit decoder
trees (`toTree`, `walk_tree`).

This is the counterpart of upstream `Bisim.v` (Jeff's verification of
Mira-Cult's machine, busy-beaver commit 297ab8df7e5de329605c3875b4934643b371a5e3,
`ZF/m254/coq/prog/Bisim.v`), developed independently; the symmetric relation
replaces upstream's second, mirrored certificate check.
-/

namespace SetTheory.BusyBeaver.ZFC.RMBisim

open RegisterPath
open RMEquiv (HN run_add hn_pre hn_succ)

/-! ## Decoder trees -/

inductive Tree where
  | none
  | leaf (e : Edge)
  | node (a b : Tree)

/-- Unfold `fuel` levels of the program below node `n`. -/
def toTree (p : Program) : Nat → Nat → Tree
  | 0, _ => .none
  | f + 1, n =>
      .node (match (p.nodes n).1 with
          | .node m => toTree p f m
          | e => .leaf e)
        (match (p.nodes n).2 with
          | .node m => toTree p f m
          | e => .leaf e)

def sub (p : Program) (f : Nat) : Edge → Tree
  | .node m => toTree p f m
  | e => .leaf e

theorem toTree_succ (p : Program) (f n : Nat) :
    toTree p (f + 1) n = .node (sub p f (p.nodes n).1) (sub p f (p.nodes n).2) := by
  simp only [toTree]
  generalize (p.nodes n).1 = a
  generalize (p.nodes n).2 = b
  cases a <;> cases b <;> rfl

/-- The leaf reached by the bits of `P` (zero padded) and the depth reached. -/
def twalk : Tree → List Bool → Nat → Option (Edge × Nat)
  | .none, _, _ => none
  | .leaf e, _, d => some (e, d)
  | .node a _, [], d => twalk a [] (d + 1)
  | .node a b, c :: P, d =>
      match c with
      | true => twalk b P (d + 1)
      | false => twalk a P (d + 1)

theorem drop_nil_bit : ∀ {P : List Bool} {i : Nat}, P.drop i = [] →
    bit P i = false ∧ P.drop (i + 1) = []
  | [], i, _ => by simp [bit]
  | _ :: _, 0, h => by simp at h
  | _ :: P, i + 1, h => by
      simp only [List.drop_succ_cons] at h
      simpa [bit] using drop_nil_bit h

theorem drop_cons_bit : ∀ {P : List Bool} {i : Nat} {c : Bool} {rest : List Bool},
    P.drop i = c :: rest → bit P i = c ∧ P.drop (i + 1) = rest
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, h => by
      simp only [List.drop_zero, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [bit]
  | _ :: P, i + 1, _, _, h => by
      simp only [List.drop_succ_cons] at h
      simpa [bit] using drop_cons_bit h

theorem walk_tree (p : Program) : ∀ (f n : Nat) (P : List Bool) (i : Nat),
    walk p f n P i = twalk (toTree p f n) (P.drop i) i
  | 0, _, _, _ => by simp [walk, toTree, twalk]
  | f + 1, n, P, i => by
      rw [toTree_succ]
      simp only [walk]
      cases hP : P.drop i with
      | nil =>
          obtain ⟨hb, hd⟩ := drop_nil_bit hP
          simp only [hb, Bool.false_eq_true, if_false, twalk]
          generalize (p.nodes n).1 = e
          cases e <;> simp only [sub, twalk]
          rw [walk_tree p f _ P (i + 1), hd]
      | cons c rest =>
          obtain ⟨hb, hd⟩ := drop_cons_bit hP
          cases c
          · simp only [hb, Bool.false_eq_true, if_false, twalk]
            generalize (p.nodes n).1 = e
            cases e <;> simp only [sub, twalk]
            rw [walk_tree p f _ P (i + 1), hd]
          · simp only [hb, if_true, twalk]
            generalize (p.nodes n).2 = e
            cases e <;> simp only [sub, twalk]
            rw [walk_tree p f _ P (i + 1), hd]

/-- The decoder tree of a program, with the fuel of the path semantics. -/
def ptree (p : Program) : Tree := toTree p (p.nnodes + 1) p.root

/-- The leaf reached from `P`, with the bits actually read. -/
def tsite (t : Tree) (P : List Bool) : Option (Edge × List Bool) :=
  match twalk t P 0 with
  | some (e, d) => some (e, consume P d)
  | none => none

theorem walk_root (p : Program) (P : List Bool) :
    walk p (p.nnodes + 1) p.root P 0 = twalk (ptree p) P 0 := by
  rw [walk_tree]; rfl

theorem step_tsite (p : Program) (P : List Bool) (R : Registers) :
    step p ⟨P, R⟩ = match tsite (ptree p) P with
      | some (e, Q) => execute e Q R
      | none => none := by
  unfold step tsite
  rw [walk_root]
  cases twalk (ptree p) P 0 <;> rfl

theorem atHalt_tsite (p : Program) (P : List Bool) (R : Registers) :
    AtHalt p ⟨P, R⟩ ↔ ∃ Q, tsite (ptree p) P = some (.halt, Q) := by
  unfold AtHalt tsite
  rw [walk_root]
  constructor
  · rintro ⟨d, hd⟩; rw [hd]; exact ⟨_, rfl⟩
  · rintro ⟨Q, hQ⟩
    split at hQ
    · simp only [Option.some.injEq, Prod.mk.injEq] at hQ
      obtain ⟨rfl, -⟩ := hQ
      exact ⟨_, ‹_›⟩
    · cases hQ

/-! ## Halting -/

theorem halts_pre {p : Program} {n : Nat} {c c' : Configuration} (h1 : run p n c = some c')
    (h2 : Halts p c') : Halts p c := by
  obtain ⟨m, c'', h, ha⟩ := h2
  exact ⟨n + m, c'', by rwa [run_add, h1], ha⟩

/-- A halt leaf has no outgoing transition. -/
theorem atHalt_step {p : Program} {c : Configuration} (h : AtHalt p c) :
    step p c = none := by
  obtain ⟨d, hd⟩ := h
  simp only [step, hd, execute]

/-- Remove a successfully executed prefix from a halting run. -/
theorem hn_after {p : Program} {n N : Nat} {c c' : Configuration}
    (hr : run p n c = some c') (h : HN p N c) :
    ∃ N', N = n + N' ∧ HN p N' c' := by
  induction n generalizing N c with
  | zero =>
      simp only [run, Option.some.injEq] at hr
      subst c'
      exact ⟨N, by omega, h⟩
  | succ n ih =>
      cases N with
      | zero =>
          obtain ⟨d, h0, hh⟩ := h
          simp only [run, Option.some.injEq] at h0
          subst d
          simp only [run, atHalt_step hh] at hr
          contradiction
      | succ N =>
          obtain ⟨d, hs, hn⟩ := hn_succ h
          simp only [run, hs] at hr
          obtain ⟨N', he, h'⟩ := ih hr hn
          exact ⟨N', by omega, h'⟩

theorem hn_step {p : Program} {N : Nat} {P : List Bool} {R : Registers} {e : Edge}
    {Q : List Bool} {c' : Configuration} (hs : tsite (ptree p) P = some (e, Q)) (he : e ≠ .halt)
    (hl : execute e Q R = some c') (h : HN p N ⟨P, R⟩) : ∃ N', N = N' + 1 ∧ HN p N' c' := by
  cases N with
  | zero =>
      obtain ⟨c, hr, ha⟩ := h
      simp only [run, Option.some.injEq] at hr
      subst hr
      obtain ⟨Q', hQ'⟩ := (atHalt_tsite p P R).1 ha
      rw [hs] at hQ'
      simp only [Option.some.injEq, Prod.mk.injEq] at hQ'
      exact absurd hQ'.1 he
  | succ N =>
      obtain ⟨c1, hs1, hn⟩ := hn_succ h
      rw [step_tsite, hs] at hs1
      simp only at hs1
      rw [hl] at hs1
      cases hs1
      exact ⟨N, rfl, hn⟩

/-! ## Segments between tests -/

def segFuel : Nat := 1000

/-- Run leaves on the pointer alone until a test or `halt` leaf; return the
increments made and the pointer of that leaf. -/
def seg (t : Tree) : Nat → List Bool → Option (List Nat × List Bool)
  | 0, _ => none
  | f + 1, P =>
      match tsite t P with
      | some (.inc r, Q) =>
          match seg t f (incPath Q) with
          | some (l, P') => some (r :: l, P')
          | none => none
      | some (.brk k, Q) => seg t f (breakPath k Q)
      | some (.cont k, Q) => seg t f (continuePath k Q)
      | some (.decnz _, _) => some ([], P)
      | some (.halt, _) => some ([], P)
      | _ => none

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- How often register `i` occurs in `l`. -/
def cnt : List Nat → Nat → Nat
  | [], _ => 0
  | r :: l, i => cond (Nat.beq r i) 1 0 + cnt l i

theorem update_succ (R : Registers) (r i : Nat) :
    update R r (R r + 1) i = R i + cond (Nat.beq r i) 1 0 := by
  simp only [update]
  by_cases h : i = r
  · subst h; simp
  · have : Nat.beq r i = false := beq_false (Ne.symm h)
    simp [h, this]

theorem seg_run (p : Program) : ∀ (f : Nat) (P : List Bool) (l : List Nat) (P' : List Bool)
    (R : Registers), seg (ptree p) f P = some (l, P') →
    ∃ n R', run p n ⟨P, R⟩ = some ⟨P', R'⟩ ∧ ∀ i, R' i = R i + cnt l i
  | 0, _, _, _, _, h => by simp [seg] at h
  | f + 1, P, l, P', R, h => by
      simp only [seg] at h
      revert h
      cases ht : tsite (ptree p) P with
      | none => intro h; cases h
      | some eQ =>
          obtain ⟨e, Q⟩ := eQ
          have hstep : step p ⟨P, R⟩ = execute e Q R := by rw [step_tsite, ht]
          cases e with
          | inc r =>
              intro h
              simp only at h
              revert h
              cases hs : seg (ptree p) f (incPath Q) with
              | none => intro h; cases h
              | some lP =>
                  obtain ⟨l1, P1⟩ := lP
                  intro h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  obtain ⟨n, R', hr, hR⟩ := seg_run p f _ _ _ (update R r (R r + 1)) hs
                  refine ⟨n + 1, R', ?_, fun i => ?_⟩
                  · simp only [run, hstep, execute]; exact hr
                  · rw [hR, update_succ, cnt]; omega
          | brk k | cont k =>
              intro h
              obtain ⟨n, R', hr, hR⟩ := seg_run p f _ _ _ R h
              exact ⟨n + 1, R', by simp only [run, hstep, execute]; exact hr, hR⟩
          | decnz r | halt =>
              intro h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨0, R, rfl, fun i => by simp [cnt]⟩
          | node m => intro h; cases h

theorem seg_hn (p : Program) : ∀ (f : Nat) (P : List Bool) (l : List Nat) (P' : List Bool)
    (R : Registers) (N : Nat), seg (ptree p) f P = some (l, P') → HN p N ⟨P, R⟩ →
    ∃ N' R', N' ≤ N ∧ HN p N' ⟨P', R'⟩ ∧ ∀ i, R' i = R i + cnt l i := by
  intro f P l P' R N hs hN
  obtain ⟨n, R', hr, hR⟩ := seg_run p f P l P' R hs
  obtain ⟨N', he, h'⟩ := hn_after hr hN
  exact ⟨N', R', by omega, h', hR⟩

/-! ## Segment bisimulations -/

/-- Both segments exist, increment every register equally often, and end at related sites. -/
def BranchGood (t1 t2 : Tree) (S : List Bool → List Bool → Prop) (A B : List Bool) : Prop :=
  ∃ l1 P1 l2 P2, seg t1 segFuel A = some (l1, P1) ∧ seg t2 segFuel B = some (l2, P2) ∧
    (∀ i, cnt l1 i = cnt l2 i) ∧ S P1 P2

/-- Related sites: both halt, or both test the same register with good branches. -/
def EntryGood (t1 t2 : Tree) (S : List Bool → List Bool → Prop) (P1 P2 : List Bool) : Prop :=
  (∃ Q1 Q2, tsite t1 P1 = some (.halt, Q1) ∧ tsite t2 P2 = some (.halt, Q2)) ∨
  (∃ r Q1 Q2, tsite t1 P1 = some (.decnz r, Q1) ∧ tsite t2 P2 = some (.decnz r, Q2) ∧
    BranchGood t1 t2 S (incPath Q1) (incPath Q2) ∧
    BranchGood t1 t2 S (breakPath 1 Q1) (breakPath 1 Q2))

structure Bisim (t1 t2 : Tree) (S : List Bool → List Bool → Prop) : Prop where
  start : BranchGood t1 t2 S [] []
  step : ∀ P1 P2, S P1 P2 → EntryGood t1 t2 S P1 P2

theorem BranchGood.symm {t1 t2 : Tree} {S : List Bool → List Bool → Prop} {A B : List Bool}
    (h : BranchGood t1 t2 S A B) : BranchGood t2 t1 (fun a b => S b a) B A := by
  obtain ⟨l1, P1, l2, P2, h1, h2, hc, hS⟩ := h
  exact ⟨l2, P2, l1, P1, h2, h1, fun i => (hc i).symm, hS⟩

theorem Bisim.symm {t1 t2 : Tree} {S : List Bool → List Bool → Prop} (h : Bisim t1 t2 S) :
    Bisim t2 t1 (fun a b => S b a) := by
  refine ⟨h.start.symm, fun P2 P1 hS => (h.step P1 P2 hS).imp
    (fun ⟨Q1, Q2, h1, h2⟩ => ⟨Q2, Q1, h2, h1⟩)
    fun ⟨r, Q1, Q2, h1, h2, hj, hk⟩ => ⟨r, Q2, Q1, h2, h1, hj.symm, hk.symm⟩⟩

section Sound

variable {p1 p2 : Program} {S : List Bool → List Bool → Prop}

theorem branch_sim (N : Nat) {A B : List Bool} {R : Registers}
    (IH : ∀ N', N' ≤ N → ∀ P1 P2 R, S P1 P2 → HN p1 N' ⟨P1, R⟩ → Halts p2 ⟨P2, R⟩)
    (hb : BranchGood (ptree p1) (ptree p2) S A B) (h : HN p1 N ⟨A, R⟩) : Halts p2 ⟨B, R⟩ := by
  obtain ⟨l1, P1, l2, P2, h1, h2, hc, hS⟩ := hb
  obtain ⟨N', R1, hle, h', hR1⟩ := seg_hn p1 _ _ _ _ _ _ h1 h
  obtain ⟨n, R2, hr, hR2⟩ := seg_run p2 _ _ _ _ R h2
  have e : R2 = R1 := funext fun i => by rw [hR1, hR2, hc]
  subst e
  exact halts_pre hr (IH N' hle P1 P2 _ hS h')

theorem sim (hB : ∀ P1 P2, S P1 P2 → EntryGood (ptree p1) (ptree p2) S P1 P2) :
    ∀ (N : Nat) (P1 P2 : List Bool) (R : Registers), S P1 P2 → HN p1 N ⟨P1, R⟩ → Halts p2 ⟨P2, R⟩ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N IH =>
  intro P1 P2 R hS h
  rcases hB P1 P2 hS with ⟨Q1, Q2, h1, h2⟩ | ⟨r, Q1, Q2, h1, h2, hj, hk⟩
  · exact ⟨0, ⟨P2, R⟩, rfl, (atHalt_tsite p2 P2 R).2 ⟨Q2, h2⟩⟩
  · cases hv : R r with
    | zero =>
        obtain ⟨N', rfl, h'⟩ := hn_step (c' := ⟨breakPath 1 Q1, R⟩) h1 (by intro h; cases h)
          (by simp only [execute, hv]) h
        have hr : run p2 1 ⟨P2, R⟩ = some ⟨breakPath 1 Q2, R⟩ := by
          simp only [run, step_tsite, h2, execute, hv]
        exact halts_pre hr (branch_sim N' (fun N'' hle => IH N'' (by omega)) hk h')
    | succ v =>
        obtain ⟨N', rfl, h'⟩ := hn_step (c' := ⟨incPath Q1, update R r v⟩) h1 (by intro h; cases h)
          (by simp only [execute, hv]) h
        have hr : run p2 1 ⟨P2, R⟩ = some ⟨incPath Q2, update R r v⟩ := by
          simp only [run, step_tsite, h2, execute, hv]
        exact halts_pre hr (branch_sim N' (fun N'' hle => IH N'' (by omega)) hj h')

/-- **A segment bisimulation transfers halting** from the empty pointer. -/
theorem Bisim.halts (hB : Bisim (ptree p1) (ptree p2) S) (R : Registers) :
    Halts p1 ⟨[], R⟩ → Halts p2 ⟨[], R⟩ := by
  rintro ⟨N, c, hr, ha⟩
  exact branch_sim N (fun N' _ => sim hB.step N') hB.start ⟨c, hr, ha⟩

end Sound

theorem Bisim.halts_iff {p1 p2 : Program} {S : List Bool → List Bool → Prop}
    (hB : Bisim (ptree p1) (ptree p2) S) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  ⟨hB.halts R, hB.symm.halts R⟩

/-! ## The certificate checker -/

/-- A pointer coded as a number: binary `1` followed by the bits, most significant first. -/
def decodeAux : Nat → Nat → List Bool → List Bool
  | 0, _, acc => acc
  | f + 1, n, acc => if n ≤ 1 then acc else decodeAux f (n / 2) ((n % 2 == 1) :: acc)

def decode (n : Nat) : List Bool := decodeAux 128 n []

/-- An entry: two coded test-site pointers and the successor entries of the
nonzero and zero outcomes. -/
abbrev Entry := Nat × Nat × Nat × Nat

inductive CTree where
  | empty
  | leaf (x : Entry)
  | branch (cut : Nat) (l r : CTree)

def lookupC : CTree → Nat → Option Entry
  | .empty, _ => none
  | .leaf x, _ => some x
  | .branch cut l r, j => if j < cut then lookupC l j else lookupC r (j - cut)

def allC (f : Entry → Bool) : CTree → Bool
  | .empty => true
  | .leaf x => f x
  | .branch _ l r => allC f l && allC f r

theorem lookupC_all {f : Entry → Bool} : ∀ {T : CTree} {j : Nat} {x : Entry},
    lookupC T j = some x → allC f T = true → f x = true
  | .empty, _, _, h, _ => by cases h
  | .leaf y, _, _, h, hall => by cases h; exact hall
  | .branch cut l r, j, x, h, hall => by
      simp only [allC, Bool.and_eq_true] at hall
      simp only [lookupC] at h
      split at h
      · exact lookupC_all h hall.1
      · exact lookupC_all h hall.2

def lbeq : List Bool → List Bool → Bool
  | [], [] => true
  | x :: a, y :: b => (x == y) && lbeq a b
  | _, _ => false

theorem lbeq_ok : ∀ {a b : List Bool}, lbeq a b = true → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
      simp only [lbeq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, lbeq_ok h.2]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

def cntEq (l1 l2 : List Nat) : Bool := (l1 ++ l2).all fun i => Nat.beq (cnt l1 i) (cnt l2 i)

theorem cnt_zero : ∀ {l : List Nat} {i : Nat}, i ∉ l → cnt l i = 0
  | [], _, _ => rfl
  | r :: l, i, h => by
      simp only [List.mem_cons, not_or] at h
      simp [cnt, beq_false (Ne.symm h.1), cnt_zero h.2]

theorem cntEq_ok {l1 l2 : List Nat} (h : cntEq l1 l2 = true) (i : Nat) : cnt l1 i = cnt l2 i := by
  simp only [cntEq, List.all_eq_true] at h
  by_cases hi : i ∈ l1 ++ l2
  · exact Nat.eq_of_beq_eq_true (h i hi)
  · simp only [List.mem_append, not_or] at hi
    rw [cnt_zero hi.1, cnt_zero hi.2]

/-! A certificate denotes exactly the paths returned by its decoder. Soundness
requires no numeric size bound or other property of that decoder. -/
namespace WithDecoder

variable (decode : Nat → List Bool)

def getc (T : CTree) (j : Nat) : Option (List Bool × List Bool) :=
  match lookupC T j with
  | some (a, b, _, _) => some (decode a, decode b)
  | none => none

def branchOk (t1 t2 : Tree) (T : CTree) (A B : List Bool) (j : Nat) : Bool :=
  match seg t1 segFuel A, seg t2 segFuel B, getc decode T j with
  | some (l1, P1), some (l2, P2), some (Q1, Q2) => cntEq l1 l2 && lbeq P1 Q1 && lbeq P2 Q2
  | _, _, _ => false

def entryOk (t1 t2 : Tree) (T : CTree) (x : Entry) : Bool :=
  match tsite t1 (decode x.1), tsite t2 (decode x.2.1) with
  | some (.halt, _), some (.halt, _) => true
  | some (.decnz r1, Q1), some (.decnz r2, Q2) =>
      Nat.beq r1 r2 && branchOk decode t1 t2 T (incPath Q1) (incPath Q2) x.2.2.1 &&
        branchOk decode t1 t2 T (breakPath 1 Q1) (breakPath 1 Q2) x.2.2.2
  | _, _ => false

/-- The relation a certificate tree denotes: the pairs its lookup returns. -/
def Rel (T : CTree) (P1 P2 : List Bool) : Prop := ∃ j, getc decode T j = some (P1, P2)

theorem branchOk_good {t1 t2 : Tree} {T : CTree} {A B : List Bool} {j : Nat}
    (h : branchOk decode t1 t2 T A B j = true) : BranchGood t1 t2 (Rel decode T) A B := by
  unfold branchOk at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hc, e1⟩, e2⟩ := h
    obtain rfl := lbeq_ok e1
    obtain rfl := lbeq_ok e2
    exact ⟨_, _, _, _, ‹_›, ‹_›, cntEq_ok hc, j, ‹_›⟩
  · cases h

theorem entryOk_good {t1 t2 : Tree} {T : CTree} {x : Entry} (h : entryOk decode t1 t2 T x = true) :
    EntryGood t1 t2 (Rel decode T) (decode x.1) (decode x.2.1) := by
  unfold entryOk at h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, ‹_›⟩
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hr, hj⟩, hk⟩ := h
    obtain rfl := Nat.eq_of_beq_eq_true hr
    exact Or.inr ⟨_, _, _, ‹_›, ‹_›, branchOk_good decode hj, branchOk_good decode hk⟩
  · cases h

def check (t1 t2 : Tree) (T : CTree) : Bool :=
  branchOk decode t1 t2 T [] [] 0 && allC (entryOk decode t1 t2 T) T

theorem check_bisim {t1 t2 : Tree} {T : CTree} (hs : branchOk decode t1 t2 T [] [] 0 = true)
    (ha : allC (entryOk decode t1 t2 T) T = true) : Bisim t1 t2 (Rel decode T) := by
  refine ⟨branchOk_good decode hs, fun P1 P2 ⟨j, hj⟩ => ?_⟩
  unfold getc at hj
  split at hj
  · simp only [Option.some.injEq, Prod.mk.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    exact entryOk_good decode (lookupC_all ‹_› ha)
  · cases hj

/-- **Checked certificates give halting equivalence**, in both directions. -/
theorem check_halts_iff {p1 p2 : Program} {T : CTree}
    (hs : branchOk decode (ptree p1) (ptree p2) T [] [] 0 = true)
    (ha : allC (entryOk decode (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  (check_bisim decode hs ha).halts_iff R

end WithDecoder

/-! The original API retains its exact 128-fuel decoding behavior. -/

abbrev getc := WithDecoder.getc decode
abbrev branchOk := WithDecoder.branchOk decode
abbrev entryOk := WithDecoder.entryOk decode
abbrev Rel := WithDecoder.Rel decode
abbrev check := WithDecoder.check decode

theorem branchOk_good {t1 t2 : Tree} {T : CTree} {A B : List Bool} {j : Nat}
    (h : branchOk t1 t2 T A B j = true) : BranchGood t1 t2 (Rel T) A B :=
  WithDecoder.branchOk_good decode h

theorem entryOk_good {t1 t2 : Tree} {T : CTree} {x : Entry} (h : entryOk t1 t2 T x = true) :
    EntryGood t1 t2 (Rel T) (decode x.1) (decode x.2.1) :=
  WithDecoder.entryOk_good decode h

theorem check_bisim {t1 t2 : Tree} {T : CTree} (hs : branchOk t1 t2 T [] [] 0 = true)
    (ha : allC (entryOk t1 t2 T) T = true) : Bisim t1 t2 (Rel T) :=
  WithDecoder.check_bisim decode hs ha

theorem check_halts_iff {p1 p2 : Program} {T : CTree}
    (hs : branchOk (ptree p1) (ptree p2) T [] [] 0 = true)
    (ha : allC (entryOk (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  WithDecoder.check_halts_iff decode hs ha R

end SetTheory.BusyBeaver.ZFC.RMBisim
