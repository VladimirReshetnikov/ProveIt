import BusyBeaver.ZFC.RegisterPath
import BusyBeaver.ZFC.RMDag

/-!
Wade's path semantics and the structured semantics of register DAGs agree.

The Turing machine runs a register program in the *path* semantics of
`RegisterPath` (the instruction pointer is a bit path, advanced by increment
and strip arithmetic). The program-level proofs (L2) use the *structured*
big-step semantics of `RMDag`. For every well-formed DAG `p` with `nn` used
nodes this file proves

    Halts (ofDag p nn) ⟨[], R⟩ ↔ IterHalts p R,

where `ofDag p nn` is `p` read as a path program. Well-formedness (`WF`) asks
for an acyclic node table of height at most `nn + 1` (so the decoder fuel of
the path semantics suffices) and that no break or continue escapes the root;
`wfCheck_sound` reduces it to a Boolean check against candidate tables.

The proof follows the method of the published verification's `RMEquiv.v`
(Jeff's verification of Mira-Cult's machine, busy-beaver commit
297ab8df7e5de329605c3875b4934643b371a5e3, `ZF/m254/coq/tm/RMEquiv.v`; Wade
supplied the TMBuilder framework): a forward simulation by induction on the
big-step derivation, and a backward simulation by strong induction on the
number of path steps with an inner induction on the height of the edge.
Paths are compared up to trailing zeros (`ipeq`), since finishing a cdr leaves
a trailing zero bit behind. This is an independent Lean development, not a
relicensing of the upstream snapshot.
-/

namespace SetTheory.BusyBeaver.ZFC.RMEquiv

open RMDag
open RegisterPath (bit walk incRev incPath stripRev stripPath breakPath continuePath consume
  execute step run AtHalt Halts Configuration)

/-! ## A DAG as a path program -/

def toPath : Edge → RegisterPath.Edge
  | .node n => .node n
  | .inc r => .inc r
  | .decnz r => .decnz r
  | .brk k => .brk k
  | .cont k => .cont k
  | .halt => .halt

def ofDag (p : Prog) (nn : Nat) : RegisterPath.Program :=
  ⟨fun n => (toPath (p.nodes n).1, toPath (p.nodes n).2), p.root, nn⟩

@[simp] theorem ofDag_nnodes (p : Prog) (nn : Nat) : (ofDag p nn).nnodes = nn := rfl
@[simp] theorem ofDag_root (p : Prog) (nn : Nat) : (ofDag p nn).root = p.root := rfl

/-- The child of node `n` selected by bit `b` (car for `false`, cdr for `true`). -/
def child (p : Prog) (n : Nat) (b : Bool) : Edge := if b then (p.nodes n).2 else (p.nodes n).1

/-- Follow exactly the bits of `Q` from edge `e`. -/
def fol (p : Prog) : Edge → List Bool → Option Edge
  | e, [] => some e
  | .node n, b :: Q => fol p (child p n b) Q
  | _, _ :: _ => none

/-! ## Well-formedness -/

def edgeOk (nn : Nat) : Edge → Prop
  | .node n => n < nn
  | .brk k => 0 < k
  | .cont k => 0 < k
  | _ => True

/-- Height of an edge for a height table. -/
def hE (H : Nat → Nat) : Edge → Nat
  | .node m => H m
  | _ => 0

/-- Largest break level an edge can exit with, for a table. -/
def bE (B : Nat → Nat) : Edge → Nat
  | .node m => B m
  | .decnz _ => 1
  | .brk k => k
  | _ => 0

/-- Largest continue level an edge can exit with, for a table. -/
def cE (C : Nat → Nat) : Edge → Nat
  | .node m => C m
  | .cont k => k
  | _ => 0

structure WF (p : Prog) (nn : Nat) : Prop where
  root : p.root < nn
  edges : ∀ n b, n < nn → edgeOk nn (child p n b)
  height : ∃ H : Nat → Nat, H p.root ≤ nn + 1 ∧ ∀ n b, n < nn → hE H (child p n b) < H n
  escape : ∃ B C : Nat → Nat, B p.root = 0 ∧ C p.root = 0 ∧ ∀ n, n < nn →
    bE B (p.nodes n).1 ≤ B n + 1 ∧ bE B (p.nodes n).2 ≤ B n ∧
    cE C (p.nodes n).1 ≤ C n ∧ cE C (p.nodes n).2 ≤ C n + 1

/-! ## Bits and paths up to trailing zeros -/

def ipeq (P P' : List Bool) : Prop := ∀ i, bit P i = bit P' i

theorem ipeq.refl (P : List Bool) : ipeq P P := fun _ => rfl
theorem ipeq.symm {P P' : List Bool} (h : ipeq P P') : ipeq P' P := fun i => (h i).symm
theorem ipeq.trans {P1 P2 P3 : List Bool} (h1 : ipeq P1 P2) (h2 : ipeq P2 P3) : ipeq P1 P3 :=
  fun i => (h1 i).trans (h2 i)

@[simp] theorem bit_nil (i : Nat) : bit [] i = false := by simp [bit]
@[simp] theorem bit_cons_zero (a : Bool) (P : List Bool) : bit (a :: P) 0 = a := by simp [bit]
@[simp] theorem bit_cons_succ (a : Bool) (P : List Bool) (i : Nat) : bit (a :: P) (i + 1) = bit P i := by
  simp [bit]
theorem bit_tail (P : List Bool) (i : Nat) : bit P.tail i = bit P (i + 1) := by
  cases P <;> simp

theorem ipeq_snoc_false : ∀ Q : List Bool, ipeq (Q ++ [false]) Q
  | [], i => by cases i <;> simp
  | a :: Q, i => by
      cases i with
      | zero => simp
      | succ i => simpa using ipeq_snoc_false Q i

/-- The first `d` bits of a path, zero padded. -/
def pre (P : List Bool) : Nat → List Bool
  | 0 => []
  | d + 1 => bit P 0 :: pre P.tail d

theorem take_pad : ∀ (d m : Nat) (P : List Bool), d ≤ m →
    (P ++ List.replicate m false).take d = pre P d
  | 0, _, _, _ => by simp [pre]
  | d + 1, m, P, h => by
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      cases P with
      | nil =>
          have := take_pad d m [] (by omega)
          simp only [List.nil_append] at this
          simp only [List.nil_append, List.replicate_succ, List.take_succ_cons, pre, bit_nil,
            List.tail_nil, this]
      | cons a P =>
          simp only [List.cons_append, List.take_succ_cons, pre, bit_cons_zero, List.tail_cons,
            take_pad d (m + 1) P (by omega)]

theorem consume_eq (P : List Bool) (d : Nat) : consume P d = pre P d := take_pad d d P (Nat.le_refl d)

theorem pre_ipeq : ∀ (d : Nat) {P P' : List Bool}, ipeq P P' → pre P d = pre P' d
  | 0, _, _, _ => rfl
  | d + 1, P, P', h => by
      simp only [pre, h 0, pre_ipeq d (P := P.tail) (P' := P'.tail)
        (fun i => by rw [bit_tail, bit_tail, h])]

theorem pad_eq : ∀ (Q : List Bool) {P : List Bool}, ipeq P Q → pre P Q.length = Q
  | [], _, _ => rfl
  | b :: Q, P, h => by
      simp only [List.length_cons, pre, h 0, bit_cons_zero,
        pad_eq Q (P := P.tail) (fun i => by rw [bit_tail, h (i + 1), bit_cons_succ])]

/-! ## Path arithmetic at the right end -/

theorem incPath_snoc_false (Q : List Bool) : incPath (Q ++ [false]) = Q ++ [true] := by
  simp [incPath, incRev]

theorem incPath_snoc_true (Q : List Bool) : incPath (Q ++ [true]) = incPath Q ++ [false] := by
  simp [incPath, incRev]

theorem brk0 (Q : List Bool) : breakPath 0 Q = incPath Q := by
  simp [breakPath, stripPath, stripRev]

theorem brk_car1 (Q : List Bool) : breakPath 1 (Q ++ [false]) = incPath Q := by
  simp [breakPath, stripPath, stripRev]

theorem brk_carS (k : Nat) (Q : List Bool) : breakPath (k + 2) (Q ++ [false]) = breakPath (k + 1) Q := by
  simp [breakPath, stripPath, stripRev]

theorem brk_cdr (k : Nat) (Q : List Bool) : breakPath (k + 1) (Q ++ [true]) = breakPath (k + 1) Q := by
  simp [breakPath, stripPath, stripRev]

theorem cont_car (k : Nat) (Q : List Bool) :
    continuePath (k + 1) (Q ++ [false]) = continuePath (k + 1) Q := by
  simp [continuePath, stripPath, stripRev]

theorem cont_cdr1 (Q : List Bool) : continuePath 1 (Q ++ [true]) = Q := by
  simp [continuePath, stripPath, stripRev]

theorem cont_cdrS (k : Nat) (Q : List Bool) :
    continuePath (k + 2) (Q ++ [true]) = continuePath (k + 1) Q := by
  simp [continuePath, stripPath, stripRev]

/-! ## Following paths -/

variable {p : Prog} {nn : Nat}

theorem fol_snoc {e : Edge} {n : Nat} (b : Bool) :
    ∀ {Q : List Bool}, fol p e Q = some (.node n) → fol p e (Q ++ [b]) = some (child p n b)
  | [], h => by simp only [fol, Option.some.injEq] at h; subst h; rfl
  | c :: Q, h => by
      cases e with
      | node m => exact fol_snoc (e := child p m c) b (Q := Q) h
      | _ => simp [fol] at h

theorem fol_ok (W : WF p nn) : ∀ {e : Edge} {Q : List Bool} {e' : Edge},
    edgeOk nn e → fol p e Q = some e' → edgeOk nn e'
  | e, [], e', ok, h => by simp only [fol, Option.some.injEq] at h; subst h; exact ok
  | e, b :: Q, e', ok, h => by
      cases e with
      | node m => exact fol_ok W (W.edges m b ok) h
      | _ => simp [fol] at h

theorem root_ok (W : WF p nn) : edgeOk nn (.node p.root) := W.root

/-! ## Walks -/

theorem walk_succ (f n : Nat) (P : List Bool) (i : Nat) :
    walk (ofDag p nn) (f + 1) n P i =
      match child p n (bit P i) with
      | .node m => walk (ofDag p nn) f m P (i + 1)
      | e => some (toPath e, i + 1) := by
  simp only [walk, ofDag, child]
  cases bit P i <;> simp only [Bool.false_eq_true, if_false, if_true]
  · generalize (p.nodes n).1 = e; cases e <;> rfl
  · generalize (p.nodes n).2 = e; cases e <;> rfl

theorem walk_ipeq (q : RegisterPath.Program) {P P' : List Bool} (E : ipeq P P') :
    ∀ f n i, walk q f n P i = walk q f n P' i
  | 0, _, _ => rfl
  | f + 1, n, i => by simp only [walk, E i, walk_ipeq q E f]

theorem walk_path (W : WF p nn) {H : Nat → Nat} (HH : ∀ n b, n < nn → hE H (child p n b) < H n) :
    ∀ (Q : List Bool) (f n i : Nat) (P : List Bool) (e : Edge), n < nn → H n ≤ f →
      fol p (.node n) Q = some e → (∀ m, e ≠ .node m) →
      (∀ j, j < Q.length → bit P (i + j) = bit Q j) →
      walk (ofDag p nn) f n P i = some (toPath e, i + Q.length)
  | [], f, n, i, P, e, _, _, F, Hl, _ => by
      simp only [fol, Option.some.injEq] at F; exact absurd F.symm (Hl n)
  | b :: Q, f, n, i, P, e, hn, hf, F, Hl, A => by
      have hc := HH n b hn
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hb : bit P i = b := by simpa using A 0 (by simp)
      rw [walk_succ, hb]
      simp only [fol] at F
      have ok := W.edges n b hn
      revert F hc ok
      generalize child p n b = c
      intro F hc ok
      cases c with
      | node m =>
          simp only [hE] at hc
          show walk (ofDag p nn) f m P (i + 1) = _
          rw [walk_path W HH Q f m (i + 1) P e ok (by omega) F Hl (fun j hj => by
            rw [show i + 1 + j = i + (j + 1) by omega, A (j + 1) (by simp; omega), bit_cons_succ])]
          simp only [List.length_cons]; congr 2; omega
      | _ => cases Q with
          | nil => simp only [fol, Option.some.injEq] at F; subst F; simp
          | cons _ _ => simp [fol] at F

theorem walk_leaf (W : WF p nn) {Q : List Bool} {e : Edge} {P : List Bool}
    (F : fol p (.node p.root) Q = some e) (Hl : ∀ m, e ≠ .node m) (E : ipeq P Q) :
    walk (ofDag p nn) (nn + 1) p.root P 0 = some (toPath e, Q.length) := by
  obtain ⟨H, Hr, HH⟩ := W.height
  have := walk_path W HH Q (nn + 1) p.root 0 P e W.root Hr F Hl (fun j _ => by rw [Nat.zero_add, E])
  rwa [Nat.zero_add] at this

/-! ## One path step at a leaf -/

theorem leaf_step (W : WF p nn) {Q : List Bool} {e : Edge} {P : List Bool}
    (F : fol p (.node p.root) Q = some e) (Hl : ∀ m, e ≠ .node m) (E : ipeq P Q) (R : Regs) :
    step (ofDag p nn) ⟨P, R⟩ = execute (toPath e) Q R := by
  unfold step
  simp only [ofDag_nnodes, ofDag_root]
  rw [walk_leaf W F Hl E]
  simp only [consume_eq, pad_eq Q E]

theorem step_ipeq (q : RegisterPath.Program) {P P' : List Bool} (E : ipeq P P') (R : Regs) :
    step q ⟨P, R⟩ = step q ⟨P', R⟩ := by
  unfold step
  simp only [walk_ipeq q E]
  cases walk q (q.nnodes + 1) q.root P' 0 with
  | none => rfl
  | some ed => simp only [consume_eq, pre_ipeq _ E]

/-! ## Runs -/

theorem run_add (q : RegisterPath.Program) : ∀ (a b : Nat) (c : Configuration),
    run q (a + b) c = match run q a c with
      | some c' => run q b c'
      | none => none
  | 0, b, c => by simp [run]
  | a + 1, b, c => by
      rw [Nat.add_right_comm]
      simp only [run]
      cases step q c with
      | none => rfl
      | some c1 => exact run_add q a b c1

/-- Halting after exactly `N` path steps. -/
def HN (q : RegisterPath.Program) (N : Nat) (c : Configuration) : Prop :=
  ∃ c', run q N c = some c' ∧ AtHalt q c'

theorem hn_pre {q : RegisterPath.Program} {N1 N2 : Nat} {c c1 : Configuration}
    (h1 : run q N1 c = some c1) (h2 : HN q N2 c1) : HN q (N1 + N2) c := by
  obtain ⟨c', h, ha⟩ := h2
  exact ⟨c', by rwa [run_add, h1], ha⟩

theorem hn_succ {q : RegisterPath.Program} {N : Nat} {c : Configuration} (h : HN q (N + 1) c) :
    ∃ c1, step q c = some c1 ∧ HN q N c1 := by
  obtain ⟨c', hr, ha⟩ := h
  simp only [run] at hr
  split at hr <;> first | exact ⟨_, ‹_›, c', hr, ha⟩ | cases hr

theorem hn_ipeq {q : RegisterPath.Program} {N : Nat} {P P' : List Bool} {R : Regs}
    (E : ipeq P P') (h : HN q N ⟨P, R⟩) : HN q N ⟨P', R⟩ := by
  cases N with
  | zero =>
      obtain ⟨c', hr, d, hd⟩ := h
      simp only [run, Option.some.injEq] at hr
      subst hr
      exact ⟨⟨P', R⟩, rfl, d, by rwa [← walk_ipeq q E]⟩
  | succ N =>
      obtain ⟨c', hr, ha⟩ := h
      refine ⟨c', ?_, ha⟩
      simp only [run] at hr ⊢
      rwa [← step_ipeq q E]

theorem run_one {q : RegisterPath.Program} {c c' : Configuration} (h : step q c = some c') :
    run q 1 c = some c' := by
  simp [run, h]

/-! ## Exit positions -/

def target (Q : List Bool) : Exit → List Bool
  | .normal => incPath Q
  | .brk k => breakPath k Q
  | .cont k => continuePath k Q
  | .halt => Q

theorem run_pos {e : Edge} {R : Regs} {x : Exit} {R' : Regs} (h : Run p e R x R') :
    (∀ k, x = .brk k → 0 < k) ∧ (∀ k, x = .cont k → 0 < k) := by
  induction h with
  | cdrCont1 _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | _ => constructor <;> intro k hk <;> cases hk <;> omega

theorem run_bound (W : WF p nn) {B C : Nat → Nat}
    (HBC : ∀ n, n < nn → bE B (p.nodes n).1 ≤ B n + 1 ∧ bE B (p.nodes n).2 ≤ B n ∧
      cE C (p.nodes n).1 ≤ C n ∧ cE C (p.nodes n).2 ≤ C n + 1)
    {e : Edge} {R : Regs} {x : Exit} {R' : Regs} (h : Run p e R x R') :
    edgeOk nn e → (∀ k, x = .brk k → k ≤ bE B e) ∧ (∀ k, x = .cont k → k ≤ cE C e) := by
  induction h with
  | decZero => intro _; constructor <;> intro k hk <;> cases hk; simp [bE]
  | brkS => intro _; constructor <;> intro k hk <;> cases hk; simp [bE]
  | contS => intro _; constructor <;> intro k hk <;> cases hk; simp [cE]
  | carBrkS n k R R' h ih =>
      intro ok
      have hn : n < nn := ok
      have := (ih (W.edges n false hn)).1 (k + 2) rfl
      have := (HBC n hn).1
      constructor <;> intro k' hk <;> cases hk; simp only [bE]; omega
  | carCont n k R R' h ih =>
      intro ok
      have hn : n < nn := ok
      have := (ih (W.edges n false hn)).2 (k + 1) rfl
      have := (HBC n hn).2.2.1
      constructor <;> intro k' hk <;> cases hk; simp only [cE]; omega
  | cdrBrk n k R R1 R' h1 h2 ih1 ih2 =>
      intro ok
      have hn : n < nn := ok
      have := (ih2 (W.edges n true hn)).1 (k + 1) rfl
      have := (HBC n hn).2.1
      constructor <;> intro k' hk <;> cases hk; simp only [bE]; omega
  | cdrCont1 _ _ _ _ _ _ _ _ _ _ _ ih3 => exact ih3
  | cdrContS n k R R1 R' h1 h2 ih1 ih2 =>
      intro ok
      have hn : n < nn := ok
      have := (ih2 (W.edges n true hn)).2 (k + 2) rfl
      have := (HBC n hn).2.2.2
      constructor <;> intro k' hk <;> cases hk; simp only [cE]; omega
  | _ => intro _; constructor <;> intro k hk <;> cases hk

/-- No break or continue escapes the root. -/
theorem wf_run (W : WF p nn) {R : Regs} {x : Exit} {R' : Regs} (h : Run p (.node p.root) R x R') :
    x = .normal ∨ x = .halt := by
  obtain ⟨B, C, hB, hC, HBC⟩ := W.escape
  have hb := run_bound W HBC h W.root
  have hp := run_pos h
  cases x with
  | normal => exact Or.inl rfl
  | halt => exact Or.inr rfl
  | brk k => have h1 := hb.1 k rfl; have h2 := hp.1 k rfl; simp only [bE, hB] at h1; omega
  | cont k => have h1 := hb.2 k rfl; have h2 := hp.2 k rfl; simp only [cE, hC] at h1; omega

/-! ## Structured runs are simulated by path runs -/

/-- The path configuration reaches the exit position of `x` (or halts). -/
def Reaches (p : Prog) (nn : Nat) (c : Configuration) (Q : List Bool) (x : Exit) (R' : Regs) : Prop :=
  match x with
  | .halt => ∃ N, HN (ofDag p nn) N c
  | x => ∃ N P', run (ofDag p nn) N c = some ⟨P', R'⟩ ∧ ipeq P' (target Q x)

theorem reaches_pre {N : Nat} {c c1 : Configuration} {Q : List Bool} {x : Exit} {R' : Regs}
    (h1 : run (ofDag p nn) N c = some c1) (h : Reaches p nn c1 Q x R') : Reaches p nn c Q x R' := by
  cases x with
  | halt => obtain ⟨N2, hn⟩ := h; exact ⟨N + N2, hn_pre h1 hn⟩
  | _ =>
      obtain ⟨N2, P', h2, E⟩ := h
      exact ⟨N + N2, P', by rwa [run_add, h1], E⟩

theorem fwd (W : WF p nn) {e : Edge} {R : Regs} {x : Exit} {R' : Regs} (h : Run p e R x R') :
    ∀ Q P, fol p (.node p.root) Q = some e → ipeq P Q → Reaches p nn ⟨P, R⟩ Q x R' := by
  induction h with
  | inc r R =>
      intro Q P F E
      exact ⟨1, incPath Q, run_one (by rw [leaf_step W F (fun _ h => by cases h) E]; rfl), ipeq.refl _⟩
  | decPos r R v hv =>
      intro Q P F E
      exact ⟨1, incPath Q, run_one (by
        rw [leaf_step W F (fun _ h => by cases h) E]; simp only [toPath, execute, hv]; rfl), ipeq.refl _⟩
  | decZero r R hv =>
      intro Q P F E
      exact ⟨1, breakPath 1 Q, run_one (by
        rw [leaf_step W F (fun _ h => by cases h) E]; simp only [toPath, execute, hv]), ipeq.refl _⟩
  | brk0 R =>
      intro Q P F E
      exact ⟨1, breakPath 0 Q, run_one (by rw [leaf_step W F (fun _ h => by cases h) E]; rfl),
        by rw [brk0]; exact ipeq.refl _⟩
  | brkS k R =>
      intro Q P F E
      exact ⟨1, breakPath (k + 1) Q, run_one (by rw [leaf_step W F (fun _ h => by cases h) E]; rfl),
        ipeq.refl _⟩
  | contS k R =>
      intro Q P F E
      exact ⟨1, continuePath (k + 1) Q,
        run_one (by rw [leaf_step W F (fun _ h => by cases h) E]; rfl), ipeq.refl _⟩
  | halt R =>
      intro Q P F E
      exact ⟨0, ⟨P, R⟩, rfl, Q.length, walk_leaf W F (fun _ h => by cases h) E⟩
  -- All exits through the car use the same zero-padded child path.
  | carBrk1 n R R' h ih
  | carBrkS n k R R' h ih
  | carCont n k R R' h ih
  | carHalt n R R' h ih =>
      intro Q P F E
      simpa only [Reaches, target, brk_car1, brk_carS, cont_car] using
        ih (Q ++ [false]) P (fol_snoc false F) (E.trans (ipeq_snoc_false Q).symm)
  -- Once the car finishes normally, prepend its path run to the cdr's run.
  | cdrNormal n R R1 R' h1 h2 ih1 ih2
  | cdrBrk n k R R1 R' h1 h2 ih1 ih2
  | cdrContS n k R R1 R' h1 h2 ih1 ih2
  | cdrHalt n R R1 R' h1 h2 ih1 ih2 =>
      intro Q P F E
      obtain ⟨N1, P1, hr1, E1⟩ :=
        ih1 (Q ++ [false]) P (fol_snoc false F) (E.trans (ipeq_snoc_false Q).symm)
      simp only [target, incPath_snoc_false] at E1
      have hcdr := reaches_pre hr1 (ih2 (Q ++ [true]) P1 (fol_snoc true F) E1)
      first
      | simpa only [Reaches, target, brk_cdr, cont_cdrS] using hcdr
      | obtain ⟨N2, P2, hr2, E2⟩ := hcdr
        simp only [target, incPath_snoc_true] at E2
        exact ⟨N2, P2, hr2, E2.trans (ipeq_snoc_false _)⟩
  | cdrCont1 n R R1 R2 R' x h1 h2 h3 ih1 ih2 ih3 =>
      intro Q P F E
      obtain ⟨N1, P1, hr1, E1⟩ :=
        ih1 (Q ++ [false]) P (fol_snoc false F) (E.trans (ipeq_snoc_false Q).symm)
      simp only [target, incPath_snoc_false] at E1
      obtain ⟨N2, P2, hr2, E2⟩ := ih2 (Q ++ [true]) P1 (fol_snoc true F) E1
      simp only [target, cont_cdr1] at E2
      exact reaches_pre hr1 (reaches_pre hr2 (ih3 Q P2 F E2))

/-! ## Path runs are simulated by structured runs -/

/-- From a configuration that halts in exactly `N` steps, the edge at `Q` exits
(or halts), and the remaining path run halts from the exit position. -/
def BwdGoal (p : Prog) (nn N : Nat) (e : Edge) (Q : List Bool) (R : Regs) : Prop :=
  ∃ x R', Run p e R x R' ∧
    (x = .halt ∨ ∃ m, 1 ≤ m ∧ m ≤ N ∧ HN (ofDag p nn) (N - m) ⟨target Q x, R'⟩)

theorem hn_leaf (W : WF p nn) {N : Nat} {Q : List Bool} {e : Edge} {P : List Bool} {R : Regs}
    (F : fol p (.node p.root) Q = some e) (Hl : ∀ m, e ≠ .node m) (E : ipeq P Q) (hne : e ≠ .halt)
    (hN : HN (ofDag p nn) N ⟨P, R⟩) :
    ∃ N', N = N' + 1 ∧ ∃ c1, execute (toPath e) Q R = some c1 ∧ HN (ofDag p nn) N' c1 := by
  cases N with
  | zero =>
      obtain ⟨c', hr, d, hd⟩ := hN
      simp only [run, Option.some.injEq] at hr
      subst hr
      simp only [ofDag_nnodes, ofDag_root] at hd
      rw [walk_leaf W F Hl E] at hd
      have h := (Prod.mk.inj (Option.some.inj hd)).1
      cases e <;> first | exact absurd rfl hne | cases h
  | succ N =>
      obtain ⟨c1, hs, hn⟩ := hn_succ hN
      rw [leaf_step W F Hl E] at hs
      exact ⟨N, rfl, c1, hs, hn⟩

theorem bwd_leaf (W : WF p nn) {N : Nat} {Q : List Bool} {e : Edge} {P : List Bool} {R : Regs}
    (F : fol p (.node p.root) Q = some e) (Hl : ∀ m, e ≠ .node m) (E : ipeq P Q)
    (hN : HN (ofDag p nn) N ⟨P, R⟩) : BwdGoal p nn N e Q R := by
  have ok := fol_ok W (root_ok W) F
  cases e with
  | node m => exact absurd rfl (Hl m)
  | halt => exact ⟨.halt, R, .halt R, Or.inl rfl⟩
  | inc r =>
      obtain ⟨N', rfl, c1, hs, hn⟩ := hn_leaf W F Hl E (fun h => by cases h) hN
      simp only [toPath, execute, Option.some.injEq] at hs
      subst hs
      exact ⟨.normal, _, .inc r R, Or.inr ⟨1, Nat.le_refl 1, by omega, hn⟩⟩
  | decnz r =>
      obtain ⟨N', rfl, c1, hs, hn⟩ := hn_leaf W F Hl E (fun h => by cases h) hN
      cases hv : R r with
      | zero =>
          simp only [toPath, execute, hv, Option.some.injEq] at hs
          subst hs
          exact ⟨.brk 1, R, .decZero r R hv, Or.inr ⟨1, Nat.le_refl 1, by omega, hn⟩⟩
      | succ v =>
          simp only [toPath, execute, hv, Option.some.injEq] at hs
          subst hs
          exact ⟨.normal, _, .decPos r R v hv, Or.inr ⟨1, Nat.le_refl 1, by omega, hn⟩⟩
  | brk k =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [edgeOk] at ok; omega⟩
      obtain ⟨N', rfl, c1, hs, hn⟩ := hn_leaf W F Hl E (fun h => by cases h) hN
      simp only [toPath, execute, Option.some.injEq] at hs
      subst hs
      exact ⟨.brk (k + 1), R, .brkS k R, Or.inr ⟨1, Nat.le_refl 1, by omega, hn⟩⟩
  | cont k =>
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp only [edgeOk] at ok; omega⟩
      obtain ⟨N', rfl, c1, hs, hn⟩ := hn_leaf W F Hl E (fun h => by cases h) hN
      simp only [toPath, execute, Option.some.injEq] at hs
      subst hs
      exact ⟨.cont (k + 1), R, .contS k R, Or.inr ⟨1, Nat.le_refl 1, by omega, hn⟩⟩

theorem bwd (W : WF p nn) : ∀ (N : Nat) (e : Edge) (Q P : List Bool) (R : Regs),
    fol p (.node p.root) Q = some e → ipeq P Q → HN (ofDag p nn) N ⟨P, R⟩ → BwdGoal p nn N e Q R := by
  obtain ⟨H, -, HH⟩ := W.height
  intro N
  induction N using Nat.strongRecOn with
  | ind N IHN =>
  suffices Hh : ∀ (h : Nat) (e : Edge) (Q P : List Bool) (R : Regs), hE H e ≤ h →
      fol p (.node p.root) Q = some e → ipeq P Q → HN (ofDag p nn) N ⟨P, R⟩ → BwdGoal p nn N e Q R from
    fun e Q P R => Hh _ e Q P R (Nat.le_refl _)
  intro h
  induction h with
  | zero =>
      intro e Q P R he F E hN
      cases e
      case node n =>
        have ok : n < nn := fol_ok W (root_ok W) F
        have := HH n false ok
        simp only [hE] at he; omega
      all_goals exact bwd_leaf W F (fun _ h => by cases h) E hN
  | succ h IHh =>
      intro e Q P R he F E hN
      cases e
      case node n =>
        have ok : n < nn := fol_ok W (root_ok W) F
        have Ha : hE H (p.nodes n).1 < H n := HH n false ok
        simp only [hE] at he
        have Fa : fol p (.node p.root) (Q ++ [false]) = some (p.nodes n).1 := fol_snoc false F
        have Fb : fol p (.node p.root) (Q ++ [true]) = some (p.nodes n).2 := fol_snoc true F
        obtain ⟨x1, R1, hr1, hx1⟩ :=
          IHh (p.nodes n).1 (Q ++ [false]) P R (by omega) Fa (E.trans (ipeq_snoc_false Q).symm) hN
        rcases hx1 with rfl | ⟨m1, hm1, hm1', hn1⟩
        · exact ⟨.halt, R1, .carHalt n R R1 hr1, Or.inl rfl⟩
        have hp1 := run_pos hr1
        cases x1 with
        | halt => exact ⟨.halt, R1, .carHalt n R R1 hr1, Or.inl rfl⟩
        | cont k =>
            obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := hp1.2 k rfl; omega⟩
            exact ⟨.cont (k + 1), R1, .carCont n k R R1 hr1,
              Or.inr ⟨m1, hm1, hm1', by simpa only [target, cont_car] using hn1⟩⟩
        | brk k =>
            have := hp1.1 k rfl
            match k, hr1, hn1 with
            | 1, hr1, hn1 =>
                exact ⟨.normal, R1, .carBrk1 n R R1 hr1,
                  Or.inr ⟨m1, hm1, hm1', by simpa only [target, brk_car1] using hn1⟩⟩
            | k + 2, hr1, hn1 =>
                exact ⟨.brk (k + 1), R1, .carBrkS n k R R1 hr1,
                  Or.inr ⟨m1, hm1, hm1', by simpa only [target, brk_carS] using hn1⟩⟩
        | normal =>
            simp only [target, incPath_snoc_false] at hn1
            obtain ⟨x2, R2, hr2, hx2⟩ :=
              IHN (N - m1) (by omega) (p.nodes n).2 (Q ++ [true]) (Q ++ [true]) R1 Fb (ipeq.refl _) hn1
            rcases hx2 with rfl | ⟨m2, hm2, hm2', hn2⟩
            · exact ⟨.halt, R2, .cdrHalt n R R1 R2 hr1 hr2, Or.inl rfl⟩
            have hp2 := run_pos hr2
            rw [Nat.sub_sub] at hn2
            cases x2 with
            | halt => exact ⟨.halt, R2, .cdrHalt n R R1 R2 hr1 hr2, Or.inl rfl⟩
            | normal =>
                refine ⟨.normal, R2, .cdrNormal n R R1 R2 hr1 hr2, Or.inr ⟨m1 + m2, by omega, by omega, ?_⟩⟩
                simp only [target, incPath_snoc_true] at hn2 ⊢
                exact hn_ipeq (ipeq_snoc_false _) hn2
            | brk k =>
                obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := hp2.1 k rfl; omega⟩
                exact ⟨.brk (k + 1), R2, .cdrBrk n k R R1 R2 hr1 hr2,
                  Or.inr ⟨m1 + m2, by omega, by omega, by simpa only [target, brk_cdr] using hn2⟩⟩
            | cont k =>
                have := hp2.2 k rfl
                match k, hr2, hn2 with
                | 1, hr2, hn2 =>
                    -- `continue 1`: the cons cell restarts from `Q`.
                    simp only [target, cont_cdr1] at hn2
                    obtain ⟨x3, R3, hr3, hx3⟩ :=
                      IHN (N - (m1 + m2)) (by omega) (.node n) Q Q R2 F (ipeq.refl _) hn2
                    refine ⟨x3, R3, .cdrCont1 n R R1 R2 R3 x3 hr1 hr2 hr3, ?_⟩
                    rcases hx3 with rfl | ⟨m3, hm3, hm3', hn3⟩
                    · exact Or.inl rfl
                    · rw [Nat.sub_sub] at hn3
                      exact Or.inr ⟨m1 + m2 + m3, by omega, by omega, hn3⟩
                | k + 2, hr2, hn2 =>
                    exact ⟨.cont (k + 1), R2, .cdrContS n k R R1 R2 hr1 hr2,
                      Or.inr ⟨m1 + m2, by omega, by omega, by simpa only [target, cont_cdrS] using hn2⟩⟩
      all_goals exact bwd_leaf W F (fun _ h => by cases h) E hN

/-! ## The equivalence -/

/-- **Path halting is iterated structured halting.** For a well-formed DAG, the
path program started at the empty instruction pointer halts iff iterating the
root (as the overflowing instruction pointer does) reaches `halt`. -/
theorem halts_iff_iterHalts (W : WF p nn) (R : Regs) :
    Halts (ofDag p nn) ⟨[], R⟩ ↔ IterHalts p R := by
  constructor
  · rintro ⟨N, hN⟩
    induction N using Nat.strongRecOn generalizing R with
    | ind N IHN =>
      obtain ⟨x, R', hr, hx⟩ := bwd W N (.node p.root) [] [] R rfl (ipeq.refl _) hN
      rcases hx with rfl | ⟨m, hm, hm', hn'⟩
      · exact .halt R R' hr
      rcases wf_run W hr with rfl | rfl
      · exact .next R R' hr (IHN (N - m) (by omega) R' hn')
      · exact .halt R R' hr
  · intro h
    induction h with
    | halt R R' hr => exact fwd W hr [] [] rfl (ipeq.refl _)
    | next R R' hr _ ih =>
        obtain ⟨N1, P1, hr1, E1⟩ := fwd W hr [] [] rfl (ipeq.refl _)
        obtain ⟨N2, hN2⟩ := ih
        exact ⟨N1 + N2, hn_pre hr1 (hn_ipeq (E1 : ipeq P1 []).symm hN2)⟩

/-! ## A Boolean well-formedness check -/

def edgeOkb (nn : Nat) : Edge → Bool
  | .node n => decide (n < nn)
  | .brk k => decide (0 < k)
  | .cont k => decide (0 < k)
  | _ => true

def nodeOkb (p : Prog) (nn : Nat) (H B C : Nat → Nat) (n : Nat) : Bool :=
  edgeOkb nn (p.nodes n).1 && edgeOkb nn (p.nodes n).2 &&
  decide (hE H (p.nodes n).1 < H n) && decide (hE H (p.nodes n).2 < H n) &&
  decide (bE B (p.nodes n).1 ≤ B n + 1) && decide (bE B (p.nodes n).2 ≤ B n) &&
  decide (cE C (p.nodes n).1 ≤ C n) && decide (cE C (p.nodes n).2 ≤ C n + 1)

def wfCheck (p : Prog) (nn : Nat) (H B C : Nat → Nat) : Bool :=
  decide (p.root < nn) && decide (H p.root ≤ nn + 1) && decide (B p.root = 0) &&
  decide (C p.root = 0) && (List.range nn).all (nodeOkb p nn H B C)

theorem edgeOkb_ok {e : Edge} (h : edgeOkb nn e = true) : edgeOk nn e := by
  cases e <;> simp_all [edgeOkb, edgeOk]

theorem wfCheck_sound {H B C : Nat → Nat} (h : wfCheck p nn H B C = true) : WF p nn := by
  simp only [wfCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hr, hH⟩, hB⟩, hC⟩, hall⟩ := h
  have hn : ∀ n, n < nn → _ := fun n hn => hall n hn
  simp only [nodeOkb, Bool.and_eq_true, decide_eq_true_eq] at hn
  refine ⟨hr, ?_, ⟨H, hH, ?_⟩, ⟨B, C, hB, hC, ?_⟩⟩
  · intro n b hlt
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hn n hlt
    cases b <;> exact edgeOkb_ok ‹_›
  · intro n b hlt
    obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩, _⟩ := hn n hlt
    cases b <;> assumption
  · intro n hlt
    obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hn n hlt
    exact ⟨h5, h6, h7, h8⟩

end SetTheory.BusyBeaver.ZFC.RMEquiv
