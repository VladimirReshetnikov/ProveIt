import BusyBeaver.ZFC.RMBisim

/-!
Segment bisimulation with an integer offset on register 5.

`RMBisim` relates two path programs whose segments between register tests make
equal increments. Some source rewrites keep halting but not the exact register
file: the transfer-plus-one loop `((decnz 6, (inc 5, cont 2)), inc 5)` and its
rotation `(inc 5, (decnz 6, cont 2))` both send `(R5, R6) = (a, b)` to
`(a + b + 1, 0)`, but at intermediate tests their copies of register 5 differ by
one. Here a related pair of sites carries an offset `z : ℤ` with
`R₁ i = R₂ i + δ_z i`, where `δ_z 5 = z` and `δ_z i = 0` otherwise; a test may
only read a register whose offset is zero, and segment increments must account
for the change of offset.

This is the counterpart of `OffsetBisim230.v` in Source 123 of the ZFC
closure-kernels host (`K226_ZFC_Construction`, the K226F Rocq extension of Elliot
Glazer's k230-rocq), developed independently on top of `RMBisim`; as there, the
two directions are separate checks (`omirror` negates the offsets).
-/

namespace SetTheory.BusyBeaver.ZFC.RMOffsetBisim

open RegisterPath RMBisim
open RMEquiv (HN)

/-- The offset carried by register `i`. -/
def delta (z : Int) (i : Nat) : Int := if i = 5 then z else 0

/-- Register files related by offset `z`. -/
def Related (z : Int) (R1 R2 : Registers) : Prop := ∀ i, (R1 i : Int) = R2 i + delta z i

theorem related_zero (R : Registers) : Related 0 R R := fun i => by
  simp only [delta]; split <;> simp

theorem related_symm {z : Int} {R1 R2 : Registers} (h : Related z R1 R2) : Related (-z) R2 R1 :=
  fun i => by have := h i; simp only [delta] at this ⊢; split at this <;> simp_all <;> omega

/-- Both segments exist, their increments account for the change of offset, and they end at
related sites. -/
def OBranchGood (t1 t2 : Tree) (S : List Bool → List Bool → Int → Prop) (A B : List Bool)
    (z : Int) : Prop :=
  ∃ l1 P1 l2 P2 z', seg t1 segFuel A = some (l1, P1) ∧ seg t2 segFuel B = some (l2, P2) ∧
    (∀ i, delta z i + cnt l1 i = cnt l2 i + delta z' i) ∧ S P1 P2 z'

/-- Related sites: both halt, or both test the same register, carrying offset zero there,
with good branches. -/
def OEntryGood (t1 t2 : Tree) (S : List Bool → List Bool → Int → Prop) (P1 P2 : List Bool)
    (z : Int) : Prop :=
  (∃ Q1 Q2, tsite t1 P1 = some (.halt, Q1) ∧ tsite t2 P2 = some (.halt, Q2)) ∨
  (∃ r Q1 Q2, tsite t1 P1 = some (.decnz r, Q1) ∧ tsite t2 P2 = some (.decnz r, Q2) ∧
    delta z r = 0 ∧ OBranchGood t1 t2 S (incPath Q1) (incPath Q2) z ∧
    OBranchGood t1 t2 S (breakPath 1 Q1) (breakPath 1 Q2) z)

structure OBisim (t1 t2 : Tree) (S : List Bool → List Bool → Int → Prop) : Prop where
  start : OBranchGood t1 t2 S [] [] 0
  step : ∀ P1 P2 z, S P1 P2 z → OEntryGood t1 t2 S P1 P2 z

section Sound

variable {p1 p2 : Program} {S : List Bool → List Bool → Int → Prop}

theorem related_at {z : Int} {R1 R2 : Registers} {r : Nat} (h : Related z R1 R2)
    (hz : delta z r = 0) : R1 r = R2 r := by
  have := h r; rw [hz] at this; omega

theorem related_update {z : Int} {R1 R2 : Registers} {r v : Nat} (h : Related z R1 R2)
    (hz : delta z r = 0) : Related z (update R1 r v) (update R2 r v) := fun i => by
  simp only [update]
  by_cases hi : i = r
  · subst hi; simp [hz]
  · simp only [hi, if_false]; exact h i

theorem obranch_sim (N : Nat) {A B : List Bool} {z : Int} {R1 R2 : Registers}
    (IH : ∀ N', N' ≤ N → ∀ P1 P2 z' R1 R2, S P1 P2 z' → Related z' R1 R2 →
      HN p1 N' ⟨P1, R1⟩ → Halts p2 ⟨P2, R2⟩)
    (hb : OBranchGood (ptree p1) (ptree p2) S A B z) (hR : Related z R1 R2)
    (h : HN p1 N ⟨A, R1⟩) : Halts p2 ⟨B, R2⟩ := by
  obtain ⟨l1, P1, l2, P2, z', h1, h2, hc, hS⟩ := hb
  obtain ⟨N', R1', hle, h', hR1⟩ := seg_hn p1 _ _ _ _ _ _ h1 h
  obtain ⟨n, R2', hr, hR2⟩ := seg_run p2 _ _ _ _ R2 h2
  refine halts_pre hr (IH N' hle P1 P2 z' R1' R2' hS (fun i => ?_) h')
  have e1 := hR1 i; have e2 := hR2 i; have e3 := hR i; have e4 := hc i
  rw [e1, e2]; push_cast; omega

theorem osim (hB : ∀ P1 P2 z, S P1 P2 z → OEntryGood (ptree p1) (ptree p2) S P1 P2 z) :
    ∀ (N : Nat) (P1 P2 : List Bool) (z : Int) (R1 R2 : Registers), S P1 P2 z →
      Related z R1 R2 → HN p1 N ⟨P1, R1⟩ → Halts p2 ⟨P2, R2⟩ := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N IH =>
  intro P1 P2 z R1 R2 hS hR h
  rcases hB P1 P2 z hS with ⟨Q1, Q2, h1, h2⟩ | ⟨r, Q1, Q2, h1, h2, hz, hj, hk⟩
  · exact ⟨0, ⟨P2, R2⟩, rfl, (atHalt_tsite p2 P2 R2).2 ⟨Q2, h2⟩⟩
  · have hrr := related_at hR hz
    cases hv : R1 r with
    | zero =>
        have hv2 : R2 r = 0 := by rw [← hrr, hv]
        obtain ⟨N', rfl, h'⟩ := hn_step (c' := ⟨breakPath 1 Q1, R1⟩) h1 (by intro h; cases h)
          (by simp only [execute, hv]) h
        have hr : run p2 1 ⟨P2, R2⟩ = some ⟨breakPath 1 Q2, R2⟩ := by
          simp only [run, step_tsite, h2, execute, hv2]
        exact halts_pre hr (obranch_sim N' (fun N'' hle => IH N'' (by omega)) hk hR h')
    | succ v =>
        have hv2 : R2 r = v + 1 := by rw [← hrr, hv]
        obtain ⟨N', rfl, h'⟩ := hn_step (c' := ⟨incPath Q1, update R1 r v⟩) h1
          (by intro h; cases h) (by simp only [execute, hv]) h
        have hr : run p2 1 ⟨P2, R2⟩ = some ⟨incPath Q2, update R2 r v⟩ := by
          simp only [run, step_tsite, h2, execute, hv2]
        exact halts_pre hr (obranch_sim N' (fun N'' hle => IH N'' (by omega)) hj
          (related_update hR hz) h')

/-- **An offset segment bisimulation transfers halting** from the empty pointer. -/
theorem OBisim.halts (hB : OBisim (ptree p1) (ptree p2) S) (R : Registers) :
    Halts p1 ⟨[], R⟩ → Halts p2 ⟨[], R⟩ := by
  rintro ⟨N, c, hr, ha⟩
  exact obranch_sim N (fun N' _ => osim hB.step N') hB.start (related_zero R) ⟨c, hr, ha⟩

end Sound

/-! ## The certificate checker -/

/-- An entry: two coded test-site pointers, the offset, and the successor entries of the
nonzero and zero outcomes. -/
abbrev OEntry := Nat × Nat × Int × Nat × Nat

inductive OTree where
  | empty
  | leaf (x : OEntry)
  | branch (cut : Nat) (l r : OTree)

def lookupO : OTree → Nat → Option OEntry
  | .empty, _ => none
  | .leaf x, _ => some x
  | .branch cut l r, j => if j < cut then lookupO l j else lookupO r (j - cut)

def allO (f : OEntry → Bool) : OTree → Bool
  | .empty => true
  | .leaf x => f x
  | .branch _ l r => allO f l && allO f r

theorem lookupO_all {f : OEntry → Bool} : ∀ {T : OTree} {j : Nat} {x : OEntry},
    lookupO T j = some x → allO f T = true → f x = true
  | .empty, _, _, h, _ => by cases h
  | .leaf y, _, _, h, hall => by cases h; exact hall
  | .branch cut l r, j, x, h, hall => by
      simp only [allO, Bool.and_eq_true] at hall
      simp only [lookupO] at h
      split at h
      · exact lookupO_all h hall.1
      · exact lookupO_all h hall.2

/-- Pointer decoding with room for 511-bit paths (`RMBisim.decode` stops at 127 bits; the 221's
source tree is 180 deep along the AX chain). On shorter codes the two agree. -/
def odecode (n : Nat) : List Bool := decodeAux 512 n []

def ogetc (T : OTree) (j : Nat) : Option (List Bool × List Bool × Int) :=
  match lookupO T j with
  | some (a, b, z, _, _) => some (odecode a, odecode b, z)
  | none => none

def countsOk (z z' : Int) (l1 l2 : List Nat) : Bool :=
  (5 :: (l1 ++ l2)).all fun i => delta z i + cnt l1 i == cnt l2 i + delta z' i

theorem countsOk_ok {z z' : Int} {l1 l2 : List Nat} (h : countsOk z z' l1 l2 = true) (i : Nat) :
    delta z i + cnt l1 i = cnt l2 i + delta z' i := by
  simp only [countsOk, List.all_eq_true] at h
  by_cases hi : i ∈ 5 :: (l1 ++ l2)
  · exact beq_iff_eq.mp (h i hi)
  · simp only [List.mem_cons, List.mem_append, not_or] at hi
    obtain ⟨h5, h1, h2⟩ := hi
    rw [cnt_zero h1, cnt_zero h2]; simp [delta, h5]

def obranchOk (t1 t2 : Tree) (T : OTree) (A B : List Bool) (z : Int) (j : Nat) : Bool :=
  match seg t1 segFuel A, seg t2 segFuel B, ogetc T j with
  | some (l1, P1), some (l2, P2), some (Q1, Q2, z') =>
      countsOk z z' l1 l2 && lbeq P1 Q1 && lbeq P2 Q2
  | _, _, _ => false

def oentryOk (t1 t2 : Tree) (T : OTree) (x : OEntry) : Bool :=
  match tsite t1 (odecode x.1), tsite t2 (odecode x.2.1) with
  | some (.halt, _), some (.halt, _) => true
  | some (.decnz r1, Q1), some (.decnz r2, Q2) =>
      Nat.beq r1 r2 && delta x.2.2.1 r1 == 0 &&
        obranchOk t1 t2 T (incPath Q1) (incPath Q2) x.2.2.1 x.2.2.2.1 &&
        obranchOk t1 t2 T (breakPath 1 Q1) (breakPath 1 Q2) x.2.2.1 x.2.2.2.2
  | _, _ => false

/-- The relation a certificate tree denotes: the triples its lookup returns. -/
def ORel (T : OTree) (P1 P2 : List Bool) (z : Int) : Prop := ∃ j, ogetc T j = some (P1, P2, z)

theorem obranchOk_good {t1 t2 : Tree} {T : OTree} {A B : List Bool} {z : Int} {j : Nat}
    (h : obranchOk t1 t2 T A B z j = true) : OBranchGood t1 t2 (ORel T) A B z := by
  unfold obranchOk at h
  revert h
  cases h1 : seg t1 segFuel A with
  | none => intro h; cases h
  | some lP1 =>
  cases h2 : seg t2 segFuel B with
  | none => intro h; cases h
  | some lP2 =>
  cases h3 : ogetc T j with
  | none => intro h; cases h
  | some Q =>
  intro h
  obtain ⟨l1, P1⟩ := lP1
  obtain ⟨l2, P2⟩ := lP2
  obtain ⟨Q1, Q2, z'⟩ := Q
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, e1⟩, e2⟩ := h
  rw [← lbeq_ok e1, ← lbeq_ok e2] at h3
  exact ⟨l1, P1, l2, P2, z', h1, h2, countsOk_ok hc, j, h3⟩

theorem oentryOk_good {t1 t2 : Tree} {T : OTree} {x : OEntry} (h : oentryOk t1 t2 T x = true) :
    OEntryGood t1 t2 (ORel T) (odecode x.1) (odecode x.2.1) x.2.2.1 := by
  unfold oentryOk at h
  revert h
  cases h1 : tsite t1 (odecode x.1) with
  | none => intro h; cases h
  | some eQ1 =>
  cases h2 : tsite t2 (odecode x.2.1) with
  | none => obtain ⟨e1, _⟩ := eQ1; cases e1 <;> intro h <;> cases h
  | some eQ2 =>
  obtain ⟨e1, Q1⟩ := eQ1
  obtain ⟨e2, Q2⟩ := eQ2
  cases e1 <;> cases e2 <;> intro h
  all_goals first | (simp only [Bool.false_eq_true] at h; done) | skip
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hr, hz⟩, hj⟩, hk⟩ := h
    rw [Nat.eq_of_beq_eq_true hr] at h1
    rw [Nat.eq_of_beq_eq_true hr] at hz
    exact Or.inr ⟨_, Q1, Q2, h1, h2, hz, obranchOk_good hj, obranchOk_good hk⟩
  · exact Or.inl ⟨Q1, Q2, h1, h2⟩

theorem ocheck_bisim {t1 t2 : Tree} {T : OTree} (hs : obranchOk t1 t2 T [] [] 0 0 = true)
    (ha : allO (oentryOk t1 t2 T) T = true) : OBisim t1 t2 (ORel T) := by
  refine ⟨obranchOk_good hs, fun P1 P2 z ⟨j, hj⟩ => ?_⟩
  unfold ogetc at hj
  revert hj
  cases hl : lookupO T j with
  | none => intro hj; cases hj
  | some x =>
      intro hj
      obtain ⟨a, b, c, d, e⟩ := x
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      exact oentryOk_good (x := (a, b, c, d, e)) (lookupO_all hl ha)

/-- **A checked certificate transfers halting** from the empty pointer, in one direction. -/
theorem ocheck_halts {p1 p2 : Program} {T : OTree}
    (hs : obranchOk (ptree p1) (ptree p2) T [] [] 0 0 = true)
    (ha : allO (oentryOk (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ → Halts p2 ⟨[], R⟩ :=
  (ocheck_bisim hs ha).halts R

end SetTheory.BusyBeaver.ZFC.RMOffsetBisim
