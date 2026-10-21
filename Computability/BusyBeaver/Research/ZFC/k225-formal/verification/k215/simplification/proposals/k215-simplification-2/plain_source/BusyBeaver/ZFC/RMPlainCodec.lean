import BusyBeaver.ZFC.RMBisim

/-!
Ordinary (equal-register) segment certificates with a decoder parameter.
The semantic theorem is the existing RMBisim.Bisim.halts_iff. Only the small
Boolean checker interface is factored over the path decoder. In particular no
integer-offset relation is introduced.

`totalDecode n` uses the existing structurally recursive decoder with input-
dependent fuel n, rather than a fixed 128/512-bit cap. For positive n every
nonterminal quotient n / 2 is strictly smaller, so n steps suffice. The checker
soundness theorem is valid for EVERY decoder, independently of any codec law.
-/
namespace SetTheory.BusyBeaver.ZFC.RMPlainCodec

open RegisterPath RMBisim

/-- Total, structurally recursive path decoding without a fixed bit limit. -/
def totalDecode (n : Nat) : List Bool := decodeAux n n []

def getc (decodePath : Nat → List Bool) (T : CTree) (j : Nat) : Option (List Bool × List Bool) :=
  match lookupC T j with
  | some (a, b, _, _) => some (decodePath a, decodePath b)
  | none => none

def branchOk (decodePath : Nat → List Bool) (t1 t2 : Tree) (T : CTree)
    (A B : List Bool) (j : Nat) : Bool :=
  match seg t1 segFuel A, seg t2 segFuel B, getc decodePath T j with
  | some (l1, P1), some (l2, P2), some (Q1, Q2) => cntEq l1 l2 && lbeq P1 Q1 && lbeq P2 Q2
  | _, _, _ => false

def entryOk (decodePath : Nat → List Bool) (t1 t2 : Tree) (T : CTree) (x : Entry) : Bool :=
  match tsite t1 (decodePath x.1), tsite t2 (decodePath x.2.1) with
  | some (.halt, _), some (.halt, _) => true
  | some (.decnz r1, Q1), some (.decnz r2, Q2) =>
      Nat.beq r1 r2 && branchOk decodePath t1 t2 T (incPath Q1) (incPath Q2) x.2.2.1 &&
        branchOk decodePath t1 t2 T (breakPath 1 Q1) (breakPath 1 Q2) x.2.2.2
  | _, _ => false

def Rel (decodePath : Nat → List Bool) (T : CTree) (P1 P2 : List Bool) : Prop :=
  ∃ j, getc decodePath T j = some (P1, P2)

theorem branchOk_good {decodePath : Nat → List Bool} {t1 t2 : Tree} {T : CTree}
    {A B : List Bool} {j : Nat}
    (h : branchOk decodePath t1 t2 T A B j = true) :
    BranchGood t1 t2 (Rel decodePath T) A B := by
  unfold branchOk at h
  revert h
  cases h1 : seg t1 segFuel A with
  | none => intro h; cases h
  | some lP1 =>
  cases h2 : seg t2 segFuel B with
  | none => intro h; cases h
  | some lP2 =>
  cases h3 : getc decodePath T j with
  | none => intro h; cases h
  | some Q =>
  intro h
  obtain ⟨l1, P1⟩ := lP1
  obtain ⟨l2, P2⟩ := lP2
  obtain ⟨Q1, Q2⟩ := Q
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, e1⟩, e2⟩ := h
  rw [← lbeq_ok e1, ← lbeq_ok e2] at h3
  exact ⟨l1, P1, l2, P2, h1, h2, cntEq_ok hc, j, h3⟩

theorem entryOk_good {decodePath : Nat → List Bool} {t1 t2 : Tree} {T : CTree} {x : Entry}
    (h : entryOk decodePath t1 t2 T x = true) :
    EntryGood t1 t2 (Rel decodePath T) (decodePath x.1) (decodePath x.2.1) := by
  unfold entryOk at h
  revert h
  cases h1 : tsite t1 (decodePath x.1) with
  | none => intro h; cases h
  | some eQ1 =>
  cases h2 : tsite t2 (decodePath x.2.1) with
  | none => obtain ⟨e1, _⟩ := eQ1; cases e1 <;> intro h <;> cases h
  | some eQ2 =>
  obtain ⟨e1, Q1⟩ := eQ1
  obtain ⟨e2, Q2⟩ := eQ2
  cases e1 <;> cases e2 <;> intro h
  all_goals first | (simp only [Bool.false_eq_true] at h; done) | skip
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hr, hj⟩, hk⟩ := h
    rw [Nat.eq_of_beq_eq_true hr] at h1
    exact Or.inr ⟨_, Q1, Q2, h1, h2, branchOk_good hj, branchOk_good hk⟩
  · exact Or.inl ⟨Q1, Q2, h1, h2⟩

theorem check_bisim {decodePath : Nat → List Bool} {t1 t2 : Tree} {T : CTree}
    (hs : branchOk decodePath t1 t2 T [] [] 0 = true)
    (ha : allC (entryOk decodePath t1 t2 T) T = true) :
    Bisim t1 t2 (Rel decodePath T) := by
  refine ⟨branchOk_good hs, fun P1 P2 ⟨j, hj⟩ => ?_⟩
  unfold getc at hj
  revert hj
  cases hl : lookupC T j with
  | none => intro hj; cases hj
  | some x =>
      intro hj
      obtain ⟨a, b, c, d⟩ := x
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      exact entryOk_good (x := (a, b, c, d)) (lookupC_all hl ha)

/-- One ordinary certificate establishes both directions, for every register file. -/
theorem check_halts_iff {decodePath : Nat → List Bool} {p1 p2 : Program} {T : CTree}
    (hs : branchOk decodePath (ptree p1) (ptree p2) T [] [] 0 = true)
    (ha : allC (entryOk decodePath (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  (check_bisim hs ha).halts_iff R

#print axioms check_halts_iff

end SetTheory.BusyBeaver.ZFC.RMPlainCodec
