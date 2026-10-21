import BusyBeaver.ZFC.RMBisim

/-!
Source-certificate compression modulo the implicit trailing zeros of Wade paths.
This module changes only the certificate relation and checker. It reuses the
existing segment-bisimulation soundness theorem and the exact path semantics.
Long pointers use 512 decoding steps, as in RMOffsetBisim. No offset is needed
for the pinned K215 source certificate: all its offsets are zero.
-/

namespace SetTheory.BusyBeaver.ZFC.RMNormalizedBisim

open RegisterPath RMBisim
open RMEquiv (ipeq)

def zeros : List Bool → Bool
  | [] => true
  | b :: P => (!b) && zeros P

theorem zeros_ok : ∀ {P : List Bool}, zeros P = true → ipeq P []
  | [], _ => ipeq.refl _
  | b :: P, h => by
      cases b with
      | false =>
        have hP : zeros P = true := by simpa [zeros] using h
        intro i
        cases i with
        | zero => simp [RegisterPath.bit]
        | succ i => simpa only [RMEquiv.bit_cons_succ, RMEquiv.bit_nil] using zeros_ok hP i
      | true => simp [zeros] at h

/-- Equality of implicit infinite zero extensions, checked on finite paths. -/
def ibeq : List Bool → List Bool → Bool
  | [], Q => zeros Q
  | P, [] => zeros P
  | b :: P, c :: Q => (b == c) && ibeq P Q

theorem ibeq_ok : ∀ {P Q : List Bool}, ibeq P Q = true → ipeq P Q
  | [], Q, h => (zeros_ok h).symm
  | b :: P, [], h => zeros_ok h
  | b :: P, c :: Q, h => by
      simp only [ibeq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, hPQ⟩ := h
      intro i
      cases i with
      | zero => rfl
      | succ i => exact ibeq_ok hPQ i

/-- The actual leaf observation is insensitive to implicit trailing zeros. -/
theorem tsite_ipeq (p : Program) {P Q : List Bool} (h : ipeq P Q) :
    tsite (ptree p) P = tsite (ptree p) Q := by
  unfold tsite
  rw [← walk_root p P, ← walk_root p Q, RMEquiv.walk_ipeq p h]
  cases walk p (p.nnodes + 1) p.root Q 0 with
  | none => rfl
  | some ed =>
      obtain ⟨e, d⟩ := ed
      simp only [RMEquiv.consume_eq, RMEquiv.pre_ipeq d h]

def decodeLong (n : Nat) : List Bool := decodeAux 512 n []

def getc (T : CTree) (j : Nat) : Option (List Bool × List Bool) :=
  match lookupC T j with
  | some (a, b, _, _) => some (decodeLong a, decodeLong b)
  | none => none

/-- Saturation is the sole semantic change: entries denote equivalence classes
of finite paths with the same implicit zero-extended bits. -/
def Rel (T : CTree) (P Q : List Bool) : Prop :=
  ∃ j A B, getc T j = some (A, B) ∧ ipeq P A ∧ ipeq Q B

def branchOk (t1 t2 : Tree) (T : CTree) (A B : List Bool) (j : Nat) : Bool :=
  match seg t1 segFuel A, seg t2 segFuel B, getc T j with
  | some (l1, P1), some (l2, P2), some (Q1, Q2) =>
      cntEq l1 l2 && ibeq P1 Q1 && ibeq P2 Q2
  | _, _, _ => false

def entryOk (t1 t2 : Tree) (T : CTree) (x : Entry) : Bool :=
  match tsite t1 (decodeLong x.1), tsite t2 (decodeLong x.2.1) with
  | some (.halt, _), some (.halt, _) => true
  | some (.decnz r1, Q1), some (.decnz r2, Q2) =>
      Nat.beq r1 r2 && branchOk t1 t2 T (incPath Q1) (incPath Q2) x.2.2.1 &&
        branchOk t1 t2 T (breakPath 1 Q1) (breakPath 1 Q2) x.2.2.2
  | _, _ => false

theorem branchOk_good {t1 t2 : Tree} {T : CTree} {A B : List Bool} {j : Nat}
    (h : branchOk t1 t2 T A B j = true) : BranchGood t1 t2 (Rel T) A B := by
  unfold branchOk at h
  revert h
  cases h1 : seg t1 segFuel A with
  | none => intro h; cases h
  | some lP1 =>
  cases h2 : seg t2 segFuel B with
  | none => intro h; cases h
  | some lP2 =>
  cases h3 : getc T j with
  | none => intro h; cases h
  | some Q =>
  intro h
  obtain ⟨l1, P1⟩ := lP1
  obtain ⟨l2, P2⟩ := lP2
  obtain ⟨Q1, Q2⟩ := Q
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, e1⟩, e2⟩ := h
  exact ⟨l1, P1, l2, P2, h1, h2, cntEq_ok hc, j, Q1, Q2, h3,
    ibeq_ok e1, ibeq_ok e2⟩

theorem entryOk_good {t1 t2 : Tree} {T : CTree} {x : Entry}
    (h : entryOk t1 t2 T x = true) :
    EntryGood t1 t2 (Rel T) (decodeLong x.1) (decodeLong x.2.1) := by
  unfold entryOk at h
  revert h
  cases h1 : tsite t1 (decodeLong x.1) with
  | none => intro h; cases h
  | some eQ1 =>
  cases h2 : tsite t2 (decodeLong x.2.1) with
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

theorem check_bisim {p1 p2 : Program} {T : CTree}
    (hs : branchOk (ptree p1) (ptree p2) T [] [] 0 = true)
    (ha : allC (entryOk (ptree p1) (ptree p2) T) T = true) :
    Bisim (ptree p1) (ptree p2) (Rel T) := by
  refine ⟨branchOk_good hs, fun P Q ⟨j, A, B, hj, hPA, hQB⟩ => ?_⟩
  have he : EntryGood (ptree p1) (ptree p2) (Rel T) A B := by
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
  unfold EntryGood at he ⊢
  rw [tsite_ipeq p1 hPA, tsite_ipeq p2 hQB]
  exact he

/-- A compressed, checked certificate proves the identical all-register
halting equivalence as the original literal-path certificate. -/
theorem check_halts_iff {p1 p2 : Program} {T : CTree}
    (hs : branchOk (ptree p1) (ptree p2) T [] [] 0 = true)
    (ha : allC (entryOk (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  (check_bisim hs ha).halts_iff R

#print axioms ibeq_ok
#print axioms tsite_ipeq
#print axioms check_halts_iff

end SetTheory.BusyBeaver.ZFC.RMNormalizedBisim
