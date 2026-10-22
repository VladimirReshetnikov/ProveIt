import BusyBeaver.ZFC.RMBisim

/-!
Source-certificate compression modulo the implicit trailing zeros of Wade paths.
This module changes only the certificate relation and checker. It reuses the
existing segment-bisimulation soundness theorem and the exact path semantics.
The generic checker accepts any decoder, reusing RMBisim.WithDecoder.getc.
Its soundness needs no numerical bound or injectivity assumption. K215 supplies an
explicit 512-step decoder at its use site; RMBisim.decode stays at 128.

Adapted from Source168 / batch205A RMNormalizedBisim.lean, preserved with its
NOTICE. The normalized relation and proof originate in that contribution.
This adaptation only factors the decoder and reuses the maintained lookup.
Consumed paths remain intact before incPath and breakPath are applied.
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

/-! The decoder changes only which finite paths an entry denotes. -/
namespace WithDecoder

variable (decode : Nat → List Bool)

abbrev getc := RMBisim.WithDecoder.getc decode

/-- Saturation is the sole semantic change: entries denote equivalence classes
of finite paths with the same implicit zero-extended bits. -/
def Rel (T : CTree) (P Q : List Bool) : Prop :=
  ∃ j A B, getc decode T j = some (A, B) ∧ ipeq P A ∧ ipeq Q B

def branchOk (t1 t2 : Tree) (T : CTree) (A B : List Bool) (j : Nat) : Bool :=
  match seg t1 segFuel A, seg t2 segFuel B, getc decode T j with
  | some (l1, P1), some (l2, P2), some (Q1, Q2) =>
      cntEq l1 l2 && ibeq P1 Q1 && ibeq P2 Q2
  | _, _, _ => false

def entryOk (t1 t2 : Tree) (T : CTree) (x : Entry) : Bool :=
  match tsite t1 (decode x.1), tsite t2 (decode x.2.1) with
  | some (.halt, _), some (.halt, _) => true
  | some (.decnz r1, Q1), some (.decnz r2, Q2) =>
      Nat.beq r1 r2 && branchOk decode t1 t2 T (incPath Q1) (incPath Q2) x.2.2.1 &&
        branchOk decode t1 t2 T (breakPath 1 Q1) (breakPath 1 Q2) x.2.2.2
  | _, _ => false

theorem branchOk_good {t1 t2 : Tree} {T : CTree} {A B : List Bool} {j : Nat}
    (h : branchOk decode t1 t2 T A B j = true) : BranchGood t1 t2 (Rel decode T) A B := by
  unfold branchOk at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hc, e1⟩, e2⟩ := h
    exact ⟨_, _, _, _, ‹_›, ‹_›, cntEq_ok hc, j, _, _, ‹_›, ibeq_ok e1, ibeq_ok e2⟩
  · cases h

theorem entryOk_good {t1 t2 : Tree} {T : CTree} {x : Entry}
    (h : entryOk decode t1 t2 T x = true) :
    EntryGood t1 t2 (Rel decode T) (decode x.1) (decode x.2.1) := by
  unfold entryOk at h
  split at h
  · exact Or.inl ⟨_, _, ‹_›, ‹_›⟩
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hr, hj⟩, hk⟩ := h
    obtain rfl := Nat.eq_of_beq_eq_true hr
    exact Or.inr ⟨_, _, _, ‹_›, ‹_›, branchOk_good decode hj, branchOk_good decode hk⟩
  · cases h

theorem check_bisim {p1 p2 : Program} {T : CTree}
    (hs : branchOk decode (ptree p1) (ptree p2) T [] [] 0 = true)
    (ha : allC (entryOk decode (ptree p1) (ptree p2) T) T = true) :
    Bisim (ptree p1) (ptree p2) (Rel decode T) := by
  refine ⟨branchOk_good decode hs, fun P Q ⟨j, A, B, hj, hPA, hQB⟩ => ?_⟩
  have he : EntryGood (ptree p1) (ptree p2) (Rel decode T) A B := by
    unfold getc RMBisim.WithDecoder.getc at hj
    revert hj
    cases hl : lookupC T j with
    | none => intro hj; cases hj
    | some x =>
        intro hj
        obtain ⟨a, b, c, d⟩ := x
        simp only [Option.some.injEq, Prod.mk.injEq] at hj
        obtain ⟨rfl, rfl⟩ := hj
        exact entryOk_good decode (x := (a, b, c, d)) (lookupC_all hl ha)
  unfold EntryGood at he ⊢
  rwa [tsite_ipeq p1 hPA, tsite_ipeq p2 hQB]

/-- A compressed, checked certificate proves the identical all-register
halting equivalence as the original literal-path certificate. -/
theorem check_halts_iff {p1 p2 : Program} {T : CTree}
    (hs : branchOk decode (ptree p1) (ptree p2) T [] [] 0 = true)
    (ha : allC (entryOk decode (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  (check_bisim decode hs ha).halts_iff R

end WithDecoder

end SetTheory.BusyBeaver.ZFC.RMNormalizedBisim
