import BusyBeaver.ZFC.RMOffsetBisim

/-!
SUPERSEDED ALTERNATIVE ONLY. This file has not been compiled.
Latest main e0b8f9cb already provides the more general signed OBisim symmetry,
so this draft is retained only as an explanatory historical prototype.
It leaves the offset certificate checker and its 512-bit decoder unchanged,
and projects its zero-offset semantic result to the existing symmetric Bisim.
-/

namespace SetTheory.BusyBeaver.ZFC.RMOffsetBisim

open RegisterPath RMBisim

theorem OBranchGood.toBranchGood
    {t1 t2 : Tree} {S : List Bool → List Bool → Int → Prop}
    (hz : ∀ P Q z, S P Q z → z = 0) {A B : List Bool}
    (h : OBranchGood t1 t2 S A B 0) :
    BranchGood t1 t2 (fun P Q => S P Q 0) A B := by
  obtain ⟨l1, P1, l2, P2, z, h1, h2, hc, hS⟩ := h
  have he : z = 0 := hz P1 P2 z hS
  subst z
  refine ⟨l1, P1, l2, P2, h1, h2, ?_, hS⟩
  intro i
  have hi := hc i
  simp only [delta] at hi
  split at hi <;> omega

theorem OBisim.toBisim
    {t1 t2 : Tree} {S : List Bool → List Bool → Int → Prop}
    (h : OBisim t1 t2 S) (hz : ∀ P Q z, S P Q z → z = 0) :
    Bisim t1 t2 (fun P Q => S P Q 0) := by
  refine ⟨OBranchGood.toBranchGood hz h.start, ?_⟩
  intro P Q hS
  rcases h.step P Q 0 hS with hhalt | ⟨r, Q1, Q2, h1, h2, _, hj, hk⟩
  · exact Or.inl hhalt
  · exact Or.inr ⟨r, Q1, Q2, h1, h2,
      OBranchGood.toBranchGood hz hj, OBranchGood.toBranchGood hz hk⟩

def zeroOffsets (T : OTree) : Bool := allO (fun x => decide (x.2.2.1 = 0)) T

theorem ORel.zero_of_checked {T : OTree} (hz : zeroOffsets T = true)
    {P Q : List Bool} {z : Int} (h : ORel T P Q z) : z = 0 := by
  obtain ⟨j, hj⟩ := h
  unfold ogetc at hj
  cases he : lookupO T j with
  | none => simp only [he] at hj; cases hj
  | some x =>
      have hx0 : x.2.2.1 = 0 := of_decide_eq_true (lookupO_all he hz)
      simp only [he, Option.some.injEq, Prod.mk.injEq] at hj
      exact hj.2.2.symm.trans hx0

theorem ocheck_zero_halts_iff {p1 p2 : Program} {T : OTree}
    (hs : obranchOk (ptree p1) (ptree p2) T [] [] 0 0 = true)
    (ha : allO (oentryOk (ptree p1) (ptree p2) T) T = true)
    (hz : zeroOffsets T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  (OBisim.toBisim (ocheck_bisim hs ha)
    (fun _ _ _ h => ORel.zero_of_checked hz h)).halts_iff R

end SetTheory.BusyBeaver.ZFC.RMOffsetBisim
