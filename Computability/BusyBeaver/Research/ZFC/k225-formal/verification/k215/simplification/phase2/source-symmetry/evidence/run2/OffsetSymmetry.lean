import BusyBeaver.ZFC.RMOffsetBisim

namespace SetTheory.BusyBeaver.ZFC.RMOffsetBisim

open RegisterPath RMBisim

@[simp] theorem delta_neg (z : Int) (i : Nat) : delta (-z) i = -delta z i := by
  unfold delta
  split <;> simp

/-- Reverse both program sites and the register offset. -/
theorem OBranchGood.symm {t1 t2 : Tree} {S : List Bool → List Bool → Int → Prop}
    {A B : List Bool} {z : Int} (h : OBranchGood t1 t2 S A B z) :
    OBranchGood t2 t1 (fun P2 P1 z => S P1 P2 (-z)) B A (-z) := by
  obtain ⟨l1, P1, l2, P2, z', h1, h2, hc, hS⟩ := h
  refine ⟨l2, P2, l1, P1, -z', h2, h1, fun i => ?_, ?_⟩
  · have := hc i
    simp only [delta_neg]
    omega
  · simpa only [Int.neg_neg] using hS

/-- Offset segment bisimulation is symmetric; one certificate proves both directions. -/
theorem OBisim.symm {t1 t2 : Tree} {S : List Bool → List Bool → Int → Prop}
    (h : OBisim t1 t2 S) : OBisim t2 t1 (fun P2 P1 z => S P1 P2 (-z)) := by
  refine ⟨?_, ?_⟩
  · simpa using h.start.symm
  · intro P2 P1 z hS
    rcases h.step P1 P2 (-z) hS with ⟨Q1, Q2, h1, h2⟩ | ⟨r, Q1, Q2, h1, h2, hz, hj, hk⟩
    · exact Or.inl ⟨Q2, Q1, h2, h1⟩
    · refine Or.inr ⟨r, Q2, Q1, h2, h1, ?_, ?_, ?_⟩
      · simp only [delta_neg] at hz
        omega
      · simpa only [Int.neg_neg] using hj.symm
      · simpa only [Int.neg_neg] using hk.symm

/-- A single checked offset certificate gives halting equivalence for every register file. -/
theorem ocheck_halts_iff {p1 p2 : Program} {T : OTree}
    (hs : obranchOk (ptree p1) (ptree p2) T [] [] 0 0 = true)
    (ha : allO (oentryOk (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  ⟨(ocheck_bisim hs ha).halts R, (ocheck_bisim hs ha).symm.halts R⟩

#print axioms OBisim.symm
#print axioms ocheck_halts_iff

end SetTheory.BusyBeaver.ZFC.RMOffsetBisim
