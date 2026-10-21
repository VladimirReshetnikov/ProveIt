import BusyBeaver.ZFC.RMOffsetBisim

/-! Proposed kernel proof, NOT compiled in the research environment.
No new axioms, admitted facts, native_decide, or changed endpoint statements.
Compile against the pinned project before integration.
-/
namespace SetTheory.BusyBeaver.ZFC.RMOffsetBisim

open RegisterPath

def Reverse (S : List Bool → List Bool → Int → Prop)
    (B A : List Bool) (z : Int) : Prop := S A B (-z)

theorem delta_neg (z : Int) (i : Nat) : delta (-z) i = -(delta z i) := by
  unfold delta
  split <;> simp

theorem OBranchGood.reverse {t1 t2 : Tree}
    {S : List Bool → List Bool → Int → Prop} {A B : List Bool} {z : Int}
    (h : OBranchGood t1 t2 S A B z) :
    OBranchGood t2 t1 (Reverse S) B A (-z) := by
  obtain ⟨l1, P1, l2, P2, z', h1, h2, hc, hS⟩ := h
  refine ⟨l2, P2, l1, P1, -z', h2, h1, ?_, ?_⟩
  · intro i
    have hi := hc i
    simp only [delta_neg]
    omega
  · simpa only [Reverse, neg_neg] using hS

theorem OEntryGood.reverse {t1 t2 : Tree}
    {S : List Bool → List Bool → Int → Prop} {A B : List Bool} {z : Int}
    (h : OEntryGood t1 t2 S A B z) :
    OEntryGood t2 t1 (Reverse S) B A (-z) := by
  rcases h with ⟨Q1, Q2, h1, h2⟩ | ⟨r, Q1, Q2, h1, h2, hz, hj, hk⟩
  · exact Or.inl ⟨Q2, Q1, h2, h1⟩
  · refine Or.inr ⟨r, Q2, Q1, h2, h1, ?_, hj.reverse, hk.reverse⟩
    simp only [delta_neg, hz, neg_zero]

theorem OBisim.reverse {t1 t2 : Tree}
    {S : List Bool → List Bool → Int → Prop} (h : OBisim t1 t2 S) :
    OBisim t2 t1 (Reverse S) := by
  constructor
  · simpa only [neg_zero] using h.start.reverse
  · intro B A z hS
    have he := (h.step A B (-z) hS).reverse
    simpa only [neg_neg] using he

theorem OBisim.halts_iff {p1 p2 : Program}
    {S : List Bool → List Bool → Int → Prop}
    (h : OBisim (ptree p1) (ptree p2) S) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  ⟨h.halts R, h.reverse.halts R⟩

theorem ocheck_halts_iff {p1 p2 : Program} {T : OTree}
    (hs : obranchOk (ptree p1) (ptree p2) T [] [] 0 0 = true)
    (ha : allO (oentryOk (ptree p1) (ptree p2) T) T = true) (R : Registers) :
    Halts p1 ⟨[], R⟩ ↔ Halts p2 ⟨[], R⟩ :=
  (ocheck_bisim hs ha).halts_iff R

#print axioms ocheck_halts_iff
end SetTheory.BusyBeaver.ZFC.RMOffsetBisim
