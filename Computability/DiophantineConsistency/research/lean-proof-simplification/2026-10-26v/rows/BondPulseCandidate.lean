import DiophantineConsistency.WangTiles942StepConstruction

/-!
UNCOMPILED proposal for ProveIt 22e020937caa81d0cb72a4f63071d6c0bcc1eba9.
The original stepTile/transitionRow/receiveTile definitions are not changed.
The rail is indexed by the LEFT endpoint of the unique moved-head bond.
Right movement: bond starts at old head. Left movement: bond starts at new head.
This is not a premise asserting horizontal compatibility: the paired result
is derived by reducing those three existing tile constructors.
-/

namespace DiophantineConsistency.WangRowsRound3

open SetTheory.BusyBeaver WangTiles942 WangTiles942StepConstruction

def bondSignal (cfg : Config 215) (q : Fin 215) (x : ℤ) : ℕ :=
  let a := WangTiles942.action (sourceIndex cfg q)
  if x = (if a.2.1 then cfg.head else nextHead cfg q)
    then rail a.2.1 a.2.2 else 0

theorem stepTile_edges_candidate (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q x).west = bondSignal cfg q (x-1) ∧
      (stepTile cfg q x).east = bondSignal cfg q x := by
  have hm := nextHead_eq cfg q
  have hshift :
      (x-1 = (if (WangTiles942.action (sourceIndex cfg q)).2.1
        then cfg.head else nextHead cfg q)) ↔
      (x = (if (WangTiles942.action (sourceIndex cfg q)).2.1
        then nextHead cfg q else cfg.head)) := by
    cases hd : (WangTiles942.action (sourceIndex cfg q)).2.1 <;>
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hm ⊢ <;> omega
  simp only [bondSignal, hshift]
  have hne := nextHead_ne cfg q
  by_cases ho : x = cfg.head <;> by_cases hn : x = nextHead cfg q <;>
    cases hd : (WangTiles942.action (sourceIndex cfg q)).2.1 <;>
    simp_all [stepTile, transitionRow, receiveTile]

theorem stepTile_west_pulse (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q x).west = bondSignal cfg q (x-1) :=
  (stepTile_edges_candidate cfg q x).1

theorem stepTile_east_pulse (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q x).east = bondSignal cfg q x :=
  (stepTile_edges_candidate cfg q x).2

theorem stepTile_horizontal_candidate (cfg : Config 215) (q : Fin 215) (x : ℤ) :
    (stepTile cfg q (x+1)).west = (stepTile cfg q x).east := by
  simp only [stepTile_west_pulse, stepTile_east_pulse, add_sub_cancel_right]

end DiophantineConsistency.WangRowsRound3

#print axioms DiophantineConsistency.WangRowsRound3.stepTile_edges_candidate
#print axioms DiophantineConsistency.WangRowsRound3.stepTile_west_pulse
#print axioms DiophantineConsistency.WangRowsRound3.stepTile_east_pulse
#print axioms DiophantineConsistency.WangRowsRound3.stepTile_horizontal_candidate
