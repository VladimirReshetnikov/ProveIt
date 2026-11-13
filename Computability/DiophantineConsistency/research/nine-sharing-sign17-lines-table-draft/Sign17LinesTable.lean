import DiophantineConsistency.Sign17LinesTargetOrder

/-! SOURCE ONLY. The ordered tile table reconstructed from the in-Lean seed lines. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17LinesTable

open Sign17LinesDecoder Sign17LinesRails Sign17LinesTargetOrder

def lineRail (d : Bool) (q : ℕ) : ℕ :=
  205 - 199 * d.toNat + (WangTiles942.targetsFrom d lineActions ∩ Finset.range q).card

def lineTransition (j : Fin 430) : ℕ × WangTiles942.Tile :=
  let a := Sign17ParamDecoder.actionAt displayedSeed j.val
  let d := a.2.1.toNat
  (j.val + 1, ⟨(1-d) * lineRail false a.2.2,
    WangTiles942.headColor (j.val / 2) (j.val % 2),
    d * lineRail true a.2.2, a.1.toNat⟩)

theorem lineTransition_eq (j : Fin 430) : lineTransition j = WangTiles942.transitionRow j := by
  exact (transition_row_from_lines_and_rails j).symm

def lineSignalRows (d : Bool) : List (ℕ × WangTiles942.Tile) :=
  (lineTargetList d).flatMap (fun q => (List.range 2).map (fun b =>
    (423 + 2 * lineRail d q + b,
      ⟨d.toNat * lineRail d q, b, (1-d.toNat) * lineRail d q,
        WangTiles942.headColor q b⟩)))

theorem lineSignalRows_eq (d : Bool) : lineSignalRows d = WangTiles942.signalRows d := by
  simp only [lineSignalRows, lineRail, ← rail_from_lines, ← targetList_from_lines,
    WangTiles942.signalRows]

def lineOrderedRows : List (ℕ × WangTiles942.Tile) :=
  [(0, WangTiles942.start)] ++ List.ofFn lineTransition ++
    (WangTiles942.copyRows 1 ++ WangTiles942.copyRows 0) ++
    (lineSignalRows true ++ lineSignalRows false) ++ WangTiles942.tailRows

theorem lineOrderedRows_eq : lineOrderedRows = WangTiles942.orderedRows := by
  have htrans : List.ofFn lineTransition = List.ofFn WangTiles942.transitionRow := by
    apply congrArg List.ofFn
    funext j
    exact lineTransition_eq j
  simp only [lineOrderedRows, WangTiles942.orderedRows, htrans, lineSignalRows_eq]

theorem lineOrderedRows_length : lineOrderedRows.length = 942 := by
  rw [lineOrderedRows_eq]
  exact WangTiles942.ordered_count

def lineTile (i : Fin 942) : WangTiles942.Tile :=
  (lineOrderedRows[i.val]'(by rw [lineOrderedRows_length]; exact i.isLt)).2

theorem lineTile_eq (i : Fin 942) : lineTile i = WangTiles942.tile i := by
  simp only [lineTile, lineOrderedRows_eq, WangTiles942.tile]

end DiophantineConsistency.Sign17LinesTable
#print axioms DiophantineConsistency.Sign17LinesTable.lineOrderedRows_eq
#print axioms DiophantineConsistency.Sign17LinesTable.lineTile_eq
