import BusyBeaver.ZFC.TableCombined243

/-!
Seven literal positive-block identities comparing Rotation244 and Combined243.
This is a source-only port of the checked compensated244 block calculations.
All row dependencies are unaffected by the QT edit/delete26. Every unspecified
tape cell and the exact list representation are retained. Explicit read
premises are supplied by Rotation244Invariant at the167 and81 entries.
No global simulation or actual kernel acceptance is asserted here.
-/
namespace SetTheory.BusyBeaver.ZFC.Combined243Blocks

def cfgOld (q : Nat) (h : Int) (t : Tape) : Config 244 :=
  ⟨some (oldStateRotation244 q), h, t⟩
def cfgNew (q : Nat) (h : Int) (t : Tape) : Config 243 :=
  ⟨some (oldStateCombined243 q), h, t⟩

private theorem step_read {n : Nat} (M : Machine n) (q q' : Fin n)
    (move : Move) (b : Bool) (h : Int) (t : Tape)
    (hb : Tape.read t h = b) (hr : M.transition q b = ⟨b, move, some q'⟩) :
    M.step ⟨some q, h, t⟩ = ⟨some q', move.apply h, t⟩ := by
  simp only [Machine.step, hb, hr]
  rw [← hb, Tape.write_read_self]

private theorem step_write {n : Nat} (M : Machine n) (q q' : Fin n)
    (move : Move) (b w : Bool) (h : Int) (t : Tape)
    (hb : Tape.read t h = b) (hr : M.transition q b = ⟨w, move, some q'⟩) :
    M.step ⟨some q, h, t⟩ = ⟨some q', move.apply h, Tape.write t h w⟩ := by
  simp only [Machine.step, hb, hr]

private theorem enter122_from104_read0_old (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineRotation244.runFrom (cfgOld 104 h t) 2 =
      cfgOld 25 (h + 2) t := by
  have s1 : machineRotation244.step (cfgOld 104 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRotation244 (oldStateRotation244 104)
        (oldStateRotation244 122) .right true h t
        h0 foldRowRotation244_old104_true)
  have s2 : machineRotation244.step (cfgOld 122 (h + 1) t) =
      cfgOld 25 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 122)
        (oldStateRotation244 25) .right false (h + 1) t
        hp1 foldRowRotation244_old122_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from104_read0_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCombined243.runFrom (cfgNew 104 h t) 4 =
      cfgNew 25 (h + 2) t := by
  have s1 : machineCombined243.step (cfgNew 104 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 104)
        (oldStateCombined243 92) .right true h t
        h0 foldRowCombined243_old104_true)
  have s2 : machineCombined243.step (cfgNew 92 (h + 1) t) =
      cfgNew 107 h t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) - 1 = h by omega)] using
      (step_read machineCombined243 (oldStateCombined243 92)
        (oldStateCombined243 107) .left false (h + 1) t
        hp1 foldRowCombined243_old92_false)
  have s3 : machineCombined243.step (cfgNew 107 h t) =
      cfgNew 125 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 107)
        (oldStateCombined243 125) .right true h t
        h0 foldRowCombined243_old107_true)
  have s4 : machineCombined243.step (cfgNew 125 (h + 1) t) =
      cfgNew 25 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCombined243 (oldStateCombined243 125)
        (oldStateCombined243 25) .right false (h + 1) t
        hp1 foldRowCombined243_old125_false)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4]

theorem enter122_from104_read0 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    embedConfig243 (machineCombined243.runFrom (cfgNew 104 h t) 4) =
      machineRotation244.runFrom (cfgOld 104 h t) 2 := by
  rw [enter122_from104_read0_new h t h0 hp1, enter122_from104_read0_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig243, Option.map_some, embedState243_old25]

private theorem enter122_from104_read1_old (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineRotation244.runFrom (cfgOld 104 h t) 2 =
      cfgOld 66 (h + 2) t := by
  have s1 : machineRotation244.step (cfgOld 104 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRotation244 (oldStateRotation244 104)
        (oldStateRotation244 122) .right true h t
        h0 foldRowRotation244_old104_true)
  have s2 : machineRotation244.step (cfgOld 122 (h + 1) t) =
      cfgOld 66 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 122)
        (oldStateRotation244 66) .right true (h + 1) t
        hp1 foldRowRotation244_old122_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from104_read1_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCombined243.runFrom (cfgNew 104 h t) 2 =
      cfgNew 66 (h + 2) t := by
  have s1 : machineCombined243.step (cfgNew 104 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 104)
        (oldStateCombined243 92) .right true h t
        h0 foldRowCombined243_old104_true)
  have s2 : machineCombined243.step (cfgNew 92 (h + 1) t) =
      cfgNew 66 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCombined243 (oldStateCombined243 92)
        (oldStateCombined243 66) .right true (h + 1) t
        hp1 foldRowCombined243_old92_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem enter122_from104_read1 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    embedConfig243 (machineCombined243.runFrom (cfgNew 104 h t) 2) =
      machineRotation244.runFrom (cfgOld 104 h t) 2 := by
  rw [enter122_from104_read1_new h t h0 hp1, enter122_from104_read1_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig243, Option.map_some, embedState243_old66]

private theorem enter122_from106_read0_old (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineRotation244.runFrom (cfgOld 106 h t) 2 =
      cfgOld 25 (h + 2) t := by
  have s1 : machineRotation244.step (cfgOld 106 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRotation244 (oldStateRotation244 106)
        (oldStateRotation244 122) .right true h t
        h0 foldRowRotation244_old106_true)
  have s2 : machineRotation244.step (cfgOld 122 (h + 1) t) =
      cfgOld 25 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 122)
        (oldStateRotation244 25) .right false (h + 1) t
        hp1 foldRowRotation244_old122_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from106_read0_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCombined243.runFrom (cfgNew 106 h t) 4 =
      cfgNew 25 (h + 2) t := by
  have s1 : machineCombined243.step (cfgNew 106 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 106)
        (oldStateCombined243 92) .right true h t
        h0 foldRowCombined243_old106_true)
  have s2 : machineCombined243.step (cfgNew 92 (h + 1) t) =
      cfgNew 107 h t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) - 1 = h by omega)] using
      (step_read machineCombined243 (oldStateCombined243 92)
        (oldStateCombined243 107) .left false (h + 1) t
        hp1 foldRowCombined243_old92_false)
  have s3 : machineCombined243.step (cfgNew 107 h t) =
      cfgNew 125 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 107)
        (oldStateCombined243 125) .right true h t
        h0 foldRowCombined243_old107_true)
  have s4 : machineCombined243.step (cfgNew 125 (h + 1) t) =
      cfgNew 25 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCombined243 (oldStateCombined243 125)
        (oldStateCombined243 25) .right false (h + 1) t
        hp1 foldRowCombined243_old125_false)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4]

theorem enter122_from106_read0 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    embedConfig243 (machineCombined243.runFrom (cfgNew 106 h t) 4) =
      machineRotation244.runFrom (cfgOld 106 h t) 2 := by
  rw [enter122_from106_read0_new h t h0 hp1, enter122_from106_read0_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig243, Option.map_some, embedState243_old25]

private theorem enter122_from106_read1_old (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineRotation244.runFrom (cfgOld 106 h t) 2 =
      cfgOld 66 (h + 2) t := by
  have s1 : machineRotation244.step (cfgOld 106 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRotation244 (oldStateRotation244 106)
        (oldStateRotation244 122) .right true h t
        h0 foldRowRotation244_old106_true)
  have s2 : machineRotation244.step (cfgOld 122 (h + 1) t) =
      cfgOld 66 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 122)
        (oldStateRotation244 66) .right true (h + 1) t
        hp1 foldRowRotation244_old122_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from106_read1_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCombined243.runFrom (cfgNew 106 h t) 2 =
      cfgNew 66 (h + 2) t := by
  have s1 : machineCombined243.step (cfgNew 106 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 106)
        (oldStateCombined243 92) .right true h t
        h0 foldRowCombined243_old106_true)
  have s2 : machineCombined243.step (cfgNew 92 (h + 1) t) =
      cfgNew 66 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCombined243 (oldStateCombined243 92)
        (oldStateCombined243 66) .right true (h + 1) t
        hp1 foldRowCombined243_old92_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem enter122_from106_read1 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    embedConfig243 (machineCombined243.runFrom (cfgNew 106 h t) 2) =
      machineRotation244.runFrom (cfgOld 106 h t) 2 := by
  rw [enter122_from106_read1_new h t h0 hp1, enter122_from106_read1_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig243, Option.map_some, embedState243_old66]

private theorem repair167_old (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineRotation244.runFrom (cfgOld 167 h t) 2 =
      cfgOld 24 (h - 2) t := by
  have s1 : machineRotation244.step (cfgOld 167 h t) =
      cfgOld 92 (h - 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRotation244 (oldStateRotation244 167)
        (oldStateRotation244 92) .left true h t
        h0 foldRowRotation244_old167_true)
  have s2 : machineRotation244.step (cfgOld 92 (h - 1) t) =
      cfgOld 24 (h - 2) t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 92)
        (oldStateRotation244 24) .left true (h - 1) t
        hm1 foldRowRotation244_old92_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem repair167_new (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCombined243.runFrom (cfgNew 167 h t) 2 =
      cfgNew 24 (h - 2) t := by
  have s1 : machineCombined243.step (cfgNew 167 h t) =
      cfgNew 151 (h - 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 167)
        (oldStateCombined243 151) .left true h t
        h0 foldRowCombined243_old167_true)
  have s2 : machineCombined243.step (cfgNew 151 (h - 1) t) =
      cfgNew 24 (h - 2) t := by
    simpa only [cfgNew, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineCombined243 (oldStateCombined243 151)
        (oldStateCombined243 24) .left true (h - 1) t
        hm1 foldRowCombined243_old151_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem repair167 (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    embedConfig243 (machineCombined243.runFrom (cfgNew 167 h t) 2) =
      machineRotation244.runFrom (cfgOld 167 h t) 2 := by
  rw [repair167_new h t hm1 h0, repair167_old h t hm1 h0]
  simp only [cfgNew, cfgOld, embedConfig243, Option.map_some, embedState243_old24]

private theorem enter92_from81_zero_old (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    machineRotation244.runFrom (cfgOld 81 h t) 2 =
      cfgOld 107 (h - 2) t := by
  have s1 : machineRotation244.step (cfgOld 81 h t) =
      cfgOld 92 (h - 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRotation244 (oldStateRotation244 81)
        (oldStateRotation244 92) .left true h t
        h0 foldRowRotation244_old81_true)
  have s2 : machineRotation244.step (cfgOld 92 (h - 1) t) =
      cfgOld 107 (h - 2) t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 92)
        (oldStateRotation244 107) .left false (h - 1) t
        hm1 foldRowRotation244_old92_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter92_from81_zero_new (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    machineCombined243.runFrom (cfgNew 81 h t) 2 =
      cfgNew 107 (h - 2) t := by
  have s1 : machineCombined243.step (cfgNew 81 h t) =
      cfgNew 92 (h - 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 81)
        (oldStateCombined243 92) .left true h t
        h0 foldRowCombined243_old81_true)
  have s2 : machineCombined243.step (cfgNew 92 (h - 1) t) =
      cfgNew 107 (h - 2) t := by
    simpa only [cfgNew, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineCombined243 (oldStateCombined243 92)
        (oldStateCombined243 107) .left false (h - 1) t
        hm1 foldRowCombined243_old92_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem enter92_from81_zero (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    embedConfig243 (machineCombined243.runFrom (cfgNew 81 h t) 2) =
      machineRotation244.runFrom (cfgOld 81 h t) 2 := by
  rw [enter92_from81_zero_new h t hm1 h0, enter92_from81_zero_old h t hm1 h0]
  simp only [cfgNew, cfgOld, embedConfig243, Option.map_some, embedState243_old107]

private theorem enter92_from81_one_old (h : Int) (t : Tape)
    (hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineRotation244.runFrom (cfgOld 81 h t) 6 =
      cfgOld 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
  have s1 : machineRotation244.step (cfgOld 81 h t) =
      cfgOld 92 (h - 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRotation244 (oldStateRotation244 81)
        (oldStateRotation244 92) .left true h t
        h0 foldRowRotation244_old81_true)
  have s2 : machineRotation244.step (cfgOld 92 (h - 1) t) =
      cfgOld 24 (h - 2) t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 92)
        (oldStateRotation244 24) .left true (h - 1) t
        hm1 foldRowRotation244_old92_true)
  have s3 : machineRotation244.step (cfgOld 24 (h - 2) t) =
      cfgOld 37 (h - 1) t := by
    simpa only [cfgOld, Move.apply, (show (h - 2) + 1 = (h - 1) by omega)] using
      (step_read machineRotation244 (oldStateRotation244 24)
        (oldStateRotation244 37) .right true (h - 2) t
        hm2 foldRowRotation244_old24_true)
  have s4 : machineRotation244.step (cfgOld 37 (h - 1) t) =
      cfgOld 55 h t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) + 1 = h by omega)] using
      (step_read machineRotation244 (oldStateRotation244 37)
        (oldStateRotation244 55) .right true (h - 1) t
        hm1 foldRowRotation244_old37_true)
  have s5 : machineRotation244.step (cfgOld 55 h t) =
      cfgOld 20 (h - 1) (Tape.write t h false) := by
    simpa only [cfgOld, Move.apply] using
      (step_write machineRotation244 (oldStateRotation244 55)
        (oldStateRotation244 20) .left true false h t
        h0 foldRowRotation244_old55_true)
  have r6 : Tape.read (Tape.write t h false) (h - 1) = true := by
    rw [Tape.read_write_of_ne t (by omega : (h - 1) ≠ h) false]
    exact hm1
  have s6 : machineRotation244.step (cfgOld 20 (h - 1) (Tape.write t h false)) =
      cfgOld 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_write machineRotation244 (oldStateRotation244 20)
        (oldStateRotation244 2) .left true false (h - 1) (Tape.write t h false)
        r6 foldRowRotation244_old20_true)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4, s5, s6]

private theorem enter92_from81_one_new (h : Int) (t : Tape)
    (_hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCombined243.runFrom (cfgNew 81 h t) 4 =
      cfgNew 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
  have s1 : machineCombined243.step (cfgNew 81 h t) =
      cfgNew 92 (h - 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCombined243 (oldStateCombined243 81)
        (oldStateCombined243 92) .left true h t
        h0 foldRowCombined243_old81_true)
  have s2 : machineCombined243.step (cfgNew 92 (h - 1) t) =
      cfgNew 66 h t := by
    simpa only [cfgNew, Move.apply, (show (h - 1) + 1 = h by omega)] using
      (step_read machineCombined243 (oldStateCombined243 92)
        (oldStateCombined243 66) .right true (h - 1) t
        hm1 foldRowCombined243_old92_true)
  have s3 : machineCombined243.step (cfgNew 66 h t) =
      cfgNew 20 (h - 1) (Tape.write t h false) := by
    simpa only [cfgNew, Move.apply] using
      (step_write machineCombined243 (oldStateCombined243 66)
        (oldStateCombined243 20) .left true false h t
        h0 foldRowCombined243_old66_true)
  have r4 : Tape.read (Tape.write t h false) (h - 1) = true := by
    rw [Tape.read_write_of_ne t (by omega : (h - 1) ≠ h) false]
    exact hm1
  have s4 : machineCombined243.step (cfgNew 20 (h - 1) (Tape.write t h false)) =
      cfgNew 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
    simpa only [cfgNew, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_write machineCombined243 (oldStateCombined243 20)
        (oldStateCombined243 2) .left true false (h - 1) (Tape.write t h false)
        r4 foldRowCombined243_old20_true)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4]

theorem enter92_from81_one (h : Int) (t : Tape)
    (hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    embedConfig243 (machineCombined243.runFrom (cfgNew 81 h t) 4) =
      machineRotation244.runFrom (cfgOld 81 h t) 6 := by
  rw [enter92_from81_one_new h t hm2 hm1 h0, enter92_from81_one_old h t hm2 hm1 h0]
  simp only [cfgNew, cfgOld, embedConfig243, Option.map_some, embedState243_old2]

theorem enter122_from104_read0_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCombined243.runFrom (cfgNew 104 h t) 4 =
      cfgNew 25 (h + 2) t :=
  enter122_from104_read0_new h t h0 hp1

theorem enter122_from104_read1_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCombined243.runFrom (cfgNew 104 h t) 2 =
      cfgNew 66 (h + 2) t :=
  enter122_from104_read1_new h t h0 hp1

theorem enter122_from106_read0_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCombined243.runFrom (cfgNew 106 h t) 4 =
      cfgNew 25 (h + 2) t :=
  enter122_from106_read0_new h t h0 hp1

theorem enter122_from106_read1_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCombined243.runFrom (cfgNew 106 h t) 2 =
      cfgNew 66 (h + 2) t :=
  enter122_from106_read1_new h t h0 hp1

theorem repair167_new_endpoint (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCombined243.runFrom (cfgNew 167 h t) 2 =
      cfgNew 24 (h - 2) t :=
  repair167_new h t hm1 h0

theorem enter92_from81_zero_new_endpoint (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    machineCombined243.runFrom (cfgNew 81 h t) 2 =
      cfgNew 107 (h - 2) t :=
  enter92_from81_zero_new h t hm1 h0

theorem enter92_from81_one_new_endpoint (h : Int) (t : Tape)
    (hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCombined243.runFrom (cfgNew 81 h t) 4 =
      cfgNew 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) :=
  enter92_from81_one_new h t hm2 hm1 h0

end SetTheory.BusyBeaver.ZFC.Combined243Blocks
