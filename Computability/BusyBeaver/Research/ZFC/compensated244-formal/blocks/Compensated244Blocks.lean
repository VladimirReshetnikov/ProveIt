import BusyBeaver.ZFC.TableCompensated244

/-!
Seven literal positive-block identities on arbitrary Core finite-support tapes.
All unspecified tape cells and the exact list representation are retained.
Each lemma states explicit read premises; the original245 invariant supplies
those premises for the167 and81 entries. No global simulation is asserted here.
-/
namespace SetTheory.BusyBeaver.ZFC.Compensated244Blocks

def cfgOld (q : Nat) (h : Int) (t : Tape) : Config 245 :=
  ⟨some (oldStateRouting245 q), h, t⟩
def cfgNew (q : Nat) (h : Int) (t : Tape) : Config 244 :=
  ⟨some (oldStateCompensated244 q), h, t⟩

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
    machineRouting245.runFrom (cfgOld 104 h t) 2 =
      cfgOld 25 (h + 2) t := by
  have s1 : machineRouting245.step (cfgOld 104 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRouting245 (oldStateRouting245 104)
        (oldStateRouting245 122) .right true h t
        h0 foldRowRouting245_old104_true)
  have s2 : machineRouting245.step (cfgOld 122 (h + 1) t) =
      cfgOld 25 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 122)
        (oldStateRouting245 25) .right false (h + 1) t
        hp1 foldRowRouting245_old122_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from104_read0_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCompensated244.runFrom (cfgNew 104 h t) 4 =
      cfgNew 25 (h + 2) t := by
  have s1 : machineCompensated244.step (cfgNew 104 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 104)
        (oldStateCompensated244 92) .right true h t
        h0 foldRowCompensated244_old104_true)
  have s2 : machineCompensated244.step (cfgNew 92 (h + 1) t) =
      cfgNew 107 h t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) - 1 = h by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 92)
        (oldStateCompensated244 107) .left false (h + 1) t
        hp1 foldRowCompensated244_old92_false)
  have s3 : machineCompensated244.step (cfgNew 107 h t) =
      cfgNew 125 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 107)
        (oldStateCompensated244 125) .right true h t
        h0 foldRowCompensated244_old107_true)
  have s4 : machineCompensated244.step (cfgNew 125 (h + 1) t) =
      cfgNew 25 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 125)
        (oldStateCompensated244 25) .right false (h + 1) t
        hp1 foldRowCompensated244_old125_false)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4]

theorem enter122_from104_read0 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 104 h t) 4) =
      machineRouting245.runFrom (cfgOld 104 h t) 2 := by
  rw [enter122_from104_read0_new h t h0 hp1, enter122_from104_read0_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old25]

private theorem enter122_from104_read1_old (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineRouting245.runFrom (cfgOld 104 h t) 2 =
      cfgOld 66 (h + 2) t := by
  have s1 : machineRouting245.step (cfgOld 104 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRouting245 (oldStateRouting245 104)
        (oldStateRouting245 122) .right true h t
        h0 foldRowRouting245_old104_true)
  have s2 : machineRouting245.step (cfgOld 122 (h + 1) t) =
      cfgOld 66 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 122)
        (oldStateRouting245 66) .right true (h + 1) t
        hp1 foldRowRouting245_old122_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from104_read1_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCompensated244.runFrom (cfgNew 104 h t) 2 =
      cfgNew 66 (h + 2) t := by
  have s1 : machineCompensated244.step (cfgNew 104 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 104)
        (oldStateCompensated244 92) .right true h t
        h0 foldRowCompensated244_old104_true)
  have s2 : machineCompensated244.step (cfgNew 92 (h + 1) t) =
      cfgNew 66 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 92)
        (oldStateCompensated244 66) .right true (h + 1) t
        hp1 foldRowCompensated244_old92_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem enter122_from104_read1 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 104 h t) 2) =
      machineRouting245.runFrom (cfgOld 104 h t) 2 := by
  rw [enter122_from104_read1_new h t h0 hp1, enter122_from104_read1_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old66]

private theorem enter122_from106_read0_old (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineRouting245.runFrom (cfgOld 106 h t) 2 =
      cfgOld 25 (h + 2) t := by
  have s1 : machineRouting245.step (cfgOld 106 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRouting245 (oldStateRouting245 106)
        (oldStateRouting245 122) .right true h t
        h0 foldRowRouting245_old106_true)
  have s2 : machineRouting245.step (cfgOld 122 (h + 1) t) =
      cfgOld 25 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 122)
        (oldStateRouting245 25) .right false (h + 1) t
        hp1 foldRowRouting245_old122_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from106_read0_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCompensated244.runFrom (cfgNew 106 h t) 4 =
      cfgNew 25 (h + 2) t := by
  have s1 : machineCompensated244.step (cfgNew 106 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 106)
        (oldStateCompensated244 92) .right true h t
        h0 foldRowCompensated244_old106_true)
  have s2 : machineCompensated244.step (cfgNew 92 (h + 1) t) =
      cfgNew 107 h t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) - 1 = h by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 92)
        (oldStateCompensated244 107) .left false (h + 1) t
        hp1 foldRowCompensated244_old92_false)
  have s3 : machineCompensated244.step (cfgNew 107 h t) =
      cfgNew 125 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 107)
        (oldStateCompensated244 125) .right true h t
        h0 foldRowCompensated244_old107_true)
  have s4 : machineCompensated244.step (cfgNew 125 (h + 1) t) =
      cfgNew 25 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 125)
        (oldStateCompensated244 25) .right false (h + 1) t
        hp1 foldRowCompensated244_old125_false)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4]

theorem enter122_from106_read0 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 106 h t) 4) =
      machineRouting245.runFrom (cfgOld 106 h t) 2 := by
  rw [enter122_from106_read0_new h t h0 hp1, enter122_from106_read0_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old25]

private theorem enter122_from106_read1_old (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineRouting245.runFrom (cfgOld 106 h t) 2 =
      cfgOld 66 (h + 2) t := by
  have s1 : machineRouting245.step (cfgOld 106 h t) =
      cfgOld 122 (h + 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRouting245 (oldStateRouting245 106)
        (oldStateRouting245 122) .right true h t
        h0 foldRowRouting245_old106_true)
  have s2 : machineRouting245.step (cfgOld 122 (h + 1) t) =
      cfgOld 66 (h + 2) t := by
    simpa only [cfgOld, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 122)
        (oldStateRouting245 66) .right true (h + 1) t
        hp1 foldRowRouting245_old122_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter122_from106_read1_new (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCompensated244.runFrom (cfgNew 106 h t) 2 =
      cfgNew 66 (h + 2) t := by
  have s1 : machineCompensated244.step (cfgNew 106 h t) =
      cfgNew 92 (h + 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 106)
        (oldStateCompensated244 92) .right true h t
        h0 foldRowCompensated244_old106_true)
  have s2 : machineCompensated244.step (cfgNew 92 (h + 1) t) =
      cfgNew 66 (h + 2) t := by
    simpa only [cfgNew, Move.apply, (show (h + 1) + 1 = (h + 2) by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 92)
        (oldStateCompensated244 66) .right true (h + 1) t
        hp1 foldRowCompensated244_old92_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem enter122_from106_read1 (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 106 h t) 2) =
      machineRouting245.runFrom (cfgOld 106 h t) 2 := by
  rw [enter122_from106_read1_new h t h0 hp1, enter122_from106_read1_old h t h0 hp1]
  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old66]

private theorem repair167_old (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineRouting245.runFrom (cfgOld 167 h t) 2 =
      cfgOld 24 (h - 2) t := by
  have s1 : machineRouting245.step (cfgOld 167 h t) =
      cfgOld 92 (h - 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRouting245 (oldStateRouting245 167)
        (oldStateRouting245 92) .left true h t
        h0 foldRowRouting245_old167_true)
  have s2 : machineRouting245.step (cfgOld 92 (h - 1) t) =
      cfgOld 24 (h - 2) t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 92)
        (oldStateRouting245 24) .left true (h - 1) t
        hm1 foldRowRouting245_old92_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem repair167_new (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCompensated244.runFrom (cfgNew 167 h t) 2 =
      cfgNew 24 (h - 2) t := by
  have s1 : machineCompensated244.step (cfgNew 167 h t) =
      cfgNew 151 (h - 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 167)
        (oldStateCompensated244 151) .left true h t
        h0 foldRowCompensated244_old167_true)
  have s2 : machineCompensated244.step (cfgNew 151 (h - 1) t) =
      cfgNew 24 (h - 2) t := by
    simpa only [cfgNew, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 151)
        (oldStateCompensated244 24) .left true (h - 1) t
        hm1 foldRowCompensated244_old151_true)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem repair167 (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 167 h t) 2) =
      machineRouting245.runFrom (cfgOld 167 h t) 2 := by
  rw [repair167_new h t hm1 h0, repair167_old h t hm1 h0]
  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old24]

private theorem enter92_from81_zero_old (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    machineRouting245.runFrom (cfgOld 81 h t) 2 =
      cfgOld 107 (h - 2) t := by
  have s1 : machineRouting245.step (cfgOld 81 h t) =
      cfgOld 92 (h - 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRouting245 (oldStateRouting245 81)
        (oldStateRouting245 92) .left true h t
        h0 foldRowRouting245_old81_true)
  have s2 : machineRouting245.step (cfgOld 92 (h - 1) t) =
      cfgOld 107 (h - 2) t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 92)
        (oldStateRouting245 107) .left false (h - 1) t
        hm1 foldRowRouting245_old92_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

private theorem enter92_from81_zero_new (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    machineCompensated244.runFrom (cfgNew 81 h t) 2 =
      cfgNew 107 (h - 2) t := by
  have s1 : machineCompensated244.step (cfgNew 81 h t) =
      cfgNew 92 (h - 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 81)
        (oldStateCompensated244 92) .left true h t
        h0 foldRowCompensated244_old81_true)
  have s2 : machineCompensated244.step (cfgNew 92 (h - 1) t) =
      cfgNew 107 (h - 2) t := by
    simpa only [cfgNew, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 92)
        (oldStateCompensated244 107) .left false (h - 1) t
        hm1 foldRowCompensated244_old92_false)
  simp only [Machine.runFrom]
  rw [s1, s2]

theorem enter92_from81_zero (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 81 h t) 2) =
      machineRouting245.runFrom (cfgOld 81 h t) 2 := by
  rw [enter92_from81_zero_new h t hm1 h0, enter92_from81_zero_old h t hm1 h0]
  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old107]

private theorem enter92_from81_one_old (h : Int) (t : Tape)
    (hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineRouting245.runFrom (cfgOld 81 h t) 6 =
      cfgOld 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
  have s1 : machineRouting245.step (cfgOld 81 h t) =
      cfgOld 92 (h - 1) t := by
    simpa only [cfgOld, Move.apply] using
      (step_read machineRouting245 (oldStateRouting245 81)
        (oldStateRouting245 92) .left true h t
        h0 foldRowRouting245_old81_true)
  have s2 : machineRouting245.step (cfgOld 92 (h - 1) t) =
      cfgOld 24 (h - 2) t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 92)
        (oldStateRouting245 24) .left true (h - 1) t
        hm1 foldRowRouting245_old92_true)
  have s3 : machineRouting245.step (cfgOld 24 (h - 2) t) =
      cfgOld 37 (h - 1) t := by
    simpa only [cfgOld, Move.apply, (show (h - 2) + 1 = (h - 1) by omega)] using
      (step_read machineRouting245 (oldStateRouting245 24)
        (oldStateRouting245 37) .right true (h - 2) t
        hm2 foldRowRouting245_old24_true)
  have s4 : machineRouting245.step (cfgOld 37 (h - 1) t) =
      cfgOld 55 h t := by
    simpa only [cfgOld, Move.apply, (show (h - 1) + 1 = h by omega)] using
      (step_read machineRouting245 (oldStateRouting245 37)
        (oldStateRouting245 55) .right true (h - 1) t
        hm1 foldRowRouting245_old37_true)
  have s5 : machineRouting245.step (cfgOld 55 h t) =
      cfgOld 20 (h - 1) (Tape.write t h false) := by
    simpa only [cfgOld, Move.apply] using
      (step_write machineRouting245 (oldStateRouting245 55)
        (oldStateRouting245 20) .left true false h t
        h0 foldRowRouting245_old55_true)
  have r6 : Tape.read (Tape.write t h false) (h - 1) = true := by
    rw [Tape.read_write_of_ne t (by omega : (h - 1) ≠ h) false]
    exact hm1
  have s6 : machineRouting245.step (cfgOld 20 (h - 1) (Tape.write t h false)) =
      cfgOld 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
    simpa only [cfgOld, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_write machineRouting245 (oldStateRouting245 20)
        (oldStateRouting245 2) .left true false (h - 1) (Tape.write t h false)
        r6 foldRowRouting245_old20_true)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4, s5, s6]

private theorem enter92_from81_one_new (h : Int) (t : Tape)
    (_hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCompensated244.runFrom (cfgNew 81 h t) 4 =
      cfgNew 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
  have s1 : machineCompensated244.step (cfgNew 81 h t) =
      cfgNew 92 (h - 1) t := by
    simpa only [cfgNew, Move.apply] using
      (step_read machineCompensated244 (oldStateCompensated244 81)
        (oldStateCompensated244 92) .left true h t
        h0 foldRowCompensated244_old81_true)
  have s2 : machineCompensated244.step (cfgNew 92 (h - 1) t) =
      cfgNew 66 h t := by
    simpa only [cfgNew, Move.apply, (show (h - 1) + 1 = h by omega)] using
      (step_read machineCompensated244 (oldStateCompensated244 92)
        (oldStateCompensated244 66) .right true (h - 1) t
        hm1 foldRowCompensated244_old92_true)
  have s3 : machineCompensated244.step (cfgNew 66 h t) =
      cfgNew 20 (h - 1) (Tape.write t h false) := by
    simpa only [cfgNew, Move.apply] using
      (step_write machineCompensated244 (oldStateCompensated244 66)
        (oldStateCompensated244 20) .left true false h t
        h0 foldRowCompensated244_old66_true)
  have r4 : Tape.read (Tape.write t h false) (h - 1) = true := by
    rw [Tape.read_write_of_ne t (by omega : (h - 1) ≠ h) false]
    exact hm1
  have s4 : machineCompensated244.step (cfgNew 20 (h - 1) (Tape.write t h false)) =
      cfgNew 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) := by
    simpa only [cfgNew, Move.apply, (show (h - 1) - 1 = (h - 2) by omega)] using
      (step_write machineCompensated244 (oldStateCompensated244 20)
        (oldStateCompensated244 2) .left true false (h - 1) (Tape.write t h false)
        r4 foldRowCompensated244_old20_true)
  simp only [Machine.runFrom]
  rw [s1, s2, s3, s4]

theorem enter92_from81_one (h : Int) (t : Tape)
    (hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 81 h t) 4) =
      machineRouting245.runFrom (cfgOld 81 h t) 6 := by
  rw [enter92_from81_one_new h t hm2 hm1 h0, enter92_from81_one_old h t hm2 hm1 h0]
  simp only [cfgNew, cfgOld, embedConfig244, Option.map_some, embedState244_old2]

theorem enter122_from104_read0_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCompensated244.runFrom (cfgNew 104 h t) 4 =
      cfgNew 25 (h + 2) t :=
  enter122_from104_read0_new h t h0 hp1

theorem enter122_from104_read1_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCompensated244.runFrom (cfgNew 104 h t) 2 =
      cfgNew 66 (h + 2) t :=
  enter122_from104_read1_new h t h0 hp1

theorem enter122_from106_read0_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    machineCompensated244.runFrom (cfgNew 106 h t) 4 =
      cfgNew 25 (h + 2) t :=
  enter122_from106_read0_new h t h0 hp1

theorem enter122_from106_read1_new_endpoint (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    machineCompensated244.runFrom (cfgNew 106 h t) 2 =
      cfgNew 66 (h + 2) t :=
  enter122_from106_read1_new h t h0 hp1

theorem repair167_new_endpoint (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCompensated244.runFrom (cfgNew 167 h t) 2 =
      cfgNew 24 (h - 2) t :=
  repair167_new h t hm1 h0

theorem enter92_from81_zero_new_endpoint (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    machineCompensated244.runFrom (cfgNew 81 h t) 2 =
      cfgNew 107 (h - 2) t :=
  enter92_from81_zero_new h t hm1 h0

theorem enter92_from81_one_new_endpoint (h : Int) (t : Tape)
    (hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    machineCompensated244.runFrom (cfgNew 81 h t) 4 =
      cfgNew 2 (h - 2) (Tape.write (Tape.write t h false) (h - 1) false) :=
  enter92_from81_one_new h t hm2 hm1 h0

end SetTheory.BusyBeaver.ZFC.Compensated244Blocks
