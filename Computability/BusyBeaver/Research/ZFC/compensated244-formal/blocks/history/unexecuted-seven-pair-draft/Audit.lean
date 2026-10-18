import BusyBeaver.ZFC.Compensated244Blocks

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.Compensated244Blocks

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.enter122_from104_read0
example (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 104 h t) 4) =
      machineRouting245.runFrom (cfgOld 104 h t) 2 :=
  enter122_from104_read0 h t h0 hp1

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.enter122_from104_read1
example (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 104 h t) 2) =
      machineRouting245.runFrom (cfgOld 104 h t) 2 :=
  enter122_from104_read1 h t h0 hp1

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.enter122_from106_read0
example (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = false) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 106 h t) 4) =
      machineRouting245.runFrom (cfgOld 106 h t) 2 :=
  enter122_from106_read0 h t h0 hp1

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.enter122_from106_read1
example (h : Int) (t : Tape)
    (h0 : Tape.read t h = true)
    (hp1 : Tape.read t (h + 1) = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 106 h t) 2) =
      machineRouting245.runFrom (cfgOld 106 h t) 2 :=
  enter122_from106_read1 h t h0 hp1

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.repair167
example (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 167 h t) 2) =
      machineRouting245.runFrom (cfgOld 167 h t) 2 :=
  repair167 h t hm1 h0

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.enter92_from81_zero
example (h : Int) (t : Tape)
    (hm1 : Tape.read t (h - 1) = false)
    (h0 : Tape.read t h = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 81 h t) 2) =
      machineRouting245.runFrom (cfgOld 81 h t) 2 :=
  enter92_from81_zero h t hm1 h0

#print axioms SetTheory.BusyBeaver.ZFC.Compensated244Blocks.enter92_from81_one
example (h : Int) (t : Tape)
    (hm2 : Tape.read t (h - 2) = true)
    (hm1 : Tape.read t (h - 1) = true)
    (h0 : Tape.read t h = true) :
    embedConfig244 (machineCompensated244.runFrom (cfgNew 81 h t) 4) =
      machineRouting245.runFrom (cfgOld 81 h t) 6 :=
  enter92_from81_one h t hm2 hm1 h0

