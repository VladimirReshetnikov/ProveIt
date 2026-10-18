import BusyBeaver.ZFC.TableCombined243

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.rawTableCombined243_size
#print axioms SetTheory.BusyBeaver.ZFC.rawTableCombined243_transition_count
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_ne_deleted
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_zero
#print axioms SetTheory.BusyBeaver.ZFC.embedConfig243_initial
#print axioms SetTheory.BusyBeaver.ZFC.combined243_common_action
#print axioms SetTheory.BusyBeaver.ZFC.combined243_common_next
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old20_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old24_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old37_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old55_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old66_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old81_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old92_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old92_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old104_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old106_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old107_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old122_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old122_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old125_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old151_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRotation244_old167_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old20_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old24_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old37_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old55_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old66_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old81_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old92_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old92_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old104_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old106_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old107_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old125_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old151_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCombined243_old167_true
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old2
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old20
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old24
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old25
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old37
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old55
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old66
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old81
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old92
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old95
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old104
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old106
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old107
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old125
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old151
#print axioms SetTheory.BusyBeaver.ZFC.embedState243_old167

example : Machine 243 := machineCombined243
example : rawTableCombined243.size = 243 := rawTableCombined243_size
example (q : Fin 243) : embedState243 q ≠ oldStateRotation244 122 := embedState243_ne_deleted q
example : embedConfig243 (initial 243) = initial 244 := embedConfig243_initial
example (q : Fin 243) (b : Bool) (h : q ≠ oldStateCombined243 92)
    (he : ¬ exceptionalRow243 q b) :
    embedAction243 (machineCombined243.transition q b) = machineRotation244.transition (embedState243 q) b :=
  combined243_common_action q b h he
example (q : Fin 243) (b : Bool) (h : q ≠ oldStateCombined243 92)
    (he : ¬ exceptionalRow243 q b) :
    (machineCombined243.transition q b).next ≠ some (oldStateCombined243 92) :=
  combined243_common_next q b h he
