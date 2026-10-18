import BusyBeaver.ZFC.TableCompensated244

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.rawTableCompensated244_size
#print axioms SetTheory.BusyBeaver.ZFC.rawTableCompensated244_transition_count
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_ne_deleted
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_zero
#print axioms SetTheory.BusyBeaver.ZFC.embedConfig244_initial
#print axioms SetTheory.BusyBeaver.ZFC.compensated244_common_action
#print axioms SetTheory.BusyBeaver.ZFC.compensated244_common_next
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old20_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old24_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old37_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old55_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old66_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old81_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old92_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old92_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old104_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old106_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old107_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old122_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old122_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old125_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old151_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowRouting245_old167_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old20_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old24_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old37_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old55_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old66_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old81_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old92_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old92_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old104_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old106_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old107_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old125_false
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old151_true
#print axioms SetTheory.BusyBeaver.ZFC.foldRowCompensated244_old167_true
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old2
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old20
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old24
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old25
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old37
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old55
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old66
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old81
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old92
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old95
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old104
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old106
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old107
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old125
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old151
#print axioms SetTheory.BusyBeaver.ZFC.embedState244_old167

example : Machine 244 := machineCompensated244
example : rawTableCompensated244.size = 244 := rawTableCompensated244_size
example (q : Fin 244) : embedState244 q ≠ oldStateRouting245 122 := embedState244_ne_deleted q
example : embedConfig244 (initial 244) = initial 245 := embedConfig244_initial
example (q : Fin 244) (b : Bool) (h : q ≠ oldStateCompensated244 92)
    (he : ¬ exceptionalRow244 q b) :
    embedAction244 (machineCompensated244.transition q b) = machineRouting245.transition (embedState244 q) b :=
  compensated244_common_action q b h he
example (q : Fin 244) (b : Bool) (h : q ≠ oldStateCompensated244 92)
    (he : ¬ exceptionalRow244 q b) :
    (machineCompensated244.transition q b).next ≠ some (oldStateCompensated244 92) :=
  compensated244_common_next q b h he
