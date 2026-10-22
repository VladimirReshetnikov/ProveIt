import BusyBeaver.ZFC.KSource215Program
import BusyBeaver.ZFC.KResidualSites215Batch000
import BusyBeaver.ZFC.KResidualSites215Batch001
import BusyBeaver.ZFC.KResidualSites215Batch002
import BusyBeaver.ZFC.KResidualSites215Batch003
import BusyBeaver.ZFC.KResidualSites215Batch004
import BusyBeaver.ZFC.KResidualSites215Batch005
import BusyBeaver.ZFC.KResidualSites215Batch006
import BusyBeaver.ZFC.KResidualSites215Batch007
import BusyBeaver.ZFC.KResidualSites215Batch008

/-!
The 215's decoder-site coverage: every leaf of the source tree passes the residual site check
`KResidual215.residualTest tm215` (4751 leaves in 105 kernel blocks, joined to the root).
Partition inherited unchanged from generate_sites215_lean.py; checker changed by adapt_sites.py.
-/

namespace SetTheory.BusyBeaver.ZFC.KResidualSites215

open RegisterPath RMBisim SiteCoverage KTableCore

theorem all_sites : allSites (KResidual215.residualTest tm215) [] KSource215.t215 = true :=
  (allSites_join _ _ _ _
    block_0
    (allSites_join _ _ _ _
      block_1
      (allSites_join _ _ _ _
        (allSites_join _ _ _ _
          block_2
          (allSites_join _ _ _ _
            (allSites_join _ _ _ _
              (allSites_join _ _ _ _
                block_3
                (allSites_join _ _ _ _
                  (allSites_join _ _ _ _
                    (allSites_join _ _ _ _
                      block_4
                      (allSites_join _ _ _ _
                        (allSites_join _ _ _ _
                          block_5
                          block_6)
                        (allSites_join _ _ _ _
                          block_7
                          (allSites_join _ _ _ _
                            (allSites_join _ _ _ _
                              (allSites_join _ _ _ _
                                block_8
                                (allSites_join _ _ _ _
                                  block_9
                                  (allSites_join _ _ _ _
                                    block_10
                                    block_11)))
                              (allSites_join _ _ _ _
                                (allSites_join _ _ _ _
                                  block_12
                                  (allSites_join _ _ _ _
                                    (allSites_join _ _ _ _
                                      block_13
                                      (allSites_join _ _ _ _
                                        (allSites_join _ _ _ _
                                          block_14
                                          (allSites_join _ _ _ _
                                            block_15
                                            (allSites_join _ _ _ _
                                              block_16
                                              block_17)))
                                        (allSites_join _ _ _ _
                                          (allSites_join _ _ _ _
                                            (allSites_join _ _ _ _
                                              (allSites_join _ _ _ _
                                                (allSites_join _ _ _ _
                                                  block_18
                                                  (allSites_join _ _ _ _
                                                    block_19
                                                    (allSites_join _ _ _ _
                                                      (allSites_join _ _ _ _
                                                        block_20
                                                        block_21)
                                                      block_22)))
                                                (allSites_join _ _ _ _
                                                  block_23
                                                  (allSites_join _ _ _ _
                                                    block_24
                                                    (allSites_join _ _ _ _
                                                      (allSites_join _ _ _ _
                                                        block_25
                                                        block_26)
                                                      (allSites_join _ _ _ _
                                                        (allSites_join _ _ _ _
                                                          block_27
                                                          (allSites_join _ _ _ _
                                                            block_28
                                                            block_29))
                                                        block_30)))))
                                              (allSites_join _ _ _ _
                                                (allSites_join _ _ _ _
                                                  (allSites_join _ _ _ _
                                                    block_31
                                                    (allSites_join _ _ _ _
                                                      block_32
                                                      (allSites_join _ _ _ _
                                                        block_33
                                                        block_34)))
                                                  (allSites_join _ _ _ _
                                                    block_35
                                                    (allSites_join _ _ _ _
                                                      block_36
                                                      block_37)))
                                                (allSites_join _ _ _ _
                                                  block_38
                                                  (allSites_join _ _ _ _
                                                    (allSites_join _ _ _ _
                                                      (allSites_join _ _ _ _
                                                        (allSites_join _ _ _ _
                                                          (allSites_join _ _ _ _
                                                            block_39
                                                            (allSites_join _ _ _ _
                                                              (allSites_join _ _ _ _
                                                                (allSites_join _ _ _ _
                                                                  block_40
                                                                  (allSites_join _ _ _ _
                                                                    (allSites_join _ _ _ _
                                                                      block_41
                                                                      block_42)
                                                                    (allSites_join _ _ _ _
                                                                      block_43
                                                                      (allSites_join _ _ _ _
                                                                        (allSites_join _ _ _ _
                                                                          block_44
                                                                          block_45)
                                                                        block_46))))
                                                                (allSites_join _ _ _ _
                                                                  block_47
                                                                  block_48))
                                                              (allSites_join _ _ _ _
                                                                block_49
                                                                block_50)))
                                                          (allSites_join _ _ _ _
                                                            block_51
                                                            (allSites_join _ _ _ _
                                                              (allSites_join _ _ _ _
                                                                block_52
                                                                block_53)
                                                              (allSites_join _ _ _ _
                                                                (allSites_join _ _ _ _
                                                                  block_54
                                                                  block_55)
                                                                (allSites_join _ _ _ _
                                                                  block_56
                                                                  (allSites_join _ _ _ _
                                                                    (allSites_join _ _ _ _
                                                                      block_57
                                                                      block_58)
                                                                    block_59))))))
                                                        (allSites_join _ _ _ _
                                                          block_60
                                                          (allSites_join _ _ _ _
                                                            block_61
                                                            block_62)))
                                                      (allSites_join _ _ _ _
                                                        block_63
                                                        (allSites_join _ _ _ _
                                                          (allSites_join _ _ _ _
                                                            (allSites_join _ _ _ _
                                                              block_64
                                                              (allSites_join _ _ _ _
                                                                block_65
                                                                block_66))
                                                            (allSites_join _ _ _ _
                                                              block_67
                                                              block_68))
                                                          (allSites_join _ _ _ _
                                                            (allSites_join _ _ _ _
                                                              block_69
                                                              (allSites_join _ _ _ _
                                                                block_70
                                                                (allSites_join _ _ _ _
                                                                  block_71
                                                                  block_72)))
                                                            (allSites_join _ _ _ _
                                                              (allSites_join _ _ _ _
                                                                block_73
                                                                (allSites_join _ _ _ _
                                                                  (allSites_join _ _ _ _
                                                                    block_74
                                                                    block_75)
                                                                  block_76))
                                                              (allSites_join _ _ _ _
                                                                block_77
                                                                (allSites_join _ _ _ _
                                                                  block_78
                                                                  block_79)))))))
                                                    (allSites_join _ _ _ _
                                                      block_80
                                                      (allSites_join _ _ _ _
                                                        block_81
                                                        (allSites_join _ _ _ _
                                                          (allSites_join _ _ _ _
                                                            block_82
                                                            (allSites_join _ _ _ _
                                                              block_83
                                                              block_84))
                                                          (allSites_join _ _ _ _
                                                            (allSites_join _ _ _ _
                                                              block_85
                                                              (allSites_join _ _ _ _
                                                                (allSites_join _ _ _ _
                                                                  block_86
                                                                  block_87)
                                                                block_88))
                                                            (allSites_join _ _ _ _
                                                              block_89
                                                              (allSites_join _ _ _ _
                                                                block_90
                                                                block_91))))))))))
                                            (allSites_join _ _ _ _
                                              block_92
                                              block_93))
                                          (allSites_join _ _ _ _
                                            block_94
                                            block_95))))
                                    block_96))
                                block_97))
                            block_98))))
                    (allSites_join _ _ _ _
                      block_99
                      block_100))
                  block_101))
              block_102)
            block_103))
        block_104)))

theorem covered (B : KRuntimeCore.BoxLemmas tm215) :
    KSim.SemanticCovered tm215 KSource215.p215 :=
  KResidual215.covered_of_residual B all_sites

/-- The same concrete relation and both halting directions, now using the
shared prefix once and checked residual executions at all source leaves. -/
theorem halts_iff (B : KRuntimeCore.BoxLemmas tm215)
    (hNH : ∀ b, tm215 230 b = none) {c : Configuration} {T : KZip.Conf}
    (hc : KSim.Rel KSource215.p215 c T) :
    RegisterPath.Halts KSource215.p215 c ↔ KZip.Halts tm215 T :=
  KSim.Semantic.halts_iff (covered B) hNH hc

#print axioms all_sites
#print axioms covered
#print axioms halts_iff
end SetTheory.BusyBeaver.ZFC.KResidualSites215
