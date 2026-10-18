import BusyBeaver.ZFC.TablePrefix250

/-!
Balanced transition lookup for the exact canonical prefix250 table.
This isolates the fast table from all bootstrap calculations. The tree format
is adapted from the maintained BootPerm252 transition-tree implementation;
the 500 actions are generated anew from canonical SHA-256
0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e.
All-state equality with machinePrefix250 is checked by trusted kernel reduction.
Table attribution and the machine conventions are recorded in TablePrefix250.
-/

namespace SetTheory.BusyBeaver.ZFC.FastTablePrefix250

inductive TransitionTree (states : Nat) where
  | leaf : (Action states × Action states) → TransitionTree states
  | branch : TransitionTree states → TransitionTree states → TransitionTree states

def TransitionTree.lookup {n : Nat} : TransitionTree n → Nat → (Action n × Action n)
  | .leaf row, _ => row
  | .branch even odd, q =>
    if q % 2 = 0 then even.lookup (q / 2) else odd.lookup (q / 2)

def fastTree : TransitionTree 250 :=
  .branch
    (.branch
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨true, .right, some ⟨80, by decide⟩⟩, ⟨true, .left, some ⟨126, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨75, by decide⟩⟩, ⟨true, .right, some ⟨147, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨76, by decide⟩⟩, ⟨true, .right, some ⟨77, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨221, by decide⟩⟩, ⟨true, .right, some ⟨154, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨45, by decide⟩⟩, ⟨false, .left, some ⟨46, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨193, by decide⟩⟩, ⟨true, .right, some ⟨194, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨112, by decide⟩⟩, ⟨true, .right, some ⟨113, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨243, by decide⟩⟩, ⟨true, .right, some ⟨244, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨25, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨165, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨true, .right, some ⟨91, by decide⟩⟩, ⟨true, .right, some ⟨70, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨232, by decide⟩⟩, ⟨true, .right, some ⟨233, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨38, by decide⟩⟩, ⟨false, .left, some ⟨19, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨205, by decide⟩⟩, ⟨true, .right, some ⟨206, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨132, by decide⟩⟩, ⟨true, .right, some ⟨133, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨15, by decide⟩⟩, ⟨true, .right, some ⟨239, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨12, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨51, by decide⟩⟩, ⟨false, .left, some ⟨13, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨true, .right, some ⟨249, by decide⟩⟩, ⟨true, .left, some ⟨60, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨201, by decide⟩⟩, ⟨true, .right, some ⟨22, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨56, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨29, by decide⟩⟩, ⟨false, .right, some ⟨54, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨72, by decide⟩⟩, ⟨false, .right, some ⟨91, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨213, by decide⟩⟩, ⟨true, .right, some ⟨100, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨29, by decide⟩⟩, ⟨false, .right, some ⟨66, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨178, by decide⟩⟩, ⟨true, .right, some ⟨179, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .left, some ⟨102, by decide⟩⟩, ⟨true, .left, some ⟨23, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨201, by decide⟩⟩, ⟨true, .right, some ⟨238, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨71, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨216, by decide⟩⟩, ⟨true, .right, some ⟨217, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨142, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨122, by decide⟩⟩, ⟨true, .right, some ⟨146, by decide⟩⟩)))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨46, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨154, by decide⟩⟩, ⟨true, .right, some ⟨155, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .left, some ⟨33, by decide⟩⟩, ⟨true, .left, some ⟨79, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨55, by decide⟩⟩, ⟨false, .right, some ⟨37, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨53, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨55, by decide⟩⟩, ⟨false, .right, some ⟨54, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨118, by decide⟩⟩, ⟨true, .right, some ⟨119, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨82, by decide⟩⟩, ⟨true, .right, some ⟨67, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨29, by decide⟩⟩, ⟨false, .right, some ⟨37, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨171, by decide⟩⟩, ⟨true, .left, some ⟨172, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨97, by decide⟩⟩, ⟨true, .right, some ⟨98, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨228, by decide⟩⟩, ⟨true, .right, some ⟨230, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨67, by decide⟩⟩, ⟨true, .right, some ⟨68, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨187, by decide⟩⟩, ⟨true, .right, some ⟨207, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨139, by decide⟩⟩, ⟨true, .right, some ⟨140, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨246, by decide⟩⟩, ⟨true, .right, some ⟨247, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨18, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨68, by decide⟩⟩, ⟨true, .right, some ⟨162, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨47, by decide⟩⟩, ⟨true, .right, some ⟨86, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨216, by decide⟩⟩, ⟨true, .right, some ⟨227, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨38, by decide⟩⟩, ⟨true, .right, some ⟨59, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨170, by decide⟩⟩, ⟨true, .right, some ⟨202, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨22, by decide⟩⟩, ⟨true, .right, some ⟨127, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨185, by decide⟩⟩, ⟨true, .right, some ⟨82, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨40, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨185, by decide⟩⟩, ⟨true, .right, some ⟨186, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨105, by decide⟩⟩, ⟨true, .right, some ⟨106, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨240, by decide⟩⟩, ⟨true, .right, some ⟨148, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨46, by decide⟩⟩, ⟨true, .left, some ⟨60, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨185, by decide⟩⟩, ⟨true, .right, some ⟨208, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨116, by decide⟩⟩, ⟨true, .right, some ⟨144, by decide⟩⟩)))))))
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨4, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨150, by decide⟩⟩, ⟨true, .right, some ⟨151, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨61, by decide⟩⟩, ⟨true, .right, some ⟨66, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨223, by decide⟩⟩, ⟨true, .right, some ⟨224, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨49, by decide⟩⟩, ⟨true, .right, some ⟨50, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨45, by decide⟩⟩, ⟨true, .left, some ⟨88, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨51, by decide⟩⟩, ⟨true, .right, some ⟨115, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨232, by decide⟩⟩, ⟨true, .right, some ⟨178, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨28, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨168, by decide⟩⟩, ⟨true, .left, some ⟨23, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨93, by decide⟩⟩, ⟨true, .right, some ⟨94, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨178, by decide⟩⟩, ⟨true, .right, some ⟨228, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨64, by decide⟩⟩, ⟨true, .right, some ⟨65, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨94, by decide⟩⟩, ⟨true, .left, some ⟨208, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨136, by decide⟩⟩, ⟨true, .right, some ⟨137, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨178, by decide⟩⟩, ⟨true, .right, some ⟨208, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨14, by decide⟩⟩, ⟨true, .right, some ⟨15, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨161, by decide⟩⟩, ⟨false, .left, some ⟨3, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨84, by decide⟩⟩, ⟨true, .right, none⟩))
                                (.leaf (⟨false, .right, some ⟨208, by decide⟩⟩, ⟨true, .right, some ⟨226, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨57, by decide⟩⟩, ⟨true, .right, some ⟨42, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨108, by decide⟩⟩, ⟨true, .right, some ⟨100, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨124, by decide⟩⟩, ⟨true, .right, some ⟨125, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨109, by decide⟩⟩, ⟨true, .right, some ⟨15, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨31, by decide⟩⟩, ⟨true, .right, some ⟨38, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨172, by decide⟩⟩, ⟨true, .right, some ⟨182, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨103, by decide⟩⟩, ⟨false, .left, some ⟨48, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨202, by decide⟩⟩, ⟨true, .right, some ⟨201, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨73, by decide⟩⟩, ⟨false, .left, some ⟨32, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨215, by decide⟩⟩, ⟨true, .right, some ⟨218, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨68, by decide⟩⟩, ⟨true, .right, some ⟨48, by decide⟩⟩))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨8, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨156, by decide⟩⟩, ⟨true, .right, some ⟨158, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨80, by decide⟩⟩, ⟨true, .right, some ⟨70, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨170, by decide⟩⟩, ⟨true, .right, some ⟨33, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨55, by decide⟩⟩, ⟨false, .right, some ⟨66, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨20, by decide⟩⟩, ⟨true, .right, some ⟨197, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨116, by decide⟩⟩, ⟨true, .right, some ⟨120, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨226, by decide⟩⟩, ⟨true, .right, some ⟨15, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨33, by decide⟩⟩, ⟨true, .right, some ⟨34, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨175, by decide⟩⟩, ⟨true, .right, some ⟨176, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨89, by decide⟩⟩, ⟨true, .right, some ⟨68, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨201, by decide⟩⟩, ⟨true, .right, some ⟨173, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨30, by decide⟩⟩, ⟨true, .right, some ⟨54, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨93, by decide⟩⟩, ⟨true, .right, some ⟨213, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨78, by decide⟩⟩, ⟨true, .right, some ⟨65, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨247, by decide⟩⟩, ⟨true, .right, some ⟨248, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨20, by decide⟩⟩, ⟨true, .right, some ⟨21, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨164, by decide⟩⟩, ⟨false, .left, some ⟨19, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨62, by decide⟩⟩, ⟨true, .left, some ⟨88, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨229, by decide⟩⟩, ⟨true, .right, some ⟨230, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨7, by decide⟩⟩, ⟨true, .left, some ⟨60, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨100, by decide⟩⟩, ⟨true, .right, some ⟨100, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨128, by decide⟩⟩, ⟨true, .right, some ⟨129, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨147, by decide⟩⟩, ⟨true, .left, some ⟨240, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨42, by decide⟩⟩, ⟨true, .right, some ⟨30, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨189, by decide⟩⟩, ⟨true, .right, some ⟨190, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨100, by decide⟩⟩, ⟨true, .right, some ⟨109, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨201, by decide⟩⟩, ⟨true, .right, some ⟨182, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨57, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨202, by decide⟩⟩, ⟨true, .right, some ⟨185, by decide⟩⟩)))
                            (.leaf (⟨false, .left, some ⟨46, by decide⟩⟩, ⟨false, .left, some ⟨107, by decide⟩⟩))))))))
    (.branch
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨true, .left, some ⟨2, by decide⟩⟩, ⟨false, .left, some ⟨3, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨148, by decide⟩⟩, ⟨true, .right, some ⟨149, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨68, by decide⟩⟩, ⟨true, .right, some ⟨78, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨222, by decide⟩⟩, ⟨true, .right, some ⟨210, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨47, by decide⟩⟩, ⟨true, .right, some ⟨48, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨35, by decide⟩⟩, ⟨true, .right, some ⟨76, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨114, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨245, by decide⟩⟩, ⟨true, .right, some ⟨144, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨27, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨166, by decide⟩⟩, ⟨true, .right, some ⟨167, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨81, by decide⟩⟩, ⟨true, .right, some ⟨92, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨234, by decide⟩⟩, ⟨true, .right, some ⟨235, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨62, by decide⟩⟩, ⟨true, .right, some ⟨63, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨182, by decide⟩⟩, ⟨true, .right, some ⟨207, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨134, by decide⟩⟩, ⟨true, .right, some ⟨135, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨201, by decide⟩⟩, ⟨true, .right, some ⟨228, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨9, by decide⟩⟩, ⟨false, .right, some ⟨13, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨36, by decide⟩⟩, ⟨true, .right, some ⟨69, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨82, by decide⟩⟩, ⟨true, .right, some ⟨83, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨22, by decide⟩⟩, ⟨true, .right, some ⟨225, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨true, .right, some ⟨41, by decide⟩⟩, ⟨true, .left, some ⟨3, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨200, by decide⟩⟩, ⟨true, .right, some ⟨85, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨32, by decide⟩⟩, ⟨true, .right, some ⟨123, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨100, by decide⟩⟩, ⟨true, .right, some ⟨232, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨17, by decide⟩⟩, ⟨false, .left, some ⟨19, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨180, by decide⟩⟩, ⟨true, .right, some ⟨181, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨55, by decide⟩⟩, ⟨false, .right, some ⟨39, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨185, by decide⟩⟩, ⟨true, .right, some ⟨239, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨1, by decide⟩⟩, ⟨true, .right, some ⟨57, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨100, by decide⟩⟩, ⟨true, .right, some ⟨94, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨false, .left, some ⟨46, by decide⟩⟩))
                                (.leaf (⟨true, .left, some ⟨0, by decide⟩⟩, ⟨true, .left, some ⟨126, by decide⟩⟩)))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨6, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨156, by decide⟩⟩, ⟨true, .right, some ⟨157, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨55, by decide⟩⟩, ⟨false, .right, some ⟨61, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨10, by decide⟩⟩, ⟨false, .left, some ⟨32, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨54, by decide⟩⟩, ⟨true, .right, some ⟨37, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨196, by decide⟩⟩, ⟨false, .left, some ⟨19, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨89, by decide⟩⟩, ⟨true, .right, some ⟨117, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨231, by decide⟩⟩, ⟨true, .right, some ⟨82, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨31, by decide⟩⟩, ⟨false, .left, some ⟨32, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨173, by decide⟩⟩, ⟨true, .right, some ⟨174, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨99, by decide⟩⟩, ⟨true, .right, some ⟨100, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨149, by decide⟩⟩, ⟨true, .right, some ⟨67, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨69, by decide⟩⟩, ⟨false, .left, some ⟨19, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨211, by decide⟩⟩, ⟨true, .right, some ⟨212, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨63, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨20, by decide⟩⟩, ⟨true, .left, some ⟨161, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨19, by decide⟩⟩, ⟨false, .right, some ⟨13, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨68, by decide⟩⟩, ⟨true, .right, some ⟨163, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨87, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨109, by decide⟩⟩, ⟨true, .right, some ⟨228, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨42, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨22, by decide⟩⟩, ⟨true, .right, some ⟨203, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨67, by decide⟩⟩, ⟨true, .right, some ⟨67, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨235, by decide⟩⟩, ⟨true, .right, some ⟨231, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨41, by decide⟩⟩, ⟨false, .right, some ⟨91, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨187, by decide⟩⟩, ⟨true, .right, some ⟨188, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨108, by decide⟩⟩, ⟨true, .right, some ⟨15, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨188, by decide⟩⟩, ⟨true, .right, some ⟨226, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨27, by decide⟩⟩, ⟨true, .right, some ⟨61, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨154, by decide⟩⟩, ⟨true, .right, some ⟨219, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨102, by decide⟩⟩, ⟨true, .right, some ⟨145, by decide⟩⟩)))))))
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨3, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨152, by decide⟩⟩, ⟨true, .right, some ⟨153, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨55, by decide⟩⟩, ⟨false, .right, some ⟨30, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨109, by decide⟩⟩, ⟨true, .right, some ⟨109, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨51, by decide⟩⟩, ⟨true, .right, some ⟨52, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨195, by decide⟩⟩, ⟨false, .left, some ⟨19, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨116, by decide⟩⟩, ⟨true, .right, some ⟨117, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨109, by decide⟩⟩, ⟨true, .right, some ⟨215, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨true, .left, some ⟨3, by decide⟩⟩, ⟨false, .left, some ⟨3, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨169, by decide⟩⟩, ⟨true, .right, some ⟨170, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨95, by decide⟩⟩, ⟨true, .right, some ⟨96, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨236, by decide⟩⟩, ⟨true, .right, some ⟨237, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨29, by decide⟩⟩, ⟨false, .right, some ⟨61, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨209, by decide⟩⟩, ⟨true, .right, some ⟨210, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨138, by decide⟩⟩, ⟨false, .left, some ⟨58, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨208, by decide⟩⟩, ⟨true, .right, some ⟨245, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨16, by decide⟩⟩, ⟨true, .right, some ⟨17, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨45, by decide⟩⟩, ⟨true, .right, some ⟨79, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .left, some ⟨85, by decide⟩⟩, ⟨true, .right, some ⟨36, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨23, by decide⟩⟩, ⟨true, .right, some ⟨201, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨20, by decide⟩⟩, ⟨true, .right, some ⟨58, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨108, by decide⟩⟩, ⟨true, .right, some ⟨201, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨true, .left, some ⟨126, by decide⟩⟩, ⟨true, .left, some ⟨107, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨171, by decide⟩⟩, ⟨true, .right, some ⟨94, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨39, by decide⟩⟩, ⟨true, .right, some ⟨27, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨183, by decide⟩⟩, ⟨true, .right, some ⟨184, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨true, .right, some ⟨104, by decide⟩⟩, ⟨true, .right, some ⟨91, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨239, by decide⟩⟩, ⟨true, .right, some ⟨239, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨74, by decide⟩⟩, ⟨true, .right, some ⟨75, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨216, by decide⟩⟩, ⟨true, .right, some ⟨215, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨143, by decide⟩⟩, ⟨true, .right, some ⟨11, by decide⟩⟩))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨true, .right, some ⟨9, by decide⟩⟩, ⟨false, .left, some ⟨7, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨159, by decide⟩⟩, ⟨true, .right, some ⟨160, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .left, some ⟨81, by decide⟩⟩, ⟨true, .left, some ⟨5, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨84, by decide⟩⟩, ⟨true, .right, some ⟨108, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨37, by decide⟩⟩, ⟨true, .right, some ⟨39, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨198, by decide⟩⟩, ⟨true, .right, some ⟨199, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨121, by decide⟩⟩, ⟨true, .right, some ⟨122, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨174, by decide⟩⟩, ⟨true, .right, some ⟨108, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨35, by decide⟩⟩, ⟨true, .right, some ⟨36, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨175, by decide⟩⟩, ⟨true, .right, some ⟨177, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨101, by decide⟩⟩, ⟨false, .left, some ⟨48, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨238, by decide⟩⟩, ⟨true, .right, some ⟨213, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨41, by decide⟩⟩, ⟨false, .right, some ⟨70, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨214, by decide⟩⟩, ⟨true, .right, some ⟨215, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨64, by decide⟩⟩, ⟨true, .right, some ⟨141, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨84, by decide⟩⟩, ⟨true, .right, some ⟨138, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨22, by decide⟩⟩, ⟨true, .right, some ⟨23, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨17, by decide⟩⟩, ⟨true, .right, some ⟨162, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨89, by decide⟩⟩, ⟨true, .right, some ⟨90, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨231, by decide⟩⟩, ⟨true, .right, some ⟨173, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨29, by decide⟩⟩, ⟨false, .right, some ⟨30, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨100, by decide⟩⟩, ⟨true, .right, some ⟨204, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨130, by decide⟩⟩, ⟨true, .right, some ⟨131, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨173, by decide⟩⟩, ⟨true, .left, some ⟨183, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨43, by decide⟩⟩, ⟨true, .right, some ⟨44, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨191, by decide⟩⟩, ⟨true, .right, some ⟨192, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨110, by decide⟩⟩, ⟨true, .right, some ⟨111, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨241, by decide⟩⟩, ⟨true, .right, some ⟨242, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨67, by decide⟩⟩, ⟨false, .left, some ⟨19, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨185, by decide⟩⟩, ⟨true, .right, some ⟨220, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨146, by decide⟩⟩, ⟨true, .right, some ⟨120, by decide⟩⟩))))))))

def fastMachine : Machine 250 where
  transition q b :=
    let row := fastTree.lookup q.val
    if b then row.2 else row.1

theorem fast_transition_eq : ∀ (q : Fin 250) (b : Bool),
    fastMachine.transition q b = machinePrefix250.transition q b := by decide +kernel

theorem fastMachine_eq : fastMachine = machinePrefix250 := by
  have h : fastMachine.transition = machinePrefix250.transition := by
    funext q b
    exact fast_transition_eq q b
  exact congrArg Machine.mk h

end SetTheory.BusyBeaver.ZFC.FastTablePrefix250
