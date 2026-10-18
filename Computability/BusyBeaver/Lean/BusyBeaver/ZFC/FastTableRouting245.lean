import BusyBeaver.ZFC.TableRouting245

/-!
Balanced transition lookup for the exact canonical routing245 table.
Adapted from the checked FastTablePrefix246 implementation, whose tree format
comes from the maintained BootPerm252 transition-tree implementation;
the 490 actions are generated anew from canonical SHA-256
17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13.
All-state equality with machineRouting245 is checked by trusted kernel reduction.
Table attribution and the machine conventions are recorded in TableRouting245.
-/

namespace SetTheory.BusyBeaver.ZFC.FastTableRouting245

inductive TransitionTree (states : Nat) where
  | leaf : (Action states × Action states) → TransitionTree states
  | branch : TransitionTree states → TransitionTree states → TransitionTree states

def TransitionTree.lookup {n : Nat} : TransitionTree n → Nat → (Action n × Action n)
  | .leaf row, _ => row
  | .branch even odd, q =>
    if q % 2 = 0 then even.lookup (q / 2) else odd.lookup (q / 2)

def fastTree : TransitionTree 245 :=
  .branch
    (.branch
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨true, .right, some ⟨100, by decide⟩⟩, ⟨true, .right, some ⟨0, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨150, by decide⟩⟩, ⟨true, .right, some ⟨151, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨52, by decide⟩⟩, ⟨false, .right, some ⟨27, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨52, by decide⟩⟩, ⟨false, .right, some ⟨34, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨48, by decide⟩⟩, ⟨true, .right, some ⟨49, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨52, by decide⟩⟩, ⟨false, .right, some ⟨51, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨114, by decide⟩⟩, ⟨true, .right, some ⟨115, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨79, by decide⟩⟩, ⟨true, .right, some ⟨64, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨true, .left, some ⟨1, by decide⟩⟩, ⟨false, .left, some ⟨1, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨167, by decide⟩⟩, ⟨true, .left, some ⟨148, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨205, by decide⟩⟩, ⟨true, .right, some ⟨239, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨224, by decide⟩⟩, ⟨true, .right, some ⟨226, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨58, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨183, by decide⟩⟩, ⟨true, .right, some ⟨203, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨135, by decide⟩⟩, ⟨true, .right, some ⟨136, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨17, by decide⟩⟩, ⟨true, .left, some ⟨157, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨13, by decide⟩⟩, ⟨true, .right, some ⟨14, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨65, by decide⟩⟩, ⟨true, .right, some ⟨158, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .left, some ⟨82, by decide⟩⟩, ⟨true, .right, some ⟨33, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨212, by decide⟩⟩, ⟨true, .right, some ⟨223, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨17, by decide⟩⟩, ⟨true, .right, some ⟨55, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨156, by decide⟩⟩, ⟨true, .right, some ⟨176, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨19, by decide⟩⟩, ⟨true, .right, some ⟨123, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨230, by decide⟩⟩, ⟨true, .right, some ⟨189, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨36, by decide⟩⟩, ⟨true, .right, some ⟨24, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨170, by decide⟩⟩, ⟨true, .right, some ⟨182, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨101, by decide⟩⟩, ⟨true, .right, some ⟨102, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨236, by decide⟩⟩, ⟨true, .right, some ⟨144, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨71, by decide⟩⟩, ⟨true, .right, some ⟨72, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨181, by decide⟩⟩, ⟨true, .right, some ⟨204, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨112, by decide⟩⟩, ⟨true, .right, some ⟨140, by decide⟩⟩))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨true, .right, some ⟨6, by decide⟩⟩, ⟨false, .left, some ⟨4, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨48, by decide⟩⟩, ⟨false, .left, some ⟨10, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨123, by decide⟩⟩, ⟨true, .right, some ⟨12, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨197, by decide⟩⟩, ⟨true, .right, some ⟨19, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨34, by decide⟩⟩, ⟨true, .right, some ⟨36, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨51, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨69, by decide⟩⟩, ⟨false, .right, some ⟨0, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨209, by decide⟩⟩, ⟨true, .right, some ⟨96, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨32, by decide⟩⟩, ⟨true, .right, some ⟨33, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨166, by decide⟩⟩, ⟨true, .right, some ⟨198, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨97, by decide⟩⟩, ⟨false, .left, some ⟨45, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨197, by decide⟩⟩, ⟨true, .right, some ⟨234, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨38, by decide⟩⟩, ⟨false, .right, some ⟨67, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨149, by decide⟩⟩, ⟨true, .right, some ⟨235, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨true, .right, some ⟨138, by decide⟩⟩))
                                (.leaf (⟨true, .left, some ⟨244, by decide⟩⟩, ⟨true, .left, some ⟨122, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨19, by decide⟩⟩, ⟨true, .right, some ⟨20, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨true, .right, some ⟨161, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨86, by decide⟩⟩, ⟨true, .right, some ⟨87, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨228, by decide⟩⟩, ⟨true, .right, some ⟨229, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨27, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨169, by decide⟩⟩, ⟨true, .right, some ⟨232, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨174, by decide⟩⟩, ⟨true, .right, some ⟨202, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨12, by decide⟩⟩, ⟨true, .right, some ⟨235, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨40, by decide⟩⟩, ⟨true, .right, some ⟨41, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨12, by decide⟩⟩, ⟨true, .right, some ⟨126, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨185, by decide⟩⟩, ⟨true, .right, some ⟨198, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨152, by decide⟩⟩, ⟨true, .right, some ⟨183, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨64, by decide⟩⟩, ⟨false, .left, some ⟨16, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨187, by decide⟩⟩, ⟨true, .right, some ⟨106, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨72, by decide⟩⟩, ⟨true, .right, some ⟨143, by decide⟩⟩)))))))
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨3, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨79, by decide⟩⟩, ⟨true, .right, some ⟨226, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨52, by decide⟩⟩, ⟨false, .right, some ⟨58, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨166, by decide⟩⟩, ⟨true, .right, some ⟨30, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨51, by decide⟩⟩, ⟨true, .right, some ⟨34, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨17, by decide⟩⟩, ⟨true, .right, some ⟨193, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨112, by decide⟩⟩, ⟨true, .right, some ⟨116, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨222, by decide⟩⟩, ⟨true, .right, some ⟨12, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨28, by decide⟩⟩, ⟨false, .left, some ⟨29, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨145, by decide⟩⟩, ⟨true, .right, some ⟨208, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨95, by decide⟩⟩, ⟨true, .right, some ⟨96, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨197, by decide⟩⟩, ⟨true, .right, some ⟨169, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨66, by decide⟩⟩, ⟨false, .left, some ⟨16, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨89, by decide⟩⟩, ⟨true, .right, some ⟨209, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨75, by decide⟩⟩, ⟨true, .right, some ⟨62, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨81, by decide⟩⟩, ⟨true, .right, some ⟨134, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨16, by decide⟩⟩, ⟨false, .right, some ⟨10, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨160, by decide⟩⟩, ⟨false, .left, some ⟨16, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨true, .right, some ⟨84, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨201, by decide⟩⟩, ⟨true, .right, some ⟨181, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨23, by decide⟩⟩, ⟨false, .right, some ⟨39, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨96, by decide⟩⟩, ⟨true, .right, some ⟨96, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨128, by decide⟩⟩, ⟨true, .right, some ⟨220, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨143, by decide⟩⟩, ⟨true, .left, some ⟨236, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨38, by decide⟩⟩, ⟨false, .right, some ⟨0, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨216, by decide⟩⟩, ⟨true, .right, some ⟨184, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨96, by decide⟩⟩, ⟨true, .right, some ⟨105, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨184, by decide⟩⟩, ⟨true, .right, some ⟨219, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨24, by decide⟩⟩, ⟨true, .right, some ⟨58, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨105, by decide⟩⟩, ⟨true, .right, some ⟨147, by decide⟩⟩)))
                            (.leaf (⟨false, .left, some ⟨43, by decide⟩⟩, ⟨false, .left, some ⟨103, by decide⟩⟩))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨6, by decide⟩⟩, ⟨false, .right, some ⟨10, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨157, by decide⟩⟩, ⟨false, .left, some ⟨1, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨79, by decide⟩⟩, ⟨true, .right, some ⟨80, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨204, by decide⟩⟩, ⟨true, .right, some ⟨222, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨true, .right, some ⟨38, by decide⟩⟩, ⟨true, .left, some ⟨1, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨104, by decide⟩⟩, ⟨true, .right, some ⟨96, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨120, by decide⟩⟩, ⟨true, .right, some ⟨121, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨170, by decide⟩⟩, ⟨true, .right, some ⟨217, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨14, by decide⟩⟩, ⟨false, .left, some ⟨16, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨148, by decide⟩⟩, ⟨true, .right, some ⟨178, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨52, by decide⟩⟩, ⟨false, .right, some ⟨36, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨171, by decide⟩⟩, ⟨true, .right, some ⟨199, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨16, by decide⟩⟩, ⟨true, .right, some ⟨54, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨177, by decide⟩⟩, ⟨true, .right, some ⟨197, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨65, by decide⟩⟩, ⟨true, .right, some ⟨45, by decide⟩⟩)))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨23, by decide⟩⟩, ⟨false, .right, some ⟨24, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨164, by decide⟩⟩, ⟨true, .left, some ⟨20, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨78, by decide⟩⟩, ⟨true, .right, some ⟨88, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨174, by decide⟩⟩, ⟨true, .right, some ⟨224, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨59, by decide⟩⟩, ⟨true, .right, some ⟨60, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨90, by decide⟩⟩, ⟨true, .left, some ⟨204, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨132, by decide⟩⟩, ⟨true, .right, some ⟨133, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨204, by decide⟩⟩, ⟨true, .right, some ⟨240, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨44, by decide⟩⟩, ⟨true, .right, some ⟨45, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨42, by decide⟩⟩, ⟨true, .left, some ⟨85, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨48, by decide⟩⟩, ⟨true, .right, some ⟨111, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨228, by decide⟩⟩, ⟨true, .right, some ⟨174, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨65, by decide⟩⟩, ⟨true, .right, some ⟨75, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨188, by decide⟩⟩, ⟨true, .right, some ⟨218, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨231, by decide⟩⟩, ⟨true, .right, some ⟨206, by decide⟩⟩))))))))
    (.branch
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨1, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨173, by decide⟩⟩, ⟨true, .right, some ⟨108, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .left, some ⟨30, by decide⟩⟩, ⟨true, .left, some ⟨76, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨7, by decide⟩⟩, ⟨false, .left, some ⟨29, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨true, .right, some ⟨50, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨192, by decide⟩⟩, ⟨false, .left, some ⟨16, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨86, by decide⟩⟩, ⟨true, .right, some ⟨113, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨181, by decide⟩⟩, ⟨true, .right, some ⟨154, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨34, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨79, by decide⟩⟩, ⟨true, .right, some ⟨233, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨93, by decide⟩⟩, ⟨true, .right, some ⟨94, by decide⟩⟩))
                                (.leaf (⟨false, .left, some ⟨79, by decide⟩⟩, ⟨true, .right, some ⟨64, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨64, by decide⟩⟩, ⟨true, .right, some ⟨65, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨223, by decide⟩⟩, ⟨true, .right, some ⟨198, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨true, .right, some ⟨60, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨242, by decide⟩⟩, ⟨true, .right, some ⟨243, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨15, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨65, by decide⟩⟩, ⟨true, .right, some ⟨159, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨44, by decide⟩⟩, ⟨true, .right, some ⟨83, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨105, by decide⟩⟩, ⟨true, .right, some ⟨168, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨35, by decide⟩⟩, ⟨true, .right, some ⟨56, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨12, by decide⟩⟩, ⟨true, .right, some ⟨197, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨64, by decide⟩⟩, ⟨true, .right, some ⟨64, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨231, by decide⟩⟩, ⟨true, .right, some ⟨227, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨37, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨237, by decide⟩⟩, ⟨true, .right, some ⟨107, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨19, by decide⟩⟩, ⟨true, .right, some ⟨68, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨214, by decide⟩⟩, ⟨true, .right, some ⟨155, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨43, by decide⟩⟩, ⟨true, .left, some ⟨57, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨150, by decide⟩⟩, ⟨true, .right, some ⟨215, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨98, by decide⟩⟩, ⟨true, .right, some ⟨141, by decide⟩⟩))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨9, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨33, by decide⟩⟩, ⟨true, .right, some ⟨66, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨true, .right, some ⟨244, by decide⟩⟩, ⟨true, .left, some ⟨57, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨19, by decide⟩⟩, ⟨true, .right, some ⟨221, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨53, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨196, by decide⟩⟩, ⟨true, .right, some ⟨82, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨29, by decide⟩⟩, ⟨true, .right, some ⟨119, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨96, by decide⟩⟩, ⟨true, .right, some ⟨228, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨26, by decide⟩⟩, ⟨false, .right, some ⟨63, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨212, by decide⟩⟩, ⟨true, .right, some ⟨181, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .left, some ⟨98, by decide⟩⟩, ⟨true, .left, some ⟨20, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨207, by decide⟩⟩, ⟨true, .right, some ⟨146, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨78, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨96, by decide⟩⟩, ⟨true, .right, some ⟨90, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨false, .left, some ⟨43, by decide⟩⟩)))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨true, .right, some ⟨22, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨162, by decide⟩⟩, ⟨true, .right, some ⟨163, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨true, .right, some ⟨0, by decide⟩⟩, ⟨true, .right, some ⟨67, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨124, by decide⟩⟩, ⟨true, .right, some ⟨91, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨35, by decide⟩⟩, ⟨false, .left, some ⟨16, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨178, by decide⟩⟩, ⟨true, .right, some ⟨203, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨222, by decide⟩⟩, ⟨true, .right, some ⟨150, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨197, by decide⟩⟩, ⟨true, .right, some ⟨224, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨42, by decide⟩⟩, ⟨false, .left, some ⟨43, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨32, by decide⟩⟩, ⟨true, .right, some ⟨73, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨21, by decide⟩⟩, ⟨true, .right, some ⟨110, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨240, by decide⟩⟩, ⟨true, .right, some ⟨140, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨73, by decide⟩⟩, ⟨true, .right, some ⟨74, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨197, by decide⟩⟩, ⟨true, .right, some ⟨127, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨204, by decide⟩⟩, ⟨true, .right, some ⟨238, by decide⟩⟩)))))))
        (.branch
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨5, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨130, by decide⟩⟩, ⟨true, .right, some ⟨213, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨77, by decide⟩⟩, ⟨true, .right, some ⟨67, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨81, by decide⟩⟩, ⟨true, .right, some ⟨104, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨52, by decide⟩⟩, ⟨false, .right, some ⟨63, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨194, by decide⟩⟩, ⟨true, .right, some ⟨195, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨117, by decide⟩⟩, ⟨true, .right, some ⟨118, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨170, by decide⟩⟩, ⟨true, .right, some ⟨104, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨30, by decide⟩⟩, ⟨true, .right, some ⟨31, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨224, by decide⟩⟩, ⟨true, .right, some ⟨227, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨86, by decide⟩⟩, ⟨true, .right, some ⟨65, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨234, by decide⟩⟩, ⟨true, .right, some ⟨209, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨27, by decide⟩⟩, ⟨true, .right, some ⟨51, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨210, by decide⟩⟩, ⟨true, .right, some ⟨211, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨61, by decide⟩⟩, ⟨true, .right, some ⟨137, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨118, by decide⟩⟩, ⟨true, .right, some ⟨142, by decide⟩⟩))))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨17, by decide⟩⟩, ⟨true, .right, some ⟨18, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨14, by decide⟩⟩, ⟨true, .right, some ⟨158, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨59, by decide⟩⟩, ⟨true, .left, some ⟨85, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨227, by decide⟩⟩, ⟨true, .right, some ⟨169, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨4, by decide⟩⟩, ⟨true, .left, some ⟨57, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨96, by decide⟩⟩, ⟨true, .right, some ⟨200, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨174, by decide⟩⟩, ⟨true, .right, some ⟨125, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨169, by decide⟩⟩, ⟨true, .left, some ⟨179, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨39, by decide⟩⟩, ⟨true, .right, some ⟨27, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨225, by decide⟩⟩, ⟨true, .right, some ⟨109, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨144, by decide⟩⟩, ⟨true, .right, some ⟨175, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨152, by decide⟩⟩, ⟨true, .right, some ⟨92, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨23, by decide⟩⟩, ⟨false, .right, some ⟨54, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨186, by decide⟩⟩, ⟨true, .right, some ⟨131, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨142, by decide⟩⟩, ⟨true, .right, some ⟨116, by decide⟩⟩))))))
            (.branch
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨11, by decide⟩⟩, ⟨true, .right, some ⟨12, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨42, by decide⟩⟩, ⟨true, .right, some ⟨76, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨81, by decide⟩⟩, ⟨true, .right, none⟩))
                                (.leaf (⟨false, .right, some ⟨190, by decide⟩⟩, ⟨true, .right, some ⟨181, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨54, by decide⟩⟩, ⟨true, .right, some ⟨39, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨104, by decide⟩⟩, ⟨true, .right, some ⟨197, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨true, .left, some ⟨122, by decide⟩⟩, ⟨true, .left, some ⟨103, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨167, by decide⟩⟩, ⟨true, .right, some ⟨90, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨28, by decide⟩⟩, ⟨true, .right, some ⟨35, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨179, by decide⟩⟩, ⟨true, .right, some ⟨180, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨99, by decide⟩⟩, ⟨false, .left, some ⟨45, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨235, by decide⟩⟩, ⟨true, .right, some ⟨235, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨70, by decide⟩⟩, ⟨false, .left, some ⟨29, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨212, by decide⟩⟩, ⟨true, .right, some ⟨211, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨139, by decide⟩⟩, ⟨true, .right, some ⟨8, by decide⟩⟩)))))
                (.branch
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .left, some ⟨25, by decide⟩⟩, ⟨true, .left, some ⟨2, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨165, by decide⟩⟩, ⟨true, .right, some ⟨166, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨89, by decide⟩⟩, ⟨true, .right, some ⟨90, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨171, by decide⟩⟩, ⟨true, .right, some ⟨129, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨61, by decide⟩⟩, ⟨true, .right, some ⟨62, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨172, by decide⟩⟩, ⟨true, .right, some ⟨153, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨134, by decide⟩⟩, ⟨false, .left, some ⟨55, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨241, by decide⟩⟩, ⟨true, .right, some ⟨242, by decide⟩⟩)))))
                    (.branch
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨46, by decide⟩⟩, ⟨true, .right, some ⟨47, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨191, by decide⟩⟩, ⟨false, .left, some ⟨16, by decide⟩⟩)))
                            (.branch
                                (.leaf (⟨false, .right, some ⟨112, by decide⟩⟩, ⟨true, .right, some ⟨113, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨105, by decide⟩⟩, ⟨true, .right, some ⟨211, by decide⟩⟩))))
                        (.branch
                            (.branch
                                (.leaf (⟨false, .right, some ⟨58, by decide⟩⟩, ⟨true, .right, some ⟨63, by decide⟩⟩))
                                (.leaf (⟨false, .right, some ⟨105, by decide⟩⟩, ⟨true, .right, some ⟨105, by decide⟩⟩)))
                            (.leaf (⟨false, .right, some ⟨178, by decide⟩⟩, ⟨true, .right, some ⟨206, by decide⟩⟩))))))))

def fastMachine : Machine 245 where
  transition q b :=
    let row := fastTree.lookup q.val
    if b then row.2 else row.1

theorem fast_transition_eq : ∀ (q : Fin 245) (b : Bool),
    fastMachine.transition q b = machineRouting245.transition q b := by decide +kernel

theorem fastMachine_eq : fastMachine = machineRouting245 := by
  have h : fastMachine.transition = machineRouting245.transition := by
    funext q b
    exact fast_transition_eq q b
  exact congrArg Machine.mk h

end SetTheory.BusyBeaver.ZFC.FastTableRouting245
