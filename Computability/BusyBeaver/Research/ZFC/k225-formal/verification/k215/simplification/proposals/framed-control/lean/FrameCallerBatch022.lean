import FrameCallerCore

namespace SetTheory.BusyBeaver.ZFC.KFrameCallers
open KZip KRuntimeCore KLeftFrame KFramedTemplates KFrameContracts KTableCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def callerBatch022 : List Caller := [
  ⟨bits "1101010110110111", bits "11010101101101", 7⟩,
  ⟨bits "1101010110111", bits "110101011", 8⟩,
  ⟨bits "110101011111", bits "1101010111", 9⟩,
  ⟨bits "11010110111", bits "11010110", 0⟩,
  ⟨bits "1101011111", bits "11010111", 11⟩,
  ⟨bits "11110000101", bits "11110000", 13⟩,
  ⟨bits "1111000011", bits "111100", 14⟩,
  ⟨bits "111100101", bits "11110010", 15⟩,
  ⟨bits "1111001101", bits "1111001", 13⟩,
  ⟨bits "111100111", bits "1111", 17⟩,
  ⟨bits "111110011001", bits "111110011", 2⟩,
  ⟨bits "1111100110111", bits "11111001101", 3⟩,
  ⟨bits "1111100111", bits "1111100", 4⟩,
  ⟨bits "111110111", bits "1111101", 9⟩,
  ⟨bits "11111111", bits "111111", 11⟩,
]

theorem callerBatch022_checked : callerBatch022.all checkCaller = true := by decide +kernel

#print axioms callerBatch022_checked
end SetTheory.BusyBeaver.ZFC.KFrameCallers
