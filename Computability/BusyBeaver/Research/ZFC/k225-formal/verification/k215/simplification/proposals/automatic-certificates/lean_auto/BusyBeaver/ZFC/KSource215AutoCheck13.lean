import BusyBeaver.ZFC.KSource215AutoData

namespace SetTheory.BusyBeaver.ZFC.KSource215Auto

open RegisterPath RMBisim RMNormalizedBisim KSource215
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

private def left : CTree → CTree
  | .branch _ l _ => l
  | _ => .empty

private def right : CTree → CTree
  | .branch _ _ r => r
  | _ => .empty

private theorem part0_ok : allC checkEntry (left (left block13)) = true := by decide +kernel

private theorem part1_ok : allC checkEntry (right (left block13)) = true := by decide +kernel

private theorem part2_ok : allC checkEntry (left (right block13)) = true := by decide +kernel

private theorem part3_ok : allC checkEntry (right (right block13)) = true := by decide +kernel

theorem block_ok13 : allC checkEntry block13 = true := by
  have h : allC checkEntry block13 =
      ((allC checkEntry (left (left block13)) && allC checkEntry (right (left block13))) &&
      (allC checkEntry (left (right block13)) && allC checkEntry (right (right block13)))) := rfl
  rw [h, part0_ok, part1_ok, part2_ok, part3_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215Auto
