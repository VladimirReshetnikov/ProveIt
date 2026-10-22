import BusyBeaver.ZFC.KSource215Data

namespace SetTheory.BusyBeaver.ZFC.KSource215

open RegisterPath RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/- Split this expensive kernel reduction into four independently checked lemmas.
   The CTree, checker, import and public theorem are unchanged. This follows
   the quarter-block method already used by the incoming normalized and
   automatic-certificates proposals. -/
private def left : CTree → CTree
  | .branch _ l _ => l
  | _ => .empty

private def right : CTree → CTree
  | .branch _ _ r => r
  | _ => .empty

private theorem part0_ok : allC fwdF (left (left fwd15)) = true := by decide +kernel

private theorem part1_ok : allC fwdF (right (left fwd15)) = true := by decide +kernel

private theorem part2_ok : allC fwdF (left (right fwd15)) = true := by decide +kernel

private theorem part3_ok : allC fwdF (right (right fwd15)) = true := by decide +kernel

theorem fwd_ok15 : allC fwdF fwd15 = true := by
  have h : allC fwdF fwd15 =
      ((allC fwdF (left (left fwd15)) && allC fwdF (right (left fwd15))) &&
      (allC fwdF (left (right fwd15)) && allC fwdF (right (right fwd15)))) := rfl
  rw [h, part0_ok, part1_ok, part2_ok, part3_ok]
  rfl

end SetTheory.BusyBeaver.ZFC.KSource215
