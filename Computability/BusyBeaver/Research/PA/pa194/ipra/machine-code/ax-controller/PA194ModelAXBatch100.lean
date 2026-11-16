import PA194ModelAXPlan
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194ModelAXBlocks
open PA194ModelAXPlan
theorem block1426 : Bound 1426 1433 .copyD := .copyD 1426 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block1433 : Bound 1433 1460 .cons := .cons 1433 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block1460 : Bound 1460 1461 .incT := .incT 1460 (by decide) (by decide +kernel)
theorem block1461 : Bound 1461 1462 .incT := .incT 1461 (by decide) (by decide +kernel)
theorem block1462 : Bound 1462 1463 .incT := .incT 1462 (by decide) (by decide +kernel)
theorem block1463 : Bound 1463 1482 .push := .push 1463 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block1482 : Bound 1482 1489 .copyA := .copyA 1482 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block1489 : Bound 1489 1508 .push := .push 1489 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block1508 : Bound 1508 1515 .copyH := .copyH 1508 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block1515 : Bound 1515 1542 .cons := .cons 1515 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
#print axioms block1426
end PA194ModelAXBlocks
