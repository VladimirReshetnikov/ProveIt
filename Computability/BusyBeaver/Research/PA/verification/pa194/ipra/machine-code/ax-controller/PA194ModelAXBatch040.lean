import PA194ModelAXPlan
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194ModelAXBlocks
open PA194ModelAXPlan
theorem block650 : Bound 650 657 .copyD := .copyD 650 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block657 : Bound 657 684 .cons := .cons 657 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block684 : Bound 684 685 .incT := .incT 684 (by decide) (by decide +kernel)
theorem block685 : Bound 685 686 .incT := .incT 685 (by decide) (by decide +kernel)
theorem block686 : Bound 686 705 .push := .push 686 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block705 : Bound 705 706 .incT := .incT 705 (by decide) (by decide +kernel)
theorem block706 : Bound 706 733 .cons := .cons 706 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block733 : Bound 733 752 .push := .push 733 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block752 : Bound 752 759 .copyH := .copyH 752 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block759 : Bound 759 786 .cons := .cons 759 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
#print axioms block650
end PA194ModelAXBlocks
