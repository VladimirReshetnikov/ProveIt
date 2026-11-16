import PA194ModelAXPlan
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194ModelAXBlocks
open PA194ModelAXPlan
theorem block50 : Bound 50 69 .push := .push 50 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block69 : Bound 69 76 .copyH := .copyH 69 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block76 : Bound 76 95 .push := .push 76 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block95 : Bound 95 102 .copyD := .copyD 95 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block102 : Bound 102 129 .cons := .cons 102 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block129 : Bound 129 130 .incT := .incT 129 (by decide) (by decide +kernel)
theorem block130 : Bound 130 131 .incT := .incT 130 (by decide) (by decide +kernel)
theorem block131 : Bound 131 145 .readH := .readH 131 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide,by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide⟩)
theorem block145 : Bound 145 164 .push := .push 145 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block164 : Bound 164 171 .copyH := .copyH 164 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
#print axioms block50
end PA194ModelAXBlocks
