import PA194ModelAXPlan
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194ModelAXBlocks
open PA194ModelAXPlan
theorem block1164 : Bound 1164 1165 .incT := .incT 1164 (by decide) (by decide +kernel)
theorem block1165 : Bound 1165 1184 .push := .push 1165 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block1184 : Bound 1184 1191 .copyH := .copyH 1184 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block1191 : Bound 1191 1210 .push := .push 1191 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block1210 : Bound 1210 1217 .copyA := .copyA 1210 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block1217 : Bound 1217 1244 .cons := .cons 1217 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block1244 : Bound 1244 1245 .incT := .incT 1244 (by decide) (by decide +kernel)
theorem block1245 : Bound 1245 1246 .incT := .incT 1245 (by decide) (by decide +kernel)
theorem block1246 : Bound 1246 1247 .incT := .incT 1246 (by decide) (by decide +kernel)
theorem block1247 : Bound 1247 1266 .push := .push 1247 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
#print axioms block1164
end PA194ModelAXBlocks
