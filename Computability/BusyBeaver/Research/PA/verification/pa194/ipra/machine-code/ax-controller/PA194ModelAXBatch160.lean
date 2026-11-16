import PA194ModelAXPlan
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194ModelAXBlocks
open PA194ModelAXPlan
theorem block2202 : Bound 2202 2203 .incT := .incT 2202 (by decide) (by decide +kernel)
theorem block2203 : Bound 2203 2204 .incT := .incT 2203 (by decide) (by decide +kernel)
theorem block2204 : Bound 2204 2231 .cons := .cons 2204 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block2231 : Bound 2231 2258 .cons := .cons 2231 (⟨by decide,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block2258 : Bound 2258 2277 .push := .push 2258 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block2277 : Bound 2277 2284 .copyA := .copyA 2277 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block2284 : Bound 2284 2303 .push := .push 2284 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block2303 : Bound 2303 2310 .copyA := .copyA 2303 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
theorem block2310 : Bound 2310 2329 .push := .push 2310 (⟨⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩,⟨by decide,by decide +kernel,by decide +kernel,by decide +kernel⟩⟩)
theorem block2329 : Bound 2329 2336 .copyA := .copyA 2329 (⟨by decide,by decide,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩)
#print axioms block2202
end PA194ModelAXBlocks
