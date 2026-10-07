import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

section

namespace Erdos3

open scoped Manifold

def tangentModelVector {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {x : M} (v : TangentSpace I x) : E := v

end Erdos3

end

end OAI
