import Surreal.Algebra.NonzeroModuleKernel

/-!
# Injective lines in a kernel direction

The scalar cancellation used by the injective-line assertion after
`odg:dec:cor:converse`. The parameter space can be any vector space.
-/

namespace Surreal.ModuleKernelBasis

/-- A nonzero scalar direction gives an injective line with vector-space parameters. -/
theorem direction_injective {K V n : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : n → K) (hv : v ≠ 0) : Function.Injective (fun t : V => fun k => v k • t) := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hkn : v k ≠ 0 := hk
  intro s t h
  have he := congrArg (fun w : V => (v k)⁻¹ • w) (congrFun h k)
  simpa only [smul_smul, inv_mul_cancel₀ hkn, one_smul] using he

end Surreal.ModuleKernelBasis
