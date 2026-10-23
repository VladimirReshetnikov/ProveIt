import DiophantineConsistency.SplitSourceCarry

open DiophantineConsistency
open SplitSourceCarry
open Jones1982 Polynomial
open scoped BigOperators

private def weights : Fin 31 → ℕ := Fin.val
private theorem winj : Function.Injective weights := Fin.val_injective
private theorem wbound (i : Fin 31) : weights i≤116 := by have h:=i.isLt; change i.val≤116; omega

private theorem kernels : SplitWordBounds.KernelBounds (0:ℤ[X]) 0 (X^1929) 1 := by
  refine ⟨by simp,by simp,by simp,?_,?_,?_,by simp⟩
  · intro i; simp
  · intro i; simp
  · intro i; rw [coeff_X_pow]; split_ifs <;> norm_num

/-- At b=1 the unique bounded low tuple is zero. The target at position zero
still passes for a polynomial supported at degree at least 1929. No giant
integer source word is evaluated by the check. -/
example : τ 2
    (SplitCarry.word 4096 117 0 (SplitCarry.highInt 4096 0 weights 0 0 (X^1929) {0}))
    (SplitCarry.packedMask 4096 1 117 weights {0})=0 := by
  have hJ : 0≤SplitCarry.highInt 4096 0 weights 0 0 (X^1929) {0} := by
    unfold SplitCarry.highInt
    simp only [eval_zero,eval_pow,eval_X,Finset.sum_singleton,pow_zero]
    positivity
  have h := tau_product_iff (B:=4096) (b:=1) (g:=0) (k:=0) (t:=12) weights winj wbound
    (by decide) (by decide) (by decide) (by decide) (by positivity) {0}
    (by intro i hi; simp only [Finset.mem_singleton] at hi; omega)
    0 0 (X^1929) (H:=1) (by decide) kernels (by decide) hJ
  apply h.mpr
  refine ⟨fun _ => 0,by intro i; change 0<1; decide,?_,?_⟩
  · simp [LowMaskCoding.indexedCode]
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    simp [SplitCoefficientBounds.product]

#print axioms tau_product_iff
#print axioms tau_targets_iff
