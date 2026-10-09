import GowersSzemeredi.Proofs16FreimanKernelBohr

/-! A dense constant fibre produces a strict increase in the relation
subspace on a nested Bohr domain. Relations are taken on the full domain,
so restriction preserves all relations already established. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A coefficient vector becomes a relation on the Bohr set extracted from
one of its constant fibres. No normalization of the individual maps is needed. -/
theorem relation_mem_on_constant_fiber_bohr {N : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (w : κ → ZMod N) (F : Finset (ZMod N)) (hF : F ⊆ bohr Gamma (sigma / 4))
    {v : ZMod N} (hconst : ∀ x ∈ F, ∑ j, w j * L j x = v)
    {alpha : Real} (ha : 0 < alpha) (hcard : (F.card : Real) = alpha * N) :
    ((section7Spectrum F alpha).card : Real) ≤ 16 * alpha ^ (-(2 : Real)) ∧
      bohr (section7Spectrum F alpha) (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      w ∈ relationSubmodule (bohr (section7Spectrum F alpha) (1 / (8 * Real.pi))) L := by
  obtain ⟨hS, hkernel⟩ := freiman_const_on_bohr_of_dense Gamma hsigma
    (IsFreimanLinearOn.linear_combination hL w) F hF hconst ha hcard
  refine ⟨hS, fun x hx => (hkernel x hx).1, ?_⟩
  intro x hx
  have h := (hkernel x hx).2
  simp only [mul_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr h

/-- A fibre of a coefficient vector that was not a relation yields a strict
relation-subspace enlargement and an explicit rank bound. -/
theorem strict_relation_kernel_of_constant_fiber {N : Nat} [NeZero N] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (w : κ → ZMod N) (hw : w ∉ relationSubmodule (bohr Gamma sigma) L)
    (F : Finset (ZMod N)) (hF : F ⊆ bohr Gamma (sigma / 4))
    {v : ZMod N} (hconst : ∀ x ∈ F, ∑ j, w j * L j x = v)
    {alpha : Real} (ha : 0 < alpha) (hcard : (F.card : Real) = alpha * N) :
    ((section7Spectrum F alpha).card : Real) ≤ 16 * alpha ^ (-(2 : Real)) ∧
      bohr (section7Spectrum F alpha) (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      relationSubmodule (bohr Gamma sigma) L <
        relationSubmodule (bohr (section7Spectrum F alpha) (1 / (8 * Real.pi))) L := by
  obtain ⟨hS, hsub, hnew⟩ := relation_mem_on_constant_fiber_bohr Gamma hsigma L hL w F hF hconst ha hcard
  refine ⟨hS, hsub, lt_of_le_of_ne (relationSubmodule_anti hsub L) ?_⟩
  intro heq
  exact hw (heq ▸ hnew)

end LeanProofs.GowersSzemeredi
