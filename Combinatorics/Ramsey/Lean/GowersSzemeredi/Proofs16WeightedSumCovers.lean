import GowersSzemeredi.Proofs16BaseCaseUnion
import GowersSzemeredi.Proofs16Interpolation

/-! Scalar multiples and finite nonempty sums of multiply-linear partial
functions. These retain the exact sum parameter used in Section 16. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem MultiplyLinearFunction.const_mul {N d : Nat} [NeZero N]
    {gamma r : Real} {B : Finset (Point N d)} {phi : Point N d → ZMod N}
    (h : MultiplyLinearFunction gamma r B phi) (c : ZMod N) :
    MultiplyLinearFunction gamma r B (fun z => c * phi z) := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨M, q, H, Q, mu, hH, hmass, hpart, hproper, hq, hw, hmu, hc⟩ := h theta ht ht1 P hP
  refine ⟨M, q, H, Q, fun j i z => c * mu j i z, hH, hmass, hpart, hproper,
    hq, hw, fun j i => (hmu j i).const_mul c, ?_⟩
  intro j z hz hzH y hy
  obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hwy
  obtain ⟨i, hi⟩ := hc j w hz hzH (phi w) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  exact ⟨i, congrArg (fun v => c * v) hi⟩

/-- Reindex a nonempty finite family by `Fin` before applying the checked
common-refinement sum theorem. -/
theorem multiplyLinearFunction_fintype_sum {N d : Nat} [NeZero N]
    {I : Type*} [Fintype I] [Nonempty I] (gamma r : Real) (hr : 1 ≤ r)
    (B : Finset (Point N d)) (phi : I → Point N d → ZMod N)
    (hphi : ∀ i, MultiplyLinearFunction gamma r B (phi i)) :
    MultiplyLinearFunction gamma ((Fintype.card I : Real) * r) B
      (fun z => ∑ i, phi i z) := by
  let e := Fintype.equivFin I
  have hp := BaseCase.properMultiplyLinear_fin_sum gamma r hr B
    (fun i => phi (e.symm i)) (Fintype.card_pos) (fun i => hphi (e.symm i))
  have heq : (fun z => ∑ i, phi (e.symm i) z) = (fun z => ∑ i, phi i z) := by
    funext z
    exact e.symm.sum_comp (fun i => phi i z)
  rw [heq] at hp
  exact hp

end LeanProofs.GowersSzemeredi
