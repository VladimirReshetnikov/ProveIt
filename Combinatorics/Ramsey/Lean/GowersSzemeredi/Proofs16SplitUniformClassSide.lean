import GowersSzemeredi.Proofs16SplitUniformClass
import GowersSzemeredi.Proofs16PowerUniformClassSide
import GowersSzemeredi.Proofs16ClassStepDegreesSide

/-! Declarations of `Proofs16SplitUniformClass` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **A power class at one degree is a split class** at that degree:
`uniformBase^d = (n+1)^d · W^d`. -/
def PowerUniformClass.toSplit {k : Nat} {V : Real} {d : Nat} (C : PowerUniformClass k V d d d) :
    SplitUniformClass k V d d where
  U := C.U
  mono := C.mono
  empty := C.empty
  decomp := C.decomp
  cover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    have h := C.cover theta gamma ht ht1 hg hg1 N n Gamma hU
    have hfun : ∀ rho, uniformBase V n theta gamma rho ^ d =
        ((n : Real) + 1) ^ d * splitW V theta gamma rho ^ d := fun rho => by
      rw [uniformBase_eq_split, mul_pow]
    simp only [hfun] at h
    exact h

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **Dimension two is a split class** at `a = D = 2^130`. -/
theorem splitUniformClass_two {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) {d : Nat}
    (hd : (2 : Nat) ^ 130 ≤ d) :
    Nonempty (SplitUniformClass 2 V d d) := by
  obtain ⟨C⟩ := powerUniformClass_two hK1 hp1 hlemma6 hV hKV hpV
  have h89 : (2 : Nat) ^ 89 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  have h45 : (2 : Nat) ^ 45 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  exact ⟨(C.weaken hV le_rfl h89 hd h45).toSplit⟩

end

end LeanProofs.GowersSzemeredi
