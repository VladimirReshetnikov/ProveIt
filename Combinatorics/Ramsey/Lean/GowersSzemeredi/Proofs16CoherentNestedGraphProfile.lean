import GowersSzemeredi.Proofs16CoherentNestedEndpointScale

/-! The reserved cell resolution gives an actual quasirandom graph
profile on the common endpoint radius, including its one-third shrink. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem coherentNestedProfileRadius_le {sigma : Real} (hs : 0 ≤ sigma) (K J : Nat) :
    coherentNestedProfileRadius sigma K J ≤ sigma := by
  have hp : (1 : Real) ≤ 9^(K+J+2) := one_le_pow₀ (by norm_num)
  exact div_le_self hs (by nlinarith : (1 : Real) ≤ 1296^2*9^(K+J+2)*3000)

theorem DenseBohrGraphProfiles.nested_profile {N ell H m : Nat} [NeZero N]
    {B C : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N} {sigma epsilon : Real}
    (h : DenseBohrGraphProfiles B C theta H m epsilon) (hs : 0 < sigma) (hsMax : sigma < 1/4)
    (K J : Nat) (hH : 3 ≤ coherentNestedProfileRadius sigma K J*H) :
    let r := coherentNestedProfileRadius sigma K J
    ∃ delta : Real, (1/(H : Real)^m)/2 ≤ delta ∧ delta ≤ 1 ∧
      boxSum (fun (z : ↥(bohr B r)) (u : ↥C) =>
        (if (z : ZMod N) ∈ bohr (Finset.univ.image fun i => theta i u) (r/3)
          then (1 : Real) else 0)-delta) ≤
      epsilon^4*((bohr B r).card : Real)^2*(C.card : Real)^2 := by
  have hr := coherentNestedProfileRadius_pos hs K J
  have hrl := coherentNestedProfileRadius_le hs.le K J
  exact h _ _ (by positivity) (by linarith) (hrl.trans_lt hsMax) (by nlinarith only [hH])

end LeanProofs.GowersSzemeredi
