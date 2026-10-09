import GowersSzemeredi.Proofs16CoherentWordBridge

/-! Restrict vertices, increase a bridge threshold, or start later in the
same radius chain without rerunning regularity. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem CoherentBridgeSystem.mono_threshold {N ell depth : Nat} [NeZero N]
    {B X : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta eta' : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (he : eta ≤ eta') :
    CoherentBridgeSystem B X theta F sigma eta' depth := by
  intro i hi Z x y a hZ hm hx hxa hy hya hza hb
  exact h i hi Z x y a hZ
    ((mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hm) hx hxa hy hya hza hb

theorem CoherentBridgeSystem.restrict {N ell depth : Nat} [NeZero N]
    {B X Y : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (hY : Y ⊆ X) :
    CoherentBridgeSystem B Y theta F sigma eta depth := by
  intro i hi Z x y a hZ hm hx hxa hy hya hza hb
  exact h i hi Z x y a (hZ.trans hY) hm (hY hx) (hY hxa) (hY hy) (hY hya) (fun z hz => hY (hza z hz)) hb

theorem CoherentBridgeSystem.shift {N ell depth d : Nat} [NeZero N]
    {B X : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma eta : Real}
    (h : CoherentBridgeSystem B X theta F sigma eta depth) (t : Nat) (hd : t+d ≤ depth) :
    CoherentBridgeSystem B X theta F (sigma/(6 : Real)^t) eta d := by
  intro i hi Z x y a hZ hm hx hxa hy hya hza hb
  have heq : (sigma/(6 : Real)^t)/(6 : Real)^i = sigma/(6 : Real)^(t+i) := by rw [div_div,pow_add]
  rw [heq] at hb ⊢
  exact h (t+i) (by omega) Z x y a hZ hm hx hxa hy hya hza hb

theorem CoherentBridgeSystem.word_family_of_le {N ell depth : Nat} [NeZero N] [Fact N.Prime]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa eta : Real} {Q : Finset (Fin 4 → ZMod N)} (K : Nat)
    (h : CoherentBridgeSystem B X theta F sigma eta depth)
    (he : eta ≤ kappa^(coherentWordBridgePower K)/coherentWordBridgeScale K)
    (hdepth : 3 ≤ depth) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hk : 0 < kappa) (hmass : kappa*(N : Real)^3 ≤ Q.card) (hN : 2 < N) :
    HasCoherentWordFamily X B theta F sigma kappa K :=
  (h.mono_threshold he).word_family K hdepth hfamily hk hmass hN

end LeanProofs.GowersSzemeredi
