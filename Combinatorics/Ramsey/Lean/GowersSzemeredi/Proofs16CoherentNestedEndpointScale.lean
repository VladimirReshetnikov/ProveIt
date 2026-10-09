import GowersSzemeredi.Proofs16CoherentNestedProfileScale
import GowersSzemeredi.Proofs16CoherentWordEndpointIdentity

/-! Both word layers have endpoint identities on a common profile scale. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem ColumnWordIdentity.mono_radius {N : Nat} [NeZero N]
    {T : ZMod N → Finset (ZMod N)} {F : ZMod N → ZMod N → ZMod N}
    {r s : Real} {as : List (ZMod N)} {w : ColumnWord N as.length}
    (h : ColumnWordIdentity T F r as w) (hs : s ≤ r) : ColumnWordIdentity T F s as w := by
  intro y ha hw
  exact h y (fun x hx => bohr_mono_radius _ hs (ha x hx)) (fun x hx => bohr_mono_radius _ hs (hw x hx))

theorem coherentNestedProfileRadius_le_inner {sigma : Real} (hs : 0 ≤ sigma)
    (K L m : Nat) (hm : m ≤ K+L+2) :
    coherentNestedProfileRadius sigma K L ≤ coherentWordEndpointRadius (sigma/1296) m := by
  have hp : (9 : Real)^m ≤ (9 : Real)^(K+L+2) := pow_le_pow_right₀ (by norm_num) hm
  have hden : (1296 : Real)*(1296*9^m) ≤ 1296^2*9^(K+L+2)*3000 := by
    have hpos : (0 : Real) < 9^(K+L+2) := by positivity
    nlinarith only [hp,hpos]
  unfold coherentNestedProfileRadius coherentWordEndpointRadius
  rw [div_div]
  exact div_le_div_of_nonneg_left hs (by positivity) hden

theorem coherentNestedProfileRadius_le_outer {sigma : Real} (hs : 0 ≤ sigma)
    (K L m : Nat) (hm : m ≤ K+L+2) :
    coherentNestedProfileRadius sigma K L ≤ coherentWordEndpointRadius sigma m := by
  exact (coherentNestedProfileRadius_le_inner hs K L m hm).trans
    (div_le_div_of_nonneg_right (by linarith : sigma/1296 ≤ sigma) (by positivity))

theorem CoherentWordEndpointIdentities.at_nested_scale {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma : Real}
    (h : CoherentWordEndpointIdentities X B theta F sigma) (hs : 0 ≤ sigma)
    (K L : Nat) {A : Finset (ZMod N)} (hA : A ⊆ X)
    (as : List (ZMod N)) (w : ColumnWord N as.length) (hm : as.length ≤ K+L+2)
    (hw : w ∈ columnWordRepresentations A (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (sigma/1296) as) :
    ColumnWordIdentity (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F
      (coherentNestedProfileRadius sigma K L) as w :=
  (h A hA as w hw).mono_radius (coherentNestedProfileRadius_le_outer hs K L as.length hm)

end LeanProofs.GowersSzemeredi
