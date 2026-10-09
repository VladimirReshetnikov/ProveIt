import GowersSzemeredi.Proofs16CoherentWeakTransitivity
import GowersSzemeredi.Proofs16CoherentBridgeAccuracy

/-! Weak transitivity at each level of a finite radius chain, on the
same coherent family and with an explicit bridge-density threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def CoherentBridgeSystem {N ell : Nat} [NeZero N]
    (B X : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (sigma eta : Real) (depth : Nat) : Prop :=
  ∀ i ≤ depth, ∀ (Z : Finset (ZMod N)) (x y a : ZMod N),
    Z ⊆ X → eta*N ≤ (Z.card : Real) →
    x ∈ X → x+a ∈ X → y ∈ X → y+a ∈ X → (∀ z ∈ Z, z+a ∈ X) →
    (∀ z ∈ Z,
      ColumnPairIdentity (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (sigma/(6 : Real)^i) (x+a,x) (z+a,z) ∧
      ColumnPairIdentity (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (sigma/(6 : Real)^i) (z+a,z) (y+a,y)) →
    ColumnPairIdentity (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F ((sigma/(6 : Real)^i)/6) (x+a,x) (y+a,y)

theorem DenseBohrGraphProfiles.bridge_system {N ell H m : Nat} [NeZero N] [NeZero H]
    {B C X : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {epsilon sigma eta : Real} {depth : Nat}
    (h : DenseBohrGraphProfiles B C theta H m epsilon)
    (hs : 0 < sigma) (hsMax : sigma < 1/4) (he : 0 ≤ epsilon) (heta : 0 < eta)
    (hH : ∀ i ≤ depth, 3 ≤ (sigma/(6 : Real)^i)*(H : Real)) (hX : X ⊆ C)
    (htheta : ∀ j, IsFreimanLinearOn C (theta j))
    (hlocal : ∀ u ∈ X, IsFreimanLinearOn (freimanFrequencyBohr B theta sigma u) (F u) ∧ F u 0 = 0)
    (hsmall : 4*((2*H : Nat) : Real)^(4*(B.card+ell))*epsilon < (1/(H : Real)^m)*eta) :
    CoherentBridgeSystem B X theta F sigma eta depth := by
  intro i hi Z x y a hZ hmass hx hxa hy hya hza hbridge
  have hrad : sigma/(6 : Real)^i ≤ sigma := div_le_self hs.le (one_le_pow₀ (by norm_num))
  exact coherent_pair_weak_transitivity B C X Z theta F (by positivity) (hrad.trans_lt hsMax)
    he heta (hH i hi) hX hZ htheta
    (fun u hu => ⟨(hlocal u hu).1.mono (bohr_mono_radius _ hrad),(hlocal u hu).2⟩)
    h hmass hsmall x y a hx hxa hy hya hza hbridge

end LeanProofs.GowersSzemeredi
