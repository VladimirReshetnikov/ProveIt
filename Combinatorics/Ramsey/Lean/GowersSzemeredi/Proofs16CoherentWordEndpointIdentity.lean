import GowersSzemeredi.Proofs16CoherentWordDomain
import GowersSzemeredi.Proofs16ColumnWordIdentity

/-! Endpoint-only identities for coherent compatible words. The radius
loss depends on word length, with no frequency-removal modulus condition. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentWordEndpointRadius (sigma : Real) (k : Nat) : Real := sigma/(1296*(9 : Real)^k)

theorem coherentWordEndpointRadius_pos {sigma : Real} (hs : 0 < sigma) (k : Nat) :
    0 < coherentWordEndpointRadius sigma k := by unfold coherentWordEndpointRadius; positivity

def CoherentWordEndpointIdentities {N ell : Nat} [NeZero N]
    (X B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (sigma : Real) : Prop :=
  ∀ A : Finset (ZMod N), A ⊆ X → ∀ (as : List (ZMod N)) (w : ColumnWord N as.length),
    w ∈ columnWordRepresentations A (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F (sigma/1296) as →
    ColumnWordIdentity (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F
      (coherentWordEndpointRadius sigma as.length) as w

theorem coherent_word_endpoint_identities {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma : Real}
    (hs : 0 ≤ sigma) (htheta : ∀ i, IsFreimanLinearOn X (theta i)) :
    CoherentWordEndpointIdentities X B theta F sigma := by
  intro A hAX as w hw y ha he
  have hrad : coherentWordEndpointRadius sigma as.length = (sigma/1296)/(9 : Real)^as.length := by
    rw [div_div]
    rfl
  have hd := coherent_word_domain A B theta F (by positivity : 0 ≤ sigma/1296)
    (fun i => (htheta i).mono hAX) as w hw y
    (fun x hx => by simpa only [hrad,freimanFrequencyBohr] using ha x hx)
    (fun x hx => by simpa only [hrad,freimanFrequencyBohr] using he x hx)
  exact (columnWordRepresentations_spec A _ F (sigma/1296) as w hw).2.2 y hd

end LeanProofs.GowersSzemeredi
