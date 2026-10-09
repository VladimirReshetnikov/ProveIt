import GowersSzemeredi.Proofs16DenseFamilyPacking
import GowersSzemeredi.Proofs16MixedGraphOverlap

/-! Cover a Freiman graph by few translates of differences of any dense
subgraph. The packing ambient size is N, not N squared. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def freimanGraphSums {N : Nat} (A S : Finset (ZMod N)) (f : ZMod N → ZMod N) :
    Finset (ZMod N × ZMod N) :=
  (A ×ˢ S).image fun p => (p.1+p.2,f p.1+f p.2)

theorem freimanGraphSums_card_le {N : Nat} [NeZero N]
    (A S : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hSA : S ⊆ A) (hF : IsFreimanLinearOn A f) : (freimanGraphSums A S f).card ≤ N := by
  have hinj : Set.InjOn Prod.fst (freimanGraphSums A S f : Set (ZMod N × ZMod N)) := by
    intro p hp q hq he
    obtain ⟨⟨a,s⟩,has,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨b,t⟩,hbt,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha,hs⟩ := Finset.mem_product.mp has
    obtain ⟨hb,ht⟩ := Finset.mem_product.mp hbt
    exact Prod.ext he (hF a s b t ha (hSA hs) hb (hSA ht) he)
  calc (freimanGraphSums A S f).card = ((freimanGraphSums A S f).image Prod.fst).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (ZMod N) := Finset.card_le_univ _
    _ = N := ZMod.card N

/-- Dense subgraphs give a covering by at most reciprocal-density many
translates of their graph difference set, with actual representation witnesses. -/
theorem freiman_graph_translate_cover {N : Nat} [NeZero N]
    (A S : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hSA : S ⊆ A) (hF : IsFreimanLinearOn A f)
    {mu : Real} (hmu : 0 < mu) (hS : mu*N ≤ (S.card : Real)) :
    ∃ J ⊆ A, (J.card : Real)*mu ≤ 1 ∧
      ∀ x ∈ A, ∃ j ∈ J, ∃ u ∈ S, ∃ v ∈ S,
        x = j+u-v ∧ f x = f j+f u-f v := by
  let F (x : ZMod N) := S.image fun s => (x+s,f x+f s)
  have hmass (x : ZMod N) : mu*N ≤ ((F x).card : Real) := by
    have hinj : Function.Injective (fun s : ZMod N => (x+s,f x+f s)) := by
      intro s t he
      exact add_left_cancel (Prod.mk.inj he).1
    simpa only [F,Finset.card_image_of_injective _ hinj] using hS
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨J,hJA,_,hJ,hcover⟩ := dense_family_packing A (freimanGraphSums A S f) F hmu hn
    (by exact_mod_cast freimanGraphSums_card_le A S f hSA hF)
    (fun x hx p hp => by
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨(x,s),Finset.mem_product.mpr ⟨hx,hs⟩,rfl⟩)
    (fun x _ => hmass x)
  refine ⟨J,hJA,hJ,?_⟩
  intro x hx
  obtain ⟨j,hj,p,hp⟩ := hcover x hx
  have hp' : p ∈ F x ∧ p ∈ F j := by simpa only [Finset.mem_inter] using hp
  obtain ⟨u,hu,hup⟩ := Finset.mem_image.mp hp'.1
  obtain ⟨v,hv,hvp⟩ := Finset.mem_image.mp hp'.2
  have he := Prod.mk.inj (hup.trans hvp.symm)
  exact ⟨j,hj,v,hv,u,hu,by linear_combination he.1,by linear_combination he.2⟩

end LeanProofs.GowersSzemeredi
