import GowersSzemeredi.Proofs16KeyCollisionDensity
import GowersSzemeredi.Proofs16MixedQuadrupleExtraction

/-! Equal-parameter collisions project to mixed additive quadruples.
A bound on offset fibres controls precisely the projection multiplicity. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def offsetCollisionQuad {N : Nat} {I : Type*} (a : I → ZMod N)
    (p : (I × ZMod N) × (I × ZMod N)) : Fin 4 → ZMod N :=
  ![p.1.2+a p.1.1,p.1.2,p.2.2+a p.2.1,p.2.2]

def parameterCollisions {N : Nat} {I : Type*} [DecidableEq I] (Q : Finset (I × ZMod N)) :
    Finset ((I × ZMod N) × (I × ZMod N)) :=
  (Q ×ˢ Q).filter fun p => p.1.1 = p.2.1

theorem parameterCollisions_projection_card {N : Nat} [NeZero N] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a : I → ZMod N) (M : Nat)
    (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M) :
    (parameterCollisions Q).card ≤ M*((parameterCollisions Q).image (offsetCollisionQuad a)).card := by
  apply Finset.card_le_mul_card_image
  intro q _
  calc ((parameterCollisions Q).filter fun p => offsetCollisionQuad a p = q).card
      ≤ (Finset.univ.filter fun i => a i = q 0-q 1).card := by
        apply Finset.card_le_card_of_injOn (fun p => p.1.1)
        · intro p hp
          obtain ⟨hp,hpq⟩ := Finset.mem_filter.mp hp
          have h0 := congrFun hpq 0
          have h1 := congrFun hpq 1
          dsimp [offsetCollisionQuad] at h0 h1
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by linear_combination h0-h1⟩
        · intro p hp t ht he
          obtain ⟨hp,hpq⟩ := Finset.mem_filter.mp hp
          obtain ⟨ht,htq⟩ := Finset.mem_filter.mp ht
          have hpkey := (Finset.mem_filter.mp hp).2
          have htkey := (Finset.mem_filter.mp ht).2
          have hquad := hpq.trans htq.symm
          have h1 := congrFun hquad 1
          have h3 := congrFun hquad 3
          exact Prod.ext (Prod.ext he h1) (Prod.ext (hpkey.symm.trans (he.trans htkey)) h3)
    _ ≤ M := ha _

theorem offsetCollisionQuad_mem_mixed {N : Nat} [NeZero N] {I : Type*} [DecidableEq I]
    (Q : Finset (I × ZMod N)) (a v : I → ZMod N) (A : Finset (ZMod N))
    (f g : ZMod N → ZMod N)
    (hA : ∀ p ∈ Q, p.2+a p.1 ∈ A)
    (hval : ∀ p ∈ Q, f (p.2+a p.1)-g p.2 = v p.1) :
    (parameterCollisions Q).image (offsetCollisionQuad a) ⊆ mixedColumnQuadruples A ![f,g,f,g] := by
  intro q hq
  obtain ⟨⟨⟨i,x⟩,⟨j,y⟩⟩,hp,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hprod,he⟩ := Finset.mem_filter.mp hp
  change i = j at he
  subst j
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hprod
  have hfx := hval (i,x) hx
  have hfy := hval (i,y) hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hA (i,x) hx,by dsimp [offsetCollisionQuad]; ring,
    hfx.trans hfy.symm⟩

end LeanProofs.GowersSzemeredi
