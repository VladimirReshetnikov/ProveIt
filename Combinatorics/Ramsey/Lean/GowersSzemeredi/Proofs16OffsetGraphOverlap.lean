import GowersSzemeredi.Proofs16OffsetCollisionDensity
import GowersSzemeredi.Proofs16MixedGraphOverlap

/-! A dense indexed offset equation supplies a dense translated overlap
of its two endpoint graphs. The original indexed family is not replaced
by its collision image in later retention arguments. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem offset_equation_dense_overlap {N : Nat} [NeZero N] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a v : I → ZMod N)
    (A B : Finset (ZMod N)) (f g : ZMod N → ZMod N) (M : Nat)
    (hM : 0 < M) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M)
    (hA : ∀ p ∈ Q, p.2+a p.1 ∈ A) (hB : ∀ p ∈ Q, p.2 ∈ B)
    (hval : ∀ p ∈ Q, f (p.2+a p.1)-g p.2 = v p.1)
    {delta : Real} (hd : 0 ≤ delta) (hQ : delta*M*(N : Real)^2 ≤ Q.card) :
    ∃ (b c : ZMod N) (S : Finset (ZMod N)), S ⊆ B ∧ delta^2*N ≤ (S.card : Real) ∧
      ∀ x ∈ S, x+b ∈ A ∧ f (x+b) = g x+c := by
  let V := (parameterCollisions Q).image (offsetCollisionQuad a)
  have hV : V ⊆ mixedColumnQuadruples Finset.univ ![f,g,f,g] :=
    offsetCollisionQuad_mem_mixed Q a v Finset.univ f g (fun _ _ => Finset.mem_univ _) hval
  have hVA : ∀ q ∈ V, q 0 ∈ A := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact hA p.1 ((Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
  have hVB : ∀ q ∈ V, q 1 ∈ B := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact hB p.1 ((Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)
  exact mixed_configurations_dense_overlap A B ![f,g,f,g] V hV hVA hVB
    (offset_collision_quadruple_density Q a M hM ha hd hQ)

end LeanProofs.GowersSzemeredi
