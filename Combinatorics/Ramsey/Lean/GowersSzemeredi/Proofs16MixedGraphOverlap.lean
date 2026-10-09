import GowersSzemeredi.Proofs16MixedFreimanFamily

/-! Many mixed configurations force a dense translate on which the first
two maps agree up to a constant. The original configuration family remains
available for subsequent finite covering. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mixed_configurations_dense_overlap {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    (hA : ∀ q ∈ Q, q 0 ∈ A) (hB : ∀ q ∈ Q, q 1 ∈ B)
    {delta : Real} (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ (a c : ZMod N) (S : Finset (ZMod N)), S ⊆ B ∧ delta*N ≤ (S.card : Real) ∧
      ∀ x ∈ S, x+a ∈ A ∧ f 0 (x+a) = f 1 x+c := by
  let label (q : Fin 4 → ZMod N) := (q 2,q 3)
  obtain ⟨p,_,hp⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := Q) (t := (Finset.univ : Finset (ZMod N × ZMod N))) (f := label)
    (b := delta*(N : Real)) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by
      simpa only [Finset.card_univ,Fintype.card_prod,ZMod.card,nsmul_eq_mul,Nat.cast_mul,
        show (N : Real)*N*(delta*N) = delta*(N : Real)^3 by ring] using hcount)
  let R := Q.filter fun q => label q = p
  let S := R.image fun q => q 1
  have hinj : Set.InjOn (fun q : Fin 4 → ZMod N => q 1) (R : Set (Fin 4 → ZMod N)) := by
    intro q hq r hr h1
    obtain ⟨hqQ,hqp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hrQ,hrp⟩ := Finset.mem_filter.mp hr
    have h23 := Prod.mk.inj (hqp.trans hrp.symm)
    have hqd := (Finset.mem_filter.mp (hQ hqQ)).2.2.1
    have hrd := (Finset.mem_filter.mp (hQ hrQ)).2.2.1
    have h0 : q 0 = r 0 := by
      linear_combination hqd-hrd+h1+h23.1-h23.2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h23.1
    · exact h23.2
  have hS : delta*N ≤ (S.card : Real) := by
    simpa only [S,Finset.card_image_of_injOn hinj] using hp
  refine ⟨p.1-p.2,f 2 p.1-f 3 p.2,S,?_,hS,?_⟩
  · intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    exact hB q (Finset.mem_filter.mp hq).1
  · intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hqQ,hqp⟩ := Finset.mem_filter.mp hq
    have h23 := Prod.mk.inj hqp
    obtain ⟨_,_,hd,hv⟩ := Finset.mem_filter.mp (hQ hqQ)
    have h0 : q 1+(p.1-p.2) = q 0 := by
      linear_combination -hd-h23.1+h23.2
    rw [h0]
    refine ⟨hA q hqQ,?_⟩
    rw [h23.1,h23.2] at hv
    linear_combination hv

end LeanProofs.GowersSzemeredi
