import GowersSzemeredi.Proofs16JointCoherentAnchorSelection

/-! A second-moment bound for additive quadruples of indexed objects.
The map may have arbitrary fibres; distinct original objects are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mappedAdditiveQuadruples {X G : Type*} [Add G] [DecidableEq G] (S : Finset X) (f : X → G) :
    Finset (Fin 4 → X) :=
  (Fintype.piFinset fun _ : Fin 4 => S).filter fun q => f (q 0)+f (q 1) = f (q 2)+f (q 3)

theorem card_four_le_mapped_additive_quadruples {X G : Type*} [Fintype G] [Add G] [DecidableEq G]
    (S : Finset X) (f : X → G) :
    S.card^4 ≤ (mappedAdditiveQuadruples S f).card*Fintype.card G := by
  let P := S ×ˢ S
  let key := fun p : X × X => f p.1+f p.2
  let B := (P ×ˢ P).filter fun q => key q.1 = key q.2
  have hcs : P.card^2 ≤ B.card*Fintype.card G := card_sq_le_keyMatchingCount P key
  have hB : B.card ≤ (mappedAdditiveQuadruples S f).card := by
    apply Finset.card_le_card_of_injOn (fun q : (X × X) × (X × X) => ![q.1.1,q.1.2,q.2.1,q.2.2])
    · intro q hq
      obtain ⟨hprod,heq⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hprod
      obtain ⟨h0,h1⟩ := Finset.mem_product.mp ha
      obtain ⟨h2,h3⟩ := Finset.mem_product.mp hb
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,heq⟩
      intro i
      fin_cases i <;> assumption
    · intro q hq t ht he
      exact Prod.ext (Prod.ext (congrFun he 0) (congrFun he 1))
        (Prod.ext (congrFun he 2) (congrFun he 3))
  have h := hcs.trans (Nat.mul_le_mul_right _ hB)
  simp only [P,Finset.card_product] at h
  simpa only [show (S.card*S.card)^2 = S.card^4 by ring] using h

def supportedAnchorQuadruples {N : Nat} (W : Finset (ZMod N)) : Finset (Fin 4 → ZMod N) :=
  (Fintype.piFinset fun _ : Fin 4 => W).filter fun q => q 0-q 1 = q 2-q 3

theorem card_four_le_supported_anchor_quadruples {N : Nat} [NeZero N]
    (W : Finset (ZMod N)) : W.card^4 ≤ (supportedAnchorQuadruples W).card*N := by
  let P := W ×ˢ W
  let key := fun p : ZMod N × ZMod N => p.1-p.2
  let B := (P ×ˢ P).filter fun q => key q.1 = key q.2
  have hcs : P.card^2 ≤ B.card*N := by
    simpa only [ZMod.card,keyMatchingCount,B] using card_sq_le_keyMatchingCount P key
  have hB : B.card ≤ (supportedAnchorQuadruples W).card := by
    apply Finset.card_le_card_of_injOn (fun q : (ZMod N × ZMod N) × (ZMod N × ZMod N) =>
      ![q.1.1,q.1.2,q.2.1,q.2.2])
    · intro q hq
      obtain ⟨hprod,heq⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hprod
      obtain ⟨h0,h1⟩ := Finset.mem_product.mp ha
      obtain ⟨h2,h3⟩ := Finset.mem_product.mp hb
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_,heq⟩
      intro i
      fin_cases i <;> assumption
    · intro q hq t ht he
      exact Prod.ext (Prod.ext (congrFun he 0) (congrFun he 1))
        (Prod.ext (congrFun he 2) (congrFun he 3))
  have h := hcs.trans (Nat.mul_le_mul_right _ hB)
  simp only [P,Finset.card_product] at h
  simpa only [show (W.card*W.card)^2 = W.card^4 by ring] using h

end LeanProofs.GowersSzemeredi
