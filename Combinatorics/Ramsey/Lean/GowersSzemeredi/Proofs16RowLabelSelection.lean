import GowersSzemeredi.Proofs16AdditiveQuadrupleCollisions
import GowersSzemeredi.Proofs16IndexedSelection

/-! Assign one row label per point. Distinct quadruples prescribe four
consistent labels and deterministic averaging loses only `4^4`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_quadruple_row_labels {X : Type} [Fintype X]
    (Q : Finset (Fin 4 → X)) (hQ : ∀ a ∈ Q, Function.Injective a) :
    ∃ color : X → Fin 4, Q.card ≤ 256*(Q.filter fun a => ∀ j, color (a j) = j).card := by
  let req (a : Fin 4 → X) : Finset X × (X → Fin 4) :=
    (Finset.univ.image a,Function.invFun a)
  have hr : ∀ a ∈ Q, (req a).1.card ≤ 4 ∧
      ∀ x ∈ (req a).1, (req a).2 x ∈ (Finset.univ : Finset (Fin 4)) := by
    intro a ha
    exact ⟨Finset.card_image_le.trans (by simp),fun _ _ => Finset.mem_univ _⟩
  obtain ⟨color,hcolor,hcount⟩ := exists_good_indexed_selection
    (fun _ : X => (Finset.univ : Finset (Fin 4))) (fun _ => Finset.univ_nonempty)
    (K := 4) (by norm_num) (fun _ => by simp) Q req hr
  have heq : (Q.filter fun a => Meets color (req a)) =
      Q.filter fun a => ∀ j, color (a j) = j := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha,h⟩
      refine ⟨ha,fun j => ?_⟩
      have he := h (a j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
      exact he.trans (Function.leftInverse_invFun (hQ a ha) j)
    · rintro ⟨ha,h⟩
      refine ⟨ha,?_⟩
      intro x hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact (h j).trans (Function.leftInverse_invFun (hQ a ha) j).symm
  refine ⟨color,?_⟩
  simpa only [heq,show (4 : Nat)^4 = 256 by norm_num] using hcount

theorem exists_dense_quadruple_row_labels {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (hadd : ∀ a ∈ Q, a 0+a 1 = a 2+a 3)
    {kappa : Real} (hmass : kappa*(N : Real)^3 ≤ Q.card) (hN : 8 ≤ kappa*(N : Real)) :
    ∃ (color : ZMod N → Fin 4) (R : Finset (Fin 4 → ZMod N)),
      R ⊆ Q ∧ (kappa/512)*(N : Real)^3 ≤ R.card ∧
      ∀ a ∈ R, Function.Injective a ∧ ∀ j, color (a j) = j := by
  let Q' := Q.filter Function.Injective
  obtain ⟨color,hcolor⟩ := exists_quadruple_row_labels Q' (fun a ha => (Finset.mem_filter.mp ha).2)
  let R := Q'.filter fun a => ∀ j, color (a j) = j
  refine ⟨color,R,(Finset.filter_subset _ _).trans (Finset.filter_subset _ _),?_,?_⟩
  · have hhalf := additive_quadruples_distinct_mass Q hadd hmass hN
    have hc : (Q'.card : Real) ≤ 256*(R.card : Real) := by exact_mod_cast hcolor
    change (kappa/2)*(N : Real)^3 ≤ (Q'.card : Real) at hhalf
    linarith
  · intro a ha
    obtain ⟨haQ,halabel⟩ := Finset.mem_filter.mp ha
    exact ⟨(Finset.mem_filter.mp haQ).2,halabel⟩

end LeanProofs.GowersSzemeredi
