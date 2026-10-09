import GowersSzemeredi.Proofs16JointRowCommonBohr

/-! Additive quadruples of translations have three free coordinates.
Subtracting such a translation preserves the additive relation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def additiveTranslationQuadruple {N : Nat} (t : Fin 3 → ZMod N) : Fin 4 → ZMod N :=
  ![t 0,t 1,t 2,t 0+t 1-t 2]

def quadrupleTranslationCode {N : Nat} (a b : Fin 4 → ZMod N) : Fin 3 → ZMod N :=
  ![a 0-b 0,a 1-b 1,a 2-b 2]

theorem additiveTranslationQuadruple_additive {N : Nat} (t : Fin 3 → ZMod N) :
    additiveTranslationQuadruple t 0+additiveTranslationQuadruple t 1 =
      additiveTranslationQuadruple t 2+additiveTranslationQuadruple t 3 := by
  simp [additiveTranslationQuadruple]

theorem additiveTranslationQuadruple_code {N : Nat} (a b : Fin 4 → ZMod N)
    (ha : a 0+a 1 = a 2+a 3) (hb : b 0+b 1 = b 2+b 3) :
    additiveTranslationQuadruple (quadrupleTranslationCode a b) = fun j => a j-b j := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · rfl
  · change (a 0-b 0)+(a 1-b 1)-(a 2-b 2) = a 3-b 3
    linear_combination ha-hb

def localizedQuadruples {N : Nat} (Q : Finset (Fin 4 → ZMod N))
    (P : Finset (ZMod N)) (t : Fin 4 → ZMod N) : Finset (Fin 4 → ZMod N) :=
  Q.filter fun a => ∀ j, a j-t j ∈ P

theorem localized_quadruple_pair_reconstruct {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (P : Finset (ZMod N))
    (hQ : ∀ a ∈ Q, a 0+a 1 = a 2+a 3) (t : Fin 3 → ZMod N)
    {p : (Fin 4 → ZMod N) × (Fin 4 → ZMod N)}
    (hp : p ∈ (Q ×ˢ mappedAdditiveQuadruples P id).filter
      (fun p => quadrupleTranslationCode p.1 p.2 = t)) :
    p.1 ∈ localizedQuadruples Q P (additiveTranslationQuadruple t) ∧
      p.2 = fun j => p.1 j-additiveTranslationQuadruple t j := by
  obtain ⟨hp,hcode⟩ := Finset.mem_filter.mp hp
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  obtain ⟨hbP,hbadd⟩ := Finset.mem_filter.mp hb
  have hbmem := Fintype.mem_piFinset.mp hbP
  have he := additiveTranslationQuadruple_code p.1 p.2 (hQ p.1 ha) hbadd
  rw [hcode] at he
  have hr : p.2 = fun j => p.1 j-additiveTranslationQuadruple t j := by
    funext j
    have h := congrFun he j
    linear_combination h
  refine ⟨Finset.mem_filter.mpr ⟨ha,?_⟩,hr⟩
  intro j
  rw [← congrFun hr j]
  exact hbmem j

end LeanProofs.GowersSzemeredi
