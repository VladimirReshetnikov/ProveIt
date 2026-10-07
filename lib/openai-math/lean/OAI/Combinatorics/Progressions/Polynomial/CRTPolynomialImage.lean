import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.QuotientRing

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L Tag V : Type*} [Fintype L]

noncomputable def taggedOutputCRTEquiv (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k))) :
    (∀ h : Tag, J h → ZMod (∏ l, q l)) ≃+
      (∀ l : L, ∀ h : Tag, J h → ZMod (q l)) where
  toFun y l h j := ZMod.prodEquivPi q hq (y h j) l
  invFun y h j := (ZMod.prodEquivPi q hq).symm (fun l => y l h j)
  left_inv y := by
    funext h j
    exact (ZMod.prodEquivPi q hq).symm_apply_apply (y h j)
  right_inv y := by
    funext l h j
    exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => y l h j)) l
  map_add' x y := by
    funext l h j
    exact congrFun (map_add (ZMod.prodEquivPi q hq) (x h j) (y h j)) l

theorem taggedOutputCRTEquiv_apply (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (y : ∀ h : Tag, J h → ZMod (∏ l, q l)) (l : L) (h : Tag) (j : J h) :
    taggedOutputCRTEquiv J q hq y l h j =
      ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ l)) (ZMod (q l)) (y h j) :=
  ZMod.prodEquivPi_apply q hq (y h j) l

theorem taggedOutputCRTEquiv_symm_apply (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (y : ∀ l : L, ∀ h : Tag, J h → ZMod (q l)) (h : Tag) (j : J h) :
    (taggedOutputCRTEquiv J q hq).symm y h j =
      (ZMod.prodEquivPi q hq).symm (fun l => y l h j) := rfl

noncomputable def crtInput (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : ∀ l : L, V → ZMod (q l)) (v : V) : ZMod (∏ l, q l) :=
  (ZMod.prodEquivPi q hq).symm (fun l => x l v)

theorem crtInput_reduce (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : ∀ l : L, V → ZMod (q l)) (l : L) (v : V) :
    ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ l)) (ZMod (q l))
      (crtInput q hq x v) = x l v := by
  rw [← ZMod.prodEquivPi_apply q hq]
  exact congrFun ((ZMod.prodEquivPi q hq).apply_symm_apply (fun l => x l v)) l

theorem crtInput_integerPolynomial_eval (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) (l : L) :
    ZMod.prodEquivPi q hq
      (MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ k, q k))) (crtInput q hq x) F) l =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) F := by
  let e := ZMod.prodEquivPi q hq
  let φ := (Pi.evalRingHom (fun k => ZMod (q k)) l).comp e.toRingHom
  change φ (MvPolynomial.eval₂ _ _ F) = _
  rw [MvPolynomial.hom_eval₂]
  have hc : φ.comp (Int.castRingHom (ZMod (∏ k, q k))) =
      Int.castRingHom (ZMod (q l)) := Subsingleton.elim _ _
  rw [hc]
  congr 1
  funext v
  exact congrFun (e.apply_symm_apply (fun k => x k v)) l

theorem taggedOutputCRTEquiv_integerPolynomial_eval (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : ∀ h : Tag, J h → MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) :
    taggedOutputCRTEquiv J q hq
      (fun h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ l, q l)))
        (crtInput q hq x) (F h j)) =
      fun l h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) (F h j) := by
  funext l h j
  exact crtInput_integerPolynomial_eval q hq (F h j) x l

theorem taggedOutputCRTEquiv_symm_integerPolynomial_eval (J : Tag → Type*) (q : L → ℕ)
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (F : ∀ h : Tag, J h → MvPolynomial V ℤ) (x : ∀ l : L, V → ZMod (q l)) :
    (taggedOutputCRTEquiv J q hq).symm
      (fun l h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (q l))) (x l) (F h j)) =
      fun h j => MvPolynomial.eval₂ (Int.castRingHom (ZMod (∏ l, q l)))
        (crtInput q hq x) (F h j) := by
  apply (taggedOutputCRTEquiv J q hq).injective
  rw [AddEquiv.apply_symm_apply]
  exact (taggedOutputCRTEquiv_integerPolynomial_eval J q hq F x).symm

end Erdos3

end

end OAI
