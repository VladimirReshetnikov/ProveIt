import DiophantineConsistency.PRASubSuccessorInvariant
import DiophantineConsistency.PRASubAddition

/-! Equality from vanishing truncated differences in candidate PRA models. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAEqualityDifference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAExhaustion
  PRAOpenInduction PRASubtraction PRASubAddition PRASubReconstruct PRASubSuccessorInvariant PRAQCompatibility

private def X : Semiterm language ℕ 1 := .bvar 0
private def Y : Semiterm language ℕ 1 := .fvar 0
private def Z : Semiterm language ℕ 1 := .func (Code.zero 0) Fin.elim0
private def body : Semiformula language ℕ 1 :=
  (Semiformula.nrel Language.ORing.Rel.eq ![.func subCode ![X,Y], Z]) ⋎
  ((Semiformula.nrel Language.ORing.Rel.eq ![.func subCode ![Y,X], Z]) ⋎
    (Semiformula.rel Language.ORing.Rel.eq ![X,Y]))

theorem body_open : body.Open := by simp [body, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
private theorem val_pair {ξ : Type} {n : ℕ} (b : Fin n → M) (f : ξ → M)
    (u v : Semiterm language ξ n) :
    (Semiterm.val b f ∘ ![u,v]) = ![Semiterm.val b f u, Semiterm.val b f v] := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun k => Fin.elim0 k) j

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem body_eval (x : M) (e : ℕ → M) : body.Eval ![x] e ↔
    Structure.func (L := language) subCode ![x,e 0] ≠
      Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
    (Structure.func (L := language) subCode ![e 0,x] ≠
      Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨ x = e 0) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] body ↔ _
  dsimp only [body, Semiformula.EvalAux]
  rw [eqRel, eqRel, eqRel]
  have hz : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, X, Y, Z,
    Semiterm.val_func, Semiterm.val_bvar, Semiterm.val_fvar, val_pair, hz]

theorem modelBothDifferencesZero (x y : M)
    (hxy : Structure.func (L := language) subCode ![x,y] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0)
    (hyx : Structure.func (L := language) subCode ![y,x] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0) : x = y := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let p : M → M := fun x => Structure.func (L := language) predCode (fun _ => x)
  let d : M → M → M := fun x y => Structure.func (L := language) subCode ![x,y]
  let a : M → M → M := fun x y => Structure.func (L := language) addCode ![x,y]
  let e : ℕ → M := fun _ => y
  have hall : ∀ t, body.Eval ![t] e := by
    apply modelOpenInduction (M := M) body body_open e
    · apply (body_eval z e).mpr
      change d z y ≠ z ∨ (d y z ≠ z ∨ z = y)
      by_cases hy : y = z
      · exact Or.inr (Or.inr hy.symm)
      · right; left
        dsimp only [d]
        rw [modelSubZero]
        exact hy
    · intro t ht
      apply (body_eval (s t) e).mpr
      change d (s t) y ≠ z ∨ (d y (s t) ≠ z ∨ s t = y)
      by_cases h1 : d (s t) y = z
      · by_cases h2 : d y (s t) = z
        · right; right
          have h3 : d t y = z := modelSubSuccZero t y h1
          have hpred : p (d y t) = z := by
            have he := modelSubSucc y t
            change d y (s t) = p (d y t) at he
            exact he.symm.trans h2
          by_cases h4 : d y t = z
          · have ih := (body_eval t e).mp ht
            change d t y ≠ z ∨ (d y t ≠ z ∨ t = y) at ih
            have htEq : t = y := (ih.resolve_left (not_not_intro h3)).resolve_left (not_not_intro h4)
            subst y
            have hh := modelSubAdd t (s z)
            change d (a t (s z)) t = s z at hh
            have ha : a t (s z) = s t := by
              change Structure.func (L := language) addCode ![t,s z] = s t
              rw [modelAddSucc, modelAddZero]
            rw [ha] at hh
            have he : s z = z := hh.symm.trans h1
            exact False.elim (modelSuccNeZero z he)
          · have hex := modelExhaustion (M := M)
            simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
            have hd := (PRAExhaustion.body_eval (d y t) e).mp (hex e (d y t))
            have hs := hd.resolve_left h4
            change s (p (d y t)) = d y t at hs
            rw [hpred] at hs
            have hr := (modelReconstruct t y).resolve_left h4
            change a t (d y t) = y at hr
            rw [←hs] at hr
            change Structure.func (L := language) addCode ![t,s z] = y at hr
            rw [modelAddSucc, modelAddZero] at hr
            exact hr
        · exact Or.inr (Or.inl h2)
      · exact Or.inl h1
  have h := (body_eval x e).mp (hall x)
  change d x y ≠ z ∨ (d y x ≠ z ∨ x = y) at h
  exact (h.resolve_left (not_not_intro hxy)).resolve_left (not_not_intro hyx)

end models
end DiophantineConsistency.PRAEqualityDifference
