import DiophantineConsistency.PRASubAddition

/-! Reconstructing a number from a nonzero difference in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASubReconstruct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAExhaustion
  PRAOpenInduction PRAAdditionZeroLeft PRAAdditionSuccLeft PRASubtraction

def reconstructBody : Semiformula language ℕ 1 :=
  (Semiformula.rel Language.ORing.Rel.eq
    ![.func subCode ![.fvar 0, .bvar 0], .func (Code.zero 0) Fin.elim0]) ⋎
  (Semiformula.rel Language.ORing.Rel.eq
    ![.func addCode ![.bvar 0, .func subCode ![.fvar 0, .bvar 0]], .fvar 0])

theorem reconstructBody_open : reconstructBody.Open := by
  simp [reconstructBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem reconstructBody_eval (x : M) (e : ℕ → M) : reconstructBody.Eval ![x] e ↔
    Structure.func (L := language) subCode ![e 0,x] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) subCode ![e 0,x]] = e 0 := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] reconstructBody ↔ _
  dsimp only [reconstructBody, Semiformula.EvalAux]
  rw [eqRel, eqRel]
  have hz : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hp : (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = ![e 0,x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hq : (Semiterm.val ![x] e ∘
      ![(.bvar 0 : Semiterm language ℕ 1), .func subCode ![.fvar 0, .bvar 0]]) =
      ![x, Structure.func (L := language) subCode ![e 0,x]] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    change Structure.func (L := language) subCode
      (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = _
    rw [hp]
    rfl
  change (Structure.func (L := language) subCode
      (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) =
      Structure.func (L := language) (Code.zero 0)
        (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) ∨
    Structure.func (L := language) addCode (Semiterm.val ![x] e ∘
      ![(.bvar 0 : Semiterm language ℕ 1), .func subCode ![.fvar 0, .bvar 0]]) = e 0) ↔ _
  rw [hz, hp, hq]

theorem modelPredZero : Structure.func (L := language) predCode
    (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0 : Fin 1 → M) =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (Code.zero 0) (Code.proj (0 : Fin 2)) Fin.elim0
  simpa [predCode, Matrix.fun_eq_vec_one] using h

theorem modelReconstruct (x y : M) :
    Structure.func (L := language) subCode ![y,x] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 ∨
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) subCode ![y,x]] = y := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let p : M → M := fun x => Structure.func (L := language) predCode (fun _ => x)
  let d : M → M := fun x => Structure.func (L := language) subCode ![y,x]
  let a : M → M → M := fun x y => Structure.func (L := language) addCode ![x,y]
  let e : ℕ → M := fun _ => y
  apply (reconstructBody_eval x e).mp
  apply modelOpenInduction (M := M) reconstructBody reconstructBody_open e
  · apply (reconstructBody_eval z e).mpr
    right
    change a z (d z) = y
    dsimp only [d, a]
    rw [modelSubZero, modelZeroLeft]
  · intro t ht
    apply (reconstructBody_eval (s t) e).mpr
    change d (s t) = z ∨ a (s t) (d (s t)) = y
    have hds : d (s t) = p (d t) := modelSubSucc y t
    rw [hds]
    by_cases hp : p (d t) = z
    · exact Or.inl hp
    · right
      have hdt : d t ≠ z := by
        intro hh
        apply hp
        rw [hh]
        exact modelPredZero
      have ih : a t (d t) = y := by
        have hh := (reconstructBody_eval t e).mp ht
        exact hh.resolve_left hdt
      have hex := modelExhaustion (M := M)
      simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
      have h := (body_eval (d t) e).mp (hex e (d t))
      have hsucc : s (p (d t)) = d t := h.resolve_left hdt
      change Structure.func (L := language) addCode ![s t, p (d t)] = y
      rw [modelSuccLeft, ←modelAddSucc, hsucc]
      exact ih

end models
end DiophantineConsistency.PRASubReconstruct
