import DiophantineConsistency.PRAAdditionZeroLeft

/-! The left-successor equation for addition in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAdditionSuccLeft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAOpenInduction PRAAdditionZeroLeft

def succLeftBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func addCode ![.func Code.succ (fun _ => .fvar 0), .bvar 0],
      .func Code.succ (fun _ => .func addCode ![.fvar 0, .bvar 0])]

theorem succLeftBody_open : succLeftBody.Open := by
  simp [succLeftBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem succLeftBody_eval (x : M) (e : ℕ → M) : succLeftBody.Eval ![x] e ↔
    Structure.func (L := language) addCode
      ![Structure.func (L := language) Code.succ (fun _ => e 0), x] =
    Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) addCode ![e 0, x]) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] succLeftBody ↔ _
  dsimp only [succLeftBody, Semiformula.EvalAux]
  rw [eqRel]
  have hpair : (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = ![e 0, x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hleft : (Semiterm.val ![x] e ∘
      ![(.func Code.succ (fun _ => .fvar 0) : Semiterm language ℕ 1), .bvar 0]) =
      ![Structure.func (L := language) Code.succ (fun _ => e 0), x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hright : (Semiterm.val ![x] e ∘ fun _ : Fin 1 =>
      (.func addCode ![.fvar 0, .bvar 0] : Semiterm language ℕ 1)) =
      fun _ => Structure.func (L := language) addCode ![e 0, x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) addCode
      (Semiterm.val ![x] e ∘ ![(.fvar 0 : Semiterm language ℕ 1), .bvar 0]) = _
    rw [hpair]
  change Structure.func (L := language) addCode
    (Semiterm.val ![x] e ∘ ![(.func Code.succ (fun _ => .fvar 0) : Semiterm language ℕ 1), .bvar 0]) =
    Structure.func (L := language) Code.succ (Semiterm.val ![x] e ∘ fun _ : Fin 1 =>
      (.func addCode ![.fvar 0, .bvar 0] : Semiterm language ℕ 1)) ↔ _
  rw [hleft, hright]

theorem modelSuccLeft (x y : M) :
    Structure.func (L := language) addCode
      ![Structure.func (L := language) Code.succ (fun _ => x), y] =
    Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) addCode ![x,y]) := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let e : ℕ → M := fun _ => x
  apply (succLeftBody_eval y e).mp
  apply modelOpenInduction (M := M) succLeftBody succLeftBody_open e
  · apply (succLeftBody_eval z e).mpr
    change Structure.func (L := language) addCode ![s x, z] =
      s (Structure.func (L := language) addCode ![x,z])
    rw [modelAddZero, modelAddZero]
  · intro t ht
    apply (succLeftBody_eval (s t) e).mpr
    change Structure.func (L := language) addCode ![s x, s t] =
      s (Structure.func (L := language) addCode ![x,s t])
    rw [modelAddSucc, modelAddSucc, (succLeftBody_eval t e).mp ht]

end models
end DiophantineConsistency.PRAAdditionSuccLeft
