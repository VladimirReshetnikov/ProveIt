import DiophantineConsistency.PRASubReconstruct
import DiophantineConsistency.PRAQCompatibility

/-! An open-induction invariant relating subtraction of x and succ(x). -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASubSuccessorInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion
  PRAOpenInduction PRASubtraction PRASubReconstruct PRAQCompatibility

private def A : Semiterm language ℕ 1 :=
  .func subCode ![.func Code.succ (fun _ => .fvar 0), .bvar 0]
private def B : Semiterm language ℕ 1 := .func subCode ![.fvar 0, .bvar 0]
private def Z : Semiterm language ℕ 1 := .func (Code.zero 0) Fin.elim0
private def invariantBody : Semiformula language ℕ 1 :=
  (Semiformula.rel Language.ORing.Rel.eq ![A, .func Code.succ (fun _ => B)]) ⋎
  ((Semiformula.rel Language.ORing.Rel.eq ![A,Z]) ⋏
    (Semiformula.rel Language.ORing.Rel.eq ![B,Z]))

theorem invariantBody_open : invariantBody.Open := by simp [invariantBody, Semiformula.Open]

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

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
private theorem val_one {ξ : Type} {n : ℕ} (b : Fin n → M) (f : ξ → M)
    (u : Semiterm language ξ n) :
    (Semiterm.val b f ∘ fun _ : Fin 1 => u) = fun _ => Semiterm.val b f u := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem invariantBody_eval (x : M) (e : ℕ → M) : invariantBody.Eval ![x] e ↔
    Structure.func (L := language) subCode
      ![Structure.func (L := language) Code.succ (fun _ => e 0), x] =
      Structure.func (L := language) Code.succ (fun _ =>
        Structure.func (L := language) subCode ![e 0,x]) ∨
    (Structure.func (L := language) subCode
      ![Structure.func (L := language) Code.succ (fun _ => e 0), x] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0 ∧
     Structure.func (L := language) subCode ![e 0,x] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] invariantBody ↔ _
  dsimp only [invariantBody, Semiformula.EvalAux]
  rw [eqRel, eqRel, eqRel]
  have hz : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    A, B, Z, Semiterm.val_func, Semiterm.val_bvar, Semiterm.val_fvar, val_pair, val_one, hz]

theorem modelSubSuccessorInvariant (x y : M) :
    Structure.func (L := language) subCode
      ![Structure.func (L := language) Code.succ (fun _ => x), y] =
      Structure.func (L := language) Code.succ (fun _ =>
        Structure.func (L := language) subCode ![x,y]) ∨
    (Structure.func (L := language) subCode
      ![Structure.func (L := language) Code.succ (fun _ => x), y] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0 ∧
     Structure.func (L := language) subCode ![x,y] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0) := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let p : M → M := fun x => Structure.func (L := language) predCode (fun _ => x)
  let d : M → M → M := fun x y => Structure.func (L := language) subCode ![x,y]
  let e : ℕ → M := fun _ => x
  apply (invariantBody_eval y e).mp
  apply modelOpenInduction (M := M) invariantBody invariantBody_open e
  · apply (invariantBody_eval z e).mpr
    change d (s x) z = s (d x z) ∨ (d (s x) z = z ∧ d x z = z)
    left
    dsimp only [d]
    rw [modelSubZero, modelSubZero]
  · intro t ht
    apply (invariantBody_eval (s t) e).mpr
    change d (s x) (s t) = s (d x (s t)) ∨
      (d (s x) (s t) = z ∧ d x (s t) = z)
    have hu : d (s x) (s t) = p (d (s x) t) := modelSubSucc (s x) t
    have hv : d x (s t) = p (d x t) := modelSubSucc x t
    rw [hu,hv]
    have ih := (invariantBody_eval t e).mp ht
    change d (s x) t = s (d x t) ∨ (d (s x) t = z ∧ d x t = z) at ih
    rcases ih with ih | ⟨ih1,ih2⟩
    · rw [ih]
      have hp : p (s (d x t)) = d x t := modelPredSucc _
      rw [hp]
      have hex := modelExhaustion (M := M)
      simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hex
      rcases (body_eval (d x t) e).mp (hex e (d x t)) with he | he
      · right
        rw [he]
        exact ⟨rfl, modelPredZero⟩
      · exact Or.inl he.symm
    · right
      rw [ih1,ih2]
      exact ⟨modelPredZero,modelPredZero⟩

theorem modelSubSuccZero (x y : M)
    (h : Structure.func (L := language) subCode
      ![Structure.func (L := language) Code.succ (fun _ => x), y] =
        Structure.func (L := language) (Code.zero 0) Fin.elim0) :
    Structure.func (L := language) subCode ![x,y] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  rcases modelSubSuccessorInvariant x y with hs | ⟨_, hz⟩
  · have he := hs.symm.trans h
    exact False.elim (modelSuccNeZero _ he)
  · exact hz

end models
end DiophantineConsistency.PRASubSuccessorInvariant
