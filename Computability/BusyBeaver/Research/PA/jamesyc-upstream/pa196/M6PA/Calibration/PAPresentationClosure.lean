module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationRewriting
@[expose] public section

/-! Preservation of free parameters and exact universal closure. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

@[simp] theorem term_freeVariables {ξ : Type} [DecidableEq ξ] {n : Nat}
    (t : ArithmeticSemiterm ξ n) : (term t).freeVariables = t.freeVariables := by
  induction t with
  | bvar i | fvar i => rfl
  | func f ts ih =>
    cases f <;> simp [term,zero,succ,add,mul,Semiterm.freeVariables_func,Fin.univ_succ,ih]

@[simp] theorem bShift_freeVariables {ξ : Type} [DecidableEq ξ] {n : Nat}
    (t : Semiterm language ξ n) : (Rew.bShift t).freeVariables = t.freeVariables := by
  ext x
  exact Semiterm.fvar?_bShift

@[simp] theorem formula_freeVariables {ξ : Type} [DecidableEq ξ] {n : Nat}
    (p : ArithmeticSemiformula ξ n) : (formula p).freeVariables = p.freeVariables := by
  induction p with
  | verum | falsum => rfl
  | rel r ts | nrel r ts =>
    cases r <;> simp [formula,atom,eq,less,add,succ,Semiformula.neg,Semiformula.freeVariables,Semiformula.freeVariables_rel,
      Semiformula.freeVariables_nrel,Semiterm.freeVariables_func,Fin.univ_succ]
  | and p q ihp ihq | or p q ihp ihq => simp [formula,Semiformula.freeVariables,ihp,ihq]
  | all p ih | exs p ih => simp [formula,Semiformula.freeVariables,ih]

@[simp] theorem formula_fvSup {n : Nat} (p : ArithmeticSemiproposition n) :
    (formula p).fvSup = p.fvSup := by simp [Semiformula.fvSup]

@[simp] theorem translateRew_fixitr (n k : Nat) :
    translateRew (Rew.fixitr (L := ℒₒᵣ) n k) = Rew.fixitr (L := language) n k := by
  apply Rew.ext
  · intro i
    change term ((Rew.fixitr (L := ℒₒᵣ) n k) (.bvar i)) = (Rew.fixitr n k) (.bvar i)
    rw [Rew.fixitr_bvar,Rew.fixitr_bvar]; rfl
  · intro i
    change term ((Rew.fixitr (L := ℒₒᵣ) n k) (.fvar i)) = (Rew.fixitr n k) (.fvar i)
    rw [Rew.fixitr_fvar,Rew.fixitr_fvar]
    split <;> rfl

@[simp] theorem formula_allClosure {ξ : Type} {n : Nat} (p : ArithmeticSemiformula ξ n) :
    formula (∀¹* p) = ∀¹* (formula p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allClosure_succ,ih,formula]; rfl

@[simp] theorem formula_univCl' (p : ArithmeticProposition) :
    formula p.univCl' = (formula p).univCl' := by
  change formula (∀¹* Semiformula.rewAux (Rew.fixitr 0 p.fvSup) p) =
    ∀¹* Semiformula.rewAux (Rew.fixitr 0 (formula p).fvSup) (formula p)
  rw [formula_allClosure,formula_rew,translateRew_fixitr,formula_fvSup]


#print axioms formula_univCl'
end M6.PA.Presentation
