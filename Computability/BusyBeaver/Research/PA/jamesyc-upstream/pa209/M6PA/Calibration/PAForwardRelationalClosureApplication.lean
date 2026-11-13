module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalClosureSyntax
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain value equal PairGraph.orderIso

theorem formula_boundSubst {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0) (x : Term 0) :
    (formula p (bindEnv b) (shiftEnv f))/[x] = formula p (Fin.cases x b) f := by
  simp only [Rewriting.subst, app_eq_rewAux, formula_rew]
  apply formula_env_ext
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [bindEnv, shiftEnv]
  · intro i
    simp [shiftEnv]

theorem guardedImp_subst {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0) (x : Term 0) :
    (Ordinal.domain (.bvar 0) 🡒 formula p (bindEnv b) (shiftEnv f))/[x] =
      Ordinal.domain x 🡒 formula p (Fin.cases x b) f := by
  simp only [Rewriting.subst, app_eq_rewAux, Semiformula.imp_eq, Semiformula.neg_eq,
    Semiformula.rewAux]
  congr 1
  · rw [M6.PA.ForwardRelational.rew_neg, Ordinal.domain_rew]
    simp
  · exact formula_boundSubst p b f x

def formulaAllAt {Γ : List Form} {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0) (x : Term 0)
    (h : ND.Proof Γ (formula (.all p) b f)) (hx : ND.Proof Γ (Ordinal.domain x)) :
    ND.Proof Γ (formula p (Fin.cases x b) f) := by
  have ho := allElim _ x h
  have he := guardedImp_subst p b f x
  rw [he] at ho
  exact mp hx ho

/-- Exact source allClosure elimination. The hypotheses retain each target
domain guard introduced by the source interpretation. -/
def sourceAllClosureElim {Γ : List Form} {n : Nat} (p : SourceFormula n)
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (H : ∀ i, ND.Proof Γ (Ordinal.domain (b i)))
    (h : ND.Proof Γ (formula (∀¹* p) Fin.elim0 f)) : ND.Proof Γ (formula p b f) := by
  induction n generalizing Γ f with
  | zero =>
    convert h using 1
    exact formula_env_ext p b Fin.elim0 f f (fun i => Fin.elim0 i) (fun _ => rfl)
  | succ n ih =>
    have ho := ih (.all p) (fun i => b i.succ) f (fun i => H i.succ) h
    have out := formulaAllAt p _ f (b 0) ho (H 0)
    convert out using 1
    apply formula_env_ext
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · intro i
      rfl

/-- Literal source univCl' application, not closure of an unrelated target
formula. fixitr's bound/free environment is displayed in the conclusion. -/
def sourceUniversalClosureElim {Γ : List Form} (p : SourceFormula 0)
    (b : Fin (0+p.fvSup) → Term 0) (f : Nat → Term 0)
    (H : ∀ i, ND.Proof Γ (Ordinal.domain (b i)))
    (h : ND.Proof Γ (formula p.univCl' Fin.elim0 f)) :
    ND.Proof Γ (formula p Fin.elim0 (fixedEnvironment b f)) := by
  have out := sourceAllClosureElim (Semiformula.rewAux (Rew.fixitr 0 p.fvSup) p) b f H h
  simpa only [formula_sourceFixitr] using out

#print axioms formula_boundSubst
#print axioms guardedImp_subst
#print axioms formulaAllAt
#print axioms sourceAllClosureElim
#print axioms sourceUniversalClosureElim
end M6.PA.ForwardRelational
