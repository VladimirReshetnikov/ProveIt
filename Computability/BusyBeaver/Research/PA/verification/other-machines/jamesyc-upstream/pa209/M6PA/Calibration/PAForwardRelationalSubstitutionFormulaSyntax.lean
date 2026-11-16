module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalSubstitutionLift
public import M6PA.Calibration.RelationalFormulaCongruence
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain value equal PairGraph.orderIso

theorem formula_shift {n : Nat} (p : SourceFormula n)
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    (formula p b f).shift = formula p (freeShiftEnv b) (freeShiftEnv f) :=
  formula_rew p Rew.shift b f

theorem formula_boundFree {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    (formula p (bindEnv b) (shiftEnv f)).free =
      formula p (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f) := by
  simp only [Semiformula.free, Rewriting.free, app_eq_rewAux, formula_rew]
  apply formula_env_ext
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [bindEnv, shiftEnv, freeShiftEnv]
  · intro i
    simp [shiftEnv, freeShiftEnv]

theorem guardedBody_free {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    (Ordinal.domain (.bvar 0) ⋏ formula p (bindEnv b) (shiftEnv f)).free =
      Ordinal.domain (.fvar 0) ⋏ formula p (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f) := by
  simp only [Semiformula.free, Rewriting.free, app_eq_rewAux, Semiformula.rewAux,
    Ordinal.domain_rew]
  congr 1
  exact formula_boundFree p b f

theorem guardedImp_free {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    (Ordinal.domain (.bvar 0) 🡒 formula p (bindEnv b) (shiftEnv f)).free =
      Ordinal.domain (.fvar 0) 🡒 formula p (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f) := by
  simp only [Semiformula.free, Rewriting.free, app_eq_rewAux, Semiformula.imp_eq,
    Semiformula.neg_eq, Semiformula.rewAux, Semiformula.rewAux_neg, Ordinal.domain_rew]
  congr 1
  · rw [M6.PA.ForwardRelational.rew_neg, Ordinal.domain_rew]
    rfl
  · exact formula_boundFree p b f

def formulaAllOpen {Γ : List Form} {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (h : ND.Proof Γ (formula (.all p) b f)) :
    ND.Proof (shifted Γ) (Ordinal.domain (.fvar 0) 🡒
      formula p (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f)) := by
  have hs := shiftProof h
  have hs' : ND.Proof (shifted Γ) (.all
      (Ordinal.domain (.bvar 0) 🡒 formula p (bindEnv b) (shiftEnv f)).shift) := by
    convert hs using 1 <;> simp only [formula, Semiformula.shift, Rewriting.shift,
      app_eq_rewAux, Semiformula.rewAux, Rew.q_shift] <;> rfl
  have ho := allElim _ (.fvar 0) hs' 
  have he : ((Ordinal.domain (.bvar 0) 🡒 formula p (bindEnv b) (shiftEnv f)).shift/[.fvar 0]) =
      (Ordinal.domain (.bvar 0) 🡒 formula p (bindEnv b) (shiftEnv f)).free :=
    RelationalSource.open_shifted _
  rw [he] at ho
  simpa only [guardedImp_free] using ho

def formulaAllIntro {Γ : List Form} {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (h : ND.Proof (Ordinal.domain (.fvar 0) :: shifted Γ)
      (formula p (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f))) :
    ND.Proof Γ (formula (.all p) b f) := by
  apply allIntro
  simpa only [guardedImp_free] using impIntro h

def formulaExistsElim {Γ : List Form} {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0) (q : Form)
    (h : ND.Proof Γ (formula (.exs p) b f))
    (k : ND.Proof ((Ordinal.domain (.fvar 0) ⋏
      formula p (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f)) :: shifted Γ) q.shift) :
    ND.Proof Γ q := by
  apply exsElim h
  simpa only [guardedBody_free] using k

def formulaExistsFresh {Δ : List Form} {n : Nat} (p : SourceFormula (n+1))
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (h : ND.Proof Δ (Ordinal.domain (.fvar 0) ⋏
      formula p (Fin.cases (.fvar 0) (freeShiftEnv b)) (freeShiftEnv f))) :
    ND.Proof Δ (formula (.exs p) b f).shift := by
  have hf : ND.Proof Δ ((Ordinal.domain (.bvar 0) ⋏ formula p (bindEnv b) (shiftEnv f)).shift/[.fvar 0]) := by
    have he : ((Ordinal.domain (.bvar 0) ⋏ formula p (bindEnv b) (shiftEnv f)).shift/[.fvar 0]) =
        (Ordinal.domain (.bvar 0) ⋏ formula p (bindEnv b) (shiftEnv f)).free :=
      RelationalSource.open_shifted _
    rw [he]
    simpa only [guardedBody_free] using h
  have out := exsIntro _ (.fvar 0) hf
  convert out using 1 <;> simp only [formula, Semiformula.shift, Rewriting.shift,
    app_eq_rewAux, Semiformula.rewAux, Rew.q_shift] <;> rfl

#print axioms formula_shift
#print axioms formula_boundFree
#print axioms guardedBody_free
#print axioms guardedImp_free
#print axioms formulaAllOpen
#print axioms formulaAllIntro
#print axioms formulaExistsElim
#print axioms formulaExistsFresh
end M6.PA.ForwardRelational
