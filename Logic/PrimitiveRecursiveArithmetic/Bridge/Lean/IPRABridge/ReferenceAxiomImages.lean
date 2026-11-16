import IPRABridge.Syntax
import DiophantineConsistency.IPRAEqualityOnlyReference

/-! Every axiom of Foundation's equality-only reference theory has an
intuitionistic derivation from the ordinary ConciseIPRA axioms. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder Fm
open DiophantineConsistency
open PRAFiniteFunctionCodes (Code Codes)
open PRATheory (getCode)

private theorem closeConcise {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language n)
    (h : Prf PRAAx [] (toConciseFormula PTm.var Empty.elim φ)) :
    Prf PRAAx [] (toConciseClosed (∀⁰* φ)) := by
  induction n with
  | zero =>
    have hb : (PTm.var : Fin 0 → PTm 0) = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simpa only [toConciseClosed, allClosure_zero, hb] using h
  | succ n ih =>
    rw [allClosure_succ]
    apply ih
    have hb : Syn.up (PTm.var : Fin n → PTm n) = PTm.var := Syn.up_var
    have hf : (fun x : Empty => Syn.shift (Empty.elim x : PTm n)) = Empty.elim :=
      funext (fun x => Empty.elim x)
    simpa only [toConciseFormula, hb, hf] using Prf.allI (Γ := []) h

private theorem code_get {n k : ℕ} : (gs : Codes n k) → (i : Fin k) →
    toConciseCode (getCode gs i) = toConciseCodes gs i
  | .nil _, i => Fin.elim0 i
  | .cons g gs, i => by
    refine Fin.cases rfl (fun j => ?_) i
    simpa only [getCode, toConciseCodes, Fin.cases_succ] using code_get gs j

private theorem term_finCases {k n j : ℕ} (b : Fin n → PTm j)
    (t : IPRAEqualityOnlyReference.TermN n) (ts : Fin k → IPRAEqualityOnlyReference.TermN n) :
    (fun i => toConciseTerm b Empty.elim (Fin.cases t ts i)) =
      Fin.cases (toConciseTerm b Empty.elim t) (fun i => toConciseTerm b Empty.elim (ts i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cases_succ]

private theorem rawZero {n : ℕ} :
    PTm.app .zero (fun i => toConciseTerm PTm.var Empty.elim
      (Fin.elim0 i : IPRAEqualityOnlyReference.TermN n)) = PTm.zero := by
  congr 1
  funext i
  exact Fin.elim0 i

private theorem term_zero {n : ℕ} :
    toConciseTerm PTm.var Empty.elim
      (IPRAEqualityOnlyReference.applyCode (.zero 0) Fin.elim0 : IPRAEqualityOnlyReference.TermN n) =
      PTm.zero :=
  rawZero

private theorem equalImage {n : ℕ} {t u : IPRAEqualityOnlyReference.TermN n}
    (h : Prf PRAAx [] (toConciseTerm PTm.var Empty.elim t ≐
      toConciseTerm PTm.var Empty.elim u)) :
    Prf PRAAx [] (toConciseClosed (IPRAEqualityOnlyReference.equalClosure t u)) :=
  closeConcise _ h

private theorem definingImage {φ : Sentenceᵢ IPRAEqualityOnlyReference.language} (h : IPRAEqualityOnlyReference.DefiningEquation φ) :
    Prf PRAAx [] (toConciseClosed φ) := by
  cases h with
  | zero n =>
    apply equalImage
    cases n with
    | zero =>
      have hleft : toConciseTerm PTm.var Empty.elim
          (IPRAEqualityOnlyReference.applyCode (.zero 0) (IPRAEqualityOnlyReference.vars 0)) =
          (PTm.zero : PTm 0) := by
        change PTm.app .zero _ = PTm.app .zero _
        congr 1
        funext i
        exact Fin.elim0 i
      rw [hleft, term_zero]
      exact Prf.eqRefl _
    | succ n =>
      have hright :
          (fun i : Fin 0 => PTm.app (Fin.elim0 i) (PTm.var : Fin (n + 1) → PTm (n + 1))) =
            Fin.elim0 := funext (fun i => Fin.elim0 i)
      rw [term_zero]
      simpa only [hright, PTm.zero, IPRAEqualityOnlyReference.applyCode,
        IPRAEqualityOnlyReference.vars, toConciseTerm, toConciseCode] using
        PRA.comp (Γ := []) PR.zero (Fin.elim0 : Fin 0 → PR (n + 1)) PTm.var
  | projection i =>
    apply equalImage
    exact PRA.proj i PTm.var
  | composition f gs =>
    apply equalImage
    simpa only [IPRAEqualityOnlyReference.applyCode, IPRAEqualityOnlyReference.vars, toConciseTerm, toConciseCode, code_get]
      using PRA.comp (Γ := []) (toConciseCode f) (toConciseCodes gs) PTm.var
  | recursionBase f g =>
    apply equalImage
    simp only [IPRAEqualityOnlyReference.applyCode, toConciseTerm, toConciseCode,
      term_finCases, rawZero, IPRAEqualityOnlyReference.vars]
    exact PRA.precZero (toConciseCode f) (toConciseCode g) PTm.var
  | recursionStep f g =>
    apply equalImage
    simp only [IPRAEqualityOnlyReference.applyCode, toConciseTerm, toConciseCode, term_finCases]
    exact PRA.precSucc (toConciseCode f) (toConciseCode g) (PTm.var 0)
      (fun i => PTm.var i.succ)

private theorem substImage {n m : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language n)
    (σ : Fin n → IPRAEqualityOnlyReference.TermN m) :
    toConciseFormula PTm.var Empty.elim (Rew.subst σ ▹ φ) =
      (toConciseFormula PTm.var Empty.elim φ).subst
        (fun i => toConciseTerm PTm.var Empty.elim (σ i)) := by
  rw [toConciseFormula_rew, toConciseFormula_subst]
  congr 1
  funext x
  exact Empty.elim x

private theorem substitutionImage {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n + 1)) :
    Prf PRAAx [] (toConciseClosed (IPRAEqualityOnlyReference.eqSubstitution φ)) := by
  apply closeConcise
  change Prf PRAAx [] ((PTm.var 0 ≐ PTm.var 1) ⟶
    toConciseFormula PTm.var Empty.elim (IPRAEqualityOnlyReference.eqLeft φ) ⟶
    toConciseFormula PTm.var Empty.elim (IPRAEqualityOnlyReference.eqRight φ))
  let left : Fin (n + 1) → PTm (n + 2) :=
    fun i => toConciseTerm PTm.var Empty.elim (Fin.cases (.bvar 0) (fun j => .bvar j.succ.succ) i)
  let right : Fin (n + 1) → PTm (n + 2) :=
    fun i => toConciseTerm PTm.var Empty.elim (Fin.cases (.bvar 1) (fun j => .bvar j.succ.succ) i)
  rw [IPRAEqualityOnlyReference.eqLeft, IPRAEqualityOnlyReference.eqRight, substImage, substImage]
  apply Prf.impI
  apply Prf.impI
  refine Prf.eqSubst (toConciseFormula PTm.var Empty.elim φ) left right ?_ Prf.hyp0
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .hyp (by simp [left, right, toConciseTerm])
  · simpa only [left, right, Fin.cases_succ, toConciseTerm] using
      (Prf.eqRefl (Ax := PRAAx) (PTm.var j.succ.succ))

private theorem inductionImage {n : ℕ} (φ : Semisentenceᵢ IPRAEqualityOnlyReference.language (n + 1))
    (hφ : IPRAQuantifierFree.OpenI φ) :
    Prf PRAAx [] (toConciseClosed (IPRAEqualityOnlyReference.inductionAxiom φ)) := by
  let ψ := toConciseFormula PTm.var Empty.elim φ
  apply closeConcise
  have hb : Syn.up (PTm.var : Fin n → PTm n) = PTm.var := Syn.up_var
  have hf : (fun x : Empty => Syn.shift (Empty.elim x : PTm n)) = Empty.elim :=
    funext (fun x => Empty.elim x)
  have hz : toConciseFormula PTm.var Empty.elim (IPRAEqualityOnlyReference.atZero φ) = ψ.subst (Syn.inst PTm.zero) := by
    rw [IPRAEqualityOnlyReference.atZero, substImage]
    congr 1
    rw [term_finCases, term_zero]
    rfl
  have hs : toConciseFormula PTm.var Empty.elim (IPRAEqualityOnlyReference.atSucc φ) =
      ψ.subst (Syn.repl (PTm.succ (PTm.var 0))) := by
    rw [IPRAEqualityOnlyReference.atSucc, substImage]
    congr 1
    rw [term_finCases]
    rfl
  simp only [toConciseFormula, hb, hf, hz, hs]
  exact Prf.axm (PRAAx.ind ψ ((toConcise_open PTm.var Empty.elim φ).2 hφ))

/-- The closed image of each Foundation reference axiom is a ConciseIPRA theorem. -/
theorem referenceAxiomImage (φ : Sentenceᵢ IPRAEqualityOnlyReference.language) (h : IPRAEqualityOnlyReference.ReferenceAxiom φ) :
    Prf PRAAx [] (toConciseClosed φ) := by
  cases h with
  | equality he =>
    cases he with
    | refl => exact closeConcise _ (Prf.eqRefl (PTm.var 0))
    | substitution φ => exact substitutionImage φ
  | defining hd => exact definingImage hd
  | successorNonzero =>
    apply closeConcise
    change Prf PRAAx [] ((PTm.succ (PTm.var 0) ≐
      toConciseTerm PTm.var Empty.elim (IPRAEqualityOnlyReference.applyCode (.zero 0) Fin.elim0)) ⟶ Fm.bot)
    rw [term_zero]
    exact PRA.succNeZero (PTm.var 0)
  | induction φ hφ => exact inductionImage φ hφ

end IPRABridge
