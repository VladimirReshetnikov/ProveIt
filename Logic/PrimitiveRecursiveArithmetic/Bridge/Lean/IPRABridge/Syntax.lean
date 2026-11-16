import ConciseIPRA.PR
import DiophantineConsistency.IPRAEqualityOnlyReference

/-! Translations of primitive-recursive symbols, terms and formulas between
Foundation's equality-only reference language and ordinary ConciseIPRA. -/

set_option autoImplicit false

namespace IPRABridge

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open DiophantineConsistency
open PRAFiniteFunctionCodes (Code Codes pack)
open IPRAEqualityOnlyReference (EqualityRel language TermN)

mutual
  /-- Read a finite construction code as a ConciseIPRA function symbol. -/
  def toConciseCode : {n : ℕ} → Code n → PR n
    | _, .zero 0 => .zero
    | _, .zero (_ + 1) => .comp .zero Fin.elim0
    | _, .succ => .succ
    | _, .proj i => .proj i
    | _, .comp f gs => .comp (toConciseCode f) (toConciseCodes gs)
    | _, .prec f g => .prec (toConciseCode f) (toConciseCode g)

  def toConciseCodes : {n k : ℕ} → Codes n k → Fin k → PR n
    | _, _, .nil _, i => Fin.elim0 i
    | _, _, .cons f fs, i => Fin.cases (toConciseCode f) (toConciseCodes fs) i
end

/-- Use Foundation's finite tuples for the arguments of a composition. -/
def toFoundationCode : {n : ℕ} → PR n → Code n
  | _, .zero => .zero 0
  | _, .succ => .succ
  | _, .proj i => .proj i
  | _, .comp f gs => .comp (toFoundationCode f) (pack _ (fun i => toFoundationCode (gs i)))
  | _, .prec f g => .prec (toFoundationCode f) (toFoundationCode g)

theorem toConciseCodes_pack {n : ℕ} (k : ℕ) (gs : Fin k → Code n) :
    toConciseCodes (pack k gs) = fun i => toConciseCode (gs i) := by
  induction k with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun j => gs j.succ)) j

@[simp] theorem code_roundtrip {n : ℕ} (f : PR n) :
    toConciseCode (toFoundationCode f) = f := by
  induction f with
  | zero | succ | proj => rfl
  | comp f gs ih hgs =>
    simp only [toFoundationCode, toConciseCode, toConciseCodes_pack, ih, hgs]
  | prec f g ihf ihg => simp only [toFoundationCode, toConciseCode, ihf, ihg]

variable {ξ ζ : Type} {k l n m : ℕ}

/-- Read both kinds of Foundation variables in one ConciseIPRA scope. -/
def toConciseTerm (bound : Fin k → PTm n) (free : ξ → PTm n) :
    Semiterm language ξ k → PTm n
  | .bvar i => bound i
  | .fvar x => free x
  | .func c ts => .app (toConciseCode c) (fun i => toConciseTerm bound free (ts i))

def toConciseFormula : {k n : ℕ} → (Fin k → PTm n) → (ξ → PTm n) →
    Semiformulaᵢ language ξ k → Fm PTm n
  | _, _, _, _, .falsum => .bot
  | _, _, b, f, .rel (EqualityRel.eq) ts =>
      .eq (toConciseTerm b f (ts 0)) (toConciseTerm b f (ts 1))
  | _, _, b, f, .and φ ψ => .and (toConciseFormula b f φ) (toConciseFormula b f ψ)
  | _, _, b, f, .or φ ψ => .or (toConciseFormula b f φ) (toConciseFormula b f ψ)
  | _, _, b, f, .imp φ ψ => .imp (toConciseFormula b f φ) (toConciseFormula b f ψ)
  | _, _, b, f, .all φ => .all (toConciseFormula (Syn.up b) (fun x => Syn.shift (f x)) φ)
  | _, _, b, f, .exs φ => .ex (toConciseFormula (Syn.up b) (fun x => Syn.shift (f x)) φ)

def toConciseClosed (φ : Sentenceᵢ language) : Fm PTm 0 :=
  toConciseFormula Fin.elim0 Empty.elim φ

def toFoundationTerm : PTm n → TermN n
  | .var i => .bvar i
  | .app f ts => .func (toFoundationCode f) (fun i => toFoundationTerm (ts i))

def toFoundation : {n : ℕ} → Fm PTm n → Semisentenceᵢ language n
  | _, .eq t u => .rel EqualityRel.eq ![toFoundationTerm t, toFoundationTerm u]
  | _, .bot => .falsum
  | _, .and φ ψ => .and (toFoundation φ) (toFoundation ψ)
  | _, .or φ ψ => .or (toFoundation φ) (toFoundation ψ)
  | _, .imp φ ψ => .imp (toFoundation φ) (toFoundation ψ)
  | _, .all φ => .all (toFoundation φ)
  | _, .ex φ => .exs (toFoundation φ)

theorem toConciseTerm_subst (b : Fin k → PTm n) (f : ξ → PTm n) (σ : Fin n → PTm m)
    (t : Semiterm language ξ k) :
    Syn.subst σ (toConciseTerm b f t) =
      toConciseTerm (fun i => Syn.subst σ (b i)) (fun x => Syn.subst σ (f x)) t := by
  induction t with
  | bvar | fvar => rfl
  | func c ts ih => simp only [toConciseTerm, PTm.subst_app, ih]

private theorem subst_up_shift (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]
  congr 1

theorem toConciseFormula_subst (b : Fin k → PTm n) (f : ξ → PTm n) (σ : Fin n → PTm m)
    (φ : Semiformulaᵢ language ξ k) :
    (toConciseFormula b f φ).subst σ =
      toConciseFormula (fun i => Syn.subst σ (b i)) (fun x => Syn.subst σ (f x)) φ := by
  induction φ using Semiformulaᵢ.rec' generalizing n m
  case hRel r ts =>
    cases r
    simp only [toConciseFormula, Fm.subst_eq, toConciseTerm_subst]
  all_goals
    simp only [toConciseFormula, Fm.subst, *, Syn.up_comp, subst_up_shift]

theorem toConciseTerm_rew (r : Rew language ξ k ζ l) (b : Fin l → PTm n)
    (f : ζ → PTm n) (t : Semiterm language ξ k) :
    toConciseTerm b f (r t) =
      toConciseTerm (fun i => toConciseTerm b f (r (.bvar i)))
        (fun x => toConciseTerm b f (r (.fvar x))) t := by
  induction t with
  | bvar | fvar => rfl
  | func c ts ih => simp only [Rew.func', toConciseTerm, ih]

private theorem toConciseTerm_bShift (b : Fin k → PTm n) (f : ξ → PTm n)
    (t : Semiterm language ξ k) :
    toConciseTerm (Syn.up b) (fun x => Syn.shift (f x)) (Rew.bShift t) =
      Syn.shift (toConciseTerm b f t) := by
  rw [toConciseTerm_rew, Syn.shift, toConciseTerm_subst]
  simp only [Rew.bShift_bvar, Rew.bShift_fvar, toConciseTerm, Syn.up_succ]
  rfl

theorem toConciseFormula_rew (r : Rew language ξ k ζ l) (b : Fin l → PTm n)
    (f : ζ → PTm n) (φ : Semiformulaᵢ language ξ k) :
    toConciseFormula b f (r ▹ φ) =
      toConciseFormula (fun i => toConciseTerm b f (r (.bvar i)))
        (fun x => toConciseTerm b f (r (.fvar x))) φ := by
  induction φ using Semiformulaᵢ.rec' generalizing l n
  case hRel rel ts =>
    cases rel
    simp only [Semiformulaᵢ.rew_rel, toConciseFormula]
    congr 1 <;> apply toConciseTerm_rew
  case hFalsum => rfl
  case hAnd φ ψ ihφ ihψ => simp only [LogicalConnective.HomClass.map_and, toConciseFormula, ihφ, ihψ]
  case hOr φ ψ ihφ ihψ => simp only [LogicalConnective.HomClass.map_or, toConciseFormula, ihφ, ihψ]
  case hImp φ ψ ihφ ihψ => simp only [LogicalConnective.HomClass.map_imply, toConciseFormula, ihφ, ihψ]
  case hAll φ ih =>
    simp only [Rewriting.app_all, toConciseFormula, ih]
    congr 2
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [toConciseTerm]
      · simp [toConciseTerm_bShift]
    · funext x
      simp [toConciseTerm_bShift]
  case hExs φ ih =>
    simp only [Rewriting.app_exs, toConciseFormula, ih]
    congr 2
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [toConciseTerm]
      · simp [toConciseTerm_bShift]
    · funext x
      simp [toConciseTerm_bShift]

theorem toFoundationTerm_subst (σ : Fin n → PTm m) (t : PTm n) :
    toFoundationTerm (Syn.subst σ t) =
      Rew.subst (fun i => toFoundationTerm (σ i)) (toFoundationTerm t) := by
  induction t with
  | var i => simp [toFoundationTerm]
  | app f ts ih => simp only [PTm.subst_app, toFoundationTerm, Rew.func', ih]

theorem toFoundationTerm_shift (t : PTm n) :
    toFoundationTerm (Syn.shift t) = Rew.bShift (toFoundationTerm t) := by
  rw [Syn.shift, toFoundationTerm_subst]
  rfl

private theorem toFoundation_subst_up (σ : Fin n → PTm m) :
    (Rew.subst (fun i => toFoundationTerm (σ i))).q =
      Rew.subst (fun i => toFoundationTerm (Syn.up σ i)) := by
  apply Rew.ext
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [toFoundationTerm_shift]
  · intro x
    exact Empty.elim x

theorem toFoundation_subst (φ : Fm PTm n) (σ : Fin n → PTm m) :
    toFoundation (φ.subst σ) =
      Rew.subst (fun i => toFoundationTerm (σ i)) ▹ toFoundation φ := by
  induction φ generalizing m with
  | eq t u =>
    simp only [Fm.subst, toFoundation, Semiformulaᵢ.rew_rel, toFoundationTerm_subst]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => Fin.elim0 j) j
  | bot => rfl
  | and φ ψ ihφ ihψ =>
    simp only [Fm.subst, toFoundation, ihφ, ihψ]
    rfl
  | or φ ψ ihφ ihψ =>
    simp only [Fm.subst, toFoundation, ihφ, ihψ]
    rfl
  | imp φ ψ ihφ ihψ =>
    simp only [Fm.subst, toFoundation, ihφ, ihψ]
    rfl
  | all φ ih =>
    simp only [Fm.subst, toFoundation, ← toFoundation_subst_up, ih]
    rfl
  | ex φ ih =>
    simp only [Fm.subst, toFoundation, ← toFoundation_subst_up, ih]
    rfl

theorem toConcise_open (b : Fin k → PTm n) (f : ξ → PTm n)
    (φ : Semiformulaᵢ language ξ k) :
    (toConciseFormula b f φ).QF ↔ IPRAQuantifierFree.OpenI φ := by
  induction φ using Semiformulaᵢ.rec' generalizing n
  case hRel r ts => cases r; rfl
  all_goals simp [toConciseFormula, Fm.QF, IPRAQuantifierFree.OpenI, *]

theorem toFoundation_open (φ : Fm PTm n) :
    IPRAQuantifierFree.OpenI (toFoundation φ) ↔ φ.QF := by
  induction φ <;> simp [toFoundation, IPRAQuantifierFree.OpenI, Fm.QF, *]

@[simp] theorem term_roundtrip (t : PTm n) :
    toConciseTerm PTm.var Empty.elim (toFoundationTerm t) = t := by
  induction t with
  | var => rfl
  | app f ts ih => simp only [toFoundationTerm, toConciseTerm, code_roundtrip, ih]

@[simp] theorem formula_roundtrip (φ : Fm PTm n) :
    toConciseFormula PTm.var Empty.elim (toFoundation φ) = φ := by
  have h : ∀ j : ℕ, (fun x : Empty => Syn.shift (Empty.elim x : PTm j)) =
      (Empty.elim : Empty → PTm (j + 1)) := fun _ => funext (fun x => Empty.elim x)
  have hup : ∀ j : ℕ, Syn.up (PTm.var : Fin j → PTm j) = PTm.var :=
    fun _ => Syn.up_var
  induction φ <;> simp [toFoundation, toConciseFormula, *]

end IPRABridge
