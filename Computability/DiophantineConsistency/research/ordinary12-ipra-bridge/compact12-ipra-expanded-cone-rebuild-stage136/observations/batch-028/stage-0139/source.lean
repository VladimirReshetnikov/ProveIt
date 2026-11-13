import Foundation.FirstOrder.Intuitionistic.Rew
import PAHF.PACore

/-! # Ordered-arithmetic syntax in the existing PAHF language

This leaf interprets Foundation's `0,1,+,*,=,<` terms and intuitionistic
formulas in the PAHF `0,S,+,*` syntax. Order is an existential formula with
capture-avoiding shifts. All results are syntax identities; no arithmetic
axiom, proof-calculus transfer, or HA consistency equivalence is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFSyntax
open LO LO.FirstOrder
open scoped LO.FirstOrder
abbrev PTerm := SetTheory.PA.Term
abbrev PFormula := SetTheory.PA.Formula

def termAux {ξ : Type*} {n : ℕ} (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    Semiterm ℒₒᵣ ξ n → PTerm
  | .bvar i => bv i
  | .fvar x => fv x
  | .func .zero _ => .zero
  | .func .one _ => .succ .zero
  | .func .add v => .add (termAux bv fv (v 0)) (termAux bv fv (v 1))
  | .func .mul v => .mul (termAux bv fv (v 0)) (termAux bv fv (v 1))

def liftBound {n : ℕ} (bv : Fin n → PTerm) : Fin (n+1) → PTerm :=
  Fin.cases (.var 0) (fun i => SetTheory.PA.Term.rename Nat.succ (bv i))

def liftFree {ξ : Type*} (fv : ξ → PTerm) : ξ → PTerm :=
  fun x => SetTheory.PA.Term.rename Nat.succ (fv x)

/-- `a < b` means `exists z, a + S z = b`; a and b move under the binder. -/
def ltFormula (a b : PTerm) : PFormula :=
  .ex (.eq (.add (SetTheory.PA.Term.rename Nat.succ a) (.succ (.var 0)))
    (SetTheory.PA.Term.rename Nat.succ b))

def formulaAux {ξ : Type*} {n : ℕ} (bv : Fin n → PTerm) (fv : ξ → PTerm) :
    Semiformulaᵢ ℒₒᵣ ξ n → PFormula
  | .falsum => .bot
  | .rel .eq v => .eq (termAux bv fv (v 0)) (termAux bv fv (v 1))
  | .rel .lt v => ltFormula (termAux bv fv (v 0)) (termAux bv fv (v 1))
  | .and p q => .and (formulaAux bv fv p) (formulaAux bv fv q)
  | .or p q => .or (formulaAux bv fv p) (formulaAux bv fv q)
  | .imp p q => .imp (formulaAux bv fv p) (formulaAux bv fv q)
  | .all p => .all (formulaAux (liftBound bv) (liftFree fv) p)
  | .exs p => .ex (formulaAux (liftBound bv) (liftFree fv) p)

theorem termAux_subst {ξ : Type*} {n : ℕ} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (σ : ℕ → PTerm) (t : Semiterm ℒₒᵣ ξ n) :
    SetTheory.PA.Term.subst σ (termAux bv fv t) =
      termAux (fun i => SetTheory.PA.Term.subst σ (bv i)) (fun x => SetTheory.PA.Term.subst σ (fv x)) t := by
  induction t with
  | bvar => rfl
  | fvar => rfl
  | func f v ih => cases f <;> simp only [termAux, SetTheory.PA.Term.subst, ih]

theorem termAux_rename {ξ : Type*} {n : ℕ} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (r : ℕ → ℕ) (t : Semiterm ℒₒᵣ ξ n) :
    SetTheory.PA.Term.rename r (termAux bv fv t) =
      termAux (fun i => SetTheory.PA.Term.rename r (bv i)) (fun x => SetTheory.PA.Term.rename r (fv x)) t := by
  induction t with
  | bvar => rfl
  | fvar => rfl
  | func f v ih => cases f <;> simp only [termAux, SetTheory.PA.Term.rename, ih]

theorem termAux_rew {ξ ζ : Type*} {n m : ℕ} (bv : Fin m → PTerm) (fv : ζ → PTerm)
    (ω : Rew ℒₒᵣ ξ n ζ m) (t : Semiterm ℒₒᵣ ξ n) :
    termAux bv fv (ω t) =
      termAux (fun i => termAux bv fv (ω (.bvar i)))
        (fun x => termAux bv fv (ω (.fvar x))) t := by
  induction t with
  | bvar => rfl
  | fvar => rfl
  | func f v ih => rw [Rew.func]; cases f <;> simp only [termAux, Function.comp_apply, ih]

theorem subst_ltFormula (σ : ℕ → PTerm) (a b : PTerm) :
    SetTheory.PA.Formula.subst σ (ltFormula a b) = ltFormula (SetTheory.PA.Term.subst σ a) (SetTheory.PA.Term.subst σ b) := by
  simp only [ltFormula, SetTheory.PA.Formula.subst, SetTheory.PA.Term.subst, SetTheory.PA.Term.upSubst,
    SetTheory.PA.Term.subst_rename_succ_up]

theorem subst_liftBound {n : ℕ} (bv : Fin n → PTerm) (σ : ℕ → PTerm) :
    (fun i => SetTheory.PA.Term.subst (SetTheory.PA.Term.upSubst σ) (liftBound bv i)) =
      liftBound (fun i => SetTheory.PA.Term.subst σ (bv i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact SetTheory.PA.Term.subst_rename_succ_up (bv j) σ

theorem subst_liftFree {ξ : Type*} (fv : ξ → PTerm) (σ : ℕ → PTerm) :
    (fun x => SetTheory.PA.Term.subst (SetTheory.PA.Term.upSubst σ) (liftFree fv x)) =
      liftFree (fun x => SetTheory.PA.Term.subst σ (fv x)) := by
  funext x
  exact SetTheory.PA.Term.subst_rename_succ_up (fv x) σ

theorem formulaAux_subst {ξ : Type*} {n : ℕ} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (σ : ℕ → PTerm) (φ : Semiformulaᵢ ℒₒᵣ ξ n) :
    SetTheory.PA.Formula.subst σ (formulaAux bv fv φ) =
      formulaAux (fun i => SetTheory.PA.Term.subst σ (bv i)) (fun x => SetTheory.PA.Term.subst σ (fv x)) φ := by
  induction φ generalizing fv σ with
  | falsum => rfl
  | rel r v => cases r <;> simp only [formulaAux, SetTheory.PA.Formula.subst, subst_ltFormula, termAux_subst]
  | and p q hp hq => simp only [formulaAux, SetTheory.PA.Formula.subst, hp, hq]
  | or p q hp hq => simp only [formulaAux, SetTheory.PA.Formula.subst, hp, hq]
  | imp p q hp hq => simp only [formulaAux, SetTheory.PA.Formula.subst, hp, hq]
  | all p hp => simp only [formulaAux, SetTheory.PA.Formula.subst, hp, subst_liftBound, subst_liftFree]
  | exs p hp => simp only [formulaAux, SetTheory.PA.Formula.subst, hp, subst_liftBound, subst_liftFree]

theorem termAux_bShift {ξ : Type*} {n : ℕ} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (t : Semiterm ℒₒᵣ ξ n) :
    termAux (liftBound bv) (liftFree fv) (Rew.bShift t) =
      SetTheory.PA.Term.rename Nat.succ (termAux bv fv t) := by
  rw [termAux_rew, termAux_rename]
  rfl

theorem formulaAux_rew {ξ ζ : Type*} {n m : ℕ} (bv : Fin m → PTerm) (fv : ζ → PTerm)
    (ω : Rew ℒₒᵣ ξ n ζ m) (φ : Semiformulaᵢ ℒₒᵣ ξ n) :
    formulaAux bv fv (ω ▹ φ) =
      formulaAux (fun i => termAux bv fv (ω (.bvar i)))
        (fun x => termAux bv fv (ω (.fvar x))) φ := by
  induction φ generalizing m fv with
  | falsum => rfl
  | rel r v =>
      rw [Semiformulaᵢ.rew_rel]
      cases r <;> simp only [formulaAux]
      · rw [termAux_rew bv fv ω (v 0), termAux_rew bv fv ω (v 1)]
      · rw [termAux_rew bv fv ω (v 0), termAux_rew bv fv ω (v 1)]
  | and p q hp hq =>
      change SetTheory.PA.Formula.and (formulaAux bv fv (ω ▹ p)) (formulaAux bv fv (ω ▹ q)) = _
      rw [hp, hq]
      rfl
  | or p q hp hq =>
      change SetTheory.PA.Formula.or (formulaAux bv fv (ω ▹ p)) (formulaAux bv fv (ω ▹ q)) = _
      rw [hp, hq]
      rfl
  | imp p q hp hq =>
      change SetTheory.PA.Formula.imp (formulaAux bv fv (ω ▹ p)) (formulaAux bv fv (ω ▹ q)) = _
      rw [hp, hq]
      rfl
  | all p hp =>
      change SetTheory.PA.Formula.all (formulaAux (liftBound bv) (liftFree fv) (ω.q ▹ p)) = _
      rw [hp]
      congr 2
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Rew.q_bvar_zero, termAux, liftBound]
        · simp only [Rew.q_bvar_succ, termAux_bShift, liftBound, Fin.cases_succ]
      · funext x
        simp only [Rew.q_fvar, termAux_bShift, liftFree]
  | exs p hp =>
      change SetTheory.PA.Formula.ex (formulaAux (liftBound bv) (liftFree fv) (ω.q ▹ p)) = _
      rw [hp]
      congr 2
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Rew.q_bvar_zero, termAux, liftBound]
        · simp only [Rew.q_bvar_succ, termAux_bShift, liftBound, Fin.cases_succ]
      · funext x
        simp only [Rew.q_fvar, termAux_bShift, liftFree]

theorem formulaAux_rename {ξ : Type*} {n : ℕ} (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (r : ℕ → ℕ) (φ : Semiformulaᵢ ℒₒᵣ ξ n) :
    SetTheory.PA.Formula.rename r (formulaAux bv fv φ) =
      formulaAux (fun i => SetTheory.PA.Term.rename r (bv i))
        (fun x => SetTheory.PA.Term.rename r (fv x)) φ := by
  rw [← SetTheory.PA.Formula.subst_var_rename, formulaAux_subst]
  simp only [SetTheory.PA.Formula.term_subst_var_rename]

/-- Bound indices occupy `0,...,n-1`; free index `j` occupies `n+j`. -/
def term {n : ℕ} (t : SyntacticSemiterm ℒₒᵣ n) : PTerm :=
  termAux (fun i => .var i.val) (fun j => .var (n+j)) t

def formula {n : ℕ} (φ : Semiformulaᵢ ℒₒᵣ ℕ n) : PFormula :=
  formulaAux (fun i => .var i.val) (fun j => .var (n+j)) φ

/-- Closed Foundation formulas embed with no extra target free variables. -/
def sentence (φ : Sentenceᵢ ℒₒᵣ) : PFormula :=
  formula (Rewriting.emb φ)

theorem liftBound_canonical (n : ℕ) :
    liftBound (fun i : Fin n => .var i.val) = (fun i : Fin (n+1) => .var i.val) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem liftFree_canonical (n : ℕ) :
    liftFree (fun j => .var (n+j)) = (fun j => .var (n+1+j)) := by
  funext j
  simp only [liftFree, SetTheory.PA.Term.rename, Nat.succ_eq_add_one, Nat.add_right_comm]

theorem formula_all {n : ℕ} (φ : Semiformulaᵢ ℒₒᵣ ℕ (n+1)) :
    formula (.all φ) = .all (formula φ) := by
  simp only [formula, formulaAux, liftBound_canonical, liftFree_canonical]

theorem formula_exs {n : ℕ} (φ : Semiformulaᵢ ℒₒᵣ ℕ (n+1)) :
    formula (.exs φ) = .ex (formula φ) := by
  simp only [formula, formulaAux, liftBound_canonical, liftFree_canonical]

/-- Opening the only outer bound variable leaves the target indices unchanged. -/
theorem formula_free (φ : Semiformulaᵢ ℒₒᵣ ℕ 1) :
    formula (Rewriting.free φ) = formula φ := by
  unfold formula
  rw [formulaAux_rew]
  congr 1
  · funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  · funext j
    simp only [Rew.free_fvar, termAux, Nat.zero_add, Nat.add_comm 1 j]

/-- Free-variable shift on an unbound formula is the PAHF eigenvariable shift. -/
theorem formula_shift (φ : Semiformulaᵢ ℒₒᵣ ℕ 0) :
    formula (Rewriting.shift φ) = SetTheory.PA.Formula.rename Nat.succ (formula φ) := by
  unfold formula
  rw [formulaAux_rew, formulaAux_rename]
  congr 1
  · funext i
    exact Fin.elim0 i

/-- Foundation's one-variable instantiation agrees with PAHF's binder removal. -/
theorem formula_inst (φ : Semiformulaᵢ ℒₒᵣ ℕ 1) (t : SyntacticTerm ℒₒᵣ) :
    formula (φ ⇜ (fun _ => t)) =
      SetTheory.PA.Formula.subst (SetTheory.PA.Formula.instTerm (term t)) (formula φ) := by
  unfold formula
  rw [formulaAux_rew, formulaAux_subst]
  congr 1
  · funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  · funext j
    change SetTheory.PA.Term.var (0+j) =
      SetTheory.PA.Formula.instTerm (term t) (1+j)
    rw [Nat.add_comm 1 j]
    simp only [SetTheory.PA.Formula.instTerm, Nat.zero_add]

/-- Reinterpreting an unbound formula below a new binder shifts every free index. -/
theorem formula_empty_subst (φ : Semiformulaᵢ ℒₒᵣ ℕ 0) :
    formula (φ ⇜ (Fin.elim0 : Fin 0 → SyntacticSemiterm ℒₒᵣ 1)) =
      SetTheory.PA.Formula.rename Nat.succ (formula φ) := by
  unfold formula
  rw [formulaAux_rew, formulaAux_rename]
  congr 1
  · funext i
    exact Fin.elim0 i
  · funext j
    change SetTheory.PA.Term.var (1+j) = SetTheory.PA.Term.var (Nat.succ (0+j))
    simp only [Nat.zero_add, Nat.add_comm 1 j, Nat.succ_eq_add_one]

end DiophantineConsistency.FoundationPAHFSyntax
