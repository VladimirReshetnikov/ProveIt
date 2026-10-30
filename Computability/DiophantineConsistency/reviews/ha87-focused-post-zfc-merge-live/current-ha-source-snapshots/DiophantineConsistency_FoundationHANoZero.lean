import DiophantineConsistency.FoundationHAClosure
import DiophantineConsistency.ArithmeticExpression
import DiophantineConsistency.HANegativeStability

/-! # A classical source sentence for the literal HA no-zero compiler

Successor is reflected as addition of one and connected to the original
term by a genuine HA equality proof. The source uses exactly the specified
number of bound variables and a negative equality atom. Its existing GG
image and the existing arithmetic no-zero sentence have HA proofs of both
implications. No proof of either no-zero sentence is assumed or supplied.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHANoZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax

/-- Explicit variable environments avoid any free/bound index identification. -/
def reflectTerm {ξ : Type*} {n : ℕ} (v : ℕ → Semiterm ℒₒᵣ ξ n) :
    Term → Semiterm ℒₒᵣ ξ n
  | .var i => v i
  | .zero => .func .zero Fin.elim0
  | .succ t => .func .add ![reflectTerm v t, .func .one Fin.elim0]
  | .add s t => .func .add ![reflectTerm v s, reflectTerm v t]
  | .mul s t => .func .mul ![reflectTerm v s, reflectTerm v t]

/-- Structural recursion constructs actual HA proofs; it does not use term
evaluation or infer derivability from a standard arithmetic identity. -/
theorem reflectTerm_correct {ξ : Type*} {n : ℕ}
    (bv : Fin n → Term) (fv : ξ → Term) (v : ℕ → Semiterm ℒₒᵣ ξ n)
    (t : Term) : Proves (.eq (termAux bv fv (reflectTerm v t))
      (Term.subst (fun i => termAux bv fv (v i)) t)) := by
  induction t with
  | var i => exact Relative.eq_refl _
  | zero => exact Relative.eq_refl _
  | succ t ih =>
      exact (ih.eq_add_left (.succ .zero)).eq_trans (Arithmetic.add_one _)
  | add s t ihs iht =>
      exact (ihs.eq_add_left _).eq_trans (iht.eq_add_right _)
  | mul s t ihs iht =>
      exact (ihs.eq_mul_left _).eq_trans (iht.eq_mul_right _)

/-- Out-of-range slots are explicitly zero. Correctness below uses the actual
free-variable bound of the supplied term, not a surjectivity assumption. -/
def slot (n i : ℕ) : Semiterm ℒₒᵣ Empty n :=
  if h : i < n then .bvar ⟨i, h⟩ else .func .zero Fin.elim0

def sourceTerm (n : ℕ) (t : Term) : Semiterm ℒₒᵣ Empty n :=
  reflectTerm (slot n) t

def translatedTerm (n : ℕ) (t : Term) : Term :=
  term (Rew.emb (ξ := ℕ) (sourceTerm n t))

theorem term_emb_empty {n : ℕ} (t : Semiterm ℒₒᵣ Empty n) :
    term (Rew.emb (ξ := ℕ) t) =
      termAux (fun i => .var i.val) Empty.elim t := by
  unfold term
  rw [termAux_rew]
  congr 1
  funext x
  exact Empty.elim x

theorem translatedTerm_correct (n : ℕ) (t : Term)
    (ht : ∀ k, Term.Free k t → k < n) : Proves (.eq (translatedTerm n t) t) := by
  have hp := reflectTerm_correct (fun i : Fin n => Term.var i.val)
    (Empty.elim : Empty → Term) (slot n) t
  have he : Term.subst
      (fun i => termAux (fun j : Fin n => Term.var j.val) Empty.elim (slot n i)) t = t := by
    calc
      _ = Term.subst Term.var t := by
        apply Term.subst_ext_free
        intro k hk
        simp only [slot, dif_pos (ht k hk), termAux]
      _ = t := Term.subst_id t
  change Proves (.eq
    (termAux (fun i : Fin n => Term.var i.val) Empty.elim (sourceTerm n t)) _) at hp
  rw [he] at hp
  simpa only [translatedTerm, term_emb_empty] using hp

/-- This includes all odd binary-numeral successor branches, without reducing
the numeral or introducing its unary value. -/
theorem binaryNumeral_correct (n k : ℕ) :
    Proves (.eq (translatedTerm n (ArithmeticExpression.binaryNumeral k))
      (ArithmeticExpression.binaryNumeral k)) :=
  translatedTerm_correct n _ (fun i hi =>
    False.elim (ArithmeticExpression.binaryNumeral_closed k i hi))

theorem expressionTerm_correct {n : ℕ} (e : NatExpr (Fin n)) :
    Proves (.eq (translatedTerm n (ArithmeticExpression.term Fin.val e))
      (ArithmeticExpression.term Fin.val e)) := by
  apply translatedTerm_correct
  intro k hk
  obtain ⟨i, rfl⟩ := ArithmeticExpression.free_term e Fin.val k hk
  exact i.isLt

/-- Exactly n quantifiers and no free variables, including when n is zero. -/
def classicalNoZero {n : ℕ} (e : Expr (Fin n)) : Sentence ℒₒᵣ :=
  ∀⁰* (Semiformula.nrel .eq
    ![sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1),
      sourceTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2)])

def reflectedEquation {n : ℕ} (e : Expr (Fin n)) : Formula :=
  .eq (translatedTerm n (ArithmeticExpression.term Fin.val e.splitNatural.1))
    (translatedTerm n (ArithmeticExpression.term Fin.val e.splitNatural.2))

/-- Literal source GG comparison: a negative equality gets one negation. -/
theorem translated_classicalNoZero {n : ℕ} (e : Expr (Fin n)) :
    sentence (classicalNoZero e)ᴺ = Formula.closeN n (neg (reflectedEquation e)) := by
  unfold classicalNoZero sentence
  rw [Semiformula.emb_doubleNegation, Rewriting.emb_allClosure,
    FoundationHAClosure.doubleNegation_allClosure,
    FoundationHAClosure.formula_allClosure]
  rfl

/-- Universal implication uses a fresh variable and the entire shifted
assumption list; it is valid for arbitrary open formulas. -/
theorem all_imp {a b : Formula} (h : Proves (.imp a b)) :
    Proves (.imp (.all a) (.all b)) := by
  apply Relative.imp_intro
  apply Relative.all_intro Formula.Ax_s_sentences
  have hs : Relative Formula.Ax_s ([Formula.all a].map (Formula.rename Nat.succ))
      (Formula.rename Nat.succ (.all a)) := relative_of_derives (.ass _ _ List.mem_cons_self)
  have ha := Relative.all_elim (.var 0) hs
  have hb : Relative Formula.Ax_s ([Formula.all a].map (Formula.rename Nat.succ)) a := by
    simpa only [Formula.rename, Formula.subst_instTerm_var_zero_rename_up_succ] using ha
  exact (h.weaken (by simp)).mp hb

theorem closeN_imp (n : ℕ) {a b : Formula} (h : Proves (.imp a b)) :
    Proves (.imp (Formula.closeN n a) (Formula.closeN n b)) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih => exact ih (all_imp h)

/-- Congruence for a negative equality, with arbitrary ambient terms. -/
theorem neg_eq_transport {s' t' s t : Term}
    (hs : Proves (.eq s' s)) (ht : Proves (.eq t' t)) :
    Proves (.imp (neg (.eq s' t')) (neg (.eq s t))) := by
  apply Relative.imp_intro
  apply Relative.imp_intro
  have hn : Relative Formula.Ax_s [.eq s t, neg (.eq s' t')] (neg (.eq s' t')) :=
    relative_of_derives (.ass _ _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have he : Relative Formula.Ax_s [.eq s t, neg (.eq s' t')] (.eq s t) :=
    relative_of_derives (.ass _ _ List.mem_cons_self)
  exact hn.mp (((hs.weaken (by simp)).eq_trans he).eq_trans (ht.eq_symm.weaken (by simp)))

theorem source_to_noZero {n : ℕ} (e : Expr (Fin n)) :
    Proves (.imp (sentence (classicalNoZero e)ᴺ) (ArithmeticExpression.noZeroSentence e)) := by
  rw [translated_classicalNoZero]
  exact closeN_imp n (neg_eq_transport
    (expressionTerm_correct e.splitNatural.1) (expressionTerm_correct e.splitNatural.2))

theorem noZero_to_source {n : ℕ} (e : Expr (Fin n)) :
    Proves (.imp (ArithmeticExpression.noZeroSentence e) (sentence (classicalNoZero e)ᴺ)) := by
  rw [translated_classicalNoZero]
  exact closeN_imp n (neg_eq_transport
    (expressionTerm_correct e.splitNatural.1).eq_symm
    (expressionTerm_correct e.splitNatural.2).eq_symm)

/-- A proof of equivalence, not a proof of either sentence. No PA or HA proof
of a no-zero proposition, semantics, or desired consistency equivalence is assumed. -/
theorem noZero_equivalence {n : ℕ} (e : Expr (Fin n)) :
    Proves (.and
      (.imp (sentence (classicalNoZero e)ᴺ) (ArithmeticExpression.noZeroSentence e))
      (.imp (ArithmeticExpression.noZeroSentence e) (sentence (classicalNoZero e)ᴺ))) :=
  (source_to_noZero e).and_intro (noZero_to_source e)

end DiophantineConsistency.FoundationHANoZero
