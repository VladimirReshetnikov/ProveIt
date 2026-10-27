import DiophantineConsistency.FoundationHADeltaZero
import DiophantineConsistency.FoundationPAHFNatSemantics

/-! Free-variable support and standard-natural semantics of the existing
ordinary NNF interpretation. Closedness gives valuation independence in any
PAHF premodel; the arithmetic semantic comparison is specifically over Nat.
No new HA derivation or independent checker comparison is asserted. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationPAHFOrdinarySemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA FoundationPAHFSyntax FoundationHADeltaZero FoundationPAHFNatSemantics

theorem free_rename_succ (t : Term) (k : Nat) :
    Term.Free (k+1) (Term.rename Nat.succ t) ↔ Term.Free k t := by
  induction t <;> simp_all only [Term.rename, Term.Free, Nat.add_one, Nat.succ.injEq]

/-- An upper bound on support; unused environment entries need not occur. -/
theorem free_termAux {ξ : Type*} {n : Nat} (bv : Fin n → Term) (fv : ξ → Term)
    (t : Semiterm ℒₒᵣ ξ n) (k : Nat) :
    Term.Free k (termAux bv fv t) →
      (∃ i, Term.Free k (bv i)) ∨ ∃ x, Term.Free k (fv x) := by
  induction t with
  | bvar i => exact fun h => Or.inl ⟨i,h⟩
  | fvar x => exact fun h => Or.inr ⟨x,h⟩
  | func f v ih =>
    cases f with
    | zero => exact False.elim
    | one => exact False.elim
    | add => exact fun h => h.elim (ih 0) (ih 1)
    | mul => exact fun h => h.elim (ih 0) (ih 1)

theorem free_ltFormula (s t : Term) (k : Nat) :
    Formula.Free k (ltFormula s t) ↔ Term.Free k s ∨ Term.Free k t := by
  simp only [ltFormula, Formula.Free, Term.Free, free_rename_succ,
    Nat.add_one, Nat.succ_ne_zero, or_false]

private theorem lower_support {ξ : Type*} {n : Nat}
    (bv : Fin n → Term) (fv : ξ → Term) (k : Nat)
    (h : (∃ i, Term.Free (k+1) (liftBound bv i)) ∨
      ∃ x, Term.Free (k+1) (liftFree fv x)) :
    (∃ i, Term.Free k (bv i)) ∨ ∃ x, Term.Free k (fv x) := by
  rcases h with ⟨i,hi⟩ | ⟨x,hx⟩
  · cases i using Fin.cases with
    | zero => simp only [liftBound, Fin.cases_zero, Term.Free,
        Nat.add_one, Nat.succ_ne_zero] at hi
    | succ i =>
      exact Or.inl ⟨i, (free_rename_succ (bv i) k).mp hi⟩
  · exact Or.inr ⟨x, (free_rename_succ (fv x) k).mp hx⟩

theorem free_ordinaryAux {ξ : Type*} {n : Nat} (bv : Fin n → Term) (fv : ξ → Term)
    (p : Semiformula ℒₒᵣ ξ n) (k : Nat) :
    Formula.Free k (ordinaryAux bv fv p) →
      (∃ i, Term.Free k (bv i)) ∨ ∃ x, Term.Free k (fv x) := by
  induction p generalizing fv k with
  | verum => exact fun h => h.elim False.elim False.elim
  | falsum => exact False.elim
  | rel r v =>
    cases r with
    | eq => exact fun h => h.elim (free_termAux bv fv (v 0) k) (free_termAux bv fv (v 1) k)
    | lt =>
      intro h
      exact ((free_ltFormula _ _ _).mp h).elim
        (free_termAux bv fv (v 0) k) (free_termAux bv fv (v 1) k)
  | nrel r v =>
    cases r with
    | eq =>
      intro h
      exact h.elim
        (fun h => h.elim (free_termAux bv fv (v 0) k) (free_termAux bv fv (v 1) k)) False.elim
    | lt =>
      intro h
      exact h.elim
        (fun h => ((free_ltFormula _ _ _).mp h).elim
          (free_termAux bv fv (v 0) k) (free_termAux bv fv (v 1) k)) False.elim
  | and p q hp hq => exact fun h => h.elim (hp bv fv k) (hq bv fv k)
  | or p q hp hq => exact fun h => h.elim (hp bv fv k) (hq bv fv k)
  | all p hp => exact fun h => lower_support bv fv k (hp (liftBound bv) (liftFree fv) (k+1) h)
  | exs p hp => exact fun h => lower_support bv fv k (hp (liftBound bv) (liftFree fv) (k+1) h)

theorem ordinary_sentence (p : ArithmeticSentence) :
    Formula.Sentence (ordinaryAux Fin.elim0 Empty.elim p) := by
  intro k hk
  rcases free_ordinaryAux Fin.elim0 Empty.elim p k hk with ⟨i,_⟩ | ⟨x,_⟩
  · exact Fin.elim0 i
  · exact Empty.elim x

/-- Pure syntax gives valuation independence even without arithmetic axioms. -/
theorem ordinary_sentence_environment {α : Type*} (M : PreModel α)
    (p : ArithmeticSentence) (ee ff : Nat → α) :
    Formula.Sat M ee (ordinaryAux Fin.elim0 Empty.elim p) ↔
      Formula.Sat M ff (ordinaryAux Fin.elim0 Empty.elim p) :=
  Formula.Sat_ext_free M _ (fun k hk => False.elim (ordinary_sentence p k hk))

/-- Ordinary interpretation follows the source's actual eight constructors. -/
theorem sat_ordinaryAux {ξ : Type*} {n : Nat} (p : Semiformula ℒₒᵣ ξ n)
    (bv : Fin n → Term) (fv : ξ → Term) (ee : Nat → Nat) :
    Formula.Sat natStructure ee (ordinaryAux bv fv p) ↔
      p.Eval (fun i => Term.eval natStructure ee (bv i))
        (fun x => Term.eval natStructure ee (fv x)) := by
  change _ ↔ p.EvalAux _ _ _
  induction p generalizing fv ee with
  | verum => exact iff_true_intro (fun h => h)
  | falsum => rfl
  | rel r v =>
    cases r with
    | eq =>
      change (Term.eval natStructure ee (termAux bv fv (v 0)) =
        Term.eval natStructure ee (termAux bv fv (v 1))) ↔ _
      simp only [eval_termAux]; rfl
    | lt =>
      change Formula.Sat natStructure ee
        (ltFormula (termAux bv fv (v 0)) (termAux bv fv (v 1))) ↔ _
      simp only [sat_ltFormula, eval_termAux]; rfl
  | nrel r v =>
    cases r with
    | eq =>
      change (¬(Term.eval natStructure ee (termAux bv fv (v 0)) =
        Term.eval natStructure ee (termAux bv fv (v 1)))) ↔ _
      simp only [eval_termAux]; rfl
    | lt =>
      change (¬Formula.Sat natStructure ee
        (ltFormula (termAux bv fv (v 0)) (termAux bv fv (v 1)))) ↔ _
      simp only [sat_ltFormula, eval_termAux]; rfl
  | and p q hp hq => exact and_congr (hp bv fv ee) (hq bv fv ee)
  | or p q hp hq => exact or_congr (hp bv fv ee) (hq bv fv ee)
  | all p hp =>
    change (∀ d, Formula.Sat natStructure (SetTheory.scons d ee)
      (ordinaryAux (liftBound bv) (liftFree fv) p)) ↔ _
    exact forall_congr' (fun d => by
      simpa only [eval_liftBound, eval_liftFree] using
        (hp (liftBound bv) (liftFree fv) (SetTheory.scons d ee)))
  | exs p hp =>
    change (∃ d, Formula.Sat natStructure (SetTheory.scons d ee)
      (ordinaryAux (liftBound bv) (liftFree fv) p)) ↔ _
    exact exists_congr (fun d => by
      simpa only [eval_liftBound, eval_liftFree] using
        (hp (liftBound bv) (liftFree fv) (SetTheory.scons d ee)))

theorem sat_ordinary_sentence (p : ArithmeticSentence) (ee : Nat → Nat) :
    Formula.Sat natStructure ee (ordinaryAux Fin.elim0 Empty.elim p) ↔
      p.Evalb (M := Nat) ![] := by
  have hf : (fun x : Empty => Term.eval natStructure ee (Empty.elim x)) = Empty.elim := by
    funext x
    exact Empty.elim x
  simpa only [Matrix.empty_eq, hf] using sat_ordinaryAux p Fin.elim0 Empty.elim ee

end DiophantineConsistency.FoundationPAHFOrdinarySemantics
