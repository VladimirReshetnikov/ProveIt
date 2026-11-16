import PA194ArithFacts
import PA194InductionForms
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Four fixed axioms of the arithmetic theory, translated

Guarded derivations of the translations of the quoted axioms `addCongruence`,
`mulCongruence`, `addSucc` and `mulSucc` of `PA194PAeq`. The standard quantifiers are closed
one at a time with `tr_close_step`; the matrix with free variables is one of the open facts
of `PA194ArithFacts`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic

/-- The matrices of the four axioms as functions of their terms. -/
def congMatrix {n : ℕ} (op : SyntacticSemiterm PA194PAeq.language n →
    SyntacticSemiterm PA194PAeq.language n → SyntacticSemiterm PA194PAeq.language n)
    (t0 t1 t2 t3 : SyntacticSemiterm PA194PAeq.language n) :
    Semiproposition PA194PAeq.language n :=
  PA194PAeq.implies (PA194PAeq.eq t0 t1)
    (PA194PAeq.implies (PA194PAeq.eq t2 t3) (PA194PAeq.eq (op t0 t2) (op t1 t3)))
def addSuccMatrix {n : ℕ} (t0 t1 : SyntacticSemiterm PA194PAeq.language n) :
    Semiproposition PA194PAeq.language n :=
  PA194PAeq.eq (PA194PAeq.add (PA194PAeq.succ t0) t1) (PA194PAeq.succ (PA194PAeq.add t0 t1))
def mulSuccMatrix {n : ℕ} (t0 t1 : SyntacticSemiterm PA194PAeq.language n) :
    Semiproposition PA194PAeq.language n :=
  PA194PAeq.eq (PA194PAeq.mul (PA194PAeq.succ t1) t0)
    (PA194PAeq.add t0 (PA194PAeq.mul t1 t0))

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

/-! ### Quotes -/

theorem quote_free' (φ : Semiproposition PA194PAeq.language 1) :
    (⌜Rewriting.free φ⌝ : V) = free PA194PAeq.language (⌜φ⌝ : V) := by
  simp [Semiformula.quote_def]

theorem q_eq (t u : SyntacticTerm PA194PAeq.language) :
    (⌜(PA194PAeq.eq t u : Proposition PA194PAeq.language)⌝ : V) = peq (⌜t⌝ : V) ⌜u⌝ := by
  simp [PA194PAeq.eq, peq, SemitermVec.val, Semiterm.quote_def]
  constructor
  · change ((0 : Nat) : V) = 0; simp
  · constructor <;> rfl
theorem q_add (t u : SyntacticTerm PA194PAeq.language) :
    (⌜PA194PAeq.add t u⌝ : V) = addT (⌜t⌝ : V) ⌜u⌝ := by
  simp [PA194PAeq.add, addT, SemitermVec.val, Semiterm.quote_def]
  constructor
  · change ((2 : Nat) : V) = 2; simp
  · constructor <;> rfl
theorem q_mul (t u : SyntacticTerm PA194PAeq.language) :
    (⌜PA194PAeq.mul t u⌝ : V) = mulT (⌜t⌝ : V) ⌜u⌝ := by
  simp [PA194PAeq.mul, mulT, SemitermVec.val, Semiterm.quote_def]
  constructor
  · change ((3 : Nat) : V) = 3; simp
  · constructor <;> rfl
theorem q_succ (t : SyntacticTerm PA194PAeq.language) :
    (⌜PA194PAeq.succ t⌝ : V) = succT (⌜t⌝ : V) := by
  rw [PA194PAeq.quote_successor]
  rfl
theorem q_fvar (x : ℕ) :
    (⌜(&x : SyntacticTerm PA194PAeq.language)⌝ : V) = ^&(x : V) := by simp
theorem q_implies (p q : Proposition PA194PAeq.language) :
    (⌜PA194PAeq.implies p q⌝ : V) =
      imp PA194PAeq.language (⌜p⌝ : V) ⌜q⌝ := by
  show (⌜(∼p ⋎ q : Proposition PA194PAeq.language)⌝ : V) = _
  simp [imp, Semiformula.quote_def]

/-! ### Closing one standard quantifier -/

theorem tr_close_quote (φ : Semiproposition PA194PAeq.language 1)
    (h : GDerivable T (insert (tr (⌜Rewriting.free φ⌝ : V)) (∅ : V))) :
    GDerivable T (insert (tr (⌜(∀⁰ φ : Proposition PA194PAeq.language)⌝ : V)) (∅ : V)) := by
  rw [Semiformula.quote_all]
  refine tr_close_step (by simp) ?_
  rw [← quote_free']
  exact h

/-- From the open sequent `¬a, ¬b, c` to the translation of `a → (b → c)`. -/
theorem gd_imp2_tr {a b c : V} (ha : IsSemiformula PA194PAeq.language 0 a)
    (hb : IsSemiformula PA194PAeq.language 0 b) (hc : IsSemiformula PA194PAeq.language 0 c)
    (h : GDerivable T (insert (neg SourceL (tr a)) (insert (neg SourceL (tr b))
      (insert (tr c) (∅ : V))))) :
    GDerivable T (insert (tr (imp PA194PAeq.language a (imp PA194PAeq.language b c))) (∅ : V)) := by
  have hna := IsSemiformula.neg_iff.mpr ha
  have hnb := IsSemiformula.neg_iff.mpr hb
  have hbc : IsSemiformula PA194PAeq.language 0 (neg PA194PAeq.language b ^⋎ c) :=
    IsSemiformula.or.mpr ⟨hnb,hc⟩
  have fa : IsFormula SourceL (neg SourceL (tr a)) := IsSemiformula.neg_iff.mpr (tr_valid ha)
  have fb : IsFormula SourceL (neg SourceL (tr b)) := IsSemiformula.neg_iff.mpr (tr_valid hb)
  have fc : IsFormula SourceL (tr c) := tr_valid hc
  have f1 : IsFormula SourceL (neg SourceL (tr b) ^⋎ tr c) := IsSemiformula.or.mpr ⟨fb,fc⟩
  have f2 : IsFormula SourceL (neg SourceL (tr a) ^⋎ (neg SourceL (tr b) ^⋎ tr c)) :=
    IsSemiformula.or.mpr ⟨fa,f1⟩
  show GDerivable T (insert (tr (neg PA194PAeq.language a ^⋎
    (neg PA194PAeq.language b ^⋎ c))) (∅ : V))
  rw [tr_or hna hbc, tr_neg ha, tr_or hnb hc, tr_neg hb]
  refine GDerivable.or_m (p := neg SourceL (tr a)) (q := neg SourceL (tr b) ^⋎ tr c) (by simp) ?_
  refine GDerivable.or_m (p := neg SourceL (tr b)) (q := tr c) (by simp) ?_
  exact GDerivable.wk (fs_cons fb (fs_cons fc (fs_cons fa (fs_cons f1 (fs_cons f2 fs_nil)))))
    (by set_tac) h

/-! ### The four axioms -/

section axioms
variable (S : SourceFacts (V := V) T)
include S

theorem addCongruence_tr :
    GDerivable T (insert (tr (⌜PA194PAeq.addCongruence⌝ : V)) (∅ : V)) := by
  have hv : ∀ x : ℕ, IsSemiterm PA194PAeq.language 0 (^&(x : V) : V) := fun x => by simp
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ ∀⁰ ∀⁰ congMatrix PA194PAeq.add #0 #1 #2 #3) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ ∀⁰ congMatrix PA194PAeq.add #0 #1 #2 &0) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ congMatrix PA194PAeq.add #0 #1 &0 &1) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (congMatrix PA194PAeq.add #0 &0 &1 &2) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(congMatrix PA194PAeq.add &0 &1 &2 &3 :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  unfold congMatrix
  rw [q_implies, q_implies, q_eq, q_eq, q_eq, q_add, q_add, q_fvar, q_fvar, q_fvar, q_fvar]
  exact gd_imp2_tr (peq_valid (hv 0) (hv 1)) (peq_valid (hv 2) (hv 3))
    (peq_valid (addT_valid (hv 0) (hv 2)) (addT_valid (hv 1) (hv 3)))
    (cong_add S (hv 0) (hv 1) (hv 2) (hv 3))

theorem mulCongruence_tr :
    GDerivable T (insert (tr (⌜PA194PAeq.mulCongruence⌝ : V)) (∅ : V)) := by
  have hv : ∀ x : ℕ, IsSemiterm PA194PAeq.language 0 (^&(x : V) : V) := fun x => by simp
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ ∀⁰ ∀⁰ congMatrix PA194PAeq.mul #0 #1 #2 #3) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ ∀⁰ congMatrix PA194PAeq.mul #0 #1 #2 &0) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ congMatrix PA194PAeq.mul #0 #1 &0 &1) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (congMatrix PA194PAeq.mul #0 &0 &1 &2) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(congMatrix PA194PAeq.mul &0 &1 &2 &3 :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  unfold congMatrix
  rw [q_implies, q_implies, q_eq, q_eq, q_eq, q_mul, q_mul, q_fvar, q_fvar, q_fvar, q_fvar]
  exact gd_imp2_tr (peq_valid (hv 0) (hv 1)) (peq_valid (hv 2) (hv 3))
    (peq_valid (mulT_valid (hv 0) (hv 2)) (mulT_valid (hv 1) (hv 3)))
    (cong_mul S (hv 0) (hv 1) (hv 2) (hv 3))

theorem addSucc_tr (hA3 : T.internalize V ⊢ (tHyp sA3 : Bootstrapping.Semiformula V SourceL 0)) :
    GDerivable T (insert (tr (⌜PA194PAeq.addSucc⌝ : V)) (∅ : V)) := by
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ addSuccMatrix #0 #1) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (addSuccMatrix #0 &0) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(addSuccMatrix &0 &1 :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  unfold addSuccMatrix
  rw [q_eq, q_add, q_succ, q_succ, q_add, q_fvar, q_fvar]
  simpa using addSucc_open S hA3 (0 : V) (1 : V)

theorem mulSucc_tr (hM3 : T.internalize V ⊢ (tHyp sM3 : Bootstrapping.Semiformula V SourceL 0)) :
    GDerivable T (insert (tr (⌜PA194PAeq.mulSucc⌝ : V)) (∅ : V)) := by
  show GDerivable T (insert (tr (⌜(∀⁰ (∀⁰ mulSuccMatrix #0 #1) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(∀⁰ (mulSuccMatrix #0 &0) :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  refine tr_close_quote _ ?_
  show GDerivable T (insert (tr (⌜(mulSuccMatrix &0 &1 :
    Proposition PA194PAeq.language)⌝ : V)) (∅ : V))
  unfold mulSuccMatrix
  rw [q_eq, q_mul, q_succ, q_add, q_mul, q_fvar, q_fvar]
  simpa using mulSucc_open S hM3 (1 : V) (0 : V)

end axioms

#print axioms q_eq
#print axioms tr_close_quote
#print axioms addCongruence_tr
#print axioms mulCongruence_tr
#print axioms addSucc_tr
#print axioms mulSucc_tr
end generic
end PA194GuardedCompiler
