import DiophantineConsistency.PRABoundedCharacteristic

/-! Specialize the bounded-universal compiler to any bound term. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedTermCharacteristic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRAOpenFormulaCompiler
  PRAEqualityCode PRACharacteristicBit PRABooleanOps PRABoundedSearchUniversal PRABoundedCharacteristic

def termBoundedBy {n : ℕ} (φ : Semisentence language (n+1)) (t : TermN n) : Semisentence language n :=
  (boundedBy φ) ⇜ Fin.cases t (vars n)

theorem termBoundedBy_eq {n : ℕ} (φ : Semisentence language (n+1)) (t : TermN n) :
    termBoundedBy φ t = ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, Rew.bShift t])] φ := by
  simp [termBoundedBy, boundedBy, Rewriting.subst, ← TransitiveRewriting.comp_app,
    Rew.q_subst, Rew.subst_comp_embSubsts, vars]

def termUniversalCode {n : ℕ} (c : Code (n+1)) (t : TermN n) : Code n :=
  .comp (universalCode c) (.cons (compileTerm t) (pack n (fun i => .proj i)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelTermUniversalCode {n : ℕ} (c : Code (n+1)) (t : TermN n) (e : Fin n → M) :
    Structure.func (L := language) (termUniversalCode c t) e =
      Structure.func (L := language) (universalCode c)
        (Fin.cases (Semiterm.val e Empty.elim t) e) := by
  rw [termUniversalCode, modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelCompile t e
  · simp only [getCode, getCode_pack]
    exact modelProjection j e

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelTermBoundedBy {n : ℕ} (φ : Semisentence language (n+1)) (t : TermN n) (e : Fin n → M) :
    (termBoundedBy φ t).Eval e Empty.elim ↔
      (boundedBy φ).Eval (Fin.cases (Semiterm.val e Empty.elim t) e) Empty.elim := by
  rw [termBoundedBy, Semiformula.eval_substs]
  have hv : (Semiterm.val e Empty.elim ∘ Fin.cases t (vars n)) =
      Fin.cases (Semiterm.val e Empty.elim t) e := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hv]

theorem modelTermCorrect {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1)) (t : TermN n)
    (h : M↓[language] ⊧ oneCorrectSentence (universalCode c) (boundedBy φ)) :
    M↓[language] ⊧ oneCorrectSentence (termUniversalCode c t) (termBoundedBy φ t) := by
  simp only [models_iff, oneCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff] at h ⊢
  intro e
  let args : Fin (n+1) → M := Fin.cases (Semiterm.val e Empty.elim t) e
  have hc := h args
  have hargs : (Semiterm.val (L := language) args Empty.elim ∘ vars (n+1)) = args := by funext i; rfl
  have hzargs : (Semiterm.val (L := language) args Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ vars n) = e := by funext i; rfl
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hargs, hzargs] at hc
  simp [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hv, hz, modelTermUniversalCode,
    modelTermBoundedBy, args] at hc ⊢
  exact hc

theorem modelTermBit {n : ℕ} (c : Code (n+1)) (t : TermN n)
    (h : M↓[language] ⊧ bitSentence (universalCode c)) :
    M↓[language] ⊧ bitSentence (termUniversalCode c t) := by
  simp only [models_iff, bitSentence, Semiformula.eval_allClosure] at h ⊢
  intro e
  let args : Fin (n+1) → M := Fin.cases (Semiterm.val e Empty.elim t) e
  have hc := h args
  have hargs : (Semiterm.val (L := language) args Empty.elim ∘ vars (n+1)) = args := by funext i; rfl
  have hzargs : (Semiterm.val (L := language) args Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ vars n) = e := by funext i; rfl
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hargs, hzargs] at hc
  simpa [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hv, hz, modelTermUniversalCode, args] using hc

end models

theorem PRA_boundedTermStep {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1)) (t : TermN n)
    (hbit : PRA ⊢ bitSentence c) (hcorrect : PRA ⊢ oneCorrectSentence c φ) :
    ∃ d : Code n, Primrec (eval d) ∧ PRA ⊢ bitSentence d ∧ PRA ⊢ oneCorrectSentence d (termBoundedBy φ t) := by
  have hcorrect' : PRA ⊢ oneCorrectSentence (universalCode c) (boundedBy φ) :=
    PRA_proves_boundedCharacteristic c φ (PRA_proves_nonzeroCorrect c φ hbit hcorrect)
  have hbit' : PRA ⊢ bitSentence (universalCode c) := PRA_proves_universalBitSentence c
  refine ⟨termUniversalCode c t, eval_primrec _, ?_, ?_⟩
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelTermBit c t (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbit')
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelTermCorrect c φ t (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcorrect')

end DiophantineConsistency.PRABoundedTermCharacteristic
