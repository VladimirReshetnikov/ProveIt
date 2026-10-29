import DiophantineConsistency.PRABoundedSearchUniversal

/-! The bounded-universal step of a characteristic-code compiler. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedCharacteristic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenFormulaCompiler
  PRAEqualityCode PRACharacteristicBit PRABooleanOps PRANonzeroCharacter PRABoundedSearchUniversal

def nonzeroCorrectSentence {n : ℕ} (c : Code n) (φ : Semisentence language n) : Sentence language :=
  ∀⁰* ((Semiformula.nrel Language.ORing.Rel.eq
    ![applyCode c (vars n), applyCode (Code.zero 0) Fin.elim0]) 🡘 φ)

def oneCorrectSentence {n : ℕ} (c : Code n) (φ : Semisentence language n) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
    ![applyCode c (vars n), applyCode oneCode Fin.elim0]) 🡘 φ)

def boundedBy {n : ℕ} (φ : Semisentence language (n+1)) : Semisentence language (n+1) :=
  ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1])]
    (Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .bvar i.succ.succ)) ▹ φ)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelNonzeroCorrect {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (hbit : M↓[language] ⊧ bitSentence c) (hcorrect : M↓[language] ⊧ oneCorrectSentence c φ) :
    M↓[language] ⊧ nonzeroCorrectSentence c φ := by
  simp only [models_iff, bitSentence, Semiformula.eval_allClosure] at hbit
  simp only [models_iff, oneCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff] at hcorrect
  simp only [models_iff, nonzeroCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  have hb := hbit e
  have hc := hcorrect e
  simp [Semiformula.eval_rel, Semiformula.eval_nrel, eqRel, applyCode, Semiterm.val_func] at hb hc ⊢
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN n)) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at hb hc ⊢
  have hne := modelOneNeZero (M := M)
  constructor
  · intro h
    apply hc.1
    rcases hb with hzero | hone
    · exact False.elim (h hzero)
    · exact hone
  · intro h hzero
    have hone := hc.2 h
    exact hne (hone.symm.trans hzero)

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelBoundedBy {n : ℕ} (φ : Semisentence language (n+1)) (bound : M) (params : Fin n → M) :
    (boundedBy φ).Eval (Fin.cases bound params) Empty.elim ↔
      ∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,bound] →
        φ.Eval (Fin.cases x params) Empty.elim := by
  simp only [boundedBy, Semiformula.eval_ball, Semiformula.eval_rel, Semiformula.eval_rew]
  apply forall_congr'
  intro x
  have hb : (Semiterm.val (L := language) (x :> Fin.cases bound params) Empty.elim ∘
      (Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .bvar i.succ.succ))) ∘ Semiterm.bvar) =
      Fin.cases x params := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hf : (Semiterm.val (L := language) (x :> Fin.cases bound params) Empty.elim ∘
      (Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .bvar i.succ.succ))) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  simp [hb,hf]

theorem modelBoundedCharacteristic {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1))
    (hcorrect : M↓[language] ⊧ nonzeroCorrectSentence c φ) :
    M↓[language] ⊧ oneCorrectSentence (universalCode c) (boundedBy φ) := by
  simp only [models_iff, nonzeroCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff] at hcorrect
  simp only [models_iff, oneCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  have hp : Fin.cases (e 0) (fun i : Fin n => e i.succ) = e := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hb := modelBoundedBy φ (e 0) (fun i : Fin n => e i.succ)
  rw [hp] at hb
  have hu := modelUniversalCode c (e 0) (fun i => if h : i < n then e ⟨i+1, by omega⟩ else e 0)
  have he : (fun i : Fin n => (if h : i.val < n then e ⟨i.val+1, by omega⟩ else e 0)) =
      (fun i : Fin n => e i.succ) := by
    funext i
    simp only [i.isLt, ↓reduceDIte]
    congr 1
  rw [he] at hu
  have hAll : (∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,e 0] →
      Structure.func (L := language) c (Fin.cases x (fun i : Fin n => e i.succ)) ≠
        Structure.func (L := language) (Code.zero 0) Fin.elim0) ↔
      (boundedBy φ).Eval e Empty.elim := by
    rw [hb]
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro _
    have hc := hcorrect (Fin.cases x (fun i : Fin n => e i.succ))
    simpa [Semiformula.eval_nrel, eqRel, applyCode, Semiterm.val_func, vars, iff_def] using hc
  have hcode : Structure.func (L := language) (universalCode c) e =
      Structure.func (L := language) oneCode Fin.elim0 ↔ (boundedBy φ).Eval e Empty.elim := by
    simpa only [hp] using (hu.2.trans hAll)
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ vars (n+1)) = e := by funext i; rfl
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simpa [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hv, hz, iff_def] using hcode

end models

theorem PRA_proves_nonzeroCorrect {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (hbit : PRA ⊢ bitSentence c) (hcorrect : PRA ⊢ oneCorrectSentence c φ) :
    PRA ⊢ nonzeroCorrectSentence c φ := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelNonzeroCorrect c φ (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hbit)
    (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcorrect)

theorem PRA_proves_boundedCharacteristic {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1))
    (hcorrect : PRA ⊢ nonzeroCorrectSentence c φ) :
    PRA ⊢ oneCorrectSentence (universalCode c) (boundedBy φ) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelBoundedCharacteristic c φ (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcorrect)

theorem PRA_boundedUniversalStep {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1))
    (hbit : PRA ⊢ bitSentence c) (hcorrect : PRA ⊢ oneCorrectSentence c φ) :
    ∃ d : Code (n+1), Primrec (eval d) ∧ PRA ⊢ bitSentence d ∧ PRA ⊢ oneCorrectSentence d (boundedBy φ) :=
  ⟨universalCode c, universalCode_primrec c, PRA_proves_universalBitSentence c,
    PRA_proves_boundedCharacteristic c φ (PRA_proves_nonzeroCorrect c φ hbit hcorrect)⟩

end DiophantineConsistency.PRABoundedCharacteristic
