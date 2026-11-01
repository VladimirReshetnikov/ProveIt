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

omit [M↓[language] ⊧* PRA] in
theorem oneCorrectSentence_iff {n : ℕ} (c : Code n) (φ : Semisentence language n) :
    M↓[language] ⊧ oneCorrectSentence c φ ↔
      ∀ e : Fin n → M, Structure.func (L := language) c e =
        Structure.func (L := language) oneCode Fin.elim0 ↔ φ.Eval e Empty.elim := by
  simp only [models_iff, oneCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  apply forall_congr'
  intro e
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ vars n) = e := by funext i; rfl
  simp [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hv, iff_def]
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  tauto

omit [M↓[language] ⊧* PRA] in
theorem nonzeroCorrectSentence_iff {n : ℕ} (c : Code n) (φ : Semisentence language n) :
    M↓[language] ⊧ nonzeroCorrectSentence c φ ↔
      ∀ e : Fin n → M, Structure.func (L := language) c e ≠
        Structure.func (L := language) (Code.zero 0) Fin.elim0 ↔ φ.Eval e Empty.elim := by
  simp only [models_iff, nonzeroCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  apply forall_congr'
  intro e
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ vars n) = e := by funext i; rfl
  simp [Semiformula.eval_nrel, eqRel, applyCode, Semiterm.val_func, hv, iff_def]
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  tauto

theorem modelNonzeroCorrect {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (hbit : M↓[language] ⊧ bitSentence c) (hcorrect : M↓[language] ⊧ oneCorrectSentence c φ) :
    M↓[language] ⊧ nonzeroCorrectSentence c φ := by
  apply (nonzeroCorrectSentence_iff _ _).mpr
  intro e
  have hb := (PRACharacteristicBit.bitSentence_iff c).mp hbit e
  have hc := (oneCorrectSentence_iff c φ).mp hcorrect e
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
  apply (oneCorrectSentence_iff _ _).mpr
  intro e
  have hp : Fin.cases (e 0) (fun i : Fin n => e i.succ) = e := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hb := modelBoundedBy φ (e 0) (fun i : Fin n => e i.succ)
  rw [hp] at hb
  have hgood := modelBoundedFormula c (e 0) (fun i : Fin n => e i.succ)
  rw [hp] at hgood
  have hAll : (∀ x, Structure.rel (L := language) Language.ORing.Rel.lt ![x,e 0] →
      Structure.func (L := language) c (Fin.cases x (fun i : Fin n => e i.succ)) ≠
        Structure.func (L := language) (Code.zero 0) Fin.elim0) ↔
      (boundedBy φ).Eval e Empty.elim := by
    rw [hb]
    apply forall_congr'
    intro x
    apply imp_congr_right
    intro _
    exact (nonzeroCorrectSentence_iff c φ).mp hcorrect _
  exact (modelUniversalCode_eval c e).2.trans (hgood.trans hAll)

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
