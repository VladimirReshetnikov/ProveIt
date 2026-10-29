import DiophantineConsistency.PRABooleanOps
import DiophantineConsistency.PRATermCompilation
import DiophantineConsistency.PRAQOrder

/-! Compositional characteristic codes, conditional on an equality bit. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAOpenFormulaCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation
  PRABooleanOps PRAIsZero PRAQOrder

/-- Quantifier-free formulas with all variables explicitly among n arguments. -/
inductive OpenFormula (n : ℕ) : Type
  | top : OpenFormula n
  | bot : OpenFormula n
  | equal : TermN n → TermN n → OpenFormula n
  | less : TermN n → TermN n → OpenFormula n
  | not : OpenFormula n → OpenFormula n
  | and : OpenFormula n → OpenFormula n → OpenFormula n
  | or : OpenFormula n → OpenFormula n → OpenFormula n

def asFormula {n : ℕ} : OpenFormula n → Semisentence language n
  | .top => ⊤
  | .bot => ⊥
  | .equal a b => Semiformula.rel Language.ORing.Rel.eq ![a,b]
  | .less a b => Semiformula.rel Language.ORing.Rel.lt ![a,b]
  | .not p => ∼asFormula p
  | .and p q => asFormula p ⋏ asFormula q
  | .or p q => asFormula p ⋎ asFormula q

def atomCode {n : ℕ} (c : Code 2) (a b : TermN n) : Code n :=
  .comp c (.cons (compileTerm a) (.cons (compileTerm b) (.nil n)))
def notCode {n : ℕ} (c : Code n) : Code n := .comp isZeroCode (.cons c (.nil n))
def andCode {n : ℕ} (c d : Code n) : Code n :=
  .comp mulCode (.cons c (.cons d (.nil n)))
def orCode {n : ℕ} (c d : Code n) : Code n := notCode (andCode (notCode c) (notCode d))

def compileFormula {n : ℕ} (eqCode : Code 2) : OpenFormula n → Code n
  | .top => .comp oneCode (.nil n)
  | .bot => .zero n
  | .equal a b => atomCode eqCode a b
  | .less a b => atomCode ltBitCode a b
  | .not p => notCode (compileFormula eqCode p)
  | .and p q => andCode (compileFormula eqCode p) (compileFormula eqCode q)
  | .or p q => orCode (compileFormula eqCode p) (compileFormula eqCode q)

def eqBitSentence (eqCode : Code 2) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode eqCode (vars 2), applyCode (Code.zero 0) Fin.elim0]) ⋎
    (Semiformula.rel Language.ORing.Rel.eq
      ![applyCode eqCode (vars 2), applyCode oneCode Fin.elim0]) : Semisentence language 2)

def eqCorrectSentence (eqCode : Code 2) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode eqCode (vars 2), applyCode oneCode Fin.elim0]) 🡘
    (Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .bvar 1]) : Semisentence language 2)

def formulaCorrectSentence {n : ℕ} (eqCode : Code 2) (p : OpenFormula n) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode (compileFormula eqCode p) (vars n), applyCode oneCode Fin.elim0]) 🡘
    asFormula p)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

def formulaHolds {n : ℕ} (e : Fin n → M) : OpenFormula n → Prop
  | .top => True
  | .bot => False
  | .equal a b => Semiterm.val e Empty.elim a = Semiterm.val e Empty.elim b
  | .less a b => Structure.rel (L := language) Language.ORing.Rel.lt
      ![Semiterm.val e Empty.elim a, Semiterm.val e Empty.elim b]
  | .not p => ¬formulaHolds e p
  | .and p q => formulaHolds e p ∧ formulaHolds e q
  | .or p q => formulaHolds e p ∨ formulaHolds e q

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem formulaHolds_eval {n : ℕ} (p : OpenFormula n) (e : Fin n → M) :
    formulaHolds e p ↔ (asFormula p).Eval e Empty.elim := by
  induction p with
  | top => simp [formulaHolds, asFormula]
  | bot => simp [formulaHolds, asFormula]
  | equal a b =>
      simp only [formulaHolds, asFormula, Semiformula.eval_rel, eqRel]
      rfl
  | less a b =>
      simp only [formulaHolds, asFormula, Semiformula.eval_rel]
      rw [val_term_pair]
  | not p ih => simpa [formulaHolds, asFormula] using not_congr ih
  | and p q ihp ihq => simpa [formulaHolds, asFormula] using and_congr ihp ihq
  | or p q ihp ihq => simpa [formulaHolds, asFormula] using or_congr ihp ihq

theorem modelAtomCode {n : ℕ} (c : Code 2) (a b : TermN n) (e : Fin n → M) :
    Structure.func (L := language) (atomCode c a b) e =
      Structure.func (L := language) c ![Semiterm.val e Empty.elim a, Semiterm.val e Empty.elim b] := by
  rw [atomCode, modelComposition]
  have hv : (fun i => Structure.func (L := language)
      (getCode (.cons (compileTerm a) (.cons (compileTerm b) (.nil n))) i) e) =
      ![Semiterm.val e Empty.elim a, Semiterm.val e Empty.elim b] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelCompile a e
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      exact modelCompile b e
  rw [hv]

theorem modelNotCode {n : ℕ} (c : Code n) (e : Fin n → M) :
    Structure.func (L := language) (notCode c) e =
      Structure.func (L := language) isZeroCode (fun _ => Structure.func (L := language) c e) := by
  rw [notCode, modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem modelAndCode {n : ℕ} (c d : Code n) (e : Fin n → M) :
    Structure.func (L := language) (andCode c d) e =
      Structure.func (L := language) mulCode
        ![Structure.func (L := language) c e, Structure.func (L := language) d e] := by
  rw [andCode, modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun k => Fin.elim0 k) j

/-- With an equality characteristic bit verified in an arbitrary PRA model,
all Boolean combinations of equality and strict-order atoms compile correctly.
The equality-bit hypothesis is deliberately explicit. -/
theorem modelCompileFormula {n : ℕ} (eqCode : Code 2)
    (hEq : ∀ x y : M, IsBit (Structure.func (L := language) eqCode ![x,y]) ∧
      (Structure.func (L := language) eqCode ![x,y] =
        Structure.func (L := language) oneCode Fin.elim0 ↔ x = y))
    (p : OpenFormula n) (e : Fin n → M) :
    IsBit (Structure.func (L := language) (compileFormula eqCode p) e) ∧
      (Structure.func (L := language) (compileFormula eqCode p) e =
        Structure.func (L := language) oneCode Fin.elim0 ↔ formulaHolds e p) := by
  induction p with
  | top =>
      simp only [compileFormula, formulaHolds]
      rw [modelComposition]
      have h : (fun i : Fin 0 => Structure.func (L := language)
          (getCode (.nil n) i) e) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      rw [h]
      exact ⟨Or.inr rfl, iff_true_intro rfl⟩
  | bot =>
      simp only [compileFormula, formulaHolds]
      rw [modelZero]
      exact ⟨Or.inl rfl, iff_false_intro (Ne.symm (PRANonzeroCharacter.modelOneNeZero (M := M)))⟩
  | equal a b =>
      simp only [compileFormula, formulaHolds]
      rw [modelAtomCode]
      exact hEq _ _
  | less a b =>
      simp only [compileFormula, formulaHolds]
      rw [modelAtomCode]
      constructor
      · rw [modelLtBit]
        exact modelNonzeroBit _
      · exact (modelLtBitDefinition _ _).symm
  | not p ih =>
      simp only [compileFormula, formulaHolds]
      rw [modelNotCode]
      obtain ⟨hb, hc⟩ := modelNotBit _ ih.1
      exact ⟨hb, hc.trans (not_congr ih.2)⟩
  | and p q ihp ihq =>
      simp only [compileFormula, formulaHolds]
      rw [modelAndCode]
      obtain ⟨hb,hc⟩ := modelMulBit _ _ ihp.1 ihq.1
      exact ⟨hb, hc.trans (and_congr ihp.2 ihq.2)⟩
  | or p q ihp ihq =>
      simp only [compileFormula, formulaHolds]
      rw [orCode, modelNotCode, modelAndCode, modelNotCode, modelNotCode]
      obtain ⟨hp,hp'⟩ := modelNotBit _ ihp.1
      obtain ⟨hq,hq'⟩ := modelNotBit _ ihq.1
      obtain ⟨hm,hm'⟩ := modelMulBit _ _ hp hq
      obtain ⟨hb,hb'⟩ := modelNotBit _ hm
      refine ⟨hb, ?_⟩
      rw [hb']
      simp only [ne_eq, hm', hp', hq', ihp.2, ihq.2]
      tauto

omit [M↓[language] ⊧* PRA] in
theorem modelEqCertificate (eqCode : Code 2)
    (hBit : M↓[language] ⊧ eqBitSentence eqCode)
    (hCorrect : M↓[language] ⊧ eqCorrectSentence eqCode) :
    ∀ x y : M, IsBit (Structure.func (L := language) eqCode ![x,y]) ∧
      (Structure.func (L := language) eqCode ![x,y] =
        Structure.func (L := language) oneCode Fin.elim0 ↔ x = y) := by
  intro x y
  simp only [models_iff, eqBitSentence, eqCorrectSentence, Semiformula.eval_allClosure,
    LogicalConnective.iff] at hBit hCorrect
  have hb := hBit ![x,y]
  have hc := hCorrect ![x,y]
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim ![x,y] _ at hb hc
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, vars, Function.comp_def] at hb hc
  have hz : (fun i : Fin 0 => Semiterm.val ![x,y] Empty.elim (Fin.elim0 i : TermN 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at hb hc
  constructor
  · exact hb
  · tauto

theorem modelFormulaCorrectSentence {n : ℕ} (eqCode : Code 2) (p : OpenFormula n)
    (hEq : ∀ x y : M, IsBit (Structure.func (L := language) eqCode ![x,y]) ∧
      (Structure.func (L := language) eqCode ![x,y] =
        Structure.func (L := language) oneCode Fin.elim0 ↔ x = y)) :
    M↓[language] ⊧ formulaCorrectSentence eqCode p := by
  simp only [models_iff, formulaCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  have h := (modelCompileFormula eqCode hEq p e).2.trans (formulaHolds_eval p e)
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, vars, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  simp only [←Semiformula.neg_eq, Semiformula.EvalAux_neg]
  change (¬(Structure.func (L := language) (compileFormula eqCode p) e =
      Structure.func (L := language) oneCode Fin.elim0) ∨ (asFormula p).Eval e Empty.elim) ∧
    (¬(asFormula p).Eval e Empty.elim ∨ Structure.func (L := language) (compileFormula eqCode p) e =
      Structure.func (L := language) oneCode Fin.elim0)
  tauto

end models

/-- Conditional on two closed candidate-PRA certificates for one equality-bit
code, every encoded open formula has a closed characteristic correctness proof. -/
theorem PRA_proves_formulaCorrect {n : ℕ} (eqCode : Code 2) (p : OpenFormula n)
    (hBit : PRA ⊢ eqBitSentence eqCode) (hCorrect : PRA ⊢ eqCorrectSentence eqCode) :
    PRA ⊢ formulaCorrectSentence eqCode p := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  apply modelFormulaCorrectSentence
  apply modelEqCertificate
  · exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) hBit
  · exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) hCorrect
end DiophantineConsistency.PRAOpenFormulaCompiler
