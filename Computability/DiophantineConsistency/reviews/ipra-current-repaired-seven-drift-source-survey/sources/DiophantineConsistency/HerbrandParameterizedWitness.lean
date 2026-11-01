import DiophantineConsistency.HerbrandFiniteExtraction
import DiophantineConsistency.PRAHerbrandSelection

/-! Translation of Herbrand terms to parameterized primitive recursive codes. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandParameterizedWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation
  PRAUniversalCandidate PRAUniversalEquivalence HerbrandExistentialSequents
  HerbrandUniversalPreparation HerbrandFiniteExtraction PRAHerbrandSelection

def parameterTerm (n : ℕ) (t : SyntacticTerm language) : TermN n :=
  Rew.bind Fin.elim0 (fun i => if h : i < n then .bvar ⟨i,h⟩ else applyCode (Code.zero 0) Fin.elim0) t

def parameterCode (n : ℕ) (t : SyntacticTerm language) : Code n := compileTerm (parameterTerm n t)

def parameterMatrix {n : ℕ} (φ : Semisentence language (n+1)) : Semiproposition language 1 :=
  Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val)) ▹ φ

theorem parameterMatrix_open {n : ℕ} (φ : Semisentence language (n+1))
    (hφ : φ.Open) : (parameterMatrix φ).Open := by
  change (parameterMatrix φ).qr = 0
  unfold parameterMatrix
  rw [PRAFormulaParameters.qr_rew]
  exact hφ

/-- The embedded matrix reads the witness from its bound slot and the
parameters from the corresponding free variables. -/
theorem parameterMatrix_eval {M : Type} [Structure language M] {n : ℕ}
    (φ : Semisentence language (n+1)) (e : ℕ → M) (v : M) :
    (parameterMatrix φ).Eval ![v] e ↔
      φ.Eval (Fin.cases v (fun i : Fin n => e i.val)) Empty.elim := by
  unfold parameterMatrix
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := language) ![v] e ∘
      Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val)) ∘ Semiterm.bvar) =
      Fin.cases v (fun i : Fin n => e i.val) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hf : (Semiterm.val (L := language) ![v] e ∘
      Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val)) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

def parameterEnv (n : ℕ) (e : Fin n → M) (i : ℕ) : M :=
  if h : i < n then e ⟨i,h⟩ else Structure.func (L := language) (Code.zero 0) Fin.elim0

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* UniversalAxiom] in
theorem modelParameterTerm (n : ℕ) (t : SyntacticTerm language) (e : Fin n → M) :
    Semiterm.val e Empty.elim (parameterTerm n t) = Semiterm.val ![] (parameterEnv n e) t := by
  unfold parameterTerm
  rw [Semiterm.val_rew]
  congr 1
  · exact Subsingleton.elim _ _
  · funext i
    simp only [Function.comp_apply, parameterEnv]
    change Semiterm.val e Empty.elim (if h : i < n then .bvar ⟨i,h⟩ else applyCode (Code.zero 0) Fin.elim0) = _
    by_cases hi : i < n
    · simp [hi]
    · simp only [hi, ↓reduceDIte, applyCode]
      have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      change Structure.func (L := language) (Code.zero 0) (Semiterm.val e Empty.elim ∘ Fin.elim0) = _
      rw [hz]

theorem modelParameterCode (n : ℕ) (t : SyntacticTerm language) (e : Fin n → M) :
    (Structure.func (L := language) (parameterCode n t) e : M) = Semiterm.val ![] (parameterEnv n e) t := by
  letI : M↓[language] ⊧* PRA := modelCandidatePRA
  exact (modelCompile (parameterTerm n t) e).trans (modelParameterTerm n t e)

theorem modelParameterInstance {n : ℕ} (φ : Semisentence language (n+1)) (t : SyntacticTerm language)
    (e : Fin n → M) (h : ((parameterMatrix φ)/[t]).Eval ![] (parameterEnv n e)) :
    (openMatrixAt φ (parameterCode n t)).Eval e Empty.elim := by
  simp only [Semiformula.eval_substs] at h
  have hargs : (Semiterm.val ![] (parameterEnv n e) ∘ ![t]) =
      ![Semiterm.val ![] (parameterEnv n e) t] := by
    funext i
    exact Fin.cases rfl (fun i => Fin.elim0 i) i
  rw [hargs, parameterMatrix_eval] at h
  have henv : (fun i : Fin n => parameterEnv n e i.val) = e := by
    funext i
    simp [parameterEnv]
  rw [henv] at h
  rw [openMatrixAt, Semiformula.eval_substs]
  have hc : (Semiterm.val e Empty.elim ∘ Fin.cases (applyCode (parameterCode n t) (vars n)) (vars n)) =
      Fin.cases (Semiterm.val ![] (parameterEnv n e) t) e := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (parameterCode n t) (Semiterm.val e Empty.elim ∘ vars n) = _
      have hv : (Semiterm.val e Empty.elim ∘ vars n) = e := by funext j; rfl
      rw [hv, modelParameterCode]
      rfl
    · rfl
  rw [hc]
  exact h

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* UniversalAxiom] in
theorem modelListMember {n : ℕ} (φ : Semisentence language (n+1)) (fallback : Code n)
    (ws : List (Code n)) (w : Code n) (hw : w ∈ ws) (e : Fin n → M)
    (h : (openMatrixAt φ w).Eval e Empty.elim) :
    (openMatrixList φ fallback ws).Eval e Empty.elim := by
  induction ws with
  | nil => simp at hw
  | cons head tail ih =>
      simp only [List.mem_cons] at hw
      change (openMatrixAt φ head).Eval e Empty.elim ∨ (openMatrixList φ fallback tail).Eval e Empty.elim
      rcases hw with rfl | hw
      · exact Or.inl h
      · exact Or.inr (ih hw)

theorem modelExtractedParameterList {n : ℕ} (φ : Semisentence language (n+1)) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared (parameterMatrix φ) axioms) :
    M↓[language] ⊧ (∀⁰* openMatrixList φ (.zero n)
      ((existentialTerms p.derivation).map (parameterCode n))) := by
  have hOpenEmb := parameterMatrix_open φ hOpen
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  have ht := modelPreparedWitness (M := M) (parameterMatrix φ) hOpenEmb axioms hAxioms
    p (parameterEnv n e)
  obtain ⟨t,ht,hm⟩ := ht
  apply modelListMember φ (.zero n) ((existentialTerms p.derivation).map (parameterCode n)) (parameterCode n t)
  · exact List.mem_map.mpr ⟨t,ht,rfl⟩
  · exact modelParameterInstance φ t e hm

end models

/-- Extract a parameterized primitive recursive witness from a prepared sequent. -/
theorem PRA_parameterizedPreparedWitness {n : ℕ} (φ : Semisentence language (n+1)) (hOpen : φ.Open)
    (axioms : List (Sentence language)) (hAxioms : ∀ σ ∈ axioms, UniversalAxiom σ)
    (p : Prepared (parameterMatrix φ) axioms) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* openMatrixAt φ c) := by
  have hDisj : UniversalAxiom ⊢ (∀⁰* openMatrixList φ (.zero n)
      ((existentialTerms p.derivation).map (parameterCode n))) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelExtractedParameterList φ hOpen axioms hAxioms p
  exact PRA_exists_witness_of_openDisjunction φ hOpen (.zero n)
    ((existentialTerms p.derivation).map (parameterCode n)) hDisj

end DiophantineConsistency.HerbrandParameterizedWitness
