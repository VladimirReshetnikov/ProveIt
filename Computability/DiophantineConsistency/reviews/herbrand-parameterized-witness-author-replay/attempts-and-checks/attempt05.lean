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
    by_cases hi : i < n
    · simp [hi]
    · simp only [hi, ↓reduceDIte, applyCode]
      have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
      rw [hz]

theorem modelParameterCode (n : ℕ) (t : SyntacticTerm language) (e : Fin n → M) :
    (Structure.func (L := language) (parameterCode n t) e : M) = Semiterm.val ![] (parameterEnv n e) t := by
  letI : M↓[language] ⊧* PRA := modelCandidatePRA
  exact (modelCompile (parameterTerm n t) e).trans (modelParameterTerm n t e)

theorem modelParameterInstance {n : ℕ} (φ : Semisentence language (n+1)) (t : SyntacticTerm language)
    (e : Fin n → M) (h : ((parameterMatrix φ)/[t]).Eval ![] (parameterEnv n e)) :
    (openMatrixAt φ (parameterCode n t)).Eval e Empty.elim := by
  simp only [Semiformula.eval_substs] at h
  unfold parameterMatrix at h
  rw [Semiformula.eval_rew] at h
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
  have hb : (Semiterm.val (L := language) (Semiterm.val ![] (parameterEnv n e) ∘ ![t]) (parameterEnv n e) ∘
      (Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val))) ∘ Semiterm.bvar) =
      Fin.cases (Semiterm.val ![] (parameterEnv n e) t) e := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp [Function.comp_def, parameterEnv]
  rw [hb] at h
  have he : (Semiterm.val (L := language) (Semiterm.val ![] (parameterEnv n e) ∘ ![t]) (parameterEnv n e) ∘
      (Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val))) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [he] at h
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

end models
end DiophantineConsistency.HerbrandParameterizedWitness
