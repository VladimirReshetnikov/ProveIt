import ZFCinPA.ValidatorFullSeedTheory222
import ZFCinPA.ModelCodedOpenSchemaAxioms

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Explicit represented open full-seed proofs and their finite source-theory
basis. All matrix and term parameters may be internally sized. No source
interpretation, raw collection principle, or quotient premise is assumed. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment LO.Entailment.FiniteContext
open ValidatorSourceFullSeed222 ValidatorFullSeedTheory222
open ModelCodedClosedSchemaAxioms ModelCodedOpenSchemaAxioms
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A total raw constructor; its literal full-body identity requires typing. -/
def seedInstanceCode (k : V) : V := seedRecognizerBodyVal (Bootstrapping.neg ℒₛₑₜ k)
def closedSeedCode (k : V) : V := closeFormulaCode ℒₛₑₜ (seedInstanceCode k)
def openSeedProofCode (k : V) : V := openAxiomProofCode ℒₛₑₜ (seedInstanceCode k)

def seedInstanceGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out k. ∃ nk, !(Bootstrapping.negGraph ℒₛₑₜ) nk k ∧ !recognizerBodyGraph out nk”
def closedSeedGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out k. ∃ p, !seedInstanceGraph p k ∧ !(closeFormulaCodeDef ℒₛₑₜ) out p”
def openSeedProofGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out k. ∃ p, !seedInstanceGraph p k ∧ !(openAxiomProofCodeDef ℒₛₑₜ) out p”
instance seedInstance_defined : 𝚺₁-Function₁[V] seedInstanceCode via seedInstanceGraph :=
  .mk fun v => by simp [seedInstanceGraph,seedInstanceCode]
instance closedSeed_defined : 𝚺₁-Function₁[V] closedSeedCode via closedSeedGraph :=
  .mk fun v => by simp [closedSeedGraph,closedSeedCode]
instance openSeedProof_defined : 𝚺₁-Function₁[V] openSeedProofCode via openSeedProofGraph :=
  .mk fun v => by simp [openSeedProofGraph,openSeedProofCode]

theorem seedInstanceCode_eq {k : V} (hk : IsSemiformula ℒₛₑₜ 2 k) :
    seedInstanceCode k=fullSeedBodyVal k := by
  simp only [seedInstanceCode,seedRecognizerBodyVal,hk.isUFormula.neg_neg]

private theorem subst01 {k : V} (hk : IsSemiformula ℒₛₑₜ 2 k) :
    subst ℒₛₑₜ (^#0∷^#1∷0) k=k := by
  apply Bootstrapping.subst_eq_self hk (by simp)
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j,rfl⟩
  · simp
  · have : j=0 := by omega
    subst j
    simp

private theorem negative_core_le_body (k : V) :
    Bootstrapping.neg ℒₛₑₜ (subst ℒₛₑₜ (^#0∷^#1∷0) k) ≤ fullSeedBodyVal k := by
  unfold fullSeedBodyVal Bootstrapping.imp
  exact le_of_lt <| lt_trans (lt_or_left _ _) <| lt_trans (lt_forall _) <|
    lt_trans (lt_or_right _ _) <| lt_trans (lt_forall _) <|
    lt_trans (lt_K!_right _ _) <| lt_trans (lt_exists _) <|
    lt_trans (lt_or_right _ _) <| lt_trans (lt_forall _) <|
    lt_trans (lt_K!_left _ _) <| lt_trans (lt_exists _) (lt_forall _)

theorem recognizer_parameter_bound (K : Semiformula V ℒₛₑₜ 2) :
    K.val ≤ seedRecognizerBodyVal K.val := by
  have h := negative_core_le_body (∼K).val
  rw [subst01 (∼K).isSemiformula] at h
  simpa [seedRecognizerBodyVal] using h

theorem closedSeed_recognized (K : Semiformula V ℒₛₑₜ 2) : SeedR (closedSeedCode K.val) := by
  apply closeFormulaCode_schemaRecognizer seedRecognizerBodyVal (∼K)
  · simpa [seedRecognizerBodyVal,fullSeedBodyVal_eq] using (fullSeedBody K).isSemiformula
  · exact recognizer_parameter_bound (∼K)

theorem closedSeed_mem (K : Semiformula V ℒₛₑₜ 2) :
    closedSeedCode K.val ∈ seedTheory.Δ₁Class := by
  change V ⊧/![closedSeedCode K.val] ((ValidatorEqualityImages222.equalityDelta.ch ⋎
    (Theory.Δ₁.singleton irreflexiveSentence).ch) ⋎ seedCh).val
  have h := closedSeed_recognized K
  simp only [HierarchySymbol.Semiformula.val_or,LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq]
  exact Or.inr (by simpa using h)

theorem openSeed_isProof (K : Semiformula V ℒₛₑₜ 2) :
    Proof seedTheory (openSeedProofCode K.val) (fullSeedBody K).val := by
  have h := openAxiomProofCode_isProof seedTheory
    (p := seedInstanceCode K.val)
    (by simpa [seedInstanceCode_eq K.isSemiformula,fullSeedBodyVal_eq] using
      (fullSeedBody K).isSemiformula) (closedSeed_mem K)
  simpa [openSeedProofCode,seedInstanceCode_eq K.isSemiformula,fullSeedBodyVal_eq] using h

def openSeedProof (K : Semiformula V ℒₛₑₜ 2) :
    seedTheory.internalize V ⊢! fullSeedBody K :=
  typedProofOfCode seedTheory (fullSeedBody K) (openSeedProofCode K.val) (openSeed_isProof K)
@[simp] theorem openSeedProof_val (K : Semiformula V ℒₛₑₜ 2) :
    (openSeedProof K).val=openSeedProofCode K.val := rfl

abbrev Source (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] := seedTheory.internalize V

def eqTerm {n : ℕ} (t u : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  Semiformula.rel Language.Eq.eq ![t,u]
def memTerm {n : ℕ} (t u : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  Semiformula.rel Language.Mem.mem ![t,u]
def emptyAt (t : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ (memTerm (Semiterm.bvar 0) t.bShift 🡒 ⊥)
def singletonAt (c t : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ (memTerm (Semiterm.bvar 0) c.bShift 🡘 eqTerm (Semiterm.bvar 0) t.bShift)

/-- Ordinary classical source logic, with the eigenvariable shift explicit. -/
private def exists_elim {T : InternalTheory V ℒₛₑₜ} {p : Semiformula V ℒₛₑₜ 1}
    {q : Formula V ℒₛₑₜ} (h : T ⊢! p.free 🡒 q.shift) : T ⊢! (∃⁰ p) 🡒 q := by
  have hn : T ⊢! (∼q).shift 🡒 (∼p).free := by
    simpa using (show T ⊢! ∼q.shift 🡒 ∼p.free from by cl_prover [h])
  have ha := TProof.generalizeAux hn
  simpa using (show T ⊢! (∃⁰ p) 🡒 q from by cl_prover [ha])

private def source_refl (t : Term V ℒₛₑₜ) : Source V ⊢! eqTerm t t := by
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) :=
    TProof.byAxm (by simp [tmem,seedTheory]; exact Or.inl (Or.inl (Theory.Eq.refl_mem ℒₛₑₜ)))
  simpa [eqTerm] using TProof.specialize h t

end LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222
