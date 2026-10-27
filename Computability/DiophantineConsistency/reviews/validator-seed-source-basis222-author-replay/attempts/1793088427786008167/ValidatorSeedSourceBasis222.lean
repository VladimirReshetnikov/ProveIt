import ZFCinPA.ValidatorFullSeedTheory222
import ZFCinPA.ModelCodedOpenSchemaAxioms

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Explicit represented open full-seed proofs and their finite source-theory
basis. All matrix and term parameters may be internally sized. No source
interpretation, raw collection principle, or quotient premise is assumed. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222
open Classical
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
  · have : j=0 := by simpa [←one_add_one_eq_two] using hi
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
private theorem exists_elim {T : InternalTheory V ℒₛₑₜ} {p : Semiformula V ℒₛₑₜ 1}
    {q : Formula V ℒₛₑₜ} (h : T ⊢ p.free 🡒 q.shift) : T ⊢ (∃⁰ p) 🡒 q := by
  have hn : T ⊢ (∼q).shift 🡒 (∼p).free := by
    simpa [Bootstrapping.Semiformula.free] using (show T ⊢ ∼q.shift 🡒 ∼p.free from by cl_prover [h])
  have ha := TProof.generalizeAux hn.get
  have ha' : T ⊢ ∼q 🡒 ∼(∃⁰ p) := by simpa using (show T ⊢ _ from ⟨ha⟩)
  cl_prover [ha']

private theorem exists_project {T : InternalTheory V ℒₛₑₜ} {Γ : List (Formula V ℒₛₑₜ)}
    {p q : Semiformula V ℒₛₑₜ 1} {r : Formula V ℒₛₑₜ}
    (h : Γ ⊢[T] r 🡒 ∃⁰ (p ⋏ q)) : Γ ⊢[T] r 🡒 ∃⁰ p := by
  have he : Γ ⊢[T] (∃⁰ (p ⋏ q)) 🡒 ∃⁰ p := by
    apply TProof.exs_imp_exs!
    simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_and,
      Bootstrapping.Semiformula.substs_and]
    cl_prover
  cl_prover [h,he]

private def source_refl (t : Term V ℒₛₑₜ) : Source V ⊢! eqTerm t t := by
  have hm : (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl Theory.eqAxiom.refl))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) :=
    TProof.byAxm hm
  change Source V ⊢! ∀⁰ eqTerm (Semiterm.bvar 0) (Semiterm.bvar 0) at h
  simpa [eqTerm] using TProof.specialize h t



private def pairMatrix (K : Semiformula V ℒₛₑₜ 2) : Semiformula V ℒₛₑₜ 2 :=
  ((∀⁰ ((⌜seedMem 3 0 1⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) 🡒 ∃⁰
      ((K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (∀⁰ ((⌜seedSubset⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 5) 🡒 ∀⁰
          ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 6)⌝,⌜(#1 : SyntacticSemiterm ℒₛₑₜ 6)⌝]) 🡒
            ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 7)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 7)⌝]) ⋏
              (⌜seedMem 7 0 5⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 7)))))))) ⋏
    (∀⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝,⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝]) 🡒
      ∃⁰ ((K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝,⌜(#3 : SyntacticSemiterm ℒₛₑₜ 4)⌝]) ⋏
        (⌜seedMem 4 0 2⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4)))))

private def pairAt (K : Semiformula V ℒₛₑₜ 2) (a c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (pairMatrix K).subst ![c,a]
private def pairExists (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  (pairMatrix K).subst ![Semiterm.bvar 0,a.bShift]
private theorem pair_exists (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) :
    Source V ⊢ ∃⁰ pairExists K a := by
  simpa [fullSeedBody,pairExists,pairMatrix,SemitermVec.q] using
    TProof.specialize! (⟨openSeedProof K⟩) a

private theorem empty_from_pair (a c : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt ⊥ a c 🡒 emptyAt c := by
  apply deduct'!
  apply TProof.generalize!
  have hp : [pairAt ⊥ a c].map Bootstrapping.Semiformula.shift ⊢[Source V] (pairAt ⊥ a c).shift := by
    simp only [List.map_cons,List.map_nil]
    exact by_axm₀!
  simp only [pairAt,pairMatrix,Bootstrapping.Semiformula.substs_and,Bootstrapping.Semiformula.shift_and] at hp
  have hs := K!_left hp
  have hx := TProof.specializeWithCtx hs.get (Semiterm.fvar 0)
  simp [seedMem,Bootstrapping.Semiformula.free,SemitermVec.q,Bootstrapping.Semiformula.substs_substs,
    Bootstrapping.Semiformula.shift_substs] at hx
  have hx' := exists_project (show _ from ⟨hx⟩)
  have he : Source V ⊢ (∃⁰ (⊥ : Semiformula V ℒₛₑₜ 1)) 🡒 ⊥ :=
    exists_elim (by simp [Bootstrapping.Semiformula.free]; cl_prover)
  have he' := FiniteContext.of'! (Γ := [pairAt ⊥ a c].map Bootstrapping.Semiformula.shift) he
  simp [emptyAt,memTerm,Bootstrapping.Semiformula.free,SemitermVec.q,
    ←Semiterm.bShift_shift_comm]
  cl_prover [hx',he']

end LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222
