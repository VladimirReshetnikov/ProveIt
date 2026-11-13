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
  simpa [val_repSubst3Const] using
    ModelCodedSchemaAxioms.rep_core_subst_identity (⟨k,hk⟩ : Semiformula V ℒₛₑₜ 2)

theorem recognizer_parameter_bound (K : Semiformula V ℒₛₑₜ 2) :
    K.val ≤ seedRecognizerBodyVal K.val := by
  have h := ValidatorFullSeedTheory222.neg_subst_le_fullSeedBody (∼K).val
  rw [subst01 (∼K).isSemiformula] at h
  simpa [seedRecognizerBodyVal] using h

theorem closedSeed_recognized (K : Semiformula V ℒₛₑₜ 2) : SeedR (closedSeedCode K.val) := by
  apply closeFormulaCode_schemaRecognizer seedRecognizerBodyVal (∼K)
  · simp [seedRecognizerBodyVal,fullSeedBodyVal_eq]
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
    (by simp [seedInstanceCode_eq K.isSemiformula,fullSeedBodyVal_eq]) (closedSeed_mem K)
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
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) t.bShift 🡒 ⊥)
def singletonAt (c t : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡘 eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift)

/-- The function-free source language has no closed bound-variable slot. -/
theorem term_is_fvar (t : Term V ℒₛₑₜ) : ∃ x : V, t=Bootstrapping.Semiterm.fvar x := by
  obtain ⟨x,hx⟩ := SetRelativization.isTerm_eq_fvar t.isSemiterm
  exact ⟨x, by ext; exact hx⟩

/-- Ordinary classical source logic, with the eigenvariable shift explicit. -/
theorem exists_elim {T : InternalTheory V ℒₛₑₜ} {p : Semiformula V ℒₛₑₜ 1}
    {q : Formula V ℒₛₑₜ} (h : T ⊢ p.free 🡒 q.shift) : T ⊢ (∃⁰ p) 🡒 q := by
  have hn : T ⊢ (∼q).shift 🡒 (∼p).free := by
    simpa [Bootstrapping.Semiformula.free] using (show T ⊢ ∼q.shift 🡒 ∼p.free from by cl_prover [h])
  have ha := TProof.generalizeAux hn.get
  have ha' : T ⊢ ∼q 🡒 ∼(∃⁰ p) := by simpa using (show T ⊢ _ from ⟨ha⟩)
  cl_prover [ha']

theorem exists_project {T : InternalTheory V ℒₛₑₜ} {Γ : List (Formula V ℒₛₑₜ)}
    {p q : Semiformula V ℒₛₑₜ 1} {r : Formula V ℒₛₑₜ}
    (h : Γ ⊢[T] r 🡒 ∃⁰ (p ⋏ q)) : Γ ⊢[T] r 🡒 ∃⁰ p := by
  have he : Γ ⊢[T] (∃⁰ (p ⋏ q)) 🡒 ∃⁰ p := by
    apply TProof.exs_imp_exs!
    simp only [Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_and,
      Bootstrapping.Semiformula.substs_and]
    cl_prover
  cl_prover [h,he]

def source_refl (t : Term V ℒₛₑₜ) : Source V ⊢! eqTerm t t := by
  have hm : (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl Theory.eqAxiom.refl))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) :=
    TProof.byAxm hm
  change Source V ⊢! ∀⁰ eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 0) at h
  simpa [eqTerm] using TProof.specialize h t

def pairMatrix (K : Semiformula V ℒₛₑₜ 2) : Semiformula V ℒₛₑₜ 2 :=
  ValidatorSourceFullSeed222.seedPairMatrix K

def pairAt (K : Semiformula V ℒₛₑₜ 2) (a c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (pairMatrix K).subst ![c,a]
def pairExists (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  (pairMatrix K).subst ![Bootstrapping.Semiterm.bvar 0,a.bShift]
theorem pair_exists (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) :
    Source V ⊢ ∃⁰ pairExists K a := by
  simpa [fullSeedBody,pairExists,pairMatrix,SemitermVec.q] using
    TProof.specialize! (⟨openSeedProof K⟩) a

attribute [local irreducible] pairAt pairExists pairMatrix

theorem pair_support (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt K a c 🡒 (memTerm y c 🡒 ∃⁰ K.subst ![y.bShift,Bootstrapping.Semiterm.bvar 0]) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  apply deduct'!
  have hp : [pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V] pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [pairAt,pairMatrix,Bootstrapping.Semiformula.substs_and] at hp
  have hs := K!_left hp
  simp only [Bootstrapping.Semiformula.substs_all] at hs
  have hx := TProof.specialize_with_ctx! hs (Bootstrapping.Semiterm.fvar y)
  simp only [Bootstrapping.Semiformula.substs_substs,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_ex,Bootstrapping.Semiformula.substs_and] at hx
  have hx' := exists_project hx
  simpa [pairAt,pairMatrix,memTerm,seedMem,SemitermVec.q,Bootstrapping.Semiformula.substs_substs,
    Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail] using hx'

theorem pair_request (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt K a c 🡒 (K.subst ![y,a] 🡒
      ∃⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,a.bShift] ⋏ memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift)) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  apply deduct'!
  have hp : [pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V] pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [pairAt,pairMatrix,Bootstrapping.Semiformula.substs_and] at hp
  have hs := K!_right hp
  simp only [Bootstrapping.Semiformula.substs_all] at hs
  have hx := TProof.specialize_with_ctx! hs (Bootstrapping.Semiterm.fvar y)
  simpa [pairAt,pairMatrix,memTerm,seedMem,SemitermVec.q,Bootstrapping.Semiformula.substs_substs,
    Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail] using hx

@[simp] theorem pairAt_shift (K : Semiformula V ℒₛₑₜ 2) (a c : Term V ℒₛₑₜ) :
    (pairAt K a c).shift=pairAt K.shift a.shift c.shift := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [pairAt,pairMatrix,seedMem,seedSubset,Bootstrapping.Semiformula.shift_substs,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]

@[simp] theorem pairExists_free (K : Semiformula V ℒₛₑₜ 2) (a : Term V ℒₛₑₜ) :
    (pairExists K a).free=pairAt K.shift a.shift (Bootstrapping.Semiterm.fvar 0) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  simp [pairExists,pairAt,pairMatrix,seedMem,seedSubset,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]

private theorem empty_from_pair (a c : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt ⊥ a c 🡒 emptyAt c := by
  have hs := pair_support ⊥ a.shift c.shift (Bootstrapping.Semiterm.fvar 0)
  have he : Source V ⊢ (∃⁰ (⊥ : Semiformula V ℒₛₑₜ 1)) 🡒 ⊥ :=
    exists_elim (by simp [Bootstrapping.Semiformula.free])
  simp only [Bootstrapping.Semiformula.substs_falsum] at hs
  have hh : Source V ⊢ (pairAt ⊥ a c).shift 🡒
      (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡒 ⊥).free := by
    simpa [pairAt_shift, Bootstrapping.Semiformula.shift_falsum, memTerm,
      Bootstrapping.Semiformula.free, ←Bootstrapping.Semiterm.bShift_shift_comm] using
      (show Source V ⊢ pairAt ⊥ a.shift c.shift 🡒
        memTerm (Bootstrapping.Semiterm.fvar 0) c.shift 🡒 ⊥ from by cl_prover [hs,he])
  exact ⟨TProof.generalizeAux hh.get⟩

theorem source_symm (t u : Term V ℒₛₑₜ) : Source V ⊢ eqTerm t u 🡒 eqTerm u t := by
  have hm : (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl Theory.eqAxiom.symm))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) := TProof.byAxm hm
  have hq : (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ (Bootstrapping.Semiformula.nrel Language.Eq.eq
        ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0] ⋎
        eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) := rfl
  rw [hq] at h
  have h' : Source V ⊢! ∀⁰ ∀⁰ (eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) 🡒
      eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) := by
    simpa [eqTerm,Bootstrapping.Semiformula.imp_def] using h
  simpa [eqTerm] using (show Source V ⊢ _ from ⟨TProof.specialize₂ h' u t⟩)

theorem source_mem_ext (t u c d : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm t u 🡒 eqTerm c d 🡒 memTerm t c 🡒 memTerm u d := by
  have hm : (⌜(Theory.Eq.relExt Language.Mem.mem : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl (Theory.eqAxiom.relExt _)))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.relExt Language.Mem.mem) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) := TProof.byAxm hm
  have hq : (⌜(Rewriting.emb (Theory.Eq.relExt Language.Mem.mem) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ ∀⁰ ∀⁰
      ((Bootstrapping.Semiformula.nrel Language.Eq.eq ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 2] ⋎
        (Bootstrapping.Semiformula.nrel Language.Eq.eq ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 3] ⋎ ⊥)) ⋎
        (Bootstrapping.Semiformula.nrel Language.Mem.mem ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] ⋎
        memTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 3))) := rfl
  rw [hq] at h
  have h' : Source V ⊢! ∀⁰ ∀⁰ ∀⁰ ∀⁰
      ((eqTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 2) ⋏
        (eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 3) ⋏ ⊤)) 🡒
        memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
        memTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 3)) := by
    simpa [eqTerm,memTerm,Bootstrapping.Semiformula.imp_def] using h
  have hh : Source V ⊢ (eqTerm t u ⋏ (eqTerm c d ⋏ ⊤)) 🡒 memTerm t c 🡒 memTerm u d := by
    simpa [eqTerm,memTerm] using (show Source V ⊢ _ from ⟨TProof.specialize₄ h' t c u d⟩)
  cl_prover [hh]

theorem source_mem_congr (t u c : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm t u 🡒 memTerm t c 🡒 memTerm u c := by
  have hr : Source V ⊢ eqTerm c c := ⟨source_refl c⟩
  cl_prover [source_mem_ext t u c c,hr]

theorem source_trans (t u v : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm t u 🡒 eqTerm u v 🡒 eqTerm t v := by
  have hm : (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inl Theory.eqAxiom.trans))
  have h : Source V ⊢! (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) := TProof.byAxm hm
  have hq : (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ)=
      ∀⁰ ∀⁰ ∀⁰ (Bootstrapping.Semiformula.nrel Language.Eq.eq
        ![Bootstrapping.Semiterm.bvar 2,Bootstrapping.Semiterm.bvar 1] ⋎
        (Bootstrapping.Semiformula.nrel Language.Eq.eq
          ![Bootstrapping.Semiterm.bvar 1,Bootstrapping.Semiterm.bvar 0] ⋎
          eqTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 0))) := rfl
  rw [hq] at h
  have h' : Source V ⊢! ∀⁰ ∀⁰ ∀⁰
      (eqTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 1) 🡒
       eqTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) 🡒
       eqTerm (Bootstrapping.Semiterm.bvar 2) (Bootstrapping.Semiterm.bvar 0)) := by
    simpa [eqTerm,Bootstrapping.Semiformula.imp_def] using h
  simpa [eqTerm] using (show Source V ⊢ _ from ⟨TProof.specialize₃ h' v u t⟩)

private def hitBody (t c : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift ⋏ memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift
private theorem hit_mem (t c : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ hitBody t c) 🡒 memTerm t c := by
  apply exists_elim
  have h := source_mem_congr (Bootstrapping.Semiterm.fvar 0) t.shift c.shift
  simpa [hitBody,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    ←Bootstrapping.Semiterm.bShift_shift_comm] using
    (show Source V ⊢ (eqTerm (Bootstrapping.Semiterm.fvar 0) t.shift ⋏
      memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) 🡒 memTerm t.shift c.shift from by cl_prover [h])

private def singletonMatrix (t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 2 :=
  eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift.bShift
@[simp] private theorem singletonMatrix_shift (t : Term V ℒₛₑₜ) :
    (singletonMatrix t).shift=singletonMatrix t.shift := by
  simp [singletonMatrix,eqTerm,←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] private theorem singletonMatrix_subst {n : ℕ} (t : V) (u v : Semiterm V ℒₛₑₜ n) :
    (singletonMatrix (Bootstrapping.Semiterm.fvar t)).subst ![u,v]=eqTerm u (Bootstrapping.Semiterm.fvar t) := by
  simp [singletonMatrix,eqTerm]
attribute [local irreducible] singletonMatrix

private theorem singleton_member (a c t : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (singletonMatrix t) a c 🡒 memTerm t c := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  have h := pair_request (singletonMatrix (Bootstrapping.Semiterm.fvar t))
    (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c) (Bootstrapping.Semiterm.fvar t)
  have h' : Source V ⊢ pairAt (singletonMatrix (Bootstrapping.Semiterm.fvar t))
      (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c) 🡒
      eqTerm (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar t) 🡒
      ∃⁰ hitBody (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar c) := by
    simpa only [singletonMatrix_subst,Bootstrapping.Semiterm.bShift_fvar,hitBody] using h
  have hr : Source V ⊢ eqTerm (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar t) := ⟨source_refl _⟩
  have hm := hit_mem (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar c)
  cl_prover [h',hr,hm]

private theorem singleton_cover (a c t y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (singletonMatrix t) a c 🡒 (memTerm y c 🡒 eqTerm y t) := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  have h := pair_support (singletonMatrix (Bootstrapping.Semiterm.fvar t)) a c (Bootstrapping.Semiterm.fvar y)
  simp only [Bootstrapping.Semiterm.bShift_fvar,singletonMatrix_subst] at h
  have he : Source V ⊢ (∃⁰ eqTerm (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar t)) 🡒
      eqTerm (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar t) := by
    apply exists_elim
    simp [eqTerm,Bootstrapping.Semiformula.free]
  cl_prover [h,he]

private theorem singleton_from_pair (a c t : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (singletonMatrix t) a c 🡒 singletonAt c t := by
  have hc := singleton_cover a.shift c.shift t.shift (Bootstrapping.Semiterm.fvar 0)
  have hm := singleton_member a.shift c.shift t.shift
  have hs := source_symm (Bootstrapping.Semiterm.fvar 0) t.shift
  have ht := source_mem_congr t.shift (Bootstrapping.Semiterm.fvar 0) c.shift
  have hh : Source V ⊢ (pairAt (singletonMatrix t) a c).shift 🡒
      (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡘
        eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift).free := by
    simpa [pairAt_shift,singletonMatrix_shift,memTerm,eqTerm,Bootstrapping.Semiformula.free,
      ←Bootstrapping.Semiterm.bShift_shift_comm] using
      (show Source V ⊢ pairAt (singletonMatrix t.shift) a.shift c.shift 🡒
        (memTerm (Bootstrapping.Semiterm.fvar 0) c.shift 🡘
          eqTerm (Bootstrapping.Semiterm.fvar 0) t.shift) from by cl_prover [hc,hm,hs,ht])
  exact ⟨TProof.generalizeAux hh.get⟩

/-- A literal source formula; the inner index0 is the tested member. -/
def emptyBody : Semiformula V ℒₛₑₜ 1 :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒 ⊥)
def singletonBody (t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift.bShift)
def tagBody (t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0)

@[simp] theorem emptyBody_free : (emptyBody : Semiformula V ℒₛₑₜ 1).free=
    emptyAt (Bootstrapping.Semiterm.fvar 0) := by
  simp only [emptyBody,emptyAt,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_all,Bootstrapping.Semiformula.shift_imp,
    Bootstrapping.Semiformula.shift_rel,Bootstrapping.Semiformula.shift_falsum,
    Bootstrapping.Semiformula.substs_all,Bootstrapping.Semiformula.substs_imp,
    Bootstrapping.Semiformula.substs_rel,Bootstrapping.Semiformula.substs_falsum,
    Matrix.map_cons,Matrix.map_nil,Matrix.cons_val_zero,Matrix.cons_val_one,
    Bootstrapping.Semiterm.shift_bvar,
    Bootstrapping.Semiterm.substs_bvar,SemitermVec.q,Bootstrapping.Semiterm.bShift_fvar]

@[simp] theorem tagQuantifier_free :
    ((∃⁰ memTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)) :
      Semiformula V ℒₛₑₜ 1).free=∃⁰ tagBody (Bootstrapping.Semiterm.fvar 0) := by
  simp only [tagBody,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_exs,Bootstrapping.Semiformula.shift_rel,
    Bootstrapping.Semiformula.substs_ex,Bootstrapping.Semiformula.substs_rel,
    Matrix.map_cons,Matrix.map_nil,Matrix.cons_val_zero,Matrix.cons_val_one,
    Bootstrapping.Semiterm.shift_bvar,
    Bootstrapping.Semiterm.substs_bvar,SemitermVec.q,Bootstrapping.Semiterm.bShift_fvar]

attribute [local irreducible] emptyBody tagBody

theorem empty_object : Source V ⊢ ∃⁰ emptyBody := by
  have hm : Source V ⊢ (∃⁰ pairExists ⊥ (Bootstrapping.Semiterm.fvar 0)) 🡒 ∃⁰ emptyBody := by
    apply FiniteContext.provable_iff_provable.mpr
    apply TProof.exs_imp_exs!
    apply FiniteContext.of'!
    rw [pairExists_free]
    simpa only [emptyBody_free,Bootstrapping.Semiformula.shift_falsum,
      Bootstrapping.Semiterm.shift_fvar,zero_add] using
      empty_from_pair (Bootstrapping.Semiterm.fvar 1) (Bootstrapping.Semiterm.fvar 0)
  exact ⟨hm.get ⨀ (pair_exists ⊥ (Bootstrapping.Semiterm.fvar 0)).get⟩

theorem singleton_object (t : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ singletonBody t := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  have hm : Source V ⊢ (∃⁰ pairExists (singletonMatrix (Bootstrapping.Semiterm.fvar t)) (Bootstrapping.Semiterm.fvar t)) 🡒 ∃⁰ singletonBody (Bootstrapping.Semiterm.fvar t) := by
    apply FiniteContext.provable_iff_provable.mpr
    apply TProof.exs_imp_exs!
    apply FiniteContext.of'!
    rw [pairExists_free]
    simpa [singletonBody,singletonAt,eqTerm,memTerm,Bootstrapping.Semiformula.free,
      SemitermVec.q,←Bootstrapping.Semiterm.bShift_shift_comm] using
      singleton_from_pair (Bootstrapping.Semiterm.fvar t).shift (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar t).shift
  exact ⟨hm.get ⨀ (pair_exists (singletonMatrix (Bootstrapping.Semiterm.fvar t)) (Bootstrapping.Semiterm.fvar t)).get⟩

theorem tagged_nonempty (t : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ tagBody t := by
  have hm : Source V ⊢ (∃⁰ pairExists (singletonMatrix t) t) 🡒 ∃⁰ tagBody t := by
    apply FiniteContext.provable_iff_provable.mpr
    apply TProof.exs_imp_exs!
    apply FiniteContext.of'!
    rw [pairExists_free]
    simpa [tagBody,memTerm,Bootstrapping.Semiformula.free,
      ←Bootstrapping.Semiterm.bShift_shift_comm] using
      singleton_member t.shift (Bootstrapping.Semiterm.fvar 0) t.shift
  exact ⟨hm.get ⨀ (pair_exists (singletonMatrix t) t).get⟩

theorem all_tagged_nonempty : Source V ⊢ ∀⁰ ∃⁰ memTerm
    (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) := by
  apply TProof.all!
  rw [tagQuantifier_free]
  exact tagged_nonempty (Bootstrapping.Semiterm.fvar 0)

theorem empty_marker_with_inhabited_tag : Source V ⊢ (∃⁰
    (emptyBody ⋏ (∃⁰ memTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)))) := by
  have hm : Source V ⊢ (∃⁰ emptyBody) 🡒 ∃⁰
      (emptyBody ⋏ (∃⁰ memTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0))) := by
    apply FiniteContext.provable_iff_provable.mpr
    apply TProof.exs_imp_exs!
    apply FiniteContext.of'!
    have ht := tagged_nonempty (Bootstrapping.Semiterm.fvar 0 : Term V ℒₛₑₜ)
    change Source V ⊢ emptyBody.free 🡒
      (emptyBody ⋏ (∃⁰ memTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0))).free
    simp only [Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_and,
      Bootstrapping.Semiformula.substs_and]
    change Source V ⊢ emptyBody.free 🡒 (emptyBody.free ⋏
      ((∃⁰ memTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)) : Semiformula V ℒₛₑₜ 1).free)
    rw [tagQuantifier_free]
    cl_prover [ht]
  exact ⟨hm.get ⨀ empty_object.get⟩

end LeanProofs.ZFCinPA.ValidatorSeedSourceBasis222
