import ZFCinPA.ValidatorSeedGicImages222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual finite logical images in the moving-marker seed interpretation.
The source equality axioms retain raw equality. They are not the earlier
C222 Eind images, nor the profile Eqv relation. The concrete source theory
contains EQ, irreflexivity and actual GIC, and no raw container axiom. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedLogicalImages222
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment LO.Entailment.FiniteContext
open LeanProofs.BoundedPAConsistency.InternalRelativization
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedMarkerDischarge222
open ValidatorSeedMarkerRelativization222 ValidatorSeedGicImages222
open ValidatorEqualityImages222 (eqAtom memAtom)
open scoped LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def reflBody : Semiformula V ℒₛₑₜ 1 := eqAtom 0 0
def symmBody : Semiformula V ℒₛₑₜ 2 := eqAtom 1 0 🡒 eqAtom 0 1
def transBody : Semiformula V ℒₛₑₜ 3 := eqAtom 2 1 🡒 eqAtom 1 0 🡒 eqAtom 2 0
def relExtBody (r : (ℒₛₑₜ).Rel 2) : Semiformula V ℒₛₑₜ 4 :=
  (eqAtom 0 2 ⋏ (eqAtom 1 3 ⋏ ⊤)) 🡒
    Semiformula.rel r ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] 🡒
    Semiformula.rel r ![Bootstrapping.Semiterm.bvar 2,Bootstrapping.Semiterm.bvar 3]
def irBody : Semiformula V ℒₛₑₜ 1 := memAtom 0 0 🡒 ⊥

private lemma quote_sentence (σ : SetTheorySentence) :
    (⌜σ⌝ : V)=(⌜(Rewriting.emb σ : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ).val := rfl

theorem refl_binding : (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)=
    qqAlls (reflBody (V := V)).val 1 := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Formula V ℒₛₑₜ)=∀⁰ reflBody from rfl]
  simp [show (1 : V)=0+1 by simp,qqAlls_succ]
theorem symm_binding : (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V)=
    qqAlls (symmBody (V := V)).val 2 := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Formula V ℒₛₑₜ)=∀⁰ ∀⁰ symmBody from rfl]
  simp [show (2 : V)=(0+1)+1 by norm_num,qqAlls_succ]
theorem trans_binding : (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)=
    qqAlls (transBody (V := V)).val 3 := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Formula V ℒₛₑₜ)=∀⁰ ∀⁰ ∀⁰ transBody from rfl]
  simp [show (3 : V)=((0+1)+1)+1 by norm_num,qqAlls_succ]
theorem relExt_binding (r : (ℒₛₑₜ).Rel 2) :
    (⌜(Theory.Eq.relExt r : SetTheorySentence)⌝ : V)=qqAlls (relExtBody (V := V) r).val 4 := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.relExt r) : SetTheoryProposition)⌝ :
    Formula V ℒₛₑₜ)=∀⁰ ∀⁰ ∀⁰ ∀⁰ relExtBody r from rfl]
  simp [show (4 : V)=(((0+1)+1)+1)+1 by norm_num,qqAlls_succ]
theorem ir_binding : (⌜irreflexiveSentence⌝ : V)=qqAlls (irBody (V := V)).val 1 := by
  rw [quote_sentence,show (⌜(Rewriting.emb irreflexiveSentence : SetTheoryProposition)⌝ :
    Formula V ℒₛₑₜ)=∀⁰ irBody from rfl]
  simp [show (1 : V)=0+1 by simp,qqAlls_succ]

private theorem tagged_top {n : ℕ} (j : V) : tagged j (⊤ : Semiformula V ℒₛₑₜ n)=⊤ := by
  ext; exact relativize_verum
private theorem tagged_bot {n : ℕ} (j : V) : tagged j (⊥ : Semiformula V ℒₛₑₜ n)=⊥ := by
  ext; exact relativize_falsum

/-- Open the actual source axiom proof, then reclose its fixed finite matrix
with the accepted moving-marker induction. No interpreted-axiom premise. -/
private theorem finite_image {n : ℕ} (B : Semiformula V ℒₛₑₜ n)
    (σ : SetTheorySentence) (hσ : σ∈seedTheory)
    (hbind : (⌜σ⌝ : V)=qqAlls B.val (n : V)) (hs : B.shift=B)
    (hfix : ∀ j : V, tagged j B=B) (j : V) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜σ⌝ : V))) := by
  have hmem : (⌜σ⌝ : V)∈seedTheory.Δ₁Class := Δ₁Class.mem_iff.mpr hσ
  have horig : Source V ⊢! (⌜(Rewriting.emb σ : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) :=
    TProof.byAxm hmem
  have hp : Provable seedTheory (⌜σ⌝ : V) := tprovable_iff_provable.mp ⟨horig⟩
  rw [hbind] at hp ⊢
  obtain ⟨d,hd⟩ := hp
  have hw := ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) (V := V) (n : V)
  have hq := ModelCodedSpecialization.specializedProofCode_isProof seedTheory (n : V)
    B.val d B.isSemiformula hd
  let Q : Formula V ℒₛₑₜ := ⟨subst ℒₛₑₜ (fvarVec (n : V)) B.val,by simpa using B.isSemiformula.subst hw⟩
  have hQ : Source V ⊢ Q :=
    ⟨ModelCodedOpenSchemaAxioms.typedProofOfCode seedTheory Q _ hq⟩
  have hi : Source V ⊢ emptyAt (Bootstrapping.Semiterm.fvar (j+(n : V))) 🡒 Q := by
    cl_prover [hQ]
  have hi' := tprovable_iff_provable.mp hi
  apply close_guarded B.isSemiformula (by
    simpa only [Bootstrapping.Semiformula.val_shift] using congrArg (fun p => p.val) hs)
  have hfixed : tagRel (j+(n : V)) B.val=B.val := congrArg (fun p => p.val) (hfix _)
  rw [←tagRel_subst (j+(n : V)) B.isSemiformula hw,hfixed]
  simpa only [Bootstrapping.Semiformula.val_imp,empty_binding,Q] using hi'

theorem refl_image (j : V) : Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V))) := by
  apply finite_image reflBody _ (Or.inl (Or.inl Theory.eqAxiom.refl)) refl_binding
  · simp [reflBody,eqAtom]
  · intro k; simp [reflBody,eqAtom,tagged_rel]
theorem symm_image (j : V) : Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V))) := by
  apply finite_image symmBody _ (Or.inl (Or.inl Theory.eqAxiom.symm)) symm_binding
  · simp [symmBody,eqAtom]
  · intro k; simp [symmBody,eqAtom,tagged_imp,tagged_rel]
theorem trans_image (j : V) : Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V))) := by
  apply finite_image transBody _ (Or.inl (Or.inl Theory.eqAxiom.trans)) trans_binding
  · simp [transBody,eqAtom]
  · intro k; simp [transBody,eqAtom,tagged_imp,tagged_rel]
theorem relExt_image (r : (ℒₛₑₜ).Rel 2) (j : V) : Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜(Theory.Eq.relExt r : SetTheorySentence)⌝ : V))) := by
  apply finite_image (relExtBody r) _ (Or.inl (Or.inl (Theory.eqAxiom.relExt r))) (relExt_binding r)
  · simp [relExtBody,eqAtom]
  · intro k; simp [relExtBody,eqAtom,tagged_imp,tagged_and,tagged_rel,tagged_top]
theorem irreflexivity_image (j : V) : Provable seedTheory
    (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜irreflexiveSentence⌝ : V))) := by
  apply finite_image irBody _ (Or.inl (Or.inr rfl)) ir_binding
  · simp [irBody,memAtom]
  · intro k; simp [irBody,memAtom,tagged_imp,tagged_rel,tagged_bot]

/-- The actual equality theory has five cases: no function symbols, two relations. -/
theorem equality_image (σ : SetTheorySentence) (hσ : σ∈𝗘𝗤 ℒₛₑₜ) (j : V) :
    Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j (⌜σ⌝ : V))) := by
  cases hσ with
  | refl => exact refl_image j
  | symm => exact symm_image j
  | trans => exact trans_image j
  | funcExt f => cases f
  | relExt r => cases r with
    | eq => exact relExt_image Language.Eq.eq j
    | mem => exact relExt_image Language.Mem.mem j

private theorem implication_image {p j : V} (hp : IsFormula ℒₛₑₜ p)
    (h : Provable seedTheory (imp ℒₛₑₜ (emptyCode j) (tagRel j p))) :
    Derivable seedTheory (insert (tagRel j p) (insert (emptyGuard j) (sideSet j))) := by
  have he : Derivable seedTheory (insert (emptyCode j) (insert (emptyGuard j) (sideSet j))) :=
    Derivable.em (by simp [empty_typed,emptyGuard_typed,sideSet,isFormulaSet_domSet (domain_typed j)])
      (emptyCode j) (by simp) (by simp [emptyGuard])
  exact NativePeel.derivable_mp (tagRel_typed j hp) h he

theorem axiomImages_equality :
    letI := ValidatorEqualityImages222.equalityDelta
    AxiomImages (𝗘𝗤 ℒₛₑₜ) V := by
  letI := ValidatorEqualityImages222.equalityDelta
  intro p j hp hm _
  obtain ⟨σ,hσ,rfl⟩ := ValidatorEqualityImages222.mem_ch_ofFinite
    (𝗘𝗤 ℒₛₑₜ) Theory.EqAxiom.finite hm
  exact implication_image hp (equality_image σ hσ j)

/-- This concrete source theory does not add NativeTheory's literal container axiom. -/
def logicalTheory : SetTheory := ((𝗘𝗤 ℒₛₑₜ) ∪ {irreflexiveSentence}) ∪ gicTheory
instance logicalTheory_delta1 : logicalTheory.Δ₁ :=
  (ValidatorEqualityImages222.equalityDelta.add
    (Theory.Δ₁.singleton irreflexiveSentence)).add gicTheory_delta1

/-- Exact ofFinite/add recognizers; arbitrary internal GIC closure is retained. -/
theorem axiomImages_logicalTheory : AxiomImages logicalTheory V := by
  intro p j hp hm hj
  change V ⊧/![p] ((ValidatorEqualityImages222.equalityDelta.ch ⋎
    (Theory.Δ₁.singleton irreflexiveSentence).ch) ⋎ gicCh).val at hm
  simp only [HierarchySymbol.Semiformula.val_or,LogicalConnective.HomClass.map_or,
    LogicalConnective.Prop.or_eq] at hm
  rcases hm with (he|hi)|hgic
  · exact axiomImages_equality p j hp he hj
  · have hi' : p=ORingStructure.numeral (Encodable.encode irreflexiveSentence) := by simpa using hi
    rw [hi',numeral_eq_natCast_app,←LO.FirstOrder.Sentence.quote_eq_encode] at hp ⊢
    exact implication_image hp (irreflexivity_image j)
  · exact axiomImages_gicTheory p j hp hgic hj

/-- No remaining axiom-image premise for this concrete, smaller source theory. -/
theorem provable_falsum_of_logicalTheory (h : Provable logicalTheory (^⊥ : V)) :
    Provable seedTheory (^⊥ : V) :=
  provable_falsum_of_tagged axiomImages_logicalTheory h

theorem logicalTheory_refutation_witness [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]
    (h : Provable logicalTheory (^⊥ : V)) :
    ∃ d : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d=2 :=
  ValidatorSeedMarkerRelativization222.refutation_witness axiomImages_logicalTheory h

end LeanProofs.ZFCinPA.ValidatorSeedLogicalImages222
