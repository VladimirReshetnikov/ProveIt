import ZFCinPA.ModelCodedSpecialization

/-!
Direct represented open Separation/Replacement proof constructors.
These use the checked closing axiom code followed by the checked all-internal
specialization operation, without a shift-fixedness premise or a proof chooser.
The matrices may carry arbitrary internal free labels. These wrappers do not
interpret C254 formulas or transport proofs between different languages.
-/
namespace LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedBindFree
open LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- Total on raw formulas, independently of well-formedness or axiom membership. -/
noncomputable def openAxiomProofCode (L : Language) [L.Encodable] [L.LORDefinable]
    (p : V) : V :=
  specializedProofCode L (bv L (bindFreeAt L 0 p)) (bindFreeAt L 0 p)
    (axiomCode (closeFormulaCode L p))

noncomputable def openAxiomProofCodeDef (L : Language) [L.Encodable] [L.LORDefinable] :
    𝚺₁.Semisentence 2 := .mkSigma “out p.
      ∃ b, !(bindFreeAtDef L) b 0 p ∧ ∃ m, !(bvGraph L) m b ∧
      ∃ closed, !qqAllsDef closed b m ∧ ∃ s, !insertDef s closed 0 ∧
      ∃ axiomProof, !axmGraph axiomProof s closed ∧
      !(specializedProofCodeDef L) out m b axiomProof”
instance openAxiomProofCode_defined : 𝚺₁-Function₁[V] (openAxiomProofCode L)
    via openAxiomProofCodeDef L := .mk fun e => by
  simp [openAxiomProofCodeDef,openAxiomProofCode,axiomCode,closeFormulaCode,emptyset_def]

/-- Only this particular closed-code membership is required, not an axiom schema. -/
theorem openAxiomProofCode_isProof (T : Theory L) [T.Δ₁] {p : V}
    (hp : IsFormula L p) (hclosed : closeFormulaCode L p ∈ T.Δ₁Class) :
    Proof T (openAxiomProofCode L p) p := by
  apply openClosedCode_isProof T hp
  have hc : IsFormula L (closeFormulaCode L p) := closeFormulaCode_isFormula hp
  change DerivationOf T (axiomCode (closeFormulaCode L p)) {closeFormulaCode L p}
  refine ⟨by simp only [axiomCode,fstIdx_axm,singleton_eq_insert], Derivation.axm (by simp [hc]) (by simp) hclosed⟩

/-- Convert an explicit literal proof code to the typed carrier without choosing it. -/
noncomputable def typedProofOfCode (T : Theory L) [T.Δ₁] (p : Formula V L)
    (d : V) (hd : Proof T d p.val) : T.internalize V ⊢! p :=
  ⟨d, by simpa only [Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert] using hd⟩
@[simp] lemma typedProofOfCode_val (T : Theory L) [T.Δ₁] (p : Formula V L)
    (d : V) (hd : Proof T d p.val) : (typedProofOfCode T p d hd).val = d := rfl

theorem zfSeparation_isProof (K : Semiformula V ℒₛₑₜ 1) :
    Proof (𝗭𝗙 : SetTheory) (openAxiomProofCode ℒₛₑₜ (sepBody K).val) (sepBody K).val := by
  apply openAxiomProofCode_isProof _ (sepBody K).isSemiformula
  simpa only [closedSeparation,←sepBodyVal_eq K] using closedSeparation_mem_zf K

theorem zfReplacement_isProof (K : Semiformula V ℒₛₑₜ 2) :
    Proof (𝗭𝗙 : SetTheory) (openAxiomProofCode ℒₛₑₜ (repBody K).val) (repBody K).val := by
  apply openAxiomProofCode_isProof _ (repBody K).isSemiformula
  simpa only [closedReplacement,←repBodyVal_eq K] using closedReplacement_mem_zf K

theorem zfcSeparation_isProof (K : Semiformula V ℒₛₑₜ 1) :
    Proof (𝗭𝗙𝗖 : SetTheory) (openAxiomProofCode ℒₛₑₜ (sepBody K).val) (sepBody K).val := by
  apply openAxiomProofCode_isProof _ (sepBody K).isSemiformula
  simpa only [closedSeparation,←sepBodyVal_eq K] using closedSeparation_mem_zfc K

theorem zfcReplacement_isProof (K : Semiformula V ℒₛₑₜ 2) :
    Proof (𝗭𝗙𝗖 : SetTheory) (openAxiomProofCode ℒₛₑₜ (repBody K).val) (repBody K).val := by
  apply openAxiomProofCode_isProof _ (repBody K).isSemiformula
  simpa only [closedReplacement,←repBodyVal_eq K] using closedReplacement_mem_zfc K

noncomputable def zfSeparationProof (K : Semiformula V ℒₛₑₜ 1) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! sepBody K :=
  typedProofOfCode _ _ _ (zfSeparation_isProof K)
noncomputable def zfReplacementProof (K : Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! repBody K :=
  typedProofOfCode _ _ _ (zfReplacement_isProof K)
noncomputable def zfcSeparationProof (K : Semiformula V ℒₛₑₜ 1) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! sepBody K :=
  typedProofOfCode _ _ _ (zfcSeparation_isProof K)
noncomputable def zfcReplacementProof (K : Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! repBody K :=
  typedProofOfCode _ _ _ (zfcReplacement_isProof K)

end LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms
