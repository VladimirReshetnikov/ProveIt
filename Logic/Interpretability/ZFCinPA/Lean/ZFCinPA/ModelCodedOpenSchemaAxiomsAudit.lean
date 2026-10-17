import ZFCinPA.ModelCodedOpenSchemaAxioms
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.openAxiomProofCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.openAxiomProofCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.typedProofOfCode_val
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfSeparation_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfReplacement_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfcSeparation_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfcReplacement_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfSeparationProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfReplacementProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfcSeparationProof
#print axioms LeanProofs.ZFCinPA.ModelCodedOpenSchemaAxioms.zfcReplacementProof
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
example : 𝚺₁-Function₁[V] (openAxiomProofCode L) via openAxiomProofCodeDef L := inferInstance
example (T : Theory L) [T.Δ₁] {p : V} (hp : IsFormula L p)
    (hc : LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closeFormulaCode L p ∈ T.Δ₁Class) :
    Proof T (openAxiomProofCode L p) p := openAxiomProofCode_isProof T hp hc
example (T : Theory L) [T.Δ₁] (p : Formula V L) (d : V) (hd : Proof T d p.val) :
    (typedProofOfCode T p d hd).val = d := rfl
example (K : Semiformula V ℒₛₑₜ 1) : Proof (𝗭𝗙 : SetTheory)
    (openAxiomProofCode ℒₛₑₜ (sepBody K).val) (sepBody K).val := zfSeparation_isProof K
example (K : Semiformula V ℒₛₑₜ 2) : Proof (𝗭𝗙 : SetTheory)
    (openAxiomProofCode ℒₛₑₜ (repBody K).val) (repBody K).val := zfReplacement_isProof K
example (K : Semiformula V ℒₛₑₜ 1) : Proof (𝗭𝗙𝗖 : SetTheory)
    (openAxiomProofCode ℒₛₑₜ (sepBody K).val) (sepBody K).val := zfcSeparation_isProof K
example (K : Semiformula V ℒₛₑₜ 2) : Proof (𝗭𝗙𝗖 : SetTheory)
    (openAxiomProofCode ℒₛₑₜ (repBody K).val) (repBody K).val := zfcReplacement_isProof K
example (K : Semiformula V ℒₛₑₜ 1) : (𝗭𝗙 : SetTheory).internalize V ⊢! sepBody K := zfSeparationProof K
example (K : Semiformula V ℒₛₑₜ 2) : (𝗭𝗙 : SetTheory).internalize V ⊢! repBody K := zfReplacementProof K
example (K : Semiformula V ℒₛₑₜ 1) : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! sepBody K := zfcSeparationProof K
example (K : Semiformula V ℒₛₑₜ 2) : (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! repBody K := zfcReplacementProof K
example (K : Semiformula V ℒₛₑₜ 1) : (zfSeparationProof K).val = openAxiomProofCode ℒₛₑₜ (sepBody K).val := rfl
example (K : Semiformula V ℒₛₑₜ 2) : (zfReplacementProof K).val = openAxiomProofCode ℒₛₑₜ (repBody K).val := rfl
example (K : Semiformula V ℒₛₑₜ 1) : (zfcSeparationProof K).val = openAxiomProofCode ℒₛₑₜ (sepBody K).val := rfl
example (K : Semiformula V ℒₛₑₜ 2) : (zfcReplacementProof K).val = openAxiomProofCode ℒₛₑₜ (repBody K).val := rfl
example (K : Semiformula V ℒₛₑₜ 2) : Provable (𝗭𝗙𝗖 : SetTheory) (repBody K).val :=
  ⟨openAxiomProofCode ℒₛₑₜ (repBody K).val,zfcReplacement_isProof K⟩
