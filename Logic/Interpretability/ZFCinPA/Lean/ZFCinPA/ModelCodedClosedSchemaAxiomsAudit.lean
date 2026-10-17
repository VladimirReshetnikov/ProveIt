import ZFCinPA.ModelCodedClosedSchemaAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closeFormulaCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closeFormulaCode_isFormula
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closeFormulaCode_schemaRecognizer
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedSeparation_recognized
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedReplacement_recognized
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedSeparation_mem_zf
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedReplacement_mem_zf
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedSeparation_mem_zfc
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedReplacement_mem_zfc
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedSeparation_zf_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedReplacement_zf_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedSeparation_zfc_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms.closedReplacement_zfc_isProof
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
example : 𝚺₁-Function₁[V] (closeFormulaCode L) via closeFormulaCodeDef L := inferInstance
example {p : V} (hp : IsFormula L p) : IsFormula L (closeFormulaCode L p) :=
  closeFormulaCode_isFormula hp
example {a : Nat} (F : V → V) (K : Semiformula V L a)
    (hF : IsFormula L (F K.val)) (hb : K.val ≤ F K.val) :
    SchemaRecognizer L a F (closeFormulaCode L (F K.val)) :=
  closeFormulaCode_schemaRecognizer F K hF hb
example (K : Semiformula V ℒₛₑₜ 1) : SepR (closedSeparation K).val := closedSeparation_recognized K
example (K : Semiformula V ℒₛₑₜ 2) : RepR (closedReplacement K).val := closedReplacement_recognized K
example (K : Semiformula V ℒₛₑₜ 1) : (closedSeparation K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class := closedSeparation_mem_zf K
example (K : Semiformula V ℒₛₑₜ 2) : (closedReplacement K).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class := closedReplacement_mem_zf K
example (K : Semiformula V ℒₛₑₜ 1) : (closedSeparation K).val ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := closedSeparation_mem_zfc K
example (K : Semiformula V ℒₛₑₜ 2) : (closedReplacement K).val ∈ (𝗭𝗙𝗖 : SetTheory).Δ₁Class := closedReplacement_mem_zfc K
example (K : Semiformula V ℒₛₑₜ 1) : Proof (𝗭𝗙 : SetTheory)
    (axiomCode (closedSeparation K).val) (closedSeparation K).val := closedSeparation_zf_isProof K
example (K : Semiformula V ℒₛₑₜ 2) : Proof (𝗭𝗙 : SetTheory)
    (axiomCode (closedReplacement K).val) (closedReplacement K).val := closedReplacement_zf_isProof K
example (K : Semiformula V ℒₛₑₜ 1) : Proof (𝗭𝗙𝗖 : SetTheory)
    (axiomCode (closedSeparation K).val) (closedSeparation K).val := closedSeparation_zfc_isProof K
example (K : Semiformula V ℒₛₑₜ 2) : Proof (𝗭𝗙𝗖 : SetTheory)
    (axiomCode (closedReplacement K).val) (closedReplacement K).val := closedReplacement_zfc_isProof K
