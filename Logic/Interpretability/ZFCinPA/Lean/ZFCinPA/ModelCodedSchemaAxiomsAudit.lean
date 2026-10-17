import ZFCinPA.ModelCodedSchemaAxioms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedSchemaAxioms
open scoped LO.FirstOrder.Arithmetic
noncomputable section
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.schemaRecognizer_of_closed_body
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.sep_core_subst_identity
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.rep_core_subst_identity
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.sep_body_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.rep_body_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.sepBody_mem_zf_of_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.repBody_mem_zf_of_shift_fixed
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.zfSeparationProof_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.zfReplacementProof_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.zfcSeparationProof_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedSchemaAxioms.zfcReplacementProof_isProof
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (code : V) (hc : IsSemiformula ℒₛₑₜ ((1 : Nat) : V) code) (hs : shift ℒₛₑₜ code = code) :
    (sepBody (⟨code, hc⟩ : Semiformula V ℒₛₑₜ 1)).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class :=
  sepBody_mem_zf_of_shift_fixed _ (Semiformula.ext hs)
example (code : V) (hc : IsSemiformula ℒₛₑₜ ((2 : Nat) : V) code) (hs : shift ℒₛₑₜ code = code) :
    (repBody (⟨code, hc⟩ : Semiformula V ℒₛₑₜ 2)).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class :=
  repBody_mem_zf_of_shift_fixed _ (Semiformula.ext hs)
example (K : Semiformula V ℒₛₑₜ 1) (hs : K.shift = K) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! sepBody K := zfSeparationProof K hs
example (K : Semiformula V ℒₛₑₜ 2) (hs : K.shift = K) :
    (𝗭𝗙 : SetTheory).internalize V ⊢! repBody K := zfReplacementProof K hs
example (K : Semiformula V ℒₛₑₜ 1) (hs : K.shift = K) :
    ∃ proof : V, Proof (𝗭𝗙 : SetTheory) proof (sepBody K).val :=
  ⟨(zfSeparationProof K hs).val, zfSeparationProof_isProof K hs⟩
example (K : Semiformula V ℒₛₑₜ 2) (hs : K.shift = K) :
    ∃ proof : V, Proof (𝗭𝗙 : SetTheory) proof (repBody K).val :=
  ⟨(zfReplacementProof K hs).val, zfReplacementProof_isProof K hs⟩
example (K : Semiformula V ℒₛₑₜ 1) (hs : K.shift = K) :
    Proof (𝗭𝗙𝗖 : SetTheory) (zfcSeparationProof K hs).val (sepBody K).val :=
  zfcSeparationProof_isProof K hs
example (K : Semiformula V ℒₛₑₜ 2) (hs : K.shift = K) :
    Proof (𝗭𝗙𝗖 : SetTheory) (zfcReplacementProof K hs).val (repBody K).val :=
  zfcReplacementProof_isProof K hs
example : (sepBody (⊤ : Semiformula V ℒₛₑₜ 1)).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class :=
  sepBody_mem_zf_of_shift_fixed _ (by simp)
example : (repBody (⊤ : Semiformula V ℒₛₑₜ 2)).val ∈ (𝗭𝗙 : SetTheory).Δ₁Class :=
  repBody_mem_zf_of_shift_fixed _ (by simp)
