import ZFCinPA.ModelCodedSpecialization
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.ModelCodedBindFree
open LeanProofs.ZFCinPA.ModelCodedClosedSchemaAxioms
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open scoped LO.FirstOrder.Arithmetic
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.qVecIter_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.qVecIter_succ_left
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.qVecIter_isSemitermVec
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.subst_qqAlls
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.qVecIter_free_spec
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.fvarVec_subst_qVecIter
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.specializeCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.specializeCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.advance_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.runState_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.runState_succ_left
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.specializedProofCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.specializedProofCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedSpecialization.openClosedCode_isProof
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
example : 𝚺₁-Function₂[V] (qVecIter L) via qVecIterDef L := inferInstance
example (time vector : V) : qVecIter L (time+1) vector = qVecIter L time (qVec L vector) := qVecIter_succ_left time vector
example {n m vector : V} (hv : IsSemitermVec L n m vector) (time : V) :
    IsSemitermVec L (n+time) (m+time) (qVecIter L time vector) := qVecIter_isSemitermVec hv time
example (time n m p vector : V) (hp : IsSemiformula L (n+time) p)
    (hv : IsSemitermVec L n m vector) :
    subst L vector (qqAlls p time) = qqAlls (subst L (qVecIter L time vector) p) time :=
  subst_qqAlls time n m p vector hp hv
example (time x : V) : (qVecIter L time (^&x ∷ 0)).[time] = ^&x := (qVecIter_free_spec time x).2
example (time : V) : termSubstVec L (time+1) (fvarVec time)
    (qVecIter L time (^&time ∷ 0)) = fvarVec (time+1) := fvarVec_subst_qVecIter time
example : 𝚺₁-Function₃[V] (specializeCode L) via specializeCodeDef L := inferInstance
example (T : Theory L) [T.Δ₁] {d b t : V} (hb : IsSemiformula L 1 b)
    (ht : IsTerm L t) (hd : Proof T d (^∀ b)) :
    Proof T (specializeCode L d b t) (substs1 L t b) := specializeCode_isProof T hb ht hd
example : 𝚺₁-Function₁[V] (advance L) via advanceDef L := inferInstance
example : 𝚺₁-Function₂[V] (runState L) via runStateDef L := inferInstance
example (time state : V) : runState L (time+1) state = runState L time (advance L state) := runState_succ_left time state
example : 𝚺₁-Function₃[V] (specializedProofCode L) via specializedProofCodeDef L := inferInstance
example (T : Theory L) [T.Δ₁] (m b d : V) (hb : IsSemiformula L m b)
    (hd : Proof T d (qqAlls b m)) :
    Proof T (specializedProofCode L m b d) (subst L (fvarVec m) b) := specializedProofCode_isProof T m b d hb hd
example (T : Theory L) [T.Δ₁] {p d : V} (hp : IsFormula L p)
    (hd : Proof T d (closeFormulaCode L p)) :
    Proof T (specializedProofCode L (bv L (bindFreeAt L 0 p)) (bindFreeAt L 0 p) d) p := openClosedCode_isProof T hp hd
example (K : Semiformula V ℒₛₑₜ 1) :
    Proof (𝗭𝗙 : SetTheory)
      (specializedProofCode ℒₛₑₜ (bv ℒₛₑₜ (bindFreeAt ℒₛₑₜ 0 (sepBodyVal K.val)))
        (bindFreeAt ℒₛₑₜ 0 (sepBodyVal K.val)) (axiomCode (closedSeparation K).val)) (sepBodyVal K.val) := by
  apply openClosedCode_isProof
  · rw [sepBodyVal_eq K]; exact (sepBody K).isSemiformula
  · exact closedSeparation_zf_isProof K
example (K : Semiformula V ℒₛₑₜ 2) :
    Proof (𝗭𝗙𝗖 : SetTheory)
      (specializedProofCode ℒₛₑₜ (bv ℒₛₑₜ (bindFreeAt ℒₛₑₜ 0 (repBodyVal K.val)))
        (bindFreeAt ℒₛₑₜ 0 (repBodyVal K.val)) (axiomCode (closedReplacement K).val)) (repBodyVal K.val) := by
  apply openClosedCode_isProof
  · rw [repBodyVal_eq K]; exact (repBody K).isSemiformula
  · exact closedReplacement_zfc_isProof K
