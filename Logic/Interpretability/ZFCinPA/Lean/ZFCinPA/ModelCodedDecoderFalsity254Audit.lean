import ZFCinPA.ModelCodedDecoderFalsity254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.zf_irreflexivity_outer
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.quote_irreflexivity
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.zf_irreflexivity_internal
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.contradictionCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.contradictionCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.explosionCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.explosionCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254.decoded_one_provable_iff_bottom

example : (𝗭𝗙 : SetTheory) ⊢ irreflexivitySentence := zf_irreflexivity_outer
example : (⌜irreflexivitySentence⌝ : V) = ^∀ (^nrel 2 1 ?[^#0,^#0]) := quote_irreflexivity
example : Provable (𝗭𝗙 : SetTheory) (neg ℒₛₑₜ (atomCode 1 (0 : V) 0)) := zf_irreflexivity_internal
example (out p dp dn : V) : (contradictionCodeDef L).val.Evalb ![out,p,dp,dn] ↔
    out = contradictionCode L p dp dn := by simp
example (p dp dn : V) : ∃! out : V, (contradictionCodeDef L).val.Evalb ![out,p,dp,dn] := by
  refine ⟨contradictionCode L p dp dn,by simp,?_⟩
  intro out h; simpa using h
example (T : Theory L) [T.Δ₁] (p dp dn : V) (hp : IsFormula L p)
    (hdp : Proof T dp p) (hdn : Proof T dn (neg L p)) :
    Proof T (contradictionCode L p dp dn) (^⊥ : V) := contradictionCode_isProof T hp hdp hdn
example (out p db : V) : explosionCodeDef.val.Evalb ![out,p,db] ↔ out = explosionCode p db := by simp
example (p db : V) : ∃! out : V, explosionCodeDef.val.Evalb ![out,p,db] := by
  refine ⟨explosionCode p db,by simp,?_⟩
  intro out h; simpa using h
example (T : Theory L) [T.Δ₁] (p db : V) (hp : IsFormula L p)
    (hd : Proof T db (^⊥ : V)) : Proof T (explosionCode p db) p := explosionCode_isProof T hp hd
example (h : Provable (𝗭𝗙 : SetTheory) (decode (1 : V))) : Provable (𝗭𝗙 : SetTheory) (^⊥ : V) :=
  decoded_one_provable_iff_bottom.mp h
example (h : Provable (𝗭𝗙 : SetTheory) (^⊥ : V)) : Provable (𝗭𝗙 : SetTheory) (decode (1 : V)) :=
  decoded_one_provable_iff_bottom.mpr h
example : Provable (𝗭𝗙 : SetTheory) (decode (1 : Nat)) ↔ Provable (𝗭𝗙 : SetTheory) (^⊥ : Nat) :=
  decoded_one_provable_iff_bottom
