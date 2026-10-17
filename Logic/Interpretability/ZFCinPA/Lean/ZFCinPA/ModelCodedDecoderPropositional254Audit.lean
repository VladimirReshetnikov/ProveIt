import ZFCinPA.ModelCodedDecoderPropositional254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.impIdentityCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.impIdentityCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.mpCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.mpCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.decodedMPCode_defined
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.decodedMPCode_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.decodedZero_isProof
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.decodedProvable_mp
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254.decodedProvable_zero

example (out p : V) : (impIdentityCodeDef L).val.Evalb ![out,p] ↔ out = impIdentityCode L p := by simp
example (p : V) : ∃! out : V, (impIdentityCodeDef L).val.Evalb ![out,p] := by
  refine ⟨impIdentityCode L p,by simp,?_⟩
  intro out h; simpa using h
example (out p q di da : V) : (mpCodeDef L).val.Evalb ![out,p,q,di,da] ↔ out = mpCode L p q di da := by simp
example (p q di da : V) : ∃! out : V, (mpCodeDef L).val.Evalb ![out,p,q,di,da] := by
  refine ⟨mpCode L p q di da,by simp,?_⟩
  intro out h; simpa using h
example (T : Theory L) [T.Δ₁] (p : V) (hp : IsFormula L p) :
    Proof T (impIdentityCode L p) (imp L p p) := impIdentityCode_isProof T hp
example (T : Theory L) [T.Δ₁] (p q di da : V) (hp : IsFormula L p) (hq : IsFormula L q)
    (hi : Proof T di (imp L p q)) (ha : Proof T da p) :
    Proof T (mpCode L p q di da) q := mpCode_isProof T hp hq hi ha
example (out a b di da : V) : decodedMPCodeDef.val.Evalb ![out,a,b,di,da] ↔ out = decodedMPCode a b di da := by simp
example (a b di da : V) : ∃! out : V, decodedMPCodeDef.val.Evalb ![out,a,b,di,da] := by
  refine ⟨decodedMPCode a b di da,by simp,?_⟩
  intro out h; simpa using h
example (di da : V) : decodedMPCode 0 0 di da = da := by simp [decodedMPCode]
example (T : Theory ℒₛₑₜ) [T.Δ₁] (a b di da : V)
    (hi : Proof T di (decode (4*cantor a b))) (ha : Proof T da (decode a)) :
    Proof T (decodedMPCode a b di da) (decode b) := decodedMPCode_isProof T hi ha
example (T : Theory ℒₛₑₜ) [T.Δ₁] :
    Proof T (impIdentityCode ℒₛₑₜ (atomCode 1 (0 : V) 0)) (decode (0 : V)) := decodedZero_isProof T
example : Provable (𝗭𝗙 : SetTheory) (decode (0 : V)) := decodedProvable_zero _
example (a b : V) (hi : Provable (𝗭𝗙 : SetTheory) (decode (4*cantor a b)))
    (ha : Provable (𝗭𝗙 : SetTheory) (decode a)) : Provable (𝗭𝗙 : SetTheory) (decode b) :=
  decodedProvable_mp _ hi ha
example (a b : V) (hi : Provable (𝗭𝗙𝗖 : SetTheory) (decode (4*cantor a b)))
    (ha : Provable (𝗭𝗙𝗖 : SetTheory) (decode a)) : Provable (𝗭𝗙𝗖 : SetTheory) (decode b) :=
  decodedProvable_mp _ hi ha
