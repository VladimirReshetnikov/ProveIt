import ZFCinPA.CertificateFamily

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.CertificateFamilyCheckedAudit
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : InternalTheory V ℒₛₑₜ}

#print axioms LeanProofs.ZFCinPA.isFormula_of_proof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.intro
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.localStepProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.crossLevelProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.shiftInvariantProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.substitutionInvariantProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.axiomSoundProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.tarskiElimProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.tarskiIntroProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFields.finalConsistencyProof
#print axioms LeanProofs.ZFCinPA.conZFCSetFormula_val
#print axioms LeanProofs.ZFCinPA.isFormula_conZFCSetCodeFun_natCast
#print axioms LeanProofs.ZFCinPA.isFormula_conZFCSetCodeFun_zero
#print axioms LeanProofs.ZFCinPA.assembleZFCTruthCertificateCode_definable
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFamily.fields_sentence_val
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFamily.isFormula_conCode_of_masterProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFamily.toTProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFamily.exists_finalProof_of_masterProof
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFamily.conZFCSetCodeFun_definable
#print axioms LeanProofs.ZFCinPA.ZFCTruthCertificateFamily.code_definable_of_fields

example {L : Language} [L.Encodable] [L.LORDefinable]
    {U : Theory L} [U.Δ₁] {d p : V} (h : Proof U d p) :
    IsFormula L p := isFormula_of_proof h

example (F : ZFCTruthCertificateFields (V := V))
    (hlocal : T ⊢! F.localStep) (hcross : T ⊢! F.crossLevel)
    (hshift : T ⊢! F.shiftInvariant) (hsubst : T ⊢! F.substitutionInvariant)
    (haxiom : T ⊢! F.axiomSound) (helim : T ⊢! F.tarskiElim)
    (hintro : T ⊢! F.tarskiIntro) (hfinal : T ⊢! F.finalConsistency) :
    T ⊢! F.sentence :=
  F.intro hlocal hcross hshift hsubst haxiom helim hintro hfinal

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.localStep := ZFCTruthCertificateFields.localStepProof h

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.crossLevel := ZFCTruthCertificateFields.crossLevelProof h

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.shiftInvariant := ZFCTruthCertificateFields.shiftInvariantProof h

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.substitutionInvariant :=
  ZFCTruthCertificateFields.substitutionInvariantProof h

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.axiomSound := ZFCTruthCertificateFields.axiomSoundProof h

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.tarskiElim := ZFCTruthCertificateFields.tarskiElimProof h

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.tarskiIntro := ZFCTruthCertificateFields.tarskiIntroProof h

example {F : ZFCTruthCertificateFields (V := V)} (h : T ⊢! F.sentence) :
    T ⊢! F.finalConsistency := ZFCTruthCertificateFields.finalConsistencyProof h

example (x : V) (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun x)) :
    (conZFCSetFormula x h).val = conZFCSetCodeFun x := conZFCSetFormula_val x h

example (n : ℕ) : IsFormula ℒₛₑₜ (conZFCSetCodeFun ((n : ℕ) : V)) :=
  isFormula_conZFCSetCodeFun_natCast n

example : IsFormula ℒₛₑₜ (conZFCSetCodeFun (0 : V)) :=
  isFormula_conZFCSetCodeFun_zero

example : HierarchySymbol.sigmaOne.DefinableFunction
    (fun v : Fin 8 → V ↦ assembleZFCTruthCertificateCode
      (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  assembleZFCTruthCertificateCode_definable

example (family : ZFCTruthCertificateFamily (V := V)) (n : V)
    (h : IsFormula ℒₛₑₜ (conZFCSetCodeFun n)) :
    (family.fields n h).sentence.val = family.code n :=
  family.fields_sentence_val n h

example (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) :
    IsFormula ℒₛₑₜ (conZFCSetCodeFun n) :=
  family.isFormula_conCode_of_masterProof h

example (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (hcon : IsFormula ℒₛₑₜ (conZFCSetCodeFun n))
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) :
    (𝗭𝗙𝗖 : SetTheory).internalize V ⊢! (family.fields n hcon).sentence :=
  family.toTProof hcon h

example (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) :
    ∃ c : V, ConZFCSetCode c n ∧ Provable 𝗭𝗙𝗖 c :=
  family.exists_finalProof_of_masterProof h

example : HierarchySymbol.sigmaOne.DefinableFunction₁
    (conZFCSetCodeFun : V → V) :=
  ZFCTruthCertificateFamily.conZFCSetCodeFun_definable

example (family : ZFCTruthCertificateFamily (V := V))
    (hlocal : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.localStep n).val))
    (hcross : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.crossLevel n).val))
    (hshift : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.shiftInvariant n).val))
    (hsubst : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.substitutionInvariant n).val))
    (haxiom : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.axiomSound n).val))
    (helim : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.tarskiElim n).val))
    (hintro : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ (family.tarskiIntro n).val)) :
    HierarchySymbol.sigmaOne.DefinableFunction₁ family.code :=
  family.code_definable_of_fields hlocal hcross hshift hsubst haxiom helim hintro

-- At any internal index, the incoming represented proof itself supplies
-- formula-hood; no global typing assumption or numeral restriction is added.
example (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) : IsFormula ℒₛₑₜ (family.code n) :=
  isFormula_of_proof h

-- The extracted result is the forced builder value, not an arbitrary final
-- field chosen by the family.
example (family : ZFCTruthCertificateFamily (V := V)) {n d : V}
    (h : Proof 𝗭𝗙𝗖 d (family.code n)) : Provable 𝗭𝗙𝗖 (conZFCSetCodeFun n) := by
  rcases family.exists_finalProof_of_masterProof h with ⟨c, hc, hp⟩
  have hc' : c = conZFCSetCodeFun n := hc
  exact hc' ▸ hp

end LeanProofs.ZFCinPA.CertificateFamilyCheckedAudit
