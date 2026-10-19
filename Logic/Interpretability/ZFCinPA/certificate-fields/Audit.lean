import ZFCinPA.CertificateFields

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.CertificateFieldsFocusedAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA
open BoundedZFCConsistency (levelSatF fTagPairF fTagUnF)
open SetTheory (Form Free)

#print axioms LeanProofs.ZFCinPA.not_free_localStepF
#print axioms LeanProofs.ZFCinPA.not_free_crossLevelF
#print axioms LeanProofs.ZFCinPA.not_free_shiftInvariantF
#print axioms LeanProofs.ZFCinPA.not_free_substitutionInvariantF
#print axioms LeanProofs.ZFCinPA.not_free_axiomSoundF
#print axioms LeanProofs.ZFCinPA.not_free_tarskiElimF
#print axioms LeanProofs.ZFCinPA.not_free_tarskiIntroF
#print axioms LeanProofs.ZFCinPA.localStepCode.defined
#print axioms LeanProofs.ZFCinPA.crossLevelCode.defined
#print axioms LeanProofs.ZFCinPA.shiftInvariantCode.defined
#print axioms LeanProofs.ZFCinPA.substitutionInvariantCode.defined
#print axioms LeanProofs.ZFCinPA.axiomSoundCode.defined
#print axioms LeanProofs.ZFCinPA.tarskiElimCode.defined
#print axioms LeanProofs.ZFCinPA.tarskiIntroCode.defined
#print axioms LeanProofs.ZFCinPA.localStepCode_natCast
#print axioms LeanProofs.ZFCinPA.crossLevelCode_natCast
#print axioms LeanProofs.ZFCinPA.shiftInvariantCode_natCast
#print axioms LeanProofs.ZFCinPA.substitutionInvariantCode_natCast
#print axioms LeanProofs.ZFCinPA.axiomSoundCode_natCast
#print axioms LeanProofs.ZFCinPA.tarskiElimCode_natCast
#print axioms LeanProofs.ZFCinPA.tarskiIntroCode_natCast
#print axioms LeanProofs.ZFCinPA.free_levelSatF_canonical
#print axioms LeanProofs.ZFCinPA.free_canonAtF
#print axioms LeanProofs.ZFCinPA.free_boundedAt1F
#print axioms LeanProofs.ZFCinPA.free_polarAtF
#print axioms LeanProofs.ZFCinPA.canonAtPart.defined
#print axioms LeanProofs.ZFCinPA.polarAtCode.defined
#print axioms LeanProofs.ZFCinPA.quote_canonAtF
#print axioms LeanProofs.ZFCinPA.quote_polarAtF
#print axioms LeanProofs.ZFCinPA.quote_connClauseF
#print axioms LeanProofs.ZFCinPA.quote_quantClauseF
#print axioms LeanProofs.ZFCinPA.quote_botClauseF
#print axioms LeanProofs.ZFCinPA.not_free_connClauseF
#print axioms LeanProofs.ZFCinPA.not_free_quantClauseF

example (n : ℕ) : ∀ i, ¬ Free i (localStepF n) := not_free_localStepF n
example (n : ℕ) : ∀ i, ¬ Free i (crossLevelF n) := not_free_crossLevelF n
example (n : ℕ) : ∀ i, ¬ Free i (shiftInvariantF n) := not_free_shiftInvariantF n
example (n : ℕ) : ∀ i, ¬ Free i (substitutionInvariantF n) :=
  not_free_substitutionInvariantF n
example (n : ℕ) : ∀ i, ¬ Free i (axiomSoundF n) := not_free_axiomSoundF n
example (n : ℕ) : ∀ i, ¬ Free i (tarskiElimF n) := not_free_tarskiElimF n
example (n : ℕ) : ∀ i, ¬ Free i (tarskiIntroF n) := not_free_tarskiIntroF n

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚺₁-Function₁ (localStepCode : V → V) via localStepGraph :=
  localStepCode.defined
example : 𝚺₁-Function₁ (crossLevelCode : V → V) via crossLevelGraph :=
  crossLevelCode.defined
example : 𝚺₁-Function₁ (shiftInvariantCode : V → V) via shiftInvariantGraph :=
  shiftInvariantCode.defined
example : 𝚺₁-Function₁ (substitutionInvariantCode : V → V)
    via substitutionInvariantGraph := substitutionInvariantCode.defined
example : 𝚺₁-Function₁ (axiomSoundCode : V → V) via axiomSoundGraph :=
  axiomSoundCode.defined
example : 𝚺₁-Function₁ (tarskiElimCode : V → V) via tarskiElimGraph :=
  tarskiElimCode.defined
example : 𝚺₁-Function₁ (tarskiIntroCode : V → V) via tarskiIntroGraph :=
  tarskiIntroCode.defined

example (n : ℕ) : localStepCode ((n : ℕ) : V) = ⌜toSet 0 (localStepF n)⌝ :=
  localStepCode_natCast n
example (n : ℕ) : crossLevelCode ((n : ℕ) : V) = ⌜toSet 0 (crossLevelF n)⌝ :=
  crossLevelCode_natCast n
example (n : ℕ) : shiftInvariantCode ((n : ℕ) : V) =
    ⌜toSet 0 (shiftInvariantF n)⌝ := shiftInvariantCode_natCast n
example (n : ℕ) : substitutionInvariantCode ((n : ℕ) : V) =
    ⌜toSet 0 (substitutionInvariantF n)⌝ := substitutionInvariantCode_natCast n
example (n : ℕ) : axiomSoundCode ((n : ℕ) : V) = ⌜toSet 0 (axiomSoundF n)⌝ :=
  axiomSoundCode_natCast n
example (n : ℕ) : tarskiElimCode ((n : ℕ) : V) = ⌜toSet 0 (tarskiElimF n)⌝ :=
  tarskiElimCode_natCast n
example (n : ℕ) : tarskiIntroCode ((n : ℕ) : V) = ⌜toSet 0 (tarskiIntroF n)⌝ :=
  tarskiIntroCode_natCast n

example (n : ℕ) {i : ℕ} (h : Free i (levelSatF n 2 1 0)) : i < 3 :=
  free_levelSatF_canonical n h
example {ci ei i : ℕ} {φ : Form} (hφ : ∀ j, Free j φ → j < 2)
    (h : Free i (canonAtF ci ei φ)) : i = ci ∨ i = ei := free_canonAtF hφ h
example {n i : ℕ} (h : Free i (boundedAtF n 1)) : i < 2 := free_boundedAt1F h
example {n b ci ei i : ℕ} (h : Free i (polarAtF n b ci ei)) :
    i = ci ∨ i = ei := free_polarAtF h

example (e1 e0 : ℕ) :
    𝚺₁-Function₁ (canonAtPart e1 e0 : V → V) via canonAtGraph e1 e0 :=
  canonAtPart.defined e1 e0
example (w ci ei : ℕ) :
    𝚺₁-Function₁ (polarAtCode w ci ei : V → V) via polarAtGraph w ci ei :=
  polarAtCode.defined w ci ei

example {k : ℕ} (ci ei : ℕ) (hci : ci < k) (hei : ei < k)
    (φ : Form) (hφ : ∀ j, Free j φ → j < 2) :
    (⌜toSet k (canonAtF ci ei φ)⌝ : V) =
      canonAtPart (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))
        (⌜toSet 2 φ⌝ : V) := quote_canonAtF ci ei hci hei φ hφ
example (n b : ℕ) {k : ℕ} (ci ei : ℕ) (hci : ci < k) (hei : ei < k) :
    (⌜toSet k (polarAtF n b ci ei)⌝ : V) =
      polarAtCode (bitWitnessCode b) ci ei ((n : ℕ) : V) :=
  quote_polarAtF n b ci ei hci hei
example (t : ℕ) (prem concl : Form) :
    (⌜toSet 0 (connClauseF t prem concl)⌝ : V) =
      connSpinePart isFormCode3D4Code isFormCode2D4Code univEnv1D4Code
        (tagPairD4Code t)
        (Bootstrapping.imp ℒₛₑₜ (⌜toSet 4 prem⌝ : V) (⌜toSet 4 concl⌝ : V)) :=
  quote_connClauseF t prem concl
example (t : ℕ) (prem concl : Form) :
    (⌜toSet 0 (quantClauseF t prem concl)⌝ : V) =
      quantSpinePart isFormCode4D5Code univEnv3D5Code (tagUnD5Code t)
        econsQuantD5Code
        (Bootstrapping.imp ℒₛₑₜ (⌜toSet 5 prem⌝ : V) (⌜toSet 5 concl⌝ : V)) :=
  quote_quantClauseF t prem concl
example (n : ℕ) : (⌜toSet 0 (botClauseF n)⌝ : V) =
    botPiPart univEnv1D2Code taggedEmpty0D2Code (bitWitnessCode 0)
      ((n : ℕ) : V) := quote_botClauseF n

example (t : ℕ) (htp : freeMax (fTagPairF 0 t 3 2) ≤ 4)
    {prem concl : Form} (hp : ∀ i, Free i prem → i < 4)
    (hc : ∀ i, Free i concl → i < 4) :
    ∀ i, ¬ Free i (connClauseF t prem concl) := not_free_connClauseF t htp hp hc
example (t : ℕ) (htu : freeMax (fTagUnF 1 t 4) ≤ 5)
    {prem concl : Form} (hp : ∀ i, Free i prem → i < 5)
    (hc : ∀ i, Free i concl → i < 5) :
    ∀ i, ¬ Free i (quantClauseF t prem concl) := not_free_quantClauseF t htu hp hc

end LeanProofs.ZFCinPA.CertificateFieldsFocusedAudit
