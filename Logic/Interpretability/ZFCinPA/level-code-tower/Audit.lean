import ZFCinPA.LevelCodeTower

set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.LevelCodeTowerFocusedAudit

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA
open BoundedZFCConsistency (fNumF fTripleMemF levelSatF fSigmaTrueF fPiFalseF fPiTrueF)

#print axioms LeanProofs.ZFCinPA.levelSatF_succ_eq
#print axioms LeanProofs.ZFCinPA.fSigmaTrueF_canonical
#print axioms LeanProofs.ZFCinPA.fPiFalseF_canonical
#print axioms LeanProofs.ZFCinPA.fPiTrueF_canonical
#print axioms LeanProofs.ZFCinPA.free_lt_freeMax
#print axioms LeanProofs.ZFCinPA.free_closF
#print axioms LeanProofs.ZFCinPA.lvlInstPart.defined
#print axioms LeanProofs.ZFCinPA.allClauseCode.defined
#print axioms LeanProofs.ZFCinPA.exClauseCode.defined
#print axioms LeanProofs.ZFCinPA.justRowCode.defined
#print axioms LeanProofs.ZFCinPA.closStepCode.defined
#print axioms LeanProofs.ZFCinPA.closCode_zero
#print axioms LeanProofs.ZFCinPA.closCode_succ
#print axioms LeanProofs.ZFCinPA.closCode.defined
#print axioms LeanProofs.ZFCinPA.levelSatCode_zero
#print axioms LeanProofs.ZFCinPA.levelSatCode_succ
#print axioms LeanProofs.ZFCinPA.levelSatCode.defined
#print axioms LeanProofs.ZFCinPA.sigmaTrueCode.defined
#print axioms LeanProofs.ZFCinPA.piFalseCode.defined
#print axioms LeanProofs.ZFCinPA.piTrueCode.defined
#print axioms LeanProofs.ZFCinPA.quote_lvlInstF
#print axioms LeanProofs.ZFCinPA.quote_closF_succ
#print axioms LeanProofs.ZFCinPA.closCode_natCast
#print axioms LeanProofs.ZFCinPA.levelSatCode_natCast
#print axioms LeanProofs.ZFCinPA.sigmaTrueCode_natCast
#print axioms LeanProofs.ZFCinPA.piFalseCode_natCast
#print axioms LeanProofs.ZFCinPA.piTrueCode_natCast
#print axioms LeanProofs.ZFCinPA.eval_levelSatGraph_iff
#print axioms LeanProofs.ZFCinPA.levelSatCode_total
#print axioms LeanProofs.ZFCinPA.levelSatCode_functional
#print axioms LeanProofs.ZFCinPA.levelSatCode_existsUnique
#print axioms LeanProofs.ZFCinPA.levelSatCode_quote_numeral
#print axioms LeanProofs.ZFCinPA.sigmaTrueCode_quote_numeral
#print axioms LeanProofs.ZFCinPA.piFalseCode_quote_numeral
#print axioms LeanProofs.ZFCinPA.piTrueCode_quote_numeral

example (n c e b : ℕ) :
    levelSatF (n + 1) c e b = lvlInstF n (c + 2) (e + 2) (b + 2) :=
  levelSatF_succ_eq n c e b

example (n : ℕ) :
    fSigmaTrueF n 1 0 = .fEx (.fAnd (fNumF 0 1) (levelSatF n 2 1 0)) :=
  fSigmaTrueF_canonical n

example (n : ℕ) :
    fPiFalseF n 1 0 = .fEx (.fAnd (fNumF 0 0) (levelSatF n 2 1 0)) :=
  fPiFalseF_canonical n

example (n : ℕ) : fPiTrueF n 1 0 = .fImp (fPiFalseF n 1 0) .fBot :=
  fPiTrueF_canonical n

example (f : SetTheory.Form) (i : ℕ) (hi : SetTheory.Free i f) : i < freeMax f :=
  free_lt_freeMax f i hi

example (n : ℕ) {i : ℕ} (hi : SetTheory.Free i (closF n)) : i < 2 :=
  free_closF n hi

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (t : ℕ) : 𝚺₁-Function₂ (lvlInstPart t : V → V → V) via lvlInstGraph t :=
  lvlInstPart.defined t

example : 𝚺₁-Function₂ (allClauseCode : V → V → V) via allClauseGraph :=
  allClauseCode.defined

example : 𝚺₁-Function₂ (exClauseCode : V → V → V) via exClauseGraph :=
  exClauseCode.defined

example : 𝚺₁-Function₂ (justRowCode : V → V → V) via justRowGraph :=
  justRowCode.defined

example : 𝚺₁-Function₂ (closStepCode : V → V → V) via closStepGraph :=
  closStepCode.defined

example : closCode (0 : V) = ↑closZeroCode := closCode_zero

example (x : V) :
    closCode (x + 1) = closStepCode (numChainCode x) (closCode x) :=
  closCode_succ x

example : 𝚺₁-Function₁ (closCode : V → V) via closGraph := closCode.defined

example : levelSatCode (0 : V) = ↑levelSatZeroCode := levelSatCode_zero

example (x : V) :
    levelSatCode (x + 1) = lvlInstPart tripleMemCanonCode (numChainCode x) (closCode x) :=
  levelSatCode_succ x

example : 𝚺₁-Function₁ (levelSatCode : V → V) via levelSatGraph :=
  levelSatCode.defined

example : 𝚺₁-Function₁ (sigmaTrueCode : V → V) via sigmaTrueGraph :=
  sigmaTrueCode.defined

example : 𝚺₁-Function₁ (piFalseCode : V → V) via piFalseGraph := piFalseCode.defined

example : 𝚺₁-Function₁ (piTrueCode : V → V) via piTrueGraph := piTrueCode.defined

example (m c e b k d : ℕ) (hd : k + 1 + 1 = d) :
    (⌜toSet k (lvlInstF m c e b)⌝ : V) =
      lvlInstPart ((toSet d (fTripleMemF c e b 1)).toNat)
        (⌜toSet 1 (fNumF 0 m)⌝ : V) (⌜toSet 2 (closF m)⌝ : V) :=
  quote_lvlInstF m c e b k d hd

example (m : ℕ) :
    (⌜toSet 2 (closF (m + 1))⌝ : V) =
      closStepCode (⌜toSet 1 (fNumF 0 m)⌝ : V) (⌜toSet 2 (closF m)⌝ : V) :=
  quote_closF_succ m

example (m : ℕ) : closCode ((m : ℕ) : V) = ⌜toSet 2 (closF m)⌝ :=
  closCode_natCast m

example (m : ℕ) : levelSatCode ((m : ℕ) : V) = ⌜toSet 3 (levelSatF m 2 1 0)⌝ :=
  levelSatCode_natCast m

example (m : ℕ) : sigmaTrueCode ((m : ℕ) : V) = ⌜toSet 2 (fSigmaTrueF m 1 0)⌝ :=
  sigmaTrueCode_natCast m

example (m : ℕ) : piFalseCode ((m : ℕ) : V) = ⌜toSet 2 (fPiFalseF m 1 0)⌝ :=
  piFalseCode_natCast m

example (m : ℕ) : piTrueCode ((m : ℕ) : V) = ⌜toSet 2 (fPiTrueF m 1 0)⌝ :=
  piTrueCode_natCast m

example {c x : V} : levelSatGraph.val.Evalb ![c, x] ↔ LevelSatCode c x :=
  eval_levelSatGraph_iff

example (x : V) : ∃ c : V, LevelSatCode c x := levelSatCode_total x

example {c₁ c₂ x : V} (h₁ : LevelSatCode c₁ x) (h₂ : LevelSatCode c₂ x) : c₁ = c₂ :=
  levelSatCode_functional h₁ h₂

example (x : V) : ∃! c : V, LevelSatCode c x := levelSatCode_existsUnique x

example (n : ℕ) :
    LevelSatCode (⌜toSet 3 (levelSatF n 2 1 0)⌝ : V) (ORingStructure.numeral n) :=
  levelSatCode_quote_numeral n

example (n : ℕ) :
    sigmaTrueCode (ORingStructure.numeral n : V) = ⌜toSet 2 (fSigmaTrueF n 1 0)⌝ :=
  sigmaTrueCode_quote_numeral n

example (n : ℕ) :
    piFalseCode (ORingStructure.numeral n : V) = ⌜toSet 2 (fPiFalseF n 1 0)⌝ :=
  piFalseCode_quote_numeral n

example (n : ℕ) :
    piTrueCode (ORingStructure.numeral n : V) = ⌜toSet 2 (fPiTrueF n 1 0)⌝ :=
  piTrueCode_quote_numeral n

end LeanProofs.ZFCinPA.LevelCodeTowerFocusedAudit
