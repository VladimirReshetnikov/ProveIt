import ZFCinPA.SuccessorSources

/-!
# Source readings of the two Tarski certificate fields

`ZFCinPA.SuccessorSources` carries the field-independent half of the
compilation route — the placeholder template, the two model-coded leaves,
the level tower at the canonical slots, and the nineteen-leaf closure-step
spine.  `ZFCinPA.LocalStepSuccessor` used it to read the **first** of the
seven variable certificate fields as a fixed source formula over
`setTemplateLanguage 2 ![1, 2]`.

This module does the same for fields **six** and **seven**, the two Tarski
bundles added by the certificate redesign
(`ZFCinPA.CertificateFields.tarskiElimCode`/`tarskiIntroCode`, semantic
counterparts `EnlargedFields.TarskiElim`/`TarskiIntro`).

## What is new here beyond the pattern

The five original fields all read their level-truth payload through
`SuccessorSources.srcCanonAt`, which is hard-wired to the canonical slot
pair `(1, 0)` and to the two polarities `srcSigmaTrue`, `srcPiFalse` at
ambient arity `4`.  The Tarski rows need the *same* gadget at six other
slot pairs — `(0,1)`, `(3,1)`, `(2,1)` inside the four-binder connective
skeleton and `(1,3)`, `(4,0)` inside the five-binder quantifier skeleton —
and at the corresponding ambient arities.  The previous analysis flagged
this as a shared gap; it is closed here, once, by the arity- and
slot-generalized family

* `srcLevelSatAt m` / `srcLevelSatSuccAt m` — the canonical level instance
  at an arbitrary ambient arity `m ≥ 3`, the second built from the two
  successor spines of `SuccessorSources`;
* `srcBitWitnessAt m w` / `srcBitWitnessSuccAt m w` — the bit-`w` witness
  wrapper, with the polarity a parameter rather than two copies;
* `srcCanonAtPair m ci ei` — the canonical-slot gadget at an arbitrary
  pair;
* `srcPolarAt m w ci ei` / `srcPolarAtSucc m w ci ei` — their composite,
  the source counterpart of `CertificateFields.polarAtCode`.

`SuccessorSources.srcCanonAt srcSigmaTrue` is the instance `m = 2`,
`w = 1`, `(ci, ei) = (1, 0)` of this family; the older names are kept
because the first field's proofs are stated with them.

## Structure

The two field codes are assembled from three coded skeletons
(`connSpinePart`, `quantSpinePart`, `botPiPart`).  Each gets one source
counterpart (`srcConnSpine`, `srcQuantSpine`, `srcBotPiOf`) and one
translation identity, and the eight elimination and nine introduction rows
are then written **once**, abstractly in the polarized gadget

> `P : (m w ci ei : ℕ) → Semiproposition srcL m`

so that the base reading and the successor reading are the two
instantiations `P := srcPolarAt` and `P := srcPolarAtSucc` of the same
definitions and of the same translation proof.  That is what makes
`srcTarskiElimSucc` literally `srcTarskiElim`'s spine one level up, in the
sense `LocalStepSuccessor.srcLocalStepSucc` is `srcLocalStep`'s.

## Free-slot bounds

No new kernel `decide` is performed.  The fixed leaves of the three
skeletons (`fIsFormCodeF 3`, `fIsFormCodeF 2`, `fIsFormCodeF 4`,
`fUnivEnvF 3`, `fEconsF 0 2 3`, `fTaggedEmptyF 0 2`) have their bounds
sealed inside `CertificateFields` as private kernel evaluations; they are
recovered here from the *closedness* theorems of the three skeletons
(`not_free_connClauseF`, `not_free_quantClauseF`, `not_free_botClauseF`)
instantiated at a closed premise and conclusion, exactly the way
`LocalStepSuccessor.free_univEnv0` recovers its bound from
`not_free_localStepF`.  The tag guards reuse the exported
`freeMax_fTagPairF_*`/`freeMax_fTagUnF_*`, and `fUnivEnvF 1` reuses
`LevelCodeTower.fm02`.

## Disciplines

The parameter firewall is respected: every concrete Gödel constant is
reached only through `coe_toNat_eq_quote` or the depth-move lemma
`quote_leaf_move`/`quote_fEq_move`, never by `simp` or evaluation, and the
two `x`-dependent leaves stay behind the placeholder abstraction.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace LeanProofs
namespace ZFCinPA
namespace SuccessorSources

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.SetPlaceholders
open LeanProofs.ZFCinPA.SubstIdentity
open BoundedZFCConsistency (fNumF fTripleMemF fUnivEnvF fIsFormCodeF
  fTaggedEmptyF fTagPairF fTagUnF fEconsF)

/-! ## Free-slot bounds of the three skeletons' fixed leaves

Each bound is read off the corresponding skeleton's closedness theorem at
a closed premise and conclusion: `Free` is definitional on the skeleton's
spine, so a hypothetical free slot `k + d` of a leaf below `d` binders
would be a free slot `k` of the whole closed skeleton. -/

section SkeletonBounds

open SetTheory (Form Free)

private theorem free_bot_absurd {i : ℕ} (h : Free i Form.fBot) : i < 0 :=
  absurd h (by simp [Free])

theorem free_isFormCode3D4 {i : ℕ} (h : Free i (fIsFormCodeF 3)) : i < 4 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
  exact not_free_connClauseF 3 freeMax_fTagPairF_imp
    (prem := Form.fBot) (concl := Form.fBot)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega) k (Or.inl h)

theorem free_isFormCode2D4 {i : ℕ} (h : Free i (fIsFormCodeF 2)) : i < 4 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
  exact not_free_connClauseF 3 freeMax_fTagPairF_imp
    (prem := Form.fBot) (concl := Form.fBot)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega) k (Or.inr (Or.inl h))

theorem free_univEnv1D4 {i : ℕ} (h : Free i (fUnivEnvF 1)) : i < 2 := by
  have := free_lt_freeMax _ i h; have := fm02; omega

theorem free_tagPairD4 {t i : ℕ} (ht : freeMax (fTagPairF 0 t 3 2) ≤ 4)
    (h : Free i (fTagPairF 0 t 3 2)) : i < 4 := by
  have := free_lt_freeMax _ i h; omega

theorem free_isFormCode4D5 {i : ℕ} (h : Free i (fIsFormCodeF 4)) : i < 5 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
  exact not_free_quantClauseF 6 freeMax_fTagUnF_all
    (prem := Form.fBot) (concl := Form.fBot)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega) k (Or.inl h)

theorem free_univEnv3D5 {i : ℕ} (h : Free i (fUnivEnvF 3)) : i < 5 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
  exact not_free_quantClauseF 6 freeMax_fTagUnF_all
    (prem := Form.fBot) (concl := Form.fBot)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega) k (Or.inr (Or.inl h))

theorem free_tagUnD5 {t i : ℕ} (ht : freeMax (fTagUnF 1 t 4) ≤ 5)
    (h : Free i (fTagUnF 1 t 4)) : i < 5 := by
  have := free_lt_freeMax _ i h; omega

theorem free_econsQuantD5 {i : ℕ} (h : Free i (fEconsF 0 2 3)) : i < 5 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
  exact not_free_quantClauseF 6 freeMax_fTagUnF_all
    (prem := Form.fBot) (concl := Form.fBot)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega)
    (fun _ hj ↦ by have := free_bot_absurd hj; omega) k
    (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem free_taggedEmpty0D2 {i : ℕ} (h : Free i (fTaggedEmptyF 0 2)) :
    i < 2 := by
  by_contra hlt
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 2 := ⟨i - 2, by omega⟩
  exact not_free_botClauseF 0 k (Or.inr (Or.inl h))

end SkeletonBounds

/-! ## The level tower at an arbitrary ambient arity and slot pair -/

section GeneralTower

open SetTheory (Form Free)

/-- The canonical level instance at an arbitrary ambient arity.
`SuccessorSources.srcLevelSat` is the instance `m = 5`. -/
noncomputable def srcLevelSatAt (m : ℕ) : Semiproposition srcL m :=
  srcLvlInstP m (fTripleMemF 4 3 2 1)

/-- The canonical level instance one level up, at an arbitrary ambient
arity.  `SuccessorSources.srcLevelSatSucc` is the instance `m = 5`. -/
noncomputable def srcLevelSatSuccAt (m : ℕ) : Semiproposition srcL m :=
  srcLvlInst m (fTripleMemF 4 3 2 1) (srcNumChainSucc (m + 1 + 1))
    (srcClosStep (m + 1 + 1))

/-- The bit-`w` witness wrapper at an arbitrary ambient arity.  At `m = 4`
this is `srcSigmaTrue` (`w = 1`) and `srcPiFalse` (`w = 0`). -/
noncomputable def srcBitWitnessAt (m w : ℕ) : Semiproposition srcL m :=
  ∃⁰ (liftP (toSet (m + 1) (fNumF 0 w)) ⋏ srcLevelSatAt (m + 1))

/-- The bit-`w` witness wrapper one level up. -/
noncomputable def srcBitWitnessSuccAt (m w : ℕ) : Semiproposition srcL m :=
  ∃⁰ (liftP (toSet (m + 1) (fNumF 0 w)) ⋏ srcLevelSatSuccAt (m + 1))

/-- The canonical-slot gadget at an arbitrary slot pair and ambient arity.
`SuccessorSources.srcCanonAt` is the instance `m = 2`, `(ci, ei) = (1, 0)`. -/
noncomputable def srcCanonAtPair (m ci ei : ℕ)
    (inner : Semiproposition srcL (m + 1 + 1)) : Semiproposition srcL m :=
  ∀⁰ ∀⁰ (liftP (toSet (m + 1 + 1) (Form.fEq 1 (ci + 2))) 🡒
    (liftP (toSet (m + 1 + 1) (Form.fEq 0 (ei + 2))) 🡒 inner))

/-- **The source counterpart of `CertificateFields.polarAtCode`.** -/
noncomputable def srcPolarAt (m w ci ei : ℕ) : Semiproposition srcL m :=
  srcCanonAtPair m ci ei (srcBitWitnessAt (m + 1 + 1) w)

/-- The polarized gadget one level up. -/
noncomputable def srcPolarAtSucc (m w ci ei : ℕ) : Semiproposition srcL m :=
  srcCanonAtPair m ci ei (srcBitWitnessSuccAt (m + 1 + 1) w)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translate_srcLevelSatAt (x : V) (m : ℕ) (hm : 3 ≤ m) :
    (translateFormula (levelLeaves x) (srcLevelSatAt m)).val =
      levelSatCode (x + 1) := by
  rw [levelSatCode_succ]
  exact translate_srcLvlInstP x m (fTripleMemF 4 3 2 1) 5
    (fun i hi ↦ by have := free_tripleMemCanon hi; omega)
    (fun i hi ↦ free_tripleMemCanon hi)

theorem translate_srcLevelSatSuccAt (x : V) (m : ℕ) (hm : 3 ≤ m) :
    (translateFormula (levelLeaves x) (srcLevelSatSuccAt m)).val =
      levelSatCode (x + 1 + 1) := by
  rw [levelSatCode_succ]
  unfold srcLevelSatSuccAt
  rw [translate_srcLvlInst x m (fTripleMemF 4 3 2 1) 5
      (fun i hi ↦ by have := free_tripleMemCanon hi; omega)
      (fun i hi ↦ free_tripleMemCanon hi),
    translate_srcNumChainSucc x (m + 1 + 1) (by omega),
    translate_srcClosStep x (m + 1 + 1) (by omega)]
  rfl

theorem translate_srcBitWitnessAt (x : V) (m w : ℕ) (hm : 2 ≤ m) :
    (translateFormula (levelLeaves x) (srcBitWitnessAt m w)).val =
      bitWitnessPart (bitWitnessCode w) (x + 1) := by
  rw [bitWitnessPart]
  simp only [srcBitWitnessAt, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSatAt x (m + 1) (by omega)]
  rw [quote_leaf_move (V := V) (fNumF 0 w) (m + 1) 3
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

theorem translate_srcBitWitnessSuccAt (x : V) (m w : ℕ) (hm : 2 ≤ m) :
    (translateFormula (levelLeaves x) (srcBitWitnessSuccAt m w)).val =
      bitWitnessPart (bitWitnessCode w) (x + 1 + 1) := by
  rw [bitWitnessPart]
  simp only [srcBitWitnessSuccAt, translate_exs, translate_and,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_and,
    translate_liftP_val, translate_srcLevelSatSuccAt x (m + 1) (by omega)]
  rw [quote_leaf_move (V := V) (fNumF 0 w) (m + 1) 3
    (fun i hi ↦ by have := free_fNumF hi; omega)
    (fun i hi ↦ by have := free_fNumF hi; omega)]
  rfl

theorem translate_srcCanonAtPair (x : V) (m ci ei : ℕ) (hci : ci < m)
    (hei : ei < m) (inner : Semiproposition srcL (m + 1 + 1)) :
    (translateFormula (levelLeaves x) (srcCanonAtPair m ci ei inner)).val =
      canonAtPart (eqGuardCode 1 (ci + 2)) (eqGuardCode 0 (ei + 2))
        (translateFormula (levelLeaves x) inner).val := by
  rw [canonAtPart]
  simp only [srcCanonAtPair, translate_all, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val]
  rw [quote_fEq_move (V := V) (show 1 < m + 1 + 1 by omega)
      (show ci + 2 < m + 1 + 1 by omega),
    quote_fEq_move (V := V) (show 0 < m + 1 + 1 by omega)
      (show ei + 2 < m + 1 + 1 by omega)]

/-- **The polarized gadget is the specialization of a fixed source
formula**, at every model index and every slot pair the Tarski rows use. -/
theorem translate_srcPolarAt (x : V) (m w ci ei : ℕ) (hci : ci < m)
    (hei : ei < m) :
    (translateFormula (levelLeaves x) (srcPolarAt m w ci ei)).val =
      polarAtCode (bitWitnessCode w) ci ei x := by
  rw [polarAtCode, srcPolarAt, translate_srcCanonAtPair x m ci ei hci hei,
    translate_srcBitWitnessAt x (m + 1 + 1) w (by omega)]

/-- The polarized gadget one level up. -/
theorem translate_srcPolarAtSucc (x : V) (m w ci ei : ℕ) (hci : ci < m)
    (hei : ei < m) :
    (translateFormula (levelLeaves x) (srcPolarAtSucc m w ci ei)).val =
      polarAtCode (bitWitnessCode w) ci ei (x + 1) := by
  rw [polarAtCode, srcPolarAtSucc,
    translate_srcCanonAtPair x m ci ei hci hei,
    translate_srcBitWitnessSuccAt x (m + 1 + 1) w (by omega)]

end GeneralTower

/-! ## The three coded skeletons, at the source level -/

section Skeletons

open SetTheory (Form Free)

/-- Source counterpart of `CertificateFields.connSpinePart` at the concrete
leaf codes: four universal quantifiers over the two subcode guards, the
environment guard and the tag guard. -/
noncomputable def srcConnSpine (t : ℕ) (body : Semiproposition srcL 4) :
    Proposition srcL :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ (liftP (toSet 4 (fIsFormCodeF 3)) 🡒
    (liftP (toSet 4 (fIsFormCodeF 2)) 🡒
      (liftP (toSet 4 (fUnivEnvF 1)) 🡒
        (liftP (toSet 4 (fTagPairF 0 t 3 2)) 🡒 body))))

/-- Source counterpart of `CertificateFields.quantSpinePart`. -/
noncomputable def srcQuantSpine (t : ℕ) (body : Semiproposition srcL 5) :
    Proposition srcL :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (liftP (toSet 5 (fIsFormCodeF 4)) 🡒
    (liftP (toSet 5 (fUnivEnvF 3)) 🡒
      (liftP (toSet 5 (fTagUnF 1 t 4)) 🡒
        (liftP (toSet 5 (fEconsF 0 2 3)) 🡒 body))))

/-- Source counterpart of `CertificateFields.botPiPart`, over an abstract
polarized gadget. -/
noncomputable def srcBotPiOf (P : (m w ci ei : ℕ) → Semiproposition srcL m) :
    Proposition srcL :=
  ∀⁰ ∀⁰ (liftP (toSet 2 (fUnivEnvF 1)) 🡒
    (liftP (toSet 2 (fTaggedEmptyF 0 2)) 🡒 P 2 0 0 1))

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translate_srcConnSpine (x : V) (t : ℕ)
    (body : Semiproposition srcL 4) :
    (translateFormula (levelLeaves x) (srcConnSpine t body)).val =
      connSpinePart isFormCode3D4Code isFormCode2D4Code univEnv1D4Code
        (tagPairD4Code t) (translateFormula (levelLeaves x) body).val := by
  rw [connSpinePart]
  simp only [srcConnSpine, translate_all, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val]
  rw [← coe_toNat_eq_quote (V := V) (toSet 4 (fIsFormCodeF 3)),
    ← coe_toNat_eq_quote (V := V) (toSet 4 (fIsFormCodeF 2)),
    ← coe_toNat_eq_quote (V := V) (toSet 4 (fUnivEnvF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 4 (fTagPairF 0 t 3 2))]
  rfl

theorem translate_srcQuantSpine (x : V) (t : ℕ)
    (body : Semiproposition srcL 5) :
    (translateFormula (levelLeaves x) (srcQuantSpine t body)).val =
      quantSpinePart isFormCode4D5Code univEnv3D5Code (tagUnD5Code t)
        econsQuantD5Code (translateFormula (levelLeaves x) body).val := by
  rw [quantSpinePart]
  simp only [srcQuantSpine, translate_all, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val]
  rw [← coe_toNat_eq_quote (V := V) (toSet 5 (fIsFormCodeF 4)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fUnivEnvF 3)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fTagUnF 1 t 4)),
    ← coe_toNat_eq_quote (V := V) (toSet 5 (fEconsF 0 2 3))]
  rfl

theorem translate_srcBotPiOf (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y) :
    (translateFormula (levelLeaves x) (srcBotPiOf P)).val =
      botPiPart univEnv1D2Code taggedEmpty0D2Code (bitWitnessCode 0) y := by
  rw [botPiPart]
  simp only [srcBotPiOf, translate_all, translateFormula_imp,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_imp,
    translate_liftP_val, hP 2 0 0 1 (by omega) (by omega)]
  rw [← coe_toNat_eq_quote (V := V) (toSet 2 (fUnivEnvF 1)),
    ← coe_toNat_eq_quote (V := V) (toSet 2 (fTaggedEmptyF 0 2))]
  rfl

end Skeletons

/-! ## The rows, over an abstract polarized gadget -/

section Rows

open SetTheory (Form Free)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translate_srcConnElimOr (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y)
    (t w0 w1 w2 : ℕ) :
    (translateFormula (levelLeaves x)
        (srcConnSpine t (P 4 w0 0 1 🡒 (P 4 w1 3 1 ⋎ P 4 w2 2 1)))).val =
      connElimOrPart isFormCode3D4Code isFormCode2D4Code univEnv1D4Code
        (tagPairD4Code t) (bitWitnessCode w0) (bitWitnessCode w1)
        (bitWitnessCode w2) y := by
  rw [connElimOrPart, translate_srcConnSpine]
  simp only [translateFormula_imp, translate_or,
    Bootstrapping.Semiformula.val_imp, Bootstrapping.Semiformula.val_or,
    hP 4 w0 0 1 (by omega) (by omega), hP 4 w1 3 1 (by omega) (by omega),
    hP 4 w2 2 1 (by omega) (by omega)]

theorem translate_srcConnElimAnd (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y)
    (t w0 w1 w2 : ℕ) :
    (translateFormula (levelLeaves x)
        (srcConnSpine t (P 4 w0 0 1 🡒 (P 4 w1 3 1 ⋏ P 4 w2 2 1)))).val =
      connElimAndPart isFormCode3D4Code isFormCode2D4Code univEnv1D4Code
        (tagPairD4Code t) (bitWitnessCode w0) (bitWitnessCode w1)
        (bitWitnessCode w2) y := by
  rw [connElimAndPart, translate_srcConnSpine]
  simp only [translateFormula_imp, translate_and,
    Bootstrapping.Semiformula.val_imp, Bootstrapping.Semiformula.val_and,
    hP 4 w0 0 1 (by omega) (by omega), hP 4 w1 3 1 (by omega) (by omega),
    hP 4 w2 2 1 (by omega) (by omega)]

theorem translate_srcConnIntroOr (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y)
    (t w0 w1 w2 : ℕ) :
    (translateFormula (levelLeaves x)
        (srcConnSpine t ((P 4 w1 3 1 ⋎ P 4 w2 2 1) 🡒 P 4 w0 0 1))).val =
      connIntroOrPart isFormCode3D4Code isFormCode2D4Code univEnv1D4Code
        (tagPairD4Code t) (bitWitnessCode w0) (bitWitnessCode w1)
        (bitWitnessCode w2) y := by
  rw [connIntroOrPart, translate_srcConnSpine]
  simp only [translateFormula_imp, translate_or,
    Bootstrapping.Semiformula.val_imp, Bootstrapping.Semiformula.val_or,
    hP 4 w0 0 1 (by omega) (by omega), hP 4 w1 3 1 (by omega) (by omega),
    hP 4 w2 2 1 (by omega) (by omega)]

theorem translate_srcConnIntroAnd (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y)
    (t w0 w1 w2 : ℕ) :
    (translateFormula (levelLeaves x)
        (srcConnSpine t ((P 4 w1 3 1 ⋏ P 4 w2 2 1) 🡒 P 4 w0 0 1))).val =
      connIntroAndPart isFormCode3D4Code isFormCode2D4Code univEnv1D4Code
        (tagPairD4Code t) (bitWitnessCode w0) (bitWitnessCode w1)
        (bitWitnessCode w2) y := by
  rw [connIntroAndPart, translate_srcConnSpine]
  simp only [translateFormula_imp, translate_and,
    Bootstrapping.Semiformula.val_imp, Bootstrapping.Semiformula.val_and,
    hP 4 w0 0 1 (by omega) (by omega), hP 4 w1 3 1 (by omega) (by omega),
    hP 4 w2 2 1 (by omega) (by omega)]

theorem translate_srcQuantElim (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y)
    (t w : ℕ) :
    (translateFormula (levelLeaves x)
        (srcQuantSpine t (P 5 w 1 3 🡒 P 5 w 4 0))).val =
      quantElimPart isFormCode4D5Code univEnv3D5Code (tagUnD5Code t)
        econsQuantD5Code (bitWitnessCode w) y := by
  rw [quantElimPart, translate_srcQuantSpine]
  simp only [translateFormula_imp, Bootstrapping.Semiformula.val_imp,
    hP 5 w 1 3 (by omega) (by omega), hP 5 w 4 0 (by omega) (by omega)]

theorem translate_srcQuantIntro (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y)
    (t w : ℕ) :
    (translateFormula (levelLeaves x)
        (srcQuantSpine t (P 5 w 4 0 🡒 P 5 w 1 3))).val =
      quantIntroPart isFormCode4D5Code univEnv3D5Code (tagUnD5Code t)
        econsQuantD5Code (bitWitnessCode w) y := by
  rw [quantIntroPart, translate_srcQuantSpine]
  simp only [translateFormula_imp, Bootstrapping.Semiformula.val_imp,
    hP 5 w 1 3 (by omega) (by omega), hP 5 w 4 0 (by omega) (by omega)]

end Rows

/-! ## The two fields, abstractly and then at the two levels -/

section Fields

open SetTheory (Form Free)

/-- **The source form of the elimination field**, over an abstract
polarized gadget.  The eight rows are exactly those of
`CertificateFields.tarskiElimF`, in the same order. -/
noncomputable def srcTarskiElimOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) : Proposition srcL :=
  srcConnSpine 3 (P 4 1 0 1 🡒 (P 4 0 3 1 ⋎ P 4 1 2 1)) ⋏
  (srcConnSpine 3 (P 4 0 0 1 🡒 (P 4 1 3 1 ⋏ P 4 0 2 1)) ⋏
  (srcConnSpine 4 (P 4 1 0 1 🡒 (P 4 1 3 1 ⋏ P 4 1 2 1)) ⋏
  (srcConnSpine 4 (P 4 0 0 1 🡒 (P 4 0 3 1 ⋎ P 4 0 2 1)) ⋏
  (srcConnSpine 5 (P 4 1 0 1 🡒 (P 4 1 3 1 ⋎ P 4 1 2 1)) ⋏
  (srcConnSpine 5 (P 4 0 0 1 🡒 (P 4 0 3 1 ⋏ P 4 0 2 1)) ⋏
  (srcQuantSpine 6 (P 5 1 1 3 🡒 P 5 1 4 0) ⋏
   srcQuantSpine 7 (P 5 0 1 3 🡒 P 5 0 4 0)))))))

/-- **The source form of the introduction field**, over an abstract
polarized gadget.  The nine rows are exactly those of
`CertificateFields.tarskiIntroF`, in the same order. -/
noncomputable def srcTarskiIntroOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m) : Proposition srcL :=
  srcBotPiOf P ⋏
  (srcConnSpine 3 ((P 4 0 3 1 ⋎ P 4 1 2 1) 🡒 P 4 1 0 1) ⋏
  (srcConnSpine 3 ((P 4 1 3 1 ⋏ P 4 0 2 1) 🡒 P 4 0 0 1) ⋏
  (srcConnSpine 4 ((P 4 1 3 1 ⋏ P 4 1 2 1) 🡒 P 4 1 0 1) ⋏
  (srcConnSpine 4 ((P 4 0 3 1 ⋎ P 4 0 2 1) 🡒 P 4 0 0 1) ⋏
  (srcConnSpine 5 ((P 4 1 3 1 ⋎ P 4 1 2 1) 🡒 P 4 1 0 1) ⋏
  (srcConnSpine 5 ((P 4 0 3 1 ⋏ P 4 0 2 1) 🡒 P 4 0 0 1) ⋏
  (srcQuantSpine 6 (P 5 0 4 0 🡒 P 5 0 1 3) ⋏
   srcQuantSpine 7 (P 5 1 4 0 🡒 P 5 1 1 3))))))))

/-- **The source form of the elimination field.** -/
noncomputable def srcTarskiElim : Proposition srcL := srcTarskiElimOf srcPolarAt

/-- **The source form of the elimination field one index up.** -/
noncomputable def srcTarskiElimSucc : Proposition srcL :=
  srcTarskiElimOf srcPolarAtSucc

/-- **The source form of the introduction field.** -/
noncomputable def srcTarskiIntro : Proposition srcL :=
  srcTarskiIntroOf srcPolarAt

/-- **The source form of the introduction field one index up.** -/
noncomputable def srcTarskiIntroSucc : Proposition srcL :=
  srcTarskiIntroOf srcPolarAtSucc

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem translate_srcTarskiElimOf (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y) :
    (translateFormula (levelLeaves x) (srcTarskiElimOf P)).val =
      tarskiElimCode y := by
  rw [tarskiElimCode]
  simp only [srcTarskiElimOf, translate_and,
    Bootstrapping.Semiformula.val_and,
    translate_srcConnElimOr x y P hP, translate_srcConnElimAnd x y P hP,
    translate_srcQuantElim x y P hP]

theorem translate_srcTarskiIntroOf (x y : V)
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m →
      (translateFormula (levelLeaves x) (P m w ci ei)).val =
        polarAtCode (bitWitnessCode w) ci ei y) :
    (translateFormula (levelLeaves x) (srcTarskiIntroOf P)).val =
      tarskiIntroCode y := by
  rw [tarskiIntroCode]
  simp only [srcTarskiIntroOf, translate_and,
    Bootstrapping.Semiformula.val_and, translate_srcBotPiOf x y P hP,
    translate_srcConnIntroOr x y P hP, translate_srcConnIntroAnd x y P hP,
    translate_srcQuantIntro x y P hP]

/-- **The elimination field code is the specialization of a fixed source
formula**, at every model index, standard or not. -/
theorem translate_srcTarskiElim (x : V) :
    (translateFormula (levelLeaves x) srcTarskiElim).val = tarskiElimCode x :=
  translate_srcTarskiElimOf x x srcPolarAt
    (fun m w ci ei hci hei ↦ translate_srcPolarAt x m w ci ei hci hei)

/-- The elimination field code one index up. -/
theorem translate_srcTarskiElimSucc (x : V) :
    (translateFormula (levelLeaves x) srcTarskiElimSucc).val =
      tarskiElimCode (x + 1) :=
  translate_srcTarskiElimOf x (x + 1) srcPolarAtSucc
    (fun m w ci ei hci hei ↦ translate_srcPolarAtSucc x m w ci ei hci hei)

/-- **The introduction field code is the specialization of a fixed source
formula.** -/
theorem translate_srcTarskiIntro (x : V) :
    (translateFormula (levelLeaves x) srcTarskiIntro).val =
      tarskiIntroCode x :=
  translate_srcTarskiIntroOf x x srcPolarAt
    (fun m w ci ei hci hei ↦ translate_srcPolarAt x m w ci ei hci hei)

/-- The introduction field code one index up. -/
theorem translate_srcTarskiIntroSucc (x : V) :
    (translateFormula (levelLeaves x) srcTarskiIntroSucc).val =
      tarskiIntroCode (x + 1) :=
  translate_srcTarskiIntroOf x (x + 1) srcPolarAtSucc
    (fun m w ci ei hci hei ↦ translate_srcPolarAtSucc x m w ci ei hci hei)

/-! ### Typed forms -/

theorem translate_srcTarskiElim_formula (x : V) :
    translateFormula (levelLeaves x) srcTarskiElim = tarskiElimFormula x :=
  Bootstrapping.Semiformula.ext (translate_srcTarskiElim x)

theorem translate_srcTarskiElimSucc_formula (x : V) :
    translateFormula (levelLeaves x) srcTarskiElimSucc =
      tarskiElimFormula (x + 1) :=
  Bootstrapping.Semiformula.ext (translate_srcTarskiElimSucc x)

theorem translate_srcTarskiIntro_formula (x : V) :
    translateFormula (levelLeaves x) srcTarskiIntro = tarskiIntroFormula x :=
  Bootstrapping.Semiformula.ext (translate_srcTarskiIntro x)

theorem translate_srcTarskiIntroSucc_formula (x : V) :
    translateFormula (levelLeaves x) srcTarskiIntroSucc =
      tarskiIntroFormula (x + 1) :=
  Bootstrapping.Semiformula.ext (translate_srcTarskiIntroSucc x)

end Fields

/-! ## Free-variable-freeness -/

section FvFreeTarski

open SetTheory (Form Free)

theorem fvFree_srcLevelSatAt (m : ℕ) (hm : 3 ≤ m) : FvFree (srcLevelSatAt m) :=
  fvFree_srcLvlInstP (fun i hi ↦ by have := free_tripleMemCanon hi; omega)

theorem fvFree_srcLevelSatSuccAt (m : ℕ) (hm : 3 ≤ m) :
    FvFree (srcLevelSatSuccAt m) :=
  fvFree_srcLvlInst (fun i hi ↦ by have := free_tripleMemCanon hi; omega)
    (fvFree_srcNumChainSucc (m + 1 + 1) (by omega))
    (fvFree_srcClosStep (m + 1 + 1) (by omega))

theorem fvFree_srcBitWitnessAt (m w : ℕ) (hm : 2 ≤ m) :
    FvFree (srcBitWitnessAt m w) :=
  .exs ((fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)).and
    (fvFree_srcLevelSatAt (m + 1) (by omega)))

theorem fvFree_srcBitWitnessSuccAt (m w : ℕ) (hm : 2 ≤ m) :
    FvFree (srcBitWitnessSuccAt m w) :=
  .exs ((fvFree_liftP (fun i hi ↦ by have := free_fNumF hi; omega)).and
    (fvFree_srcLevelSatSuccAt (m + 1) (by omega)))

theorem fvFree_srcCanonAtPair (m ci ei : ℕ) (hci : ci < m) (hei : ei < m)
    {inner : Semiproposition srcL (m + 1 + 1)} (h : FvFree inner) :
    FvFree (srcCanonAtPair m ci ei inner) := by
  refine FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.imp ?_ h)))
  · exact fvFree_liftP (fun i hi ↦ by
      rcases free_fEq hi with rfl | rfl <;> omega)
  · exact fvFree_liftP (fun i hi ↦ by
      rcases free_fEq hi with rfl | rfl <;> omega)

theorem fvFree_srcPolarAt (m w ci ei : ℕ) (hci : ci < m) (hei : ei < m) :
    FvFree (srcPolarAt m w ci ei) :=
  fvFree_srcCanonAtPair m ci ei hci hei
    (fvFree_srcBitWitnessAt (m + 1 + 1) w (by omega))

theorem fvFree_srcPolarAtSucc (m w ci ei : ℕ) (hci : ci < m) (hei : ei < m) :
    FvFree (srcPolarAtSucc m w ci ei) :=
  fvFree_srcCanonAtPair m ci ei hci hei
    (fvFree_srcBitWitnessSuccAt (m + 1 + 1) w (by omega))

/-- The connective skeleton is free-variable-free.  The tag guard's bound
is an explicit argument, exactly as in
`CertificateFields.not_free_connClauseF`, so that the statement holds
uniformly in the tag while the kernel evaluations stay per-declaration. -/
theorem fvFree_srcConnSpine (t : ℕ) (ht : freeMax (fTagPairF 0 t 3 2) ≤ 4)
    {body : Semiproposition srcL 4} (h : FvFree body) :
    FvFree (srcConnSpine t body) := by
  refine FvFree.all (FvFree.all (FvFree.all (FvFree.all
    (FvFree.imp ?_ (FvFree.imp ?_ (FvFree.imp ?_ (FvFree.imp ?_ h)))))))
  · exact fvFree_liftP (fun _ hi ↦ free_isFormCode3D4 hi)
  · exact fvFree_liftP (fun _ hi ↦ free_isFormCode2D4 hi)
  · exact fvFree_liftP (fun _ hi ↦ by have := free_univEnv1D4 hi; omega)
  · exact fvFree_liftP (fun _ hi ↦ free_tagPairD4 ht hi)

/-- The quantifier skeleton is free-variable-free. -/
theorem fvFree_srcQuantSpine (t : ℕ) (ht : freeMax (fTagUnF 1 t 4) ≤ 5)
    {body : Semiproposition srcL 5} (h : FvFree body) :
    FvFree (srcQuantSpine t body) := by
  refine FvFree.all (FvFree.all (FvFree.all (FvFree.all (FvFree.all
    (FvFree.imp ?_ (FvFree.imp ?_ (FvFree.imp ?_ (FvFree.imp ?_ h))))))))
  · exact fvFree_liftP (fun _ hi ↦ free_isFormCode4D5 hi)
  · exact fvFree_liftP (fun _ hi ↦ free_univEnv3D5 hi)
  · exact fvFree_liftP (fun _ hi ↦ free_tagUnD5 ht hi)
  · exact fvFree_liftP (fun _ hi ↦ free_econsQuantD5 hi)

/-- The falsity row is free-variable-free. -/
theorem fvFree_srcBotPiOf (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei)) :
    FvFree (srcBotPiOf P) := by
  refine FvFree.all (FvFree.all (FvFree.imp ?_ (FvFree.imp ?_ ?_)))
  · exact fvFree_liftP (fun _ hi ↦ by have := free_univEnv1D4 hi; omega)
  · exact fvFree_liftP (fun _ hi ↦ free_taggedEmpty0D2 hi)
  · exact hP 2 0 0 1 (by omega) (by omega)

theorem fvFree_srcTarskiElimOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei)) :
    FvFree (srcTarskiElimOf P) := by
  have hc : ∀ w0 w1 w2 : ℕ,
      FvFree (P 4 w0 0 1 🡒 (P 4 w1 3 1 ⋎ P 4 w2 2 1)) := fun w0 w1 w2 ↦
    FvFree.imp (hP 4 w0 0 1 (by omega) (by omega))
      (FvFree.or (hP 4 w1 3 1 (by omega) (by omega))
        (hP 4 w2 2 1 (by omega) (by omega)))
  have ha : ∀ w0 w1 w2 : ℕ,
      FvFree (P 4 w0 0 1 🡒 (P 4 w1 3 1 ⋏ P 4 w2 2 1)) := fun w0 w1 w2 ↦
    FvFree.imp (hP 4 w0 0 1 (by omega) (by omega))
      (FvFree.and (hP 4 w1 3 1 (by omega) (by omega))
        (hP 4 w2 2 1 (by omega) (by omega)))
  have hq : ∀ w : ℕ, FvFree (P 5 w 1 3 🡒 P 5 w 4 0) := fun w ↦
    FvFree.imp (hP 5 w 1 3 (by omega) (by omega))
      (hP 5 w 4 0 (by omega) (by omega))
  exact FvFree.and (fvFree_srcConnSpine 3 freeMax_fTagPairF_imp (hc 1 0 1))
    (FvFree.and (fvFree_srcConnSpine 3 freeMax_fTagPairF_imp (ha 0 1 0))
    (FvFree.and (fvFree_srcConnSpine 4 freeMax_fTagPairF_and (ha 1 1 1))
    (FvFree.and (fvFree_srcConnSpine 4 freeMax_fTagPairF_and (hc 0 0 0))
    (FvFree.and (fvFree_srcConnSpine 5 freeMax_fTagPairF_or (hc 1 1 1))
    (FvFree.and (fvFree_srcConnSpine 5 freeMax_fTagPairF_or (ha 0 0 0))
    (FvFree.and (fvFree_srcQuantSpine 6 freeMax_fTagUnF_all (hq 1))
      (fvFree_srcQuantSpine 7 freeMax_fTagUnF_ex (hq 0))))))))

theorem fvFree_srcTarskiIntroOf
    (P : (m w ci ei : ℕ) → Semiproposition srcL m)
    (hP : ∀ m w ci ei, ci < m → ei < m → FvFree (P m w ci ei)) :
    FvFree (srcTarskiIntroOf P) := by
  have hc : ∀ w0 w1 w2 : ℕ,
      FvFree ((P 4 w1 3 1 ⋎ P 4 w2 2 1) 🡒 P 4 w0 0 1) := fun w0 w1 w2 ↦
    FvFree.imp (FvFree.or (hP 4 w1 3 1 (by omega) (by omega))
        (hP 4 w2 2 1 (by omega) (by omega)))
      (hP 4 w0 0 1 (by omega) (by omega))
  have ha : ∀ w0 w1 w2 : ℕ,
      FvFree ((P 4 w1 3 1 ⋏ P 4 w2 2 1) 🡒 P 4 w0 0 1) := fun w0 w1 w2 ↦
    FvFree.imp (FvFree.and (hP 4 w1 3 1 (by omega) (by omega))
        (hP 4 w2 2 1 (by omega) (by omega)))
      (hP 4 w0 0 1 (by omega) (by omega))
  have hq : ∀ w : ℕ, FvFree (P 5 w 4 0 🡒 P 5 w 1 3) := fun w ↦
    FvFree.imp (hP 5 w 4 0 (by omega) (by omega))
      (hP 5 w 1 3 (by omega) (by omega))
  exact FvFree.and (fvFree_srcBotPiOf P hP)
    (FvFree.and (fvFree_srcConnSpine 3 freeMax_fTagPairF_imp (hc 1 0 1))
    (FvFree.and (fvFree_srcConnSpine 3 freeMax_fTagPairF_imp (ha 0 1 0))
    (FvFree.and (fvFree_srcConnSpine 4 freeMax_fTagPairF_and (ha 1 1 1))
    (FvFree.and (fvFree_srcConnSpine 4 freeMax_fTagPairF_and (hc 0 0 0))
    (FvFree.and (fvFree_srcConnSpine 5 freeMax_fTagPairF_or (hc 1 1 1))
    (FvFree.and (fvFree_srcConnSpine 5 freeMax_fTagPairF_or (ha 0 0 0))
    (FvFree.and (fvFree_srcQuantSpine 6 freeMax_fTagUnF_all (hq 0))
      (fvFree_srcQuantSpine 7 freeMax_fTagUnF_ex (hq 1)))))))))

theorem fvFree_srcTarskiElim : FvFree srcTarskiElim :=
  fvFree_srcTarskiElimOf srcPolarAt
    (fun m w ci ei hci hei ↦ fvFree_srcPolarAt m w ci ei hci hei)

theorem fvFree_srcTarskiElimSucc : FvFree srcTarskiElimSucc :=
  fvFree_srcTarskiElimOf srcPolarAtSucc
    (fun m w ci ei hci hei ↦ fvFree_srcPolarAtSucc m w ci ei hci hei)

theorem fvFree_srcTarskiIntro : FvFree srcTarskiIntro :=
  fvFree_srcTarskiIntroOf srcPolarAt
    (fun m w ci ei hci hei ↦ fvFree_srcPolarAt m w ci ei hci hei)

theorem fvFree_srcTarskiIntroSucc : FvFree srcTarskiIntroSucc :=
  fvFree_srcTarskiIntroOf srcPolarAtSucc
    (fun m w ci ei hci hei ↦ fvFree_srcPolarAtSucc m w ci ei hci hei)

end FvFreeTarski

end SuccessorSources
end ZFCinPA
end LeanProofs
