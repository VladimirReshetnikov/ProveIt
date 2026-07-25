import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula
import BoundedPAConsistency.FinFunext
import Foundation.FirstOrder.Completeness

/-!
# Compiled member-validity elimination for dynamic truth certificates

The body witnessing a successor-truth assertion contains a bounded universal
statement saying that every member of its HFS certificate is a valid record.
This module isolates the corresponding elimination rule:

`AcceptedCertificate(C, bound, free, p) ∧ r ∈ C → RecordValid(C, r)`.

The theorem is first proved once in the fixed source language, then compiled
at arbitrary model-coded lower truth syntax and arbitrary model levels.  The
last section specializes it at the nonstandard dynamic truth orbit.  This is
one honest local-law conjunct; it is not presented as the complete
`localStep` certificate field.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## The fixed source theorem -/

/-- Apply a closed source formula of arity four to four source terms. -/
noncomputable def apply₄ {n : ℕ}
    (p : Semisentence SourceLanguage 4)
    (t₀ t₁ t₂ t₃ : ClosedSemiterm SourceLanguage n) :
    Semisentence SourceLanguage n :=
  p ⇜ ![t₀, t₁, t₂, t₃]

/-- The body under the certificate existential in
`DynamicTruthTemplateFormula.successorTruthFormula`.

Its arguments are `(C, bound, free, p)`. -/
noncomputable def acceptedCertificateBody :
    Semisentence SourceLanguage 4 :=
  liftArithmeticFormula hasTruthStateDef.val ⋏
    (∀⁰
      (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1) 🡒
        apply₂ successorRecordValid (#1) (#0)))

/-- The same accepted-certificate data in a context which already contains
the record to be checked.

The five arguments are `(r, C, bound, free, p)`.  Spelling out the lifted
indices keeps the later universal-specialization proof transparent: under
the inner record binder the certificate itself is `#2`. -/
noncomputable def acceptedCertificateAtRecord :
    Semisentence SourceLanguage 5 :=
  apply₄ (liftArithmeticFormula hasTruthStateDef.val)
      (#1) (#2) (#3) (#4) ⋏
    (∀⁰
      (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#2) 🡒
        apply₂ successorRecordValid (#2) (#0)))

/-- Eliminate the bounded universal member check at a specified record.

The five arguments are `(r, C, bound, free, p)`. -/
noncomputable def memberValidityLocalLaw :
    Semisentence SourceLanguage 5 :=
  (acceptedCertificateAtRecord ⋏
      apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1)) 🡒
    apply₂ successorRecordValid (#1) (#0)

/-- Universal closure of the member-validity elimination rule. -/
noncomputable def memberValiditySentence : Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ memberValidityLocalLaw

/-- A fixed source derivation of member-validity elimination.

The proof is pure first-order logic: after opening the accepted certificate,
specialize its universal member check at the supplied record and apply the
membership premise.  Completeness only materializes that fixed finite source
derivation before the model-coded compiler traverses it. -/
noncomputable def sourceProof :
    parameterTemplatePeano 3 2 ⊢! memberValiditySentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, memberValiditySentence, memberValidityLocalLaw,
      acceptedCertificateAtRecord, apply₄,
      DynamicTruthTemplateFormula.apply₂,
      DynamicTruthTemplateFormula.liftArithmeticFormula]
    intro _ambient _structure _modelsPeano p free bound C r
      _hasState hall hmem
    exact hall r hmem).get

/-! ## Exact specialization at model-coded truth -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Translation commutes with applying an arity-four source formula. -/
@[simp] theorem translate_apply₄
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V)
    (p : Semisentence SourceLanguage 4)
    (t₀ t₁ t₂ t₃ : ClosedSemiterm SourceLanguage n) :
    translateFormula lower parameters
        (Rewriting.emb (apply₄ p t₀ t₁ t₂ t₃)) =
      (translateFormula lower parameters (Rewriting.emb p)).subst
        ![translateTerm parameters
            (Rew.emb t₀ : SyntacticSemiterm SourceLanguage n),
          translateTerm parameters
            (Rew.emb t₁ : SyntacticSemiterm SourceLanguage n),
          translateTerm parameters
            (Rew.emb t₂ : SyntacticSemiterm SourceLanguage n),
          translateTerm parameters
            (Rew.emb t₃ : SyntacticSemiterm SourceLanguage n)] := by
  rw [apply₄, Semiformula.coe_subst_eq_subst_coe,
    ModelCodedPredicateParameters.translateFormula_subst]
  congr 1
  exact funext_fin4 rfl rfl rfl rfl

/-- Typed accepted-certificate data in the record-checking context. -/
noncomputable def acceptedCertificateAtRecordFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 5 :=
  (⌜hasTruthStateDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 4).subst
      ![Semiterm.bvar (1 : Fin 5), Semiterm.bvar (2 : Fin 5),
        Semiterm.bvar (3 : Fin 5), Semiterm.bvar (4 : Fin 5)] ⋏
    (∀⁰
      (((⌜hfsMemDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
          ![Semiterm.bvar (0 : Fin 6), Semiterm.bvar (2 : Fin 6)]) 🡒
        (DynamicTruthFormula.successorRecordValid
            lower lowerLevel upperLevel).subst
          ![Semiterm.bvar (2 : Fin 6), Semiterm.bvar (0 : Fin 6)]))

/-- Concrete typed member-validity elimination formula. -/
noncomputable def memberValidityFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰
    ((acceptedCertificateAtRecordFormula lower lowerLevel upperLevel ⋏
      (⌜hfsMemDef.val⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Semiterm.bvar (0 : Fin 5), Semiterm.bvar (1 : Fin 5)]) 🡒
      (DynamicTruthFormula.successorRecordValid
          lower lowerLevel upperLevel).subst
        ![Semiterm.bvar (1 : Fin 5), Semiterm.bvar (0 : Fin 5)])

@[simp] theorem translate_acceptedCertificateAtRecord
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb acceptedCertificateAtRecord) =
      acceptedCertificateAtRecordFormula lower lowerLevel upperLevel := by
  simp [acceptedCertificateAtRecord, acceptedCertificateAtRecordFormula,
    apply₄,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    Bootstrapping.Semiformula.imp_def]
  constructor
  · simpa [apply₄, ModelCodedPredicateParameters.translateTerm] using
      (translate_apply₄ lower ![lowerLevel, upperLevel]
        (liftArithmeticFormula hasTruthStateDef.val)
        (#1 : ClosedSemiterm SourceLanguage 5) (#2) (#3) (#4))
  · calc
      translateFormula lower ![lowerLevel, upperLevel]
          (Semiformula.neg
            ((Rewriting.app Rew.emb)
              (apply₂ (n := 6)
                (liftArithmeticFormula hfsMemDef.val) (#0) (#2)))) =
        ∼translateFormula lower ![lowerLevel, upperLevel]
          (Rewriting.emb
            (apply₂ (n := 6)
              (liftArithmeticFormula hfsMemDef.val) (#0) (#2))) := by
            simpa only [Semiformula.neg_eq] using
              (ModelCodedPredicateParameters.translateFormula_neg
                lower ![lowerLevel, upperLevel]
                (Rewriting.emb
                  (apply₂ (n := 6)
                    (liftArithmeticFormula hfsMemDef.val) (#0) (#2))))
      _ = _ := by
        simp [ModelCodedPredicateParameters.translateTerm]

/-- Specializing the fixed source sentence gives exactly the typed rule. -/
@[simp] theorem translate_memberValiditySentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb memberValiditySentence) =
      memberValidityFormula lower lowerLevel upperLevel := by
  simp [memberValiditySentence, memberValidityLocalLaw,
    memberValidityFormula,
    ModelCodedPredicateParameters.translateFormula,
    ModelCodedPredicateParameters.translateTerm,
    Bootstrapping.Semiformula.imp_def]
  calc
    translateFormula lower ![lowerLevel, upperLevel]
        (Semiformula.neg
          ((Rewriting.app Rew.emb)
              acceptedCertificateAtRecord ⋏
            (Rewriting.app Rew.emb)
              (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1)))) =
      ∼translateFormula lower ![lowerLevel, upperLevel]
        ((Rewriting.app Rew.emb)
            acceptedCertificateAtRecord ⋏
          (Rewriting.app Rew.emb)
            (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1))) := by
        simpa only [Semiformula.neg_eq] using
          (ModelCodedPredicateParameters.translateFormula_neg
            lower ![lowerLevel, upperLevel]
            ((Rewriting.app Rew.emb)
                acceptedCertificateAtRecord ⋏
              (Rewriting.app Rew.emb)
                (apply₂ (liftArithmeticFormula hfsMemDef.val) (#0) (#1))))
    _ = _ := by
      simp [ModelCodedPredicateParameters.translateFormula,
        ModelCodedPredicateParameters.translateTerm]

/-- Compile member-validity elimination at arbitrary model-coded syntax. -/
noncomputable def compiledMemberValidityProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      memberValidityFormula lower lowerLevel upperLevel := by
  simpa only [translate_memberValiditySentence] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel] hlower sourceProof)

set_option backward.isDefEq.respectTransparency false in
/-- The compiled derivation carries an actual represented PA proof code. -/
theorem compiledMemberValidityProof_isPAProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Proof Peano
      (compiledMemberValidityProof lower lowerLevel upperLevel hlower).val
      (memberValidityFormula lower lowerLevel upperLevel).val := by
  simpa [Proof] using
    (compiledMemberValidityProof lower lowerLevel upperLevel
      hlower).derivationOf

/-! ## Exact specialization at the nonstandard orbit -/

/-- Member-validity elimination for the successor built over
`truthFormula n`. -/
noncomputable def orbitMemberValidityFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  memberValidityFormula (truthFormula n) (n + 1) (n + 1 + 1)

/-- Typed PA proof of member-validity elimination at every model level. -/
noncomputable def orbitMemberValidityProof (n : V) :
    Peano.internalize V ⊢! orbitMemberValidityFormula n :=
  compiledMemberValidityProof
    (truthFormula n) (n + 1) (n + 1 + 1) (truthFormula_shift n)

set_option backward.isDefEq.respectTransparency false in
/-- Represented-proof form of the orbit specialization. -/
theorem orbitMemberValidityProof_isPAProof (n : V) :
    Proof Peano (orbitMemberValidityProof n).val
      (orbitMemberValidityFormula n).val := by
  simpa [Proof] using (orbitMemberValidityProof n).derivationOf

end LeanProofs.BoundedPAConsistency.DynamicTruthMemberValidityTemplate
