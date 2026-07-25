import ZFCinPA.CertificateFields
import ZFCinPA.CertificateFamily

/-!
# The concrete `𝗭𝗙𝗖` truth-certificate family

`ZFCinPA.CertificateFields` builds the five variable field-code functions
and their `𝚺₁` graphs; `ZFCinPA.CertificateFamily` demands *typed*
model-coded formulas (`Bootstrapping.Formula V ℒₛₑₜ`).  This module closes
the gap and assembles the family.

## The typed-wrapper design decision

The family structure fixes the five variable fields to be typed formulas
at *every* model index, so — unlike the forced sixth field, whose
well-formedness `CertificateFamily` recovers from incoming proofs — the
five fields need `IsFormula` witnesses outright.  The witnesses are proved
here, once and for all indices, by the same route goal 1's
`DynamicTruthOrbit` used for its truth-formula orbit: model-internal `𝚺₁`
successor induction (`ISigma1.sigma1_succ_induction`) along each `PR`
tower of `ZFCinPA.LevelCodeTower`, followed by pure spine decomposition
for the five fixed splices.

Every fixed leaf is well-formed at exactly the arity of its named code:
the per-constant lemmas below are `coe_toNat_eq_quote` plus the quotation
well-formedness fact, and they respect the parameter firewall — the
constants are matched by one definitional unfolding, never evaluated.
The two tower leaves enter through arity monotonicity of `IsSemiformula`.

The five `𝚺₁` graphs are then exactly the shape
`ZFCTruthCertificateFamily.code_definable_of_fields` consumes: the typed
wrappers' `.val` projections are the raw builders definitionally. -/

set_option autoImplicit false
set_option maxRecDepth 2000

namespace LeanProofs
namespace ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open BoundedZFCConsistency (fNumF fTripleMemF fUnivEnvF levelSatF
  fLevelImpF fLevelAndF fLevelOrF fTagUnF fPiBoundedF fSigmaBoundedF
  fShiftTripleMemF fIsFormCodeF fQuantBoundedF fZFCAxiomCodeF
  fTaggedEmptyF fVarMapF fRenamesF fCompF fEconsF fSuccMapF)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Arity plumbing -/

/-- `IsSemiformula` is monotone in the arity. -/
lemma isSemiformula_of_le {p k m : V}
    (h : IsSemiformula ℒₛₑₜ k p) (hm : k ≤ m) :
    IsSemiformula ℒₛₑₜ m p :=
  ⟨h.isUFormula, le_trans h.bv_le hm⟩

/-- A named standard code is well-formed at its own translation depth. -/
lemma leafArity {k : ℕ} (φ : SetTheorySemiproposition k) :
    IsSemiformula ℒₛₑₜ ((k : ℕ) : V) ((φ.toNat : ℕ) : V) := by
  rw [coe_toNat_eq_quote]
  simp

/-! ## The fixed leaves, well-formed at their named arities

One tiny lemma per named constant.  Each is `leafArity` at the constant's
defining semiproposition; the `simpa` only normalizes the arity numeral,
and the constant itself is matched by a single definitional unfolding. -/

private lemma wf_tripleMemHead :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((tripleMemHeadCode : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fTripleMemF 2 1 0 4))

private lemma wf_univEnvLeaf :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((univEnvLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fUnivEnvF 1))

private lemma wf_numPairLeaf :
    IsSemiformula ℒₛₑₜ ((7 : ℕ) : V) ((numPairLeafCode : ℕ) : V) :=
  leafArity (V := V)
    (toSet 7 (SetTheory.Form.fAnd (fNumF 1 0) (fNumF 0 1)))

private lemma wf_impClauseLeaf :
    IsSemiformula ℒₛₑₜ ((7 : ℕ) : V) ((impClauseLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 7 (fLevelImpF 4 3 2 6 1 0))

private lemma wf_andClauseLeaf :
    IsSemiformula ℒₛₑₜ ((7 : ℕ) : V) ((andClauseLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 7 (fLevelAndF 4 3 2 6 1 0))

private lemma wf_orClauseLeaf :
    IsSemiformula ℒₛₑₜ ((7 : ℕ) : V) ((orClauseLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 7 (fLevelOrF 4 3 2 6 1 0))

private lemma wf_tagAllLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((tagAllLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 8 (fTagUnF 5 6 0))

private lemma wf_tagExLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((tagExLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 8 (fTagUnF 5 7 0))

private lemma wf_eqBitOneLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((eqBitOneLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 8 (SetTheory.Form.fEq 3 1))

private lemma wf_eqBitZeroLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((eqBitZeroLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 8 (SetTheory.Form.fEq 3 2))

private lemma wf_piBoundedLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((piBoundedLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 8 (fPiBoundedF 6 5))

private lemma wf_sigmaBoundedLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((sigmaBoundedLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 8 (fSigmaBoundedF 6 5))

private lemma wf_allWitnessLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((allWitnessLeafCode : ℕ) : V) :=
  leafArity (V := V)
    (toSet 8 (SetTheory.Form.fAnd (.fEq 3 2)
      (.fEx (fShiftTripleMemF 1 0 5 8 0))))

private lemma wf_exWitnessLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((exWitnessLeafCode : ℕ) : V) :=
  leafArity (V := V)
    (toSet 8 (SetTheory.Form.fAnd (.fEq 3 1)
      (.fEx (fShiftTripleMemF 1 0 5 8 1))))

private lemma wf_botLeaf :
    IsSemiformula ℒₛₑₜ ((8 : ℕ) : V) ((botLeafCode : ℕ) : V) :=
  leafArity (V := V) (toSet 8 SetTheory.Form.fBot)

private lemma wf_tripleMemInstA :
    IsSemiformula ℒₛₑₜ ((9 : ℕ) : V) ((tripleMemInstACode : ℕ) : V) :=
  leafArity (V := V) (toSet 9 (fTripleMemF 6 5 4 1))

private lemma wf_tripleMemInstB :
    IsSemiformula ℒₛₑₜ ((10 : ℕ) : V) ((tripleMemInstBCode : ℕ) : V) :=
  leafArity (V := V) (toSet 10 (fTripleMemF 7 6 4 1))

private lemma wf_tripleMemInstC :
    IsSemiformula ℒₛₑₜ ((10 : ℕ) : V) ((tripleMemInstCCode : ℕ) : V) :=
  leafArity (V := V) (toSet 10 (fTripleMemF 7 6 3 1))

private lemma wf_tripleMemCanon :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((tripleMemCanonCode : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fTripleMemF 4 3 2 1))

private lemma wf_levelSatZero :
    IsSemiformula ℒₛₑₜ ((3 : ℕ) : V) ((levelSatZeroCode : ℕ) : V) :=
  leafArity (V := V) (toSet 3 (levelSatF 0 2 1 0))

private lemma wf_closZero :
    IsSemiformula ℒₛₑₜ ((2 : ℕ) : V) ((closZeroCode : ℕ) : V) :=
  leafArity (V := V) (toSet 2 (closF 0))

private lemma wf_numOneWitness :
    IsSemiformula ℒₛₑₜ ((3 : ℕ) : V) ((numOneWitnessCode : ℕ) : V) :=
  leafArity (V := V) (toSet 3 (fNumF 0 1))

private lemma wf_numZeroWitness :
    IsSemiformula ℒₛₑₜ ((3 : ℕ) : V) ((numZeroWitnessCode : ℕ) : V) :=
  leafArity (V := V) (toSet 3 (fNumF 0 0))

private lemma wf_botCanon :
    IsSemiformula ℒₛₑₜ ((2 : ℕ) : V) ((botCanonCode : ℕ) : V) :=
  leafArity (V := V) (toSet 2 SetTheory.Form.fBot)

private lemma wf_numChainZero :
    IsSemiformula ℒₛₑₜ ((1 : ℕ) : V) ((numChainZeroCode : ℕ) : V) :=
  leafArity (V := V) (toSet 1 (fNumF 0 0))

private lemma wf_numChainStep :
    IsSemiformula ℒₛₑₜ ((2 : ℕ) : V) ((numChainStepCode : ℕ) : V) :=
  leafArity (V := V) (toSet 2 (SetTheory.fSuccF 1 0))

private lemma wf_eqGuard (i j : ℕ) :
    IsSemiformula ℒₛₑₜ ((max i j + 1 : ℕ) : V) ((eqGuardCode i j : ℕ) : V) :=
  leafArity (V := V) (toSet (max i j + 1) (SetTheory.Form.fEq i j))

private lemma wf_univEnv0D2 :
    IsSemiformula ℒₛₑₜ ((2 : ℕ) : V) ((univEnv0D2Code : ℕ) : V) :=
  leafArity (V := V) (toSet 2 (fUnivEnvF 0))

private lemma wf_univEnv1D4 :
    IsSemiformula ℒₛₑₜ ((4 : ℕ) : V) ((univEnv1D4Code : ℕ) : V) :=
  leafArity (V := V) (toSet 4 (fUnivEnvF 1))

private lemma wf_univEnv1D5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((univEnv1D5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fUnivEnvF 1))

private lemma wf_taggedEmptyD2 :
    IsSemiformula ℒₛₑₜ ((2 : ℕ) : V) ((taggedEmptyD2Code : ℕ) : V) :=
  leafArity (V := V) (toSet 2 (fTaggedEmptyF 1 2))

private lemma wf_isFormCode1D2 :
    IsSemiformula ℒₛₑₜ ((2 : ℕ) : V) ((isFormCode1D2Code : ℕ) : V) :=
  leafArity (V := V) (toSet 2 (fIsFormCodeF 1))

private lemma wf_isFormCode3D4 :
    IsSemiformula ℒₛₑₜ ((4 : ℕ) : V) ((isFormCode3D4Code : ℕ) : V) :=
  leafArity (V := V) (toSet 4 (fIsFormCodeF 3))

private lemma wf_isFormCode4D5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((isFormCode4D5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fIsFormCodeF 4))

private lemma wf_zfcAxiomCodeD2 :
    IsSemiformula ℒₛₑₜ ((2 : ℕ) : V) ((zfcAxiomCodeD2Code : ℕ) : V) :=
  leafArity (V := V) (toSet 2 (fZFCAxiomCodeF 1))

private lemma wf_quantBoundedD3 :
    IsSemiformula ℒₛₑₜ ((3 : ℕ) : V) ((quantBoundedD3Code : ℕ) : V) :=
  leafArity (V := V) (toSet 3 (fQuantBoundedF 0 2))

private lemma wf_succMapD5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((succMapD5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fSuccMapF 0))

private lemma wf_renamesShiftD5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((renamesShiftD5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fRenamesF 0 4 3))

private lemma wf_econsD5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((econsD5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fEconsF 0 1 2))

private lemma wf_varMap3D5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((varMap3D5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fVarMapF 3))

private lemma wf_renamesSubstD5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((renamesSubstD5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fRenamesF 3 4 2))

private lemma wf_compD5 :
    IsSemiformula ℒₛₑₜ ((5 : ℕ) : V) ((compD5Code : ℕ) : V) :=
  leafArity (V := V) (toSet 5 (fCompF 0 1 3))

/- The parameter firewall, enforced at the unification level: with the
leaf lemmas in place, nothing below may ever delta-unfold a named code
constant — a failed unification attempt against one would otherwise try
to *evaluate* the Gödel code. -/
attribute [local irreducible] tripleMemHeadCode univEnvLeafCode
  numPairLeafCode impClauseLeafCode andClauseLeafCode orClauseLeafCode
  tagAllLeafCode tagExLeafCode eqBitOneLeafCode eqBitZeroLeafCode
  piBoundedLeafCode sigmaBoundedLeafCode allWitnessLeafCode
  exWitnessLeafCode botLeafCode tripleMemInstACode tripleMemInstBCode
  tripleMemInstCCode tripleMemCanonCode levelSatZeroCode closZeroCode
  numOneWitnessCode numZeroWitnessCode botCanonCode numChainZeroCode
  numChainStepCode eqGuardCode univEnv0D2Code univEnv1D4Code
  univEnv1D5Code taggedEmptyD2Code isFormCode1D2Code isFormCode3D4Code
  isFormCode4D5Code zfcAxiomCodeD2Code quantBoundedD3Code succMapD5Code
  renamesShiftD5Code econsD5Code varMap3D5Code renamesSubstD5Code
  compD5Code

/-! ## Well-formedness along the towers

Each proof is a model-internal `𝚺₁` successor induction: the base is a
named standard code, the step a constructor application over well-formed
pieces.

The `definability` side conditions need the tower functions as
`DefinableFunction₁` *instances*; `ZFCinPA.LevelCodeTower` registers only
the `via` forms, so the conversions are registered here. -/

instance numChainCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁ (numChainCode : V → V) :=
  numChainCode.defined.to_definable

instance closCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁ (closCode : V → V) :=
  closCode.defined.to_definable

instance levelSatCode_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁ (levelSatCode : V → V) :=
  levelSatCode.defined.to_definable

/-- The numeral chain is a unary formula code at every index. -/
theorem isSemiformula_numChainCode (x : V) :
    IsSemiformula ℒₛₑₜ 1 (numChainCode x) := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [numChainCode_zero]
    exact isSemiformula_of_le wf_numChainZero (by norm_num)
  case succ x ih =>
    rw [numChainCode_succ]
    simp only [IsSemiformula.exs, IsSemiformula.and]
    exact ⟨isSemiformula_of_le ih (by norm_num),
      isSemiformula_of_le wf_numChainStep (by norm_num)⟩

/-- The closure kernel is a binary formula code at every index. -/
theorem isSemiformula_closCode (x : V) :
    IsSemiformula ℒₛₑₜ 2 (closCode x) := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [closCode_zero]
    exact isSemiformula_of_le wf_closZero (by norm_num)
  case succ x ih =>
    rw [closCode_succ]
    simp only [closStepCode, closStepPart, justRowCode, justRowPart,
      allClauseCode, allClausePart, exClauseCode, exClausePart, lvlInstPart,
      IsSemiformula.all, IsSemiformula.exs, IsSemiformula.and,
      IsSemiformula.or, IsSemiformula.imp]
    and_intros
    all_goals
      first
      | exact isSemiformula_of_le (isSemiformula_numChainCode x)
          (by norm_num)
      | exact isSemiformula_of_le ih (by norm_num)
      | exact isSemiformula_of_le wf_tripleMemHead (by norm_num)
      | exact isSemiformula_of_le wf_univEnvLeaf (by norm_num)
      | exact isSemiformula_of_le wf_numPairLeaf (by norm_num)
      | exact isSemiformula_of_le wf_impClauseLeaf (by norm_num)
      | exact isSemiformula_of_le wf_andClauseLeaf (by norm_num)
      | exact isSemiformula_of_le wf_orClauseLeaf (by norm_num)
      | exact isSemiformula_of_le wf_tagAllLeaf (by norm_num)
      | exact isSemiformula_of_le wf_tagExLeaf (by norm_num)
      | exact isSemiformula_of_le wf_eqBitOneLeaf (by norm_num)
      | exact isSemiformula_of_le wf_eqBitZeroLeaf (by norm_num)
      | exact isSemiformula_of_le wf_piBoundedLeaf (by norm_num)
      | exact isSemiformula_of_le wf_sigmaBoundedLeaf (by norm_num)
      | exact isSemiformula_of_le wf_allWitnessLeaf (by norm_num)
      | exact isSemiformula_of_le wf_exWitnessLeaf (by norm_num)
      | exact isSemiformula_of_le wf_botLeaf (by norm_num)
      | exact isSemiformula_of_le wf_tripleMemInstA (by norm_num)
      | exact isSemiformula_of_le wf_tripleMemInstB (by norm_num)
      | exact isSemiformula_of_le wf_tripleMemInstC (by norm_num)

/-- The canonical level instance is a ternary formula code at every
index. -/
theorem isSemiformula_levelSatCode (x : V) :
    IsSemiformula ℒₛₑₜ 3 (levelSatCode x) := by
  induction x using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    rw [levelSatCode_zero]
    exact isSemiformula_of_le wf_levelSatZero (by norm_num)
  case succ x _ =>
    rw [levelSatCode_succ]
    simp only [lvlInstPart, IsSemiformula.exs, IsSemiformula.and]
    and_intros
    · exact isSemiformula_of_le (isSemiformula_numChainCode x) (by norm_num)
    · exact isSemiformula_of_le (isSemiformula_closCode x) (by norm_num)
    · exact isSemiformula_of_le wf_tripleMemCanon (by norm_num)

/-- The Sigma-truth reading is a binary formula code at every index. -/
theorem isSemiformula_sigmaTrueCode (x : V) :
    IsSemiformula ℒₛₑₜ 2 (sigmaTrueCode x) := by
  simp only [sigmaTrueCode, bitWitnessPart, IsSemiformula.exs,
    IsSemiformula.and]
  exact ⟨isSemiformula_of_le wf_numOneWitness (by norm_num),
    isSemiformula_of_le (isSemiformula_levelSatCode x) (by norm_num)⟩

/-- The Pi-falsity reading is a binary formula code at every index. -/
theorem isSemiformula_piFalseCode (x : V) :
    IsSemiformula ℒₛₑₜ 2 (piFalseCode x) := by
  simp only [piFalseCode, bitWitnessPart, IsSemiformula.exs,
    IsSemiformula.and]
  exact ⟨isSemiformula_of_le wf_numZeroWitness (by norm_num),
    isSemiformula_of_le (isSemiformula_levelSatCode x) (by norm_num)⟩

/-- The Pi-truth reading is a binary formula code at every index. -/
theorem isSemiformula_piTrueCode (x : V) :
    IsSemiformula ℒₛₑₜ 2 (piTrueCode x) := by
  simp only [piTrueCode, piTruePart, IsSemiformula.imp]
  exact ⟨isSemiformula_piFalseCode x,
    isSemiformula_of_le wf_botCanon (by norm_num)⟩

/-! ## Well-formedness of the five field codes

Pure spine decomposition — no induction: the towers enter through the
invariants above and arity monotonicity, every fixed leaf at exactly its
named arity. -/

/-- The local-step field is a sentence code at every index. -/
theorem isFormula_localStepCode (x : V) :
    IsFormula ℒₛₑₜ (localStepCode x) := by
  simp only [localStepCode, localStepPart, sigmaAtCode, piTrueAtCode,
    canonAtPart, IsSemiformula.all, IsSemiformula.imp, IsSemiformula.and]
  and_intros
  all_goals
    first
    | exact isSemiformula_of_le (isSemiformula_sigmaTrueCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (isSemiformula_piTrueCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 1 3) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 0 2) (by norm_num)
    | exact isSemiformula_of_le wf_univEnv0D2 (by norm_num)
    | exact isSemiformula_of_le wf_taggedEmptyD2 (by norm_num)
    | exact isSemiformula_of_le wf_isFormCode1D2 (by norm_num)
    | exact isSemiformula_of_le wf_botCanon (by norm_num)

/-- The cross-level field is a sentence code at every index. -/
theorem isFormula_crossLevelCode (x : V) :
    IsFormula ℒₛₑₜ (crossLevelCode x) := by
  simp only [crossLevelCode, crossLevelPart, sigmaAtCode, piFalseAtCode,
    canonAtPart, boundedAtPart, IsSemiformula.all, IsSemiformula.exs,
    IsSemiformula.imp, IsSemiformula.and, IsSemiformula.or]
  and_intros
  all_goals
    first
    | exact isSemiformula_of_le (isSemiformula_sigmaTrueCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (isSemiformula_piFalseCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (isSemiformula_numChainCode x) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 1 3) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 0 2) (by norm_num)
    | exact isSemiformula_of_le wf_isFormCode1D2 (by norm_num)
    | exact isSemiformula_of_le wf_univEnv0D2 (by norm_num)
    | exact isSemiformula_of_le wf_quantBoundedD3 (by norm_num)

/-- The shift-invariance field is a sentence code at every index. -/
theorem isFormula_shiftInvariantCode (x : V) :
    IsFormula ℒₛₑₜ (shiftInvariantCode x) := by
  simp only [shiftInvariantCode, shiftInvariantPart, sigmaAtCode,
    piFalseAtCode, canonAtPart, IsSemiformula.all, IsSemiformula.exs,
    IsSemiformula.imp, IsSemiformula.and, IsSemiformula.iff]
  and_intros
  all_goals
    first
    | exact isSemiformula_of_le (isSemiformula_sigmaTrueCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (isSemiformula_piFalseCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 1 5) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 0 2) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 1 6) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 0 4) (by norm_num)
    | exact isSemiformula_of_le wf_isFormCode3D4 (by norm_num)
    | exact isSemiformula_of_le wf_succMapD5 (by norm_num)
    | exact isSemiformula_of_le wf_renamesShiftD5 (by norm_num)
    | exact isSemiformula_of_le wf_univEnv1D4 (by norm_num)
    | exact isSemiformula_of_le wf_econsD5 (by norm_num)

/-- The substitution-invariance field is a sentence code at every index. -/
theorem isFormula_substitutionInvariantCode (x : V) :
    IsFormula ℒₛₑₜ (substitutionInvariantCode x) := by
  simp only [substitutionInvariantCode, substitutionInvariantPart,
    sigmaAtCode, piFalseAtCode, canonAtPart, IsSemiformula.all,
    IsSemiformula.imp, IsSemiformula.and, IsSemiformula.iff]
  and_intros
  all_goals
    first
    | exact isSemiformula_of_le (isSemiformula_sigmaTrueCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (isSemiformula_piFalseCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 1 4) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 0 3) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 1 6) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 0 2) (by norm_num)
    | exact isSemiformula_of_le wf_isFormCode4D5 (by norm_num)
    | exact isSemiformula_of_le wf_varMap3D5 (by norm_num)
    | exact isSemiformula_of_le wf_renamesSubstD5 (by norm_num)
    | exact isSemiformula_of_le wf_univEnv1D5 (by norm_num)
    | exact isSemiformula_of_le wf_compD5 (by norm_num)

/-- The axiom-soundness field is a sentence code at every index. -/
theorem isFormula_axiomSoundCode (x : V) :
    IsFormula ℒₛₑₜ (axiomSoundCode x) := by
  simp only [axiomSoundCode, axiomSoundPart, sigmaAtCode, piTrueAtCode,
    canonAtPart, boundedAtPart, IsSemiformula.all, IsSemiformula.exs,
    IsSemiformula.imp, IsSemiformula.and]
  and_intros
  all_goals
    first
    | exact isSemiformula_of_le (isSemiformula_sigmaTrueCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (isSemiformula_piTrueCode (x + 1))
        (by norm_num)
    | exact isSemiformula_of_le (isSemiformula_numChainCode x) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 1 3) (by norm_num)
    | exact isSemiformula_of_le (wf_eqGuard 0 2) (by norm_num)
    | exact isSemiformula_of_le wf_zfcAxiomCodeD2 (by norm_num)
    | exact isSemiformula_of_le wf_univEnv0D2 (by norm_num)
    | exact isSemiformula_of_le wf_quantBoundedD3 (by norm_num)

/-! ## The typed field formulas -/

/-- Typed view of the local-step field. -/
noncomputable def localStepFormula (x : V) : Bootstrapping.Formula V ℒₛₑₜ :=
  ⟨localStepCode x, by simpa using isFormula_localStepCode x⟩

@[simp] theorem localStepFormula_val (x : V) :
    (localStepFormula x).val = localStepCode x := rfl

/-- Typed view of the cross-level field. -/
noncomputable def crossLevelFormula (x : V) : Bootstrapping.Formula V ℒₛₑₜ :=
  ⟨crossLevelCode x, by simpa using isFormula_crossLevelCode x⟩

@[simp] theorem crossLevelFormula_val (x : V) :
    (crossLevelFormula x).val = crossLevelCode x := rfl

/-- Typed view of the shift-invariance field. -/
noncomputable def shiftInvariantFormula (x : V) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  ⟨shiftInvariantCode x, by simpa using isFormula_shiftInvariantCode x⟩

@[simp] theorem shiftInvariantFormula_val (x : V) :
    (shiftInvariantFormula x).val = shiftInvariantCode x := rfl

/-- Typed view of the substitution-invariance field. -/
noncomputable def substitutionInvariantFormula (x : V) :
    Bootstrapping.Formula V ℒₛₑₜ :=
  ⟨substitutionInvariantCode x, by
    simpa using isFormula_substitutionInvariantCode x⟩

@[simp] theorem substitutionInvariantFormula_val (x : V) :
    (substitutionInvariantFormula x).val = substitutionInvariantCode x := rfl

/-- Typed view of the axiom-soundness field. -/
noncomputable def axiomSoundFormula (x : V) : Bootstrapping.Formula V ℒₛₑₜ :=
  ⟨axiomSoundCode x, by simpa using isFormula_axiomSoundCode x⟩

@[simp] theorem axiomSoundFormula_val (x : V) :
    (axiomSoundFormula x).val = axiomSoundCode x := rfl

/-! ## The assembled family -/

/-- **The concrete `𝗭𝗙𝗖` truth-certificate family**: the five internalized
level-`x+1` truth laws of `ZFCinPA.CertificateFields`.  The forced sixth
coordinate — the internalized `Conₓ(ZFC)` — is inserted by
`ZFCTruthCertificateFamily.fields` itself. -/
noncomputable def concreteZFCTruthCertificateFamily :
    ZFCTruthCertificateFamily (V := V) where
  localStep := localStepFormula
  crossLevel := crossLevelFormula
  shiftInvariant := shiftInvariantFormula
  substitutionInvariant := substitutionInvariantFormula
  axiomSound := axiomSoundFormula

@[simp] theorem concreteZFCTruthCertificateFamily_localStep (x : V) :
    (concreteZFCTruthCertificateFamily (V := V)).localStep x =
      localStepFormula x := rfl

@[simp] theorem concreteZFCTruthCertificateFamily_crossLevel (x : V) :
    (concreteZFCTruthCertificateFamily (V := V)).crossLevel x =
      crossLevelFormula x := rfl

@[simp] theorem concreteZFCTruthCertificateFamily_shiftInvariant (x : V) :
    (concreteZFCTruthCertificateFamily (V := V)).shiftInvariant x =
      shiftInvariantFormula x := rfl

@[simp] theorem concreteZFCTruthCertificateFamily_substitutionInvariant
    (x : V) :
    (concreteZFCTruthCertificateFamily (V := V)).substitutionInvariant x =
      substitutionInvariantFormula x := rfl

@[simp] theorem concreteZFCTruthCertificateFamily_axiomSound (x : V) :
    (concreteZFCTruthCertificateFamily (V := V)).axiomSound x =
      axiomSoundFormula x := rfl

/-! ## The five `𝚺₁` field-code graphs, in the endpoint's shape

The typed wrappers' `.val` projections are the raw builders
definitionally, so each graph is the `via` instance of
`ZFCinPA.CertificateFields`, re-packaged. -/

/-- `𝚺₁` graph of the local-step field codes. -/
theorem concreteFamily_localStep_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun x : V ↦
        ((concreteZFCTruthCertificateFamily (V := V)).localStep x).val) := by
  change HierarchySymbol.sigmaOne.DefinableFunction₁ (localStepCode : V → V)
  exact localStepCode.defined.to_definable

/-- `𝚺₁` graph of the cross-level field codes. -/
theorem concreteFamily_crossLevel_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun x : V ↦
        ((concreteZFCTruthCertificateFamily (V := V)).crossLevel x).val) := by
  change HierarchySymbol.sigmaOne.DefinableFunction₁ (crossLevelCode : V → V)
  exact crossLevelCode.defined.to_definable

/-- `𝚺₁` graph of the shift-invariance field codes. -/
theorem concreteFamily_shiftInvariant_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun x : V ↦
        ((concreteZFCTruthCertificateFamily (V := V)).shiftInvariant
          x).val) := by
  change HierarchySymbol.sigmaOne.DefinableFunction₁
    (shiftInvariantCode : V → V)
  exact shiftInvariantCode.defined.to_definable

/-- `𝚺₁` graph of the substitution-invariance field codes. -/
theorem concreteFamily_substitutionInvariant_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun x : V ↦
        ((concreteZFCTruthCertificateFamily (V := V)).substitutionInvariant
          x).val) := by
  change HierarchySymbol.sigmaOne.DefinableFunction₁
    (substitutionInvariantCode : V → V)
  exact substitutionInvariantCode.defined.to_definable

/-- `𝚺₁` graph of the axiom-soundness field codes. -/
theorem concreteFamily_axiomSound_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun x : V ↦
        ((concreteZFCTruthCertificateFamily (V := V)).axiomSound x).val) := by
  change HierarchySymbol.sigmaOne.DefinableFunction₁ (axiomSoundCode : V → V)
  exact axiomSoundCode.defined.to_definable

/-- The assembled six-field master code — including the forced
internalized-consistency coordinate — has one `𝚺₁` graph. -/
theorem concreteFamily_code_definable :
    HierarchySymbol.sigmaOne.DefinableFunction₁
      (concreteZFCTruthCertificateFamily (V := V)).code :=
  (concreteZFCTruthCertificateFamily (V := V)).code_definable_of_fields
    concreteFamily_localStep_definable
    concreteFamily_crossLevel_definable
    concreteFamily_shiftInvariant_definable
    concreteFamily_substitutionInvariant_definable
    concreteFamily_axiomSound_definable

end ZFCinPA
end LeanProofs
