import GowersSzemeredi.Proofs16VarietyCeilingFreeDecomposition
import GowersSzemeredi.Proofs05ExplicitSchmidtRecurrence

/-! The variety-route decomposition with named constants.

`exists_ceiling_free_variety_relation_decomposition` packages six constants
`C, p, Cv, pv, Cs, ps` existentially. A comparison with the printed Theorem
16.2 budget needs upper bounds on them (research notes, J.5b). Every layer of
the chain is now also stated at fixed constants (`…At` predicates with `…At_of`
theorems), so the constants can be followed from the two partition inputs:
* the lift side (`C, p`) starts from the multilinear partition in dimension
  three, `multilinearPartitionBoundAt_explicit 3`. The factor-two
  common-difference form multiplies the exponent constant by `k + 1 = 3`, and
  the root-width profile rounds the base constant up;
* the variety side (`Cv, pv` and `Cs, ps`) starts from the diameter partition
  in dimension two, `multilinearDiameterPartition_explicit`, with the base
  constant rounded up.

`ceilingFreeVarietyRelationDecompositionAt_explicit` is the decomposition at
these constants. The module imports the OAI port, so it is checked on the
full-verification host. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The lift base constant. -/
def explicitLiftK : Nat := Nat.ceil (multiaffinePartitionK (2 + 1) (2 ^ (2 + 1)))

/-- The lift exponent constant. -/
def explicitLiftP : Nat := (2 + 1) * multiaffinePartitionP (2 + 1) (2 ^ (2 + 1))

/-- The variety base constant. -/
def explicitVarietyK : Nat := Nat.ceil (multiaffinePartitionK 2 (2 ^ 2))

/-- The variety exponent constant. -/
def explicitVarietyP : Nat := multiaffinePartitionP 2 (2 ^ 2)

theorem two_le_ceil_multiaffinePartitionK (k h : Nat) :
    2 ≤ Nat.ceil (multiaffinePartitionK k h) := by
  exact_mod_cast (two_le_multiaffinePartitionK k h).trans (Nat.le_ceil _)

theorem two_le_explicitLiftK : 2 ≤ explicitLiftK := two_le_ceil_multiaffinePartitionK _ _

theorem explicitLiftP_pos : 0 < explicitLiftP :=
  Nat.mul_pos (by norm_num) (multiaffinePartitionP_pos _ _)

theorem two_le_explicitVarietyK : 2 ≤ explicitVarietyK := two_le_ceil_multiaffinePartitionK _ _

theorem explicitVarietyP_pos : 0 < explicitVarietyP := multiaffinePartitionP_pos _ _

/-- The all-scale multilinear cover in dimension two at the lift constants. -/
theorem allScalePolynomialMultilinearCoverAt_explicit :
    AllScalePolynomialMultilinearCoverAt 2 explicitLiftK explicitLiftP := by
  have hK := two_le_multiaffinePartitionK (2 + 1) (2 ^ (2 + 1))
  have hp := multiaffinePartitionP_pos (2 + 1) (2 ^ (2 + 1))
  have h0 := commonDiffPartitionBoundAt_of 2 hK hp
    (multilinearPartitionBoundAt_explicit (2 + 1) (by norm_num))
  have h1 := commonDiffPartitionTwoBoundAt_of 2 hK hp h0
  have hp1 : 0 < (2 + 1) * multiaffinePartitionP (2 + 1) (2 ^ (2 + 1)) := explicitLiftP_pos
  have h2 := polynomialSection16RecurrenceProfileAt_of 2 hK hp1 h1
  have hC := two_le_explicitLiftK
  have h3 := polynomialRetiledLinearityProfileAt_of 2 hC hp1 h2
  have h4 := polynomialSpectrumProductLinearityAt_of 2 hC hp1 h3
  have h5 := uniformPolynomialSpectrumProductLinearityAt_of 2 hC hp1 h4
  have h6 := polynomialLemma166At_of 2 hC hp1 h5
  have h7 := allScalePolynomialLemma166At_of 2 hC hp1 h6
  have h8 := allScalePolynomialLemma169At_of 2 hC hp1 h7
  exact allScalePolynomialMultilinearCoverAt_of 2 hC hp1 h8

/-- The variety piece-class cover at the variety constants. -/
theorem varietyPieceClassCoverAt_explicit :
    VarietyPieceClassCoverAt explicitVarietyK explicitVarietyP := by
  have hK := two_le_multiaffinePartitionK 2 (2 ^ 2)
  have hp := explicitVarietyP_pos
  have hC := two_le_explicitVarietyK
  have b1 := jointFreimanVarietyGoodPartitionAt_of hK hp multilinearDiameterPartition_explicit
  have b2 := jointFreimanVarietyCoverAt_of hC hp b1
  have b3 := uniformJointFreimanVarietyCoverAt_of hC hp b2
  have b4 := varietyPieceFamilyCoverAt_of hC hp b3
  have b5 := polynomialVarietyPieceFamilyCoverAt_of hC hp b4
  exact varietyPieceClassCoverAt_of hC hp b5

/-- **Relation pieces with named constants.** -/
theorem polynomialVarietyRelationPieceAt_explicit :
    PolynomialVarietyRelationPieceAt explicitLiftK explicitLiftP
      explicitVarietyK explicitVarietyP explicitVarietyK explicitVarietyP := by
  have hC := two_le_explicitLiftK
  have hp := explicitLiftP_pos
  have hCv := two_le_explicitVarietyK
  have hpv := explicitVarietyP_pos
  have hclass := varietyPieceClassCoverAt_explicit
  have t1 := polynomialVarietyFamilyPowerCoverAt_of hC hp hCv hpv
    allScalePolynomialMultilinearCoverAt_explicit
    (varietyFamilyGoodDomainSliceProviderAt_of hCv hpv hclass)
  have t2 := polynomialVarietyCommonBaseCoverAt_of hC hp hCv hpv t1
  have t3 := polynomialVarietyStructuredPieceAt_of hC hp hCv hpv hCv hpv t2
    (varietySpectrumRestrictionAt_of hCv hpv hclass)
  have t4 := polynomialVarietyProductGraphPieceAt_of hC hp hCv hpv hCv hpv t3
  exact polynomialVarietyRelationPieceAt_of hC hp hCv hpv hCv hpv t4

/-- **The ceiling-free decomposition with named constants.** -/
theorem ceilingFreeVarietyRelationDecompositionAt_explicit :
    CeilingFreeVarietyRelationDecompositionAt explicitLiftK explicitLiftP
      explicitVarietyK explicitVarietyP explicitVarietyK explicitVarietyP := by
  have hC := two_le_explicitLiftK
  have hp := explicitLiftP_pos
  have hCv := two_le_explicitVarietyK
  have hpv := explicitVarietyP_pos
  exact ceilingFreeVarietyRelationDecompositionAt_of hC hp hCv hpv hCv hpv
    (polynomialVarietyRelationDecompositionAt_of hC hp hCv hpv hCv hpv
      polynomialVarietyRelationPieceAt_explicit)

end LeanProofs.GowersSzemeredi
