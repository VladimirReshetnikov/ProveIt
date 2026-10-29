import DiophantineConsistency.CurrentPositiveZero2011

/-!
# Direct refutations and positive zeros of the current equation

The reverse construction starts with an actual refutation, not with the
double negation `¬ConZFC`. The final negation equivalence therefore uses
only implication introduction and elimination. Imported machine calibration
still includes the semantic K lower chain and constructible Choice transfer;
this module does not assert internal PA or HA provability.
-/

namespace DiophantineConsistency.CurrentWitnessEquivalence2011

open SetTheory SetTheory.BusyBeaver.ZFC LeanProofs.BoundedZFCConsistency
open CurrentMasks2011 CurrentCarrierArithmetic2011 CurrentPolynomialWindow2011

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K

/-- An explicit halt supplies the same actual rank-forced packing and Pell
construction as the accepted external equivalence, without an outer DNE. -/
theorem blank_halts_positive_zero
    (hh : KDenseBridge.BlankHalts DecimalMachine215.machine) :
    PositiveZero polynomial :=
  CurrentPositiveZero2011.packing_positive_zero
    (CurrentHaltPacking2011.blank_halts_constructs_packing 0 hh)

/-- Direct use of the actual syntactic refutation predicate. No inconsistency
double negation, native calibration, or desired solution is a premise. -/
theorem zfc_refutation_positive_zero (href : BProv ZFCax_s [] Form.fBot) :
    PositiveZero polynomial :=
  blank_halts_positive_zero (DecimalMachineZFC.blank_halts_iff_zfc_refutation.mpr href)

theorem positive_zero_zfc_refutation (hzero : PositiveZero polynomial) :
    BProv ZFCax_s [] Form.fBot := by
  obtain ⟨v,hv,hz⟩ := hzero
  exact CurrentSoundness2011.polynomial_zero_zfc_refutation v hv hz

/-- External witness-level equivalence with the literal ZFC axiom predicate. -/
theorem positive_zero_iff_zfc_refutation :
    PositiveZero polynomial ↔ BProv ZFCax_s [] Form.fBot :=
  ⟨positive_zero_zfc_refutation,zfc_refutation_positive_zero⟩

/-- Negating the direct witness maps needs no double-negation elimination.
This concerns the outer logical composition, not all imported proofs. -/
theorem no_positive_zero_iff_conZFC :
    (¬ PositiveZero polynomial) ↔ DiophantineConsistency.ConZFC := by
  change (¬ PositiveZero polynomial) ↔ ¬ BProv ZFCax_s [] Form.fBot
  exact ⟨fun hn href => hn (zfc_refutation_positive_zero href),
    fun hc hz => hc (positive_zero_zfc_refutation hz)⟩

end DiophantineConsistency.CurrentWitnessEquivalence2011
