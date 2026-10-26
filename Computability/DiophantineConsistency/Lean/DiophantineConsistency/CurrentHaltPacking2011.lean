import DiophantineConsistency.CurrentRankCalibration2011
import DiophantineConsistency.WangTiles942ControllerDimensions
import DiophantineConsistency.DecimalMachineZFC

/-!
# A literal machine halt constructs a rank-forced native packing

All word, controller, normalization, mask and rank data are constructed
from the actual halt. The same word retains unique Start through controller
selection and rephasing. This is a native packing endpoint, not a source
system zero, polynomial solution, or internal ZFC theorem.
-/

namespace DiophantineConsistency.CurrentHaltPacking2011

open CurrentMasks2011 CurrentControllerData2011 WangTiles942Periodic
  CurrentWordScalarWitness2011 CurrentWordCopies2011 CurrentWordConstruction2011
  CurrentFiniteDummyMutation2011 CurrentPackingRank2011

set_option Elab.async false
set_option maxRecDepth 10000

/-- A transparent existential over the same actual word, finite support,
carry normalization and printed rank. Both original and forced strides
are retained; no calibrated object is an input to the construction. -/
def ExistsPacking (wBound : ℕ) : Prop :=
  ∃ k rw : ℕ, 0 < rw ∧ rw < k ∧ d*auxiliary < auxiliary^k ∧
    wBound < auxiliary^rw ∧
    letI : NeZero (auxiliary^(k+1)) := ⟨pow_ne_zero _ (NeZero.ne auxiliary)⟩
    ∃ a : ZMod (auxiliary^(k+1)) → Fin 942,
      (∀ z, a z = 0 ↔ z = 0) ∧
      MarkedWord (auxiliary^(k+1)) ((auxiliary^rw : ℕ) : ℤ) a ∧
      ∃ S : Finset (ZMod (auxiliary^(k+1))),
      ∃ carry digits : ZMod (auxiliary^(k+1)*2011) → ℕ,
      ∃ R r t : ℕ,
        0 < S.card ∧ S.card ≤ d*auxiliary ∧ 0 < t ∧
        MarkedWord (auxiliary^(k+1)) (t : ℤ) a ∧
        CurrentNativePacking2011.Facts a (enabled S) t carry digits ∧
        (R : ℤ) = rank (auxiliary^(k+1))
          (source a (enabled S) (shiftedStartMarker a (t : ZMod _)))
          (normalized digits) ∧
        Jones1982.σ 2 R = 3*(width*auxiliary^(k+1))+2 ∧
        R%4 = 3 ∧ R = 2*r+1 ∧ 2*(width*auxiliary^(k+1)) < R ∧
        multiplier t = 2^(R-width*auxiliary^(k+1))

/-- Independent cofinal power geometry supplies all premises of the actual
rank calibration. Its word and unique marker survive unchanged. -/
theorem halt_constructs_packing (T wBound : ℕ)
    (hh : (DecimalMachine215.machine.run T).state = none) :
    ExistsPacking wBound := by
  obtain ⟨k,rw,hrw,hrwk,hlarge,hwb,a,ha,hu⟩ :=
    WangTiles942ControllerDimensions.exists_controller_marked_word T wBound hh
  refine ⟨k,rw,hrw,hrwk,hlarge,hwb,a,hu,ha,?_⟩
  exact CurrentRankCalibration2011.exists_rank_forced_packing k rw hrwk hlarge a ha

theorem blank_halts_constructs_packing (wBound : ℕ)
    (hh : SetTheory.BusyBeaver.ZFC.KDenseBridge.BlankHalts DecimalMachine215.machine) :
    ExistsPacking wBound := by
  obtain ⟨T,hT⟩ := hh
  exact halt_constructs_packing T wBound hT

/-- External Lean consequence of inconsistency for the repository's actual
ZFC axiom predicate. This does not assert inconsistency or a polynomial zero. -/
theorem not_conZFC_constructs_packing (wBound : ℕ)
    (hnot : ¬ DiophantineConsistency.ConZFC) : ExistsPacking wBound := by
  classical
  have hh : SetTheory.BusyBeaver.ZFC.KDenseBridge.BlankHalts
      DecimalMachine215.machine := by
    by_contra hn
    exact hnot (DecimalMachineZFC.blank_nonhalting_iff_conZFC.mp hn)
  exact blank_halts_constructs_packing wBound hh

end DiophantineConsistency.CurrentHaltPacking2011
