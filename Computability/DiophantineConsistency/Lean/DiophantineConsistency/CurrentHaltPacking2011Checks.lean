import DiophantineConsistency.CurrentHaltPacking2011

namespace DiophantineConsistency.CurrentHaltPacking2011Checks

open CurrentHaltPacking2011 CurrentMasks2011 CurrentControllerData2011
  CurrentWordScalarWitness2011 CurrentWordCopies2011 CurrentWordConstruction2011
  CurrentFiniteDummyMutation2011 CurrentPackingRank2011 WangTiles942Periodic
set_option Elab.async false

example (T wBound : ℕ) (hh : (DecimalMachine215.machine.run T).state = none) :
    ExistsPacking wBound := halt_constructs_packing T wBound hh

-- Unpack the transparent endpoint: the original word retains unique Start,
-- and this same word supplies the forced-stride Facts and actual rank.
example {wBound : ℕ} (h : ExistsPacking wBound) :
    ∃ k : ℕ, ∃ a : ZMod (auxiliary^(k+1)) → Fin 942,
      (∀ z, a z = 0 ↔ z = 0) ∧
      ∃ S : Finset (ZMod (auxiliary^(k+1))),
      ∃ carry digits : ZMod (auxiliary^(k+1)*2011) → ℕ,
      ∃ R t : ℕ, 0 < t ∧
        CurrentNativePacking2011.Facts a (enabled S) t carry digits ∧
        (R : ℤ) = rank (auxiliary^(k+1))
          (source a (enabled S) (shiftedStartMarker a (t : ZMod _)))
          (normalized digits) ∧
        R%4 = 3 ∧ multiplier t = 2^(R-width*auxiliary^(k+1)) := by
  obtain ⟨k,_,_,_,_,_,a,hu,_,S,carry,digits,R,_,t,_,_,ht,_,hf,hR,_,hmod,_,_,hpow⟩ := h
  exact ⟨k,a,hu,S,carry,digits,R,t,ht,hf,hR,hmod,hpow⟩

-- The width lower bound remains arbitrary; a supplied marked word, support,
-- normalization or rank calibration is not a premise here.
example (hh : SetTheory.BusyBeaver.ZFC.KDenseBridge.BlankHalts DecimalMachine215.machine) :
    ∀ wBound : ℕ, ExistsPacking wBound :=
  fun wBound => blank_halts_constructs_packing wBound hh

-- This is the exact repository consistency predicate, not a placeholder.
example (hnot : ¬ DiophantineConsistency.ConZFC) :
    ∀ wBound : ℕ, ExistsPacking wBound :=
  fun wBound => not_conZFC_constructs_packing wBound hnot

#print axioms halt_constructs_packing
#print axioms blank_halts_constructs_packing
#print axioms not_conZFC_constructs_packing

end DiophantineConsistency.CurrentHaltPacking2011Checks
