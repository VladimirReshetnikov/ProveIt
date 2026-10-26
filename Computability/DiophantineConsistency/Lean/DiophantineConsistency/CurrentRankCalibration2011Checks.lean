import DiophantineConsistency.CurrentRankCalibration2011

namespace DiophantineConsistency.CurrentRankCalibration2011Checks

open CurrentRankCalibration2011 CurrentMasks2011 CurrentControllerData2011
  CurrentWordScalarWitness2011 CurrentWordCopies2011 CurrentWordConstruction2011
  CurrentFiniteDummyMutation2011 CurrentPackingRank2011 WangTiles942Periodic
set_option Elab.async false

example (s : ℕ) : multiplier s = B^s := multiplier_power s
example (n : ℕ) : q (auxiliary^n) = CurrentControllerUnits2011.q n := window_q n

-- Independent power dimensions retain the exact signed coefficient.
example (rw n : ℕ) :
    (CurrentControllerUnits2011.Gamma rw n : ℤ) =
      NativeRankVariation.rankGamma (q (auxiliary^n) : ℤ)
        (CurrentKernel2011.K+multiplier (auxiliary^rw) : ℕ) (radix^977 : ℕ) :=
  gamma_binding rw n

-- Casting does not change the support or its canonical exponent indices.
example {N : ℕ} (S : Finset (ZMod N)) (m : ℕ) :
    (powerSum S : ZMod m) = ∑ j ∈ S, (B : ZMod m)^j.val :=
  powerSum_cast_B (ZMod m) S

-- The endpoint has only actual matching and quantitative dimension hypotheses.
-- No chosen controls, normalization, masks, rank congruence, or rank witness
-- is supplied. The printed rank and forced multiplier refer to the SAME F/C.
example (k rw : ℕ) (hrw : rw<k) (hlarge : d*auxiliary < auxiliary^k)
    (a : ZMod (auxiliary^(k+1)) → Fin 942)
    (ha : MarkedWord (auxiliary^(k+1)) ((auxiliary^rw : ℕ) : ℤ) a) :
    ∃ S : Finset (ZMod (auxiliary^(k+1))),
    ∃ carry digits : ZMod (auxiliary^(k+1)*2011) → ℕ,
    ∃ R r t : ℕ,
      0<S.card ∧ S.card≤d*auxiliary ∧ 0<t ∧
      MarkedWord (auxiliary^(k+1)) (t : ℤ) a ∧
      CurrentNativePacking2011.Facts a (enabled S) t carry digits ∧
      (R : ℤ) = rank (auxiliary^(k+1))
        (source a (enabled S) (shiftedStartMarker a (t : ZMod _))) (normalized digits) ∧
      Jones1982.σ 2 R = 3*(width*auxiliary^(k+1))+2 ∧
      R%4=3 ∧ R=2*r+1 ∧ 2*(width*auxiliary^(k+1))<R ∧
      multiplier t = 2^(R-width*auxiliary^(k+1)) :=
  exists_rank_forced_packing k rw hrw hlarge a ha

#print axioms multiplier_power
#print axioms window_q
#print axioms gamma_binding
#print axioms powerSum_cast_B
#print axioms exists_calibrated_packing
#print axioms exists_rank_forced_packing

end DiophantineConsistency.CurrentRankCalibration2011Checks
