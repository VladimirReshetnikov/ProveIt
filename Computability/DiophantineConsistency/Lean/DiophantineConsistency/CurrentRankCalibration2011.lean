import DiophantineConsistency.CurrentSafeController2011
import DiophantineConsistency.CurrentFiniteDummyMutation2011
import DiophantineConsistency.CurrentPackingParity2011
import DiophantineConsistency.CurrentRankStride2011

/-! Select and mutate actual Boolean dummy cells so the same complete native
packing has the required rank congruence. No desired ordinary increment,
selected support, or calibrated rank is supplied. Pell witnesses remain separate. -/

namespace DiophantineConsistency.CurrentRankCalibration2011

open CurrentMasks2011 CurrentControllerData2011 CurrentWordClause2011
  CurrentWordConstruction2011 CurrentWordCopies2011 CurrentWordScalarWitness2011
  CurrentFiniteDummyMutation2011 CurrentPackingRank2011 WangTiles942Periodic
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K CurrentControllerData2011.B
  CurrentControllerUnits2011.Gamma

theorem multiplier_power (s : ℕ) : multiplier s = B^s := by
  rw [multiplier,CurrentDummySafety2011.displacement_power,B,← pow_mul]

theorem window_q (n : ℕ) : q (auxiliary^n) = CurrentControllerUnits2011.q n := by
  unfold q CurrentControllerUnits2011.q CurrentControllerUnits2011.dimension
  rw [B,← pow_mul,Nat.mul_comm (auxiliary^n) 2011]

theorem gamma_binding (rw n : ℕ) :
    (CurrentControllerUnits2011.Gamma rw n : ℤ) =
      NativeRankVariation.rankGamma (q (auxiliary^n) : ℤ)
        (CurrentKernel2011.K+multiplier (auxiliary^rw) : ℕ) (radix^977 : ℕ) := by
  have h := CurrentControllerUnits2011.Gamma_cast_rankGamma rw n
  rw [← window_q] at h
  simpa only [CurrentControllerUnits2011.A,CurrentControllerUnits2011.dimension,
    multiplier_power,Nat.cast_pow] using h

theorem powerSum_cast_B {N : ℕ} (R : Type*) [Semiring R] (S : Finset (ZMod N)) :
    (powerSum S : R) = ∑ j ∈ S, (B : R)^j.val := by
  simpa only [B,Nat.cast_pow] using powerSum_cast R S

/-- Every actual marked word at admissible power dimensions has a constructed
Boolean control map, normalization, both masks and the actual rank congruence. -/
theorem exists_calibrated_packing (k rw : ℕ) (hrw : rw<k)
    (hlarge : d*auxiliary < auxiliary^k)
    (a : ZMod (auxiliary^(k+1)) → Fin 942)
    (ha : MarkedWord (auxiliary^(k+1)) ((auxiliary^rw : ℕ) : ℤ) a) :
    ∃ S : Finset (ZMod (auxiliary^(k+1))),
    ∃ carry digits : ZMod (auxiliary^(k+1)*2011) → ℕ,
      0<S.card ∧ S.card≤d*auxiliary ∧
      CurrentNativePacking2011.Facts a (enabled S) (auxiliary^rw) carry digits ∧
      ((rank (auxiliary^(k+1))
          (source a (enabled S) (shiftedStartMarker a ((auxiliary^rw : ℕ) : ZMod _)))
          (normalized digits) : ℤ) : ZMod (d*auxiliary^(k+1))) =
        ((d*auxiliary^rw : ℕ) : ZMod (d*auxiliary^(k+1))) := by
  obtain ⟨carry0,digits0,hf0⟩ := CurrentNativePacking2011.marked_constructs_packing
    a (fun _ => 0) (fun _ => by decide) (auxiliary^rw) ha
  let C0 := source a (fun _ => 0) (shiftedStartMarker a ((auxiliary^rw : ℕ) : ZMod _))
  let R0 : ℤ := rank (auxiliary^(k+1)) C0 (normalized digits0)
  obtain ⟨S,hpos,hcard,hsafe,hsum⟩ := CurrentSafeController2011.exists_safe_gamma_sum
    k rw hrw hlarge ((R0 : ZMod (d*auxiliary^(k+1)))-(d*auxiliary^rw : ℕ))
  have hs : ∀ j ∈ S, j.val+1 < auxiliary^(k+1) ∧ j.val+auxiliary^rw < auxiliary^(k+1) :=
    fun j hj => (hsafe j hj).2
  obtain ⟨carry,digits,hf,_,_⟩ := exists_finite_normalized_increment a _
    (shiftedStartMarker_boolean a _) (auxiliary^rw) S hs carry0 digits0 hf0.normalization
  have hpack := CurrentWordRephase2011.marked_packing_rephase a (enabled S)
    (enabled_boolean S) (auxiliary^rw) (auxiliary^rw) rfl ha carry digits hf
  refine ⟨S,carry,digits,hpos,hcard,hpack,?_⟩
  have hdec := finite_rank_decrement a _ (shiftedStartMarker_boolean a _)
    (auxiliary^rw) S hs carry0 digits0 carry digits hf0.normalization hf
    (lowPort : ℤ) (highPort+beta : ℕ) (NativeMaskPopulation.repunit width (auxiliary^(k+1)))
  change rank (auxiliary^(k+1))
      (source a (enabled S) (shiftedStartMarker a ((auxiliary^rw : ℕ) : ZMod _)))
      (normalized digits) = R0-
        NativeRankVariation.rankGamma (q (auxiliary^(k+1)) : ℤ)
          (CurrentKernel2011.K+multiplier (auxiliary^rw) : ℕ) (radix^977 : ℕ)*
            (powerSum S : ℤ) at hdec
  rw [← gamma_binding rw (k+1)] at hdec
  have hz := congrArg (fun z : ℤ => (z : ZMod (d*auxiliary^(k+1)))) hdec
  push_cast at hz
  have hsum' : (CurrentControllerUnits2011.Gamma rw (k+1) : ZMod (d*auxiliary^(k+1)))*
      (powerSum S : ZMod (d*auxiliary^(k+1))) =
        (R0 : ZMod (d*auxiliary^(k+1)))-(d*auxiliary^rw : ℕ) := by
    rw [powerSum_cast_B]
    exact hsum
  rw [hsum'] at hz
  simpa only [sub_sub_cancel,Nat.cast_pow] using hz

/-- The printed rank of this very packing now forces its temporal multiplier.
The source, normalized digits and carries survive the whole-period rephasing. -/
theorem exists_rank_forced_packing (k rw : ℕ) (hrw : rw<k)
    (hlarge : d*auxiliary < auxiliary^k)
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
      multiplier t = 2^(R-width*auxiliary^(k+1)) := by
  obtain ⟨S,carry,digits,hpos,hcard,hf,hcal⟩ :=
    exists_calibrated_packing k rw hrw hlarge a ha
  obtain ⟨R,r,hR,hpop,hmod4,hodd,hbound⟩ :=
    CurrentPackingParity2011.packing_rank a (enabled S) (auxiliary^rw) carry digits hf
  rw [← hR] at hcal
  have hmod : R ≡ d*auxiliary^rw [MOD d*auxiliary^(k+1)] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Int.cast_natCast] using hcal
  let t := CurrentRankStride2011.derivedStride (auxiliary^(k+1)) R
  obtain ⟨htpos,hword,hft,_,hpower⟩ := CurrentRankStride2011.packing_at_derived_stride
    a (enabled S) (enabled_boolean S) (auxiliary^rw) R ha carry digits hf hbound hmod
  have hcast : (t : ZMod (auxiliary^(k+1))) = ((auxiliary^rw : ℕ) : ZMod _) :=
    (CurrentRankStride2011.derived_spec (NeZero.pos (auxiliary^(k+1))) hbound hmod).2.2
  have hmarked := CurrentWordRephase2011.markedWord_rephase a (auxiliary^rw) t hcast.symm ha
  have hCeq : source a (enabled S) (shiftedStartMarker a (t : ZMod _)) =
      source a (enabled S) (shiftedStartMarker a ((auxiliary^rw : ℕ) : ZMod _)) := by
    exact congrArg (NativeCyclicConvolution.word radix) hword
  refine ⟨S,carry,digits,R,r,t,hpos,hcard,htpos,hmarked,hft,?_,
    hpop,hmod4,hodd,hbound,hpower⟩
  rw [hCeq]
  exact hR

end DiophantineConsistency.CurrentRankCalibration2011
