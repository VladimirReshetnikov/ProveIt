import DiophantineConsistency.CurrentHaltPacking2011
import DiophantineConsistency.NativePositiveSourceConstruction
import DiophantineConsistency.CurrentSoundness2011

/-! The actual rank-forced packing supplies every scalar premise of the
positive Pell/source construction. This closes the external Lean equivalence
for the maintained polynomial and its three accepted thirteen-variable forms.
An encoded object-language ZFC derivation is a separate formalization. -/

namespace DiophantineConsistency.CurrentPositiveZero2011

open CurrentMasks2011 CurrentWordScalarWitness2011 CurrentWordConstruction2011
  CurrentWordCopies2011 CurrentPackingRank2011 CurrentCarrierArithmetic2011
  CurrentPolynomialWindow2011

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local irreducible] CurrentKernel2011.K

/-- All scalar fields come from the same normalized source and printed rank.
The forced product is derived from the actual temporal exponent. -/
def packingData {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (s : ℕ) (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s carry digits) (R : ℕ)
    (hle : width*N ≤ R)
    (hR : (R : ℤ) = rank N (source a dummy (shiftedStartMarker a (s : ZMod N)))
      (normalized digits)) (hw : multiplier s = 2^(R-width*N)) :
    NativePositiveSourceConstruction.Data (ports (CurrentKernel2011.K : ℤ)) (width*N) R where
  J := NativeMaskPopulation.repunit width N
  F := normalized digits
  alpha := alpha (q N) (source a dummy (shiftedStartMarker a (s : ZMod N))) (normalized digits)
  z := quotientWitness (q N) ((CurrentKernel2011.K+multiplier s)*
    source a dummy (shiftedStartMarker a (s : ZMod N)))
  w := multiplier s
  C := source a dummy (shiftedStartMarker a (s : ZMod N))
  J_pos := hf.repunit_positive
  F_pos := hf.scalars.normalized_pos
  alpha_pos := hf.scalars.alpha_pos
  z_pos := hf.scalars.quotient_pos
  w_pos := hf.scalars.multiplier_pos
  C_pos := hf.scalars.source_pos
  q_balance := by
    change (beta : ℤ)*NativeMaskPopulation.repunit width N+1 = ((2^(width*N) : ℕ) : ℤ)
    have h := congrArg (fun n : ℕ => (n : ℤ)) hf.repunit_equation
    push_cast at h
    simpa only [q_binary] using h
  balance := by simpa only [q_binary] using hf.scalars.balance
  forced_product := NativePositiveSourceConstruction.forced_product_of_exponent hle hw
  transport := by
    change ((CurrentKernel2011.K : ℤ)+multiplier s)*
      source a dummy (shiftedStartMarker a (s : ZMod N))+
      (((2^(width*N) : ℕ) : ℤ)-normalized digits)-
      (quotientWitness (q N) ((CurrentKernel2011.K+multiplier s)*
        source a dummy (shiftedStartMarker a (s : ZMod N))) : ℤ)*
          (((2^(width*N) : ℕ) : ℤ)-1)=1
    simpa only [q_binary] using hf.scalars.transport_unit
  rank := by
    change NativeRankVariation.windowRank ((2^(width*N) : ℕ) : ℤ)
      (source a dummy (shiftedStartMarker a (s : ZMod N))) (normalized digits)
      lowPort (highPort+beta : ℕ) (NativeMaskPopulation.repunit width N) = R
    rw [← q_binary]
    exact hR.symm

/-- A rank-forced packing supplies positive coordinates of the literal polynomial. -/
theorem packing_positive_zero (hpacking : CurrentHaltPacking2011.ExistsPacking 0) :
    PositiveZero polynomial := by
  obtain ⟨k,_,_,_,_,_,a,_,_,S,carry,digits,R,_,t,_,_,_,_,hf,hR,hpop,hmod,_,hbound,hw⟩ :=
    hpacking
  let d := packingData a (CurrentFiniteDummyMutation2011.enabled S) t carry digits hf R
    (by omega) hR hw
  have hu : 0 < width*CurrentControllerData2011.auxiliary^(k+1) :=
    Nat.mul_pos (by decide) (pow_pos (NeZero.pos CurrentControllerData2011.auxiliary) _)
  have hb : 0 < (ports (CurrentKernel2011.K : ℤ)) 0 := by
    change (0 : ℤ) < beta
    exact_mod_cast beta_pos
  obtain ⟨v,hv,hzero,_⟩ := NativePositiveSourceConstruction.population_positive_polynomial_zero
    hb d hu hpop hmod
  exact ⟨v,hv,hzero⟩

/-- An actual inconsistency constructs positive coordinates of the literal
polynomial. No masks, tiling, calibrated rank or Pell seed is supplied. -/
theorem not_conZFC_positive_zero (hnot : ¬ DiophantineConsistency.ConZFC) :
    PositiveZero polynomial :=
  packing_positive_zero (CurrentHaltPacking2011.not_conZFC_constructs_packing 0 hnot)

/-- External equivalence for the actual fixed fourteen-variable polynomial. -/
theorem positive_zero_iff_not_conZFC :
    PositiveZero polynomial ↔ ¬ DiophantineConsistency.ConZFC := by
  constructor
  · intro hz hc
    exact CurrentSoundness2011.conZFC_no_positive_zero hc hz
  · exact not_conZFC_positive_zero

theorem no_positive_zero_iff_conZFC :
    (¬ PositiveZero polynomial) ↔ DiophantineConsistency.ConZFC := by
  classical
  constructor
  · intro hn
    by_contra hc
    exact hn (not_conZFC_positive_zero hc)
  · exact CurrentSoundness2011.conZFC_no_positive_zero

/-- Every accepted thirteen-variable frontier inherits the actual equivalence
through the already proved fixed-port positive arithmetic bijections. -/
theorem no_thirteen_positive_zero_iff_conZFC :
    ((¬ PositiveZero (polynomial69 (CurrentKernel2011.K : ℤ))) ↔ DiophantineConsistency.ConZFC) ∧
    ((¬ PositiveZero (polynomial70 (CurrentKernel2011.K : ℤ))) ↔ DiophantineConsistency.ConZFC) ∧
    ((¬ PositiveZero (polynomial71 (CurrentKernel2011.K : ℤ))) ↔ DiophantineConsistency.ConZFC) := by
  have hK : (0 : ℤ) < CurrentKernel2011.K := by exact_mod_cast CurrentKernel2011.K_pos
  have h65 : (¬ PositiveZero (polynomial65 (CurrentKernel2011.K : ℤ))) ↔
      DiophantineConsistency.ConZFC := no_positive_zero_iff_conZFC
  have h69 := (not_congr (positive_zero_65_iff_69 _ hK)).symm.trans h65
  have h70 := (not_congr (positive_zero_69_iff_70 (CurrentKernel2011.K : ℤ))).symm.trans h69
  exact ⟨h69,h70,(not_congr (positive_zero_70_iff_71 (CurrentKernel2011.K : ℤ))).symm.trans h70⟩

/-- One positive thirteen-coordinate assignment solves all three accepted
frontiers whenever the actual axiom predicate is inconsistent. -/
theorem not_conZFC_simultaneous_thirteen_zero (hnot : ¬ DiophantineConsistency.ConZFC) :
    ∃ u : Fin 13 → ℤ, (∀ j,0<u j) ∧
      MvPolynomial.eval u (polynomial69 (CurrentKernel2011.K : ℤ))=0 ∧
      MvPolynomial.eval u (polynomial70 (CurrentKernel2011.K : ℤ))=0 ∧
      MvPolynomial.eval u (polynomial71 (CurrentKernel2011.K : ℤ))=0 := by
  obtain ⟨v,hv,hzero⟩ := not_conZFC_positive_zero hnot
  have hK : (0 : ℤ) < CurrentKernel2011.K := by exact_mod_cast CurrentKernel2011.K_pos
  obtain ⟨u,hu,_,h69,h70,h71⟩ := completes _ hK v hv hzero
  exact ⟨u,hu,h69,h70,h71⟩

end DiophantineConsistency.CurrentPositiveZero2011
