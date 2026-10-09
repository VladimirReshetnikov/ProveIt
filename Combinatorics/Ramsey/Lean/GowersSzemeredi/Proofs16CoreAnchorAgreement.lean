import GowersSzemeredi.Proofs16PopularCoherentAnchors

/-! On a common quarter-radius Bohr set, the glued anchor map agrees
with every supported column difference having the same shift. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem supported_anchor_quadruple_of_bases {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) {a b c : ZMod N}
    (hb : b ∈ columnShiftBases P a) (hc : c ∈ columnShiftBases P a) :
    (![b+a,b,c+a,c] : Fin 4 → ZMod N) ∈ supportedAnchorQuadruples P := by
  obtain ⟨hb,hba⟩ := Finset.mem_filter.mp hb
  obtain ⟨hc,hca⟩ := Finset.mem_filter.mp hc
  apply Finset.mem_filter.mpr
  refine ⟨Fintype.mem_piFinset.mpr ?_,by simp⟩
  intro i
  fin_cases i
  · exact hba
  · exact hb
  · exact hca
  · exact hc

theorem even_core_shift_anchor_compatible {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N → ZMod N) {a : ZMod N} {r : Real}
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (hx : x a ∈ columnShiftBases P a) (hy : y a ∈ columnShiftBases P a) :
    ColumnPairCompatible (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r
      (shiftAnchorPair x a) (shiftAnchorPair y a) := by
  have h := even_core_anchor_compatible P Gamma T L hrel (supported_anchor_quadruple_of_bases P hx hy)
  simpa [shiftAnchorPair,Matrix.vecHead,Matrix.vecTail] using h

def coreAnchorAgreementSpectrum {N : Nat} (P Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (x : ZMod N → ZMod N) (a z : ZMod N) : Finset (ZMod N) :=
  columnDifferenceSpectrum (coreColumnSpectrum P Gamma T) (shiftAnchorPair x a) ∪
    columnDifferenceSpectrum (coreColumnSpectrum P Gamma T) (z+a,z)

theorem core_shift_anchor_agrees {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N → ZMod N) {a z : ZMod N} {r rho : Real}
    (hr : 0 ≤ r) (hrrho : r ≤ rho)
    (hL : ∀ v ∈ P, IsFreimanLinearOn (bohr (T v) rho) (L v)) (hzero : ∀ v ∈ P, L v 0 = 0)
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (hx : x a ∈ columnShiftBases P a) (hy : y a ∈ columnShiftBases P a)
    (hz : z ∈ columnShiftBases P a) :
    ∀ w ∈ bohr (coreAnchorAgreementSpectrum P Gamma T x a z) (r/4),
      shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y a w = L (z+a) w-L z w := by
  have hf := coreColumnMap_freiman P Gamma T L hrrho hL
  have hf0 := coreColumnMap_zero P L hzero
  have hxy := even_core_shift_anchor_compatible P Gamma T L x y hrel hx hy
  have hrestrict := bohrSumExtension_restrict
    (columnDifferenceSpectrum (coreColumnSpectrum P Gamma T) (shiftAnchorPair x a))
    (columnDifferenceSpectrum (coreColumnSpectrum P Gamma T) (shiftAnchorPair y a))
    (columnDifferenceMap (coreColumnMap P L) (shiftAnchorPair x a))
    (columnDifferenceMap (coreColumnMap P L) (shiftAnchorPair y a)) hr
    (columnDifferenceMap_freiman_of_local _ _ r hf _) (columnDifferenceMap_freiman_of_local _ _ r hf _)
    (columnDifferenceMap_zero_of_local _ hf0 _) (columnDifferenceMap_zero_of_local _ hf0 _) hxy
  have hxz := even_core_anchor_compatible P Gamma T L hrel (supported_anchor_quadruple_of_bases P hx hz)
  intro w hw
  have hw' : w ∈ bohr (columnDifferenceSpectrum (coreColumnSpectrum P Gamma T) (shiftAnchorPair x a)) (r/4) ∧
      w ∈ bohr (columnDifferenceSpectrum (coreColumnSpectrum P Gamma T) (z+a,z)) (r/4) := by
    simpa only [coreAnchorAgreementSpectrum,bohr_union,Finset.mem_inter] using hw
  have hr' : r/4 ≤ r := by linarith
  have he := hxz w (bohr_mono_radius _ hr' hw'.1) (bohr_mono_radius _ hr' hw'.2)
  have hza := Finset.mem_filter.mp hz
  calc _ = columnDifferenceMap (coreColumnMap P L) (shiftAnchorPair x a) w := hrestrict.2.1 w hw'.1
    _ = columnDifferenceMap (coreColumnMap P L) (z+a,z) w := he
    _ = _ := by simp only [columnDifferenceMap,coreColumnMap,if_pos hza.1,if_pos hza.2]

end LeanProofs.GowersSzemeredi
