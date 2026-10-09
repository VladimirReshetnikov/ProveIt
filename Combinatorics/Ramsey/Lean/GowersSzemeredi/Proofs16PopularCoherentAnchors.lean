import GowersSzemeredi.Proofs16PopularHigherArrangements

/-! The exact even core yields coherent anchors with popular supported
shifts. Reserving a quarter of the arrangement mass for popularity and
a quarter for selection retains the previous anchor-density conclusion. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem popular_coherent_anchor_system_of_even_core {N g d : Nat} [NeZero N] [Fact N.Prime]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r rho beta : Real}
    (hr : 0 < r) (hr4 : r < 4) (hrrho : r ≤ rho) (hb : 0 < beta)
    (hP : beta*(N : Real) ≤ P.card) (hG : Gamma.card ≤ g)
    (hT : ∀ x ∈ P, (T x).card ≤ d)
    (hL : ∀ x ∈ P, IsFreimanLinearOn (bohr (T x) rho) (L x)) (hzero : ∀ x ∈ P, L x 0 = 0)
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (hN : 16 ≤ beta^16*(N : Real)) :
    HasCoherentAnchorSystemOn (popularSupportedHigherArrangements P (beta^8/4))
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L)
      (beta^16/20) (beta^16/4) (g+d) r := by
  have hcompat : ((incompatibleAnchorQuadruples (supportedAnchorQuadruples P)
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r).card : Real) ≤ 0*(N : Real)^3 := by
    rw [even_core_incompatible_anchor_quadruples_empty P Gamma T L hrel]
    simp
  have htuples : ((columnTupleFailures (supportedColumnTuples P)
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r).card : Real) ≤ 0*(N : Real)^7 := by
    rw [even_core_column_tuple_failures_empty P Gamma T L hr.le hrel]
    simp
  have he : (beta^16-4*(beta^8/4)^2-4*0-2*0-5*(beta^16/20))/2 = beta^16/4 := by ring
  have hsize : 8 ≤ (beta^16-4*(beta^8/4)^2-4*0-2*0-5*(beta^16/20))*(N : Real) := by
    have he' : beta^16-4*(beta^8/4)^2-4*0-2*0-5*(beta^16/20) = beta^16/2 := by ring
    rw [he']
    linarith only [hN]
  have h := exists_joint_coherent_anchor_maps (popularSupportedHigherArrangements P (beta^8/4))
    (supportedAnchorQuadruples P) (supportedColumnTuples P)
    (coreColumnSpectrum P Gamma T) (coreColumnMap P L)
    hr hr4 (show 0 < beta^16/20 by positivity) (coreColumnSpectrum_card_le P Gamma T hG hT)
    (coreColumnMap_freiman P Gamma T L hrrho hL) (coreColumnMap_zero P L hzero)
    (fun q hq => (Finset.mem_filter.mp hq).2)
    (fun p hp j => supported_higher_anchor_quadruple_mem P (Finset.mem_filter.mp hp).1 j)
    (fun p hp => supported_higher_column_tuples_mem P (Finset.mem_filter.mp hp).1)
    (popular_supported_higher_arrangements_dense P hb.le hP) hcompat htuples hsize
  simpa only [HasCoherentAnchorSystemOn,he] using h

end LeanProofs.GowersSzemeredi
