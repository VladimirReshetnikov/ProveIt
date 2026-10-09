import GowersSzemeredi.Proofs16PopularAnchorRealization
import GowersSzemeredi.Proofs16ColumnBohrDomainDensity

/-! Dense agreement domains retain the selected Bohr domain. The common
core spectrum is counted once, giving rank k+g+4*d instead of k+4*(g+d). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem coreAnchorAgreementSpectrum_card_le {N g d : Nat}
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) (x : ZMod N → ZMod N)
    {a z : ZMod N} (hG : Gamma.card ≤ g) (hT : ∀ v ∈ P, (T v).card ≤ d)
    (hx : x a ∈ columnShiftBases P a) (hz : z ∈ columnShiftBases P a) :
    (coreAnchorAgreementSpectrum P Gamma T x a z).card ≤ g+4*d := by
  obtain ⟨hx,hxa⟩ := Finset.mem_filter.mp hx
  obtain ⟨hz,hza⟩ := Finset.mem_filter.mp hz
  have he : coreAnchorAgreementSpectrum P Gamma T x a z =
      Gamma ∪ (T (x a+a) ∪ T (x a) ∪ T (z+a) ∪ T z) := by
    simp only [coreAnchorAgreementSpectrum,columnDifferenceSpectrum,shiftAnchorPair,
      coreColumnSpectrum,if_pos hx,if_pos hxa,if_pos hz,if_pos hza]
    ext v
    simp only [Finset.mem_union]
    tauto
  rw [he]
  have h1 := Finset.card_union_le (T (x a+a)) (T (x a))
  have h2 := Finset.card_union_le (T (x a+a) ∪ T (x a)) (T (z+a))
  have h3 := Finset.card_union_le (T (x a+a) ∪ T (x a) ∪ T (z+a)) (T z)
  have h4 := Finset.card_union_le Gamma (T (x a+a) ∪ T (x a) ∪ T (z+a) ∪ T z)
  have ht0 := hT _ hxa
  have ht1 := hT _ hx
  have ht2 := hT _ hza
  have ht3 := hT _ hz
  omega

def coreAnchorAgreementDomain {N : Nat} [NeZero N]
    (P Gamma D : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (x : ZMod N → ZMod N) (a : ZMod N) (r sigma : Real) : Finset (ZMod N × ZMod N) :=
  columnBohrDomain (columnShiftBases P a) (fun z => D ∪ coreAnchorAgreementSpectrum P Gamma T x a z)
    (min sigma (r/4))

theorem coreAnchorAgreementDomain_density {N Q k g d : Nat} [NeZero N] [NeZero Q]
    (P Gamma D : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (x : ZMod N → ZMod N) {a : ZMod N} {r sigma t : Real}
    (hD : D.card ≤ k) (hG : Gamma.card ≤ g) (hT : ∀ v ∈ P, (T v).card ≤ d)
    (hx : x a ∈ columnShiftBases P a) (hpopular : t*N ≤ ((columnShiftBases P a).card : Real))
    (hQ : 1 ≤ min sigma (r/4)*Q) :
    t*(N : Real)^2 ≤ (Q : Real)^(k+g+4*d)*(coreAnchorAgreementDomain P Gamma D T x a r sigma).card := by
  apply columnBohrDomain_density_lower (columnShiftBases P a)
    (fun z => D ∪ coreAnchorAgreementSpectrum P Gamma T x a z) hQ _ hpopular
  intro z hz
  have hc := coreAnchorAgreementSpectrum_card_le P Gamma T x hG hT hx hz
  exact (Finset.card_union_le _ _).trans (by omega)

theorem coreAnchorAgreementDomain_agrees {N : Nat} [NeZero N]
    (P Gamma D : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N → ZMod N) {a : ZMod N} {r rho sigma : Real}
    (hr : 0 ≤ r) (hrrho : r ≤ rho)
    (hL : ∀ v ∈ P, IsFreimanLinearOn (bohr (T v) rho) (L v)) (hzero : ∀ v ∈ P, L v 0 = 0)
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (hx : x a ∈ columnShiftBases P a) (hy : y a ∈ columnShiftBases P a) :
    ∀ zw ∈ coreAnchorAgreementDomain P Gamma D T x a r sigma,
      zw.1 ∈ P ∧ zw.1+a ∈ P ∧ zw.2 ∈ bohr D sigma ∧
        shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y a zw.2 =
          L (zw.1+a) zw.2-L zw.1 zw.2 := by
  intro zw hzw
  obtain ⟨_,hz,hw⟩ := Finset.mem_filter.mp hzw
  have hw' : zw.2 ∈ bohr D (min sigma (r/4)) ∧
      zw.2 ∈ bohr (coreAnchorAgreementSpectrum P Gamma T x a zw.1) (min sigma (r/4)) := by
    simpa only [bohr_union,Finset.mem_inter] using hw
  refine ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2,
    bohr_mono_radius _ (min_le_left _ _) hw'.1,?_⟩
  exact core_shift_anchor_agrees P Gamma T L x y hr hrrho hL hzero hrel hx hy hz zw.2
    (bohr_mono_radius _ (min_le_right _ _) hw'.2)

end LeanProofs.GowersSzemeredi
