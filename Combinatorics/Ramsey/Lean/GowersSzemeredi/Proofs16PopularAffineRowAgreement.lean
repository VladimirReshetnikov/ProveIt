import GowersSzemeredi.Proofs16GlobalProgressionRows

/-! Popular retained arrangements still give dense agreement with original
core column differences inside the affine row Bohr domains. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem popular_affine_row_agreement {N m K g d : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) (c : Fin 4 → Fin m → ZMod N)
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (a b : Fin 4 → ZMod N)
    {r rho sigma t : Real} (hr : 0 < r) (hrrho : r ≤ rho) (hsigma : 0 < sigma)
    (hG : Gamma.card ≤ g) (hT : ∀ v ∈ P, (T v).card ≤ d)
    (hL : ∀ v ∈ P, IsFreimanLinearOn (bohr (T v) rho) (L v))
    (hzero : ∀ v ∈ P, L v 0 = 0) (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (hJ : ∀ j, (J j).card ≤ K) (hadd : a 0+a 1 = a 2+a 3)
    (hmem : shiftAnchorArrangement x y a ∈ popularSupportedHigherArrangements P t) :
    ∀ j, t*N ≤ ((columnShiftBases P (a j)).card : Real) ∧
      CoreAnchorAgreementAt P Gamma (affineRowConstants J c ∪ varyingRowFrequencies J psi j (b j))
        T L x y (a j) r (sigma/2) (coreAnchorAgreementDensity t (5*K) g d r (sigma/2)) := by
  intro j
  obtain ⟨hpopular,hx,hy⟩ := popular_shift_anchor_bases P x y a hadd hmem j
  refine ⟨hpopular,?_,?_⟩
  · exact coreAnchorAgreementDomain_uniform_density P Gamma
      (affineRowConstants J c ∪ varyingRowFrequencies J psi j (b j)) T x
      hr (by positivity) (affineRowFrequencies_card_le J c psi hJ j (b j)) hG hT hx hpopular
  · exact coreAnchorAgreementDomain_agrees P Gamma
      (affineRowConstants J c ∪ varyingRowFrequencies J psi j (b j)) T L x y
      hr.le hrrho hL hzero hrel hx hy

def affineRowAgreementDensity (t : Real) (g d : Nat) (r : Real) : Real :=
  coreAnchorAgreementDensity t (10*jointSelectionRank (g+d) r) g d r
    (jointSelectionRadius (g+d) r/2)

theorem affineRowAgreementDensity_pos {t r : Real} (ht : 0 < t) (hr : 0 < r)
    (g d : Nat) : 0 < affineRowAgreementDensity t g d r := by
  apply coreAnchorAgreementDensity_pos ht hr
  have h := jointSelectionRadius_pos (g+d) r
  positivity

theorem selected_affine_row_agreement {N m g d : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) (c : Fin 4 → Fin m → ZMod N)
    (psi : Fin 4 → Fin m → ZMod N → ZMod N) (a b : Fin 4 → ZMod N)
    {r rho t : Real} (hr : 0 < r) (hrrho : r ≤ rho)
    (hG : Gamma.card ≤ g) (hT : ∀ v ∈ P, (T v).card ≤ d)
    (hL : ∀ v ∈ P, IsFreimanLinearOn (bohr (T v) rho) (L v))
    (hzero : ∀ v ∈ P, L v 0 = 0) (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (hJ : ∀ j, (J j).card ≤ 2*jointSelectionRank (g+d) r)
    (hadd : a 0+a 1 = a 2+a 3)
    (hmem : shiftAnchorArrangement x y a ∈ popularSupportedHigherArrangements P t) :
    ∀ j, CoreAnchorAgreementAt P Gamma
      (affineRowConstants J c ∪ varyingRowFrequencies J psi j (b j)) T L x y (a j)
      r (jointSelectionRadius (g+d) r/2) (affineRowAgreementDensity t g d r) := by
  have h := popular_affine_row_agreement P Gamma T L x y J c psi a b hr hrrho
    (jointSelectionRadius_pos (g+d) r) hG hT hL hzero hrel hJ hadd hmem
  intro j
  simpa only [affineRowAgreementDensity,show 5*(2*jointSelectionRank (g+d) r) =
    10*jointSelectionRank (g+d) r by omega] using (h j).2

end LeanProofs.GowersSzemeredi
