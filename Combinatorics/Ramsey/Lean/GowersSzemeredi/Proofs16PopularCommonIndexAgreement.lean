import GowersSzemeredi.Proofs16UniformCoreAnchorAgreement

/-! Common-index selection preserves coherent quadruples and positive
density agreement with supported column differences at every shift. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def CoreAnchorAgreementAt {N : Nat} [NeZero N]
    (P Gamma D : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N → ZMod N) (a : ZMod N)
    (r sigma density : Real) : Prop :=
  density*(N : Real)^2 ≤ (coreAnchorAgreementDomain P Gamma D T x a r sigma).card ∧
    ∀ zw ∈ coreAnchorAgreementDomain P Gamma D T x a r sigma,
      zw.1 ∈ P ∧ zw.1+a ∈ P ∧ zw.2 ∈ bohr D sigma ∧
        shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y a zw.2 =
          L (zw.1+a) zw.2-L zw.1 zw.2

theorem popular_common_indices_agree {N g d : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r rho t delta kappa : Real}
    (hr : 0 < r) (hrrho : r ≤ rho) (hd : 0 < delta) (hk : 0 < kappa)
    (hG : Gamma.card ≤ g) (hT : ∀ v ∈ P, (T v).card ≤ d)
    (hL : ∀ v ∈ P, IsFreimanLinearOn (bohr (T v) rho) (L v)) (hzero : ∀ v ∈ P, L v 0 = 0)
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    (h : HasCoherentAnchorSystemOn (popularSupportedHigherArrangements P t)
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L) delta kappa (g+d) r) :
    ∃ (s : PairSelectionState N) (J : Finset (Fin s.maps.length))
      (x y : ZMod N → ZMod N) (R : Finset (Fin 4 → ZMod N)),
      s.JointValid (coreColumnSpectrum P Gamma T) delta (g+d) r ∧
      (s.maps.length : Real)*jointSelectionGain delta (g+d) r ≤ jointSelectionRank (g+d) r ∧
      J.card ≤ 8*jointSelectionRank (g+d) r ∧
      uniformAnchorIndexDensity delta kappa (g+d) r*(N : Real)^3 ≤ R.card ∧
      ∀ a ∈ R, a 0+a 1 = a 2+a 3 ∧ Function.Injective a ∧
        shiftAnchorArrangement x y a ∈ popularSupportedHigherArrangements P t ∧
        (∀ j : Fin 4, IsFreimanLinearOn
          (bohr (commonIndexAnchorFrequencies s J (a j)) (jointSelectionRadius (g+d) r))
          (shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y (a j)) ∧
          shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y (a j) 0 = 0) ∧
        (∀ z, (∀ j : Fin 4, z ∈ bohr (commonIndexAnchorFrequencies s J (a j))
            (jointSelectionRadius (g+d) r)) →
          shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y (a 0) z+
            shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y (a 1) z =
          shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y (a 2) z+
            shiftAnchorMap (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r x y (a 3) z) ∧
        (∀ j : Fin 4, t*N ≤ ((columnShiftBases P (a j)).card : Real) ∧
          CoreAnchorAgreementAt P Gamma (commonIndexAnchorFrequencies s J (a j)) T L x y (a j)
            r (jointSelectionRadius (g+d) r)
            (coreAnchorAgreementDensity t (8*jointSelectionRank (g+d) r) g d r
              (jointSelectionRadius (g+d) r))) := by
  obtain ⟨s,J,x,y,R,hs,hbudget,hJ,hmass,hproperties⟩ :=
    h.common_indices_uniform hk hd (coreColumnSpectrum_card_le P Gamma T hG hT)
  refine ⟨s,J,x,y,R,hs,hbudget,hJ,hmass,?_⟩
  intro a ha
  obtain ⟨hadd,hinj,hmem,hlocal,hcoherent⟩ := hproperties a ha
  refine ⟨hadd,hinj,hmem,hlocal,hcoherent,?_⟩
  intro j
  obtain ⟨hpopular,hx,hy⟩ := popular_shift_anchor_bases P x y a hadd hmem j
  have hD : (commonIndexAnchorFrequencies s J (a j)).card ≤ 8*jointSelectionRank (g+d) r :=
    Finset.card_image_le.trans hJ
  refine ⟨hpopular,?_,?_⟩
  · exact coreAnchorAgreementDomain_uniform_density P Gamma (commonIndexAnchorFrequencies s J (a j)) T x
      hr (jointSelectionRadius_pos (g+d) r) hD hG hT hx hpopular
  · exact coreAnchorAgreementDomain_agrees P Gamma (commonIndexAnchorFrequencies s J (a j)) T L x y
      hr.le hrrho hL hzero hrel hx hy

end LeanProofs.GowersSzemeredi
