import GowersSzemeredi.Proofs16CubicSpectrumRestriction
import GowersSzemeredi.Proofs16CommonBaseLineCovers
import GowersSzemeredi.Proofs16WithLemma9

/-! Construct common-base geometry with explicit spectrum control functions.
The density, selection, and identity witnesses are the same as in the
original common-base construction. In dimension two the strengthened base
case supplies the spectrum input with loss-independent graph count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

structure Section16CommonBaseDataWith {N k : Nat} [NeZero N]
    (theta gamma : Real) (Qb Eb : Real → Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) where
  H : Finset (Point N k)
  J : Finset (Point N k)
  Y : (h : Point N k) → Finset (Section16CubeElement B h)
  phiPrime : Point N k → ZMod N → ZMod N
  x0 : Point N k
  Hmass : section16ThetaOne theta gamma k / 4 * (N : Real) ^ k ≤ H.card
  intersect_mass : section16ThetaOne theta gamma k / 8 * (N : Real) ^ k ≤ (H ∩ J).card
  cube_mass : ∀ h ∈ H, section16ThetaOne theta gamma k / 4 * (N : Real) ^ (k + 1) ≤
    (section16CubeDomain B h).card
  selected_mass : ∀ h ∈ H, (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 *
    (section16CubeDomain B h).card ≤ (Y h).card
  selection : Section16InducedSelection B phi H Y
    (fun h => section16LargeSpectrum B h (section16Delta (section16ThetaOne theta gamma k)))
    (section16Zeta theta gamma k) phiPrime
  spectrum : MultiplyLinearWith Qb Eb
    (restrictRelation (section16SpectrumRelation B (section16Delta (section16ThetaOne theta gamma k))) J)
  good_mass : section16ThetaTwo (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1) ≤
    section16GoodInducedPairCount B (H ∩ J) Y x0
  identity : Section16PhiOneIdentity (section16GoodDomain B (H ∩ J) Y x0) phi x0 phiPrime

/-- Assemble the common geometry from a spectrum restriction with arbitrary
multiple-linearity controls. -/
theorem section16_common_base_data_with {N k : Nat} [NeZero N] [Fact N.Prime]
    {theta gamma : Real} {Qb Eb : Real → Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hB : Section16StructuredPair theta gamma B phi)
    (hspectrum : ∃ J : Finset (Point N k),
      (1 - section16ThetaOne theta gamma k / 8) * (N : Real) ^ k ≤ J.card ∧
      MultiplyLinearWith Qb Eb
        (restrictRelation (section16SpectrumRelation B
          (section16Delta (section16ThetaOne theta gamma k))) J)) :
    Nonempty (Section16CommonBaseDataWith theta gamma Qb Eb B phi) := by
  classical
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection (Fact.out : N.Prime) theta gamma B phi ht ht1 hg hg1 hB
  obtain ⟨J, hJ, hspectrum⟩ := hspectrum
  have hmass : section16ThetaOne theta gamma k / 8 * (N : Real) ^ k ≤ (H ∩ J).card := by
    have hcard : ((H ∪ J).card : Real) + (H ∩ J).card = H.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter H J
    have hu : ((H ∪ J).card : Real) ≤ (N : Real) ^ k := by
      exact_mod_cast (show (H ∪ J).card ≤ N ^ k by
        simpa [Point, ZMod.card] using Finset.card_le_univ (H ∪ J))
    nlinarith only [hcard, hu, hH, hJ]
  obtain ⟨x0, hgood, hidentity⟩ := lemma_16_7_holds N k theta gamma B phi (H ∩ J) Y phiPrime
    hmass (fun h hh => hcube h (Finset.mem_inter.mp hh).1)
    (fun h hh => hselected h (Finset.mem_inter.mp hh).1)
    (hselection.mono Finset.inter_subset_left)
  exact ⟨{
    H := H, J := J, Y := Y, phiPrime := phiPrime, x0 := x0
    Hmass := hH, intersect_mass := hmass, cube_mass := hcube, selected_mass := hselected
    selection := hselection, spectrum := hspectrum, good_mass := hgood
    identity := section16_phi_one_identity_of_common_base B phi (H ∩ J) Y x0 phiPrime hidentity }⟩

theorem Section16CommonBaseDataWith.all_box_line_covers
    {N k : Nat} [NeZero N] [Fact N.Prime] {theta gamma : Real} {Qb Eb : Real → Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseDataWith theta gamma Qb Eb B phi)
    (h : Section16StructuredPair theta gamma B phi)
    (hQE : ∀ s, 0 < s → s ≤ 1 → 0 ≤ Qb s ∧ 0 < Eb s ∧ Eb s ≤ 1)
    (hk : 1 ≤ k) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    Section16AllBoxLineCoversWith theta gamma Qb Eb
      (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0) (section16PhiOne phi D.x0) := by
  exact section16_all_box_line_covers_with N k hk theta gamma ht ht1 hg hg1 Qb Eb hQE
    B phi D.H D.J (D.H ∩ D.J) D.Y D.phiPrime D.x0 rfl
    D.spectrum D.selection D.identity
    (h.good_domain_remainder_cover hk ht ht1 hg hg1 (D.H ∩ D.J) D.Y D.x0)

/-- The dimension-two structured pair supplies actual common-base data and
line covers with a spectrum count independent of the inner loss. -/
theorem section16_cubic_common_base_line_covers {N : Nat} [Fact N.Prime]
    {theta gamma : Real} {B : Finset (Point N 2)} {phi : Point N 2 → ZMod N}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (h : Section16StructuredPair theta gamma B phi) :
    ∃ D : Section16CommonBaseDataWith theta gamma
      (fun _ => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real))
      (cubicBaseExponent (section16CubicSpectrumCount theta gamma)) B phi,
      Section16AllBoxLineCoversWith theta gamma
        (fun _ => ((3 * section16CubicSpectrumCount theta gamma : Nat) : Real))
        (cubicBaseExponent (section16CubicSpectrumCount theta gamma))
        (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0) (section16PhiOne phi D.x0) := by
  obtain ⟨D⟩ := section16_common_base_data_with ht ht1 hg hg1 h
    (by simpa only [pow_one] using section16_cubic_spectrum_restriction ht ht1 hg hg1 B)
  refine ⟨D, D.all_box_line_covers h ?_ (by decide) ht ht1 hg hg1⟩
  intro s hs hs1
  exact ⟨by positivity, cubicBaseExponent_pos (section16CubicSpectrumCount_pos theta gamma) hs,
    cubicBaseExponent_le_one (section16CubicSpectrumCount_pos theta gamma) hs hs1⟩

end LeanProofs.GowersSzemeredi
