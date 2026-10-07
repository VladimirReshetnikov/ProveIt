import GowersSzemeredi.Proofs16DenseSelection
import GowersSzemeredi.Proofs16SpectrumInduction
import GowersSzemeredi.Proofs16CommonBase
import GowersSzemeredi.Proofs16VertexIdentity

/-! Construct the common witnesses entering Lemmas 16.6--16.10 from the
structured pair and the preceding-dimensional induction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem Section16InducedSelection.mono {N k : Nat} [NeZero N]
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {H H1 : Finset (Point N k)}
    {Y : (h : Point N k) → Finset (Section16CubeElement B h)}
    {K : Point N k → Finset (ZMod N)} {zeta : Real}
    {phiPrime : Point N k → ZMod N → ZMod N}
    (h : Section16InducedSelection B phi H Y K zeta phiPrime) (hsub : H1 ⊆ H) :
    Section16InducedSelection B phi H1 Y K zeta phiPrime := by
  classical
  refine ⟨fun x hx => h.1 x (hsub hx), ?_⟩
  intro x hx m hm d hd I hstep hlen
  have heq : (I.carrier.filter fun s => (x, s) ∈ section16InducedDomain B H1 Y) =
      (I.carrier.filter fun s => (x, s) ∈ section16InducedDomain B H Y) := by
    ext s
    simp [section16InducedDomain, hx, hsub hx]
  rw [heq]
  exact h.2 x (hsub hx) m hm d hd I hstep hlen

/-- The actual common-base witnesses; all fields are constructed before
asking for any multiply-linearity conclusion about the all-ones graph. -/
structure Section16CommonBaseData {N k : Nat} [NeZero N]
    (theta gamma : Real) (B : Finset (Point N (k + 1)))
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
  spectrum : MultiplyLinear (section16Delta (section16ThetaOne theta gamma k))
    (section16T (section16Delta (section16ThetaOne theta gamma k)) (section16ThetaOne theta gamma k) k)
    (restrictRelation (section16SpectrumRelation B (section16Delta (section16ThetaOne theta gamma k))) J)
  good_mass : section16ThetaTwo (section16ThetaOne theta gamma k) * (N : Real) ^ (k + 1) ≤
    section16GoodInducedPairCount B (H ∩ J) Y x0
  identity : Section16PhiOneIdentity (section16GoodDomain B (H ∩ J) Y x0) phi x0 phiPrime

/-- Lemmas 16.5 and 16.7 and the spectrum restriction now supply compatible
witnesses, with one threshold independent of the structured input pair. -/
theorem Theorem162At.common_base_data {k : Nat} (hth : Theorem162At k)
    (theta gamma : Real) (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        Section16StructuredPair theta gamma B phi → Nonempty (Section16CommonBaseData theta gamma B phi) := by
  classical
  obtain ⟨N0, hN0⟩ := hth.restrict_spectrum theta gamma ht ht1 hg hg1
  refine ⟨N0, fun N _ _ hN B phi hB => ?_⟩
  obtain ⟨H, Y, phiPrime, hH, hcube, hselected, hselection⟩ :=
    section16_dense_induced_selection (Fact.out : N.Prime) theta gamma B phi ht ht1 hg hg1 hB
  obtain ⟨J, hJ, hspectrum⟩ := hN0 N hN B
  have hmass : section16ThetaOne theta gamma k / 8 * (N : Real) ^ k ≤ (H ∩ J).card := by
    have hcard : ((H ∪ J).card : Real) + (H ∩ J).card = H.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter H J
    have hu : ((H ∪ J).card : Real) ≤ (N : Real) ^ k := by
      exact_mod_cast (show (H ∪ J).card ≤ N ^ k by simpa [Point, ZMod.card] using Finset.card_le_univ (H ∪ J))
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

end LeanProofs.GowersSzemeredi
