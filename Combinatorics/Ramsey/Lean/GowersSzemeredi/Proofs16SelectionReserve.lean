import GowersSzemeredi.Proofs16SelectedCandidateDomain

/-! The common-base density leaves enough mass to select a colour class
from an alphabet of size at most theta^-1. This handles such inputs without
asserting a unit cover of the entire good domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exact selection reserve is at least the reciprocal input density. -/
theorem section16UnitSelectionReserve_ge_inv_theta {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    theta⁻¹ ≤ section16UnitSelectionReserve theta gamma k := by
  let delta := section16ThetaTwo (section16ThetaOne theta gamma k)
  have hd : 0 < delta := by dsimp [delta, section16ThetaTwo, section16ThetaOne]; positivity
  have hi := section16_thetaTwo_inverse_le_iteration k ht ht1 hg hg1
  have hmass : 1 ≤ delta * multipleS theta gamma k := by
    calc
      1 = delta * delta⁻¹ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hi hd.le
  have htg : 0 < theta * gamma := mul_pos ht hg
  have htg1 : theta * gamma ≤ 1 := mul_le_one₀ ht1 hg.le hg1
  have hb : (1 : Real) ≤ 2 / (theta * gamma) := (le_div_iff₀ htg).mpr (by linarith)
  have hexp : (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) + 1 ≤
      (2 : Nat) ^ ((2 : Nat) ^ (k + 1 + 6)) := by
    apply Nat.succ_le_of_lt
    apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
    apply Nat.pow_lt_pow_right (by norm_num : 1 < 2)
    omega
  have hstep : (2 / (theta * gamma)) * multipleS theta gamma k ≤ multipleS theta gamma (k + 1) := by
    unfold multipleS
    rw [mul_comm, ← pow_succ]
    exact pow_le_pow_right₀ hb hexp
  have hbase : theta⁻¹ ≤ 2 / (theta * gamma) := by
    rw [← one_div]
    apply (div_le_div_iff₀ ht htg).mpr
    nlinarith only [ht.le, hg1]
  calc
    theta⁻¹ ≤ 2 / (theta * gamma) := hbase
    _ ≤ (2 / (theta * gamma)) * (delta * multipleS theta gamma k) :=
      le_mul_of_one_le_right (by positivity) hmass
    _ = delta * ((2 / (theta * gamma)) * multipleS theta gamma k) := by ring
    _ ≤ delta * multipleS theta gamma (k + 1) := mul_le_mul_of_nonneg_left hstep hd.le
    _ = _ := rfl

/-- Every value on the all-ones good domain is a value of the original
partial function on its actual domain. -/
theorem section16GoodDomain_value_image_subset {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (H : Finset (Point N k)) (Y : (h : Point N k) → Finset (Section16CubeElement B h))
    (x0 : Point N k) :
    (section16GoodDomain B H Y x0).image (section16PhiOne phi x0) ⊆ B.image phi := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hgraph : GraphContained B phi (partialGraph B phi) := fun z hz =>
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hmem : (x + appendCoordinate x0 0, section16PhiOne phi x0 x) ∈
      section16TranslatedGoodGraph B phi H Y x0 :=
    Finset.mem_image.mpr ⟨(x, section16PhiOne phi x0 x), Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩
  have h := section16TranslatedGoodGraph_subset (partialGraph B phi) B phi H Y x0 hgraph hmem
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp h
  exact Finset.mem_image.mpr ⟨z, hz, congrArg Prod.snd heq⟩

/-- Every common-base witness admits a successful further selection when
the original partial function has at most theta^-1 distinct values. This
is a selection theorem for that class, not a full-good-domain cover claim. -/
theorem Section16CommonBaseData.selected_unit_domain_of_value_budget
    {N k : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hvalues : ((B.image phi).card : Real) ≤ theta⁻¹) : Section16SelectedUnitDomain D := by
  apply D.selected_unit_domain_of_finite_range ht ht1 hg hg1
  exact (Nat.cast_le.mpr (Finset.card_le_card
    (section16GoodDomain_value_image_subset B phi (D.H ∩ D.J) D.Y D.x0))).trans
    (hvalues.trans (section16UnitSelectionReserve_ge_inv_theta k ht ht1 hg hg1))

end LeanProofs.GowersSzemeredi
