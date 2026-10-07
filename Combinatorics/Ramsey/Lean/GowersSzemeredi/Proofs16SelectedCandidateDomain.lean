import GowersSzemeredi.Proofs16SelectedDomainTransport
import GowersSzemeredi.Proofs16DenseMultilinearBox
import GowersSzemeredi.Proofs16GlobalGraphCover
import GowersSzemeredi.Proofs16CommonBasePieceBudget

/-! The common-base mass reserve permits selecting one global multilinear
candidate. This is a proved selection case, not a universal lifting theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- How many candidates may share the good-domain mass while leaving one
piece large enough for the exact Section 16 induction. -/
def section16UnitSelectionReserve (theta gamma : Real) (k : Nat) : Real :=
  section16ThetaTwo (section16ThetaOne theta gamma k) * multipleS theta gamma (k + 1)

theorem section16UnitSelectionReserve_gt_one {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    1 < section16UnitSelectionReserve theta gamma k := by
  have hd : 0 < section16ThetaTwo (section16ThetaOne theta gamma k) := by
    unfold section16ThetaTwo section16ThetaOne
    positivity
  have hi := (section16_thetaTwo_inverse_le_iteration k ht ht1 hg hg1).trans_lt
    (multipleS_strictMono_dimension ht ht1 hg hg1 (Nat.lt_succ_self k))
  unfold section16UnitSelectionReserve
  calc
    1 = section16ThetaTwo (section16ThetaOne theta gamma k) *
      (section16ThetaTwo (section16ThetaOne theta gamma k))⁻¹ := by field_simp
    _ < _ := mul_lt_mul_of_pos_left hi hd

/-- A bounded finite cover by global multilinear maps admits a selected
unit-multiply-linear domain of the exact source mass. The common-base
witness and every one of its certified fields remain unchanged. -/
theorem Section16CommonBaseData.selected_unit_domain_of_candidates
    {N k q : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (mu : Fin q → Point N (k + 1) → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (hc : ∀ x ∈ section16GoodDomain B (D.H ∩ D.J) D.Y D.x0,
      ∃ i, section16PhiOne phi D.x0 x = mu i x)
    (hq : (q : Real) ≤ section16UnitSelectionReserve theta gamma k) :
    Section16SelectedUnitDomain D := by
  classical
  let U := section16GoodDomain B (D.H ∩ D.J) D.Y D.x0
  let delta := section16ThetaTwo (section16ThetaOne theta gamma k)
  have hd : 0 < delta := by dsimp [delta, section16ThetaTwo, section16ThetaOne]; positivity
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hm : delta * (N : Real) ^ (k + 1) ≤ U.card := by
    rw [section16GoodDomain_card]
    exact D.good_mass
  have hUne : U.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast ((mul_pos hd (pow_pos hN _)).trans_le hm))
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨i, _⟩ := hc x hx
  have hqpos : 0 < q := Nat.zero_lt_of_lt i.isLt
  have hqreal : (0 : Real) < q := by exact_mod_cast hqpos
  obtain ⟨i, C, hCU, hCm, hagree⟩ := finite_graph_cover_dense_piece hqpos U
    (section16PhiOne phi D.x0) mu hc le_rfl hd.le (by positivity : (0 : Real) ≤ (N : Real) ^ (k + 1)) hm
  refine ⟨C, hCU, ?_, ?_⟩
  · have hS := zero_lt_one.trans_le (one_le_multipleS (k + 1) ht ht1 hg hg1)
    have hcoef : 1 / multipleS theta gamma (k + 1) ≤ delta / (q : Real) := by
      apply (div_le_div_iff₀ hS hqreal).mpr
      simpa only [one_mul, section16UnitSelectionReserve, delta] using hq
    calc
      _ = (1 / multipleS theta gamma (k + 1)) * (N : Real) ^ (k + 1) := by ring
      _ ≤ delta / (q : Real) * (N : Real) ^ (k + 1) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ _ := hCm
  · have heq : partialGraph C (section16PhiOne phi D.x0) = partialGraph C (mu i) := by
      apply Finset.image_congr
      intro x hx
      exact congrArg (Prod.mk x) (hagree x hx)
    change MultiplyLinear gamma 1 (partialGraph C (section16PhiOne phi D.x0))
    rw [heq]
    exact (hmu i).multiplyLinearFunction C hg hg1 le_rfl

/-- In particular, a sufficiently small value set can always be thinned to
a constant graph of the required mass, regardless of the behavior on the
rest of the good domain. -/
theorem Section16CommonBaseData.selected_unit_domain_of_finite_range
    {N k : Nat} [NeZero N] {theta gamma : Real}
    {B : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    (D : Section16CommonBaseData theta gamma B phi)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hcard : (((section16GoodDomain B (D.H ∩ D.J) D.Y D.x0).image
      (section16PhiOne phi D.x0)).card : Real) ≤ section16UnitSelectionReserve theta gamma k) :
    Section16SelectedUnitDomain D := by
  classical
  let S := (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0).image (section16PhiOne phi D.x0)
  let e := Fintype.equivFin {y // y ∈ S}
  let mu : Fin (Fintype.card {y // y ∈ S}) → Point N (k + 1) → ZMod N :=
    fun i _ => (e.symm i).val
  apply D.selected_unit_domain_of_candidates ht ht1 hg hg1 mu
    (fun i => isMultilinear_constant (e.symm i).val) ?_ ?_
  · intro x hx
    let y : {y // y ∈ S} := ⟨section16PhiOne phi D.x0 x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
    exact ⟨e y, by simp [mu, y]⟩
  · simpa only [Fintype.card_coe] using hcard

end LeanProofs.GowersSzemeredi
