import GowersSzemeredi.Proofs16SlabSpectrum
import GowersSzemeredi.Proofs16CommonBaseAssembly

/-! A complete common-base witness with full cube selection on a sufficiently
dense slab. This construction makes no claim of unit multiply-linearity of
the arbitrary value word on its good domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Every base can be used, with H=J=univ, all admissible cubes selected,
and zero induced map. All fields of the actual common-base structure are
certified, including its spectrum and its quantitative mass requirements. -/
def section16SlabCommonBaseData {N k : Nat} [NeZero N]
    (hk : 1 ≤ k) (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (x0 : Point N k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hmass : section16ThetaOne theta gamma k / 4 * (N : Real) ≤ A.card) :
    Section16CommonBaseData (k := k) theta gamma
      (lastProductSet Finset.univ A) (fun z => f (section16Last z)) := by
  classical
  have hranges := section16_theta_delta_bounds k ht ht1 hg hg1
  have hth := hranges.1
  have hth1 := hranges.2.1
  have hd := hranges.2.2.1
  have hd1 := hranges.2.2.2
  have hU : ((Finset.univ : Finset (Point N k)).card : Real) = (N : Real) ^ k := by
    simp [Point, ZMod.card]
  have hcube : section16ThetaOne theta gamma k / 4 * (N : Real) ^ (k + 1) ≤
      (N : Real) ^ k * A.card := by
    calc
      _ = (N : Real) ^ k * (section16ThetaOne theta gamma k / 4 * N) := by
        rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  have hselected : (2 : Real) ^ (-(27 : Real)) * (section16ThetaOne theta gamma k) ^ 6 ≤ 1 := by
    apply mul_le_one₀ _ (by positivity) (pow_le_one₀ hth.le hth1)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have htheta2 : section16ThetaTwo (section16ThetaOne theta gamma k) ≤
      section16ThetaOne theta gamma k / 4 := by
    calc
      _ ≤ (1 / 4 : Real) * section16ThetaOne theta gamma k := by
        unfold section16ThetaTwo
        apply mul_le_mul (by norm_num : (2 : Real) ^ (-(32 : Real)) ≤ 1 / 4)
          (pow_le_of_le_one hth.le hth1 (by norm_num : (8 : Nat) ≠ 0))
          (by positivity) (by norm_num)
      _ = _ := by ring
  refine {
    H := Finset.univ
    J := Finset.univ
    Y := fun _ => Finset.univ
    phiPrime := fun _ _ => 0
    x0 := x0
    Hmass := ?_
    intersect_mass := ?_
    cube_mass := ?_
    selected_mass := ?_
    selection := section16_slab_full_induced_selection hk A f _ _
    spectrum := ?_
    good_mass := ?_
    identity := ?_ }
  · rw [hU]
    exact mul_le_of_le_one_left (by positivity) (by linarith)
  · rw [Finset.inter_self, hU]
    exact mul_le_of_le_one_left (by positivity) (by linarith)
  · intro h hh
    rw [section16_slab_cube_card, Nat.cast_mul, Nat.cast_pow]
    exact hcube
  · intro h hh
    simp only [Finset.card_univ, Fintype.card_coe]
    exact mul_le_of_le_one_left (by positivity) hselected
  · simp only [restrictRelation, Finset.mem_univ, Finset.filter_true]
    exact section16_slab_spectrum_multiplyLinear A hd hd1 hth hth1
  · rw [Finset.inter_self, section16_slab_full_good_count, Nat.cast_mul, Nat.cast_pow]
    exact (mul_le_mul_of_nonneg_right htheta2 (by positivity)).trans hcube
  · simp only [Finset.inter_self]
    exact section16_slab_full_common_base_identity hk A f x0

theorem section16SlabCommonBaseData_good_domain {N k : Nat} [NeZero N]
    (hk : 1 ≤ k) (A : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (x0 : Point N k) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hmass : section16ThetaOne theta gamma k / 4 * (N : Real) ≤ A.card) :
    let D := section16SlabCommonBaseData hk A f x0 ht ht1 hg hg1 hmass
    section16GoodDomain (lastProductSet Finset.univ A) (D.H ∩ D.J) D.Y D.x0 =
      lastProductSet Finset.univ A := by
  dsimp only [section16SlabCommonBaseData]
  rw [Finset.inter_self]
  exact section16_slab_full_good_domain A x0

end LeanProofs.GowersSzemeredi
