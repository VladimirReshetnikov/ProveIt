import GowersSzemeredi.Proofs16AdditiveTupleEnergy
import GowersSzemeredi.Proofs16SlabCommonBaseWitness
import GowersSzemeredi.Proofs16UniformFaceParameter

/-! Slabs with a sufficiently small value alphabet satisfy the actual
structured-pair hypotheses, with the source arrangement-density parameter. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section16ThetaOne_le_density_sixteen {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    section16ThetaOne theta gamma k ≤ theta ^ (16 : Nat) := by
  have he : (4 : Nat) ≤ 2 ^ (k + 5) := by
    calc
      4 = 2 ^ (2 : Nat) := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have he' : (16 : Nat) ≤ 2 ^ (2 ^ (k + 5)) := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : Nat)) he
  unfold section16ThetaOne
  calc
    _ ≤ theta ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))) := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith only [ht.le, hg1]
    _ ≤ theta ^ (16 : Nat) := pow_le_pow_of_le_one ht.le ht1 he'

theorem additiveTupleCount_eight_density {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {alpha : Real} (ha : 0 ≤ alpha)
    (hA : alpha * N ≤ A.card) :
    alpha ^ (16 : Nat) * (N : Real) ^ (15 : Nat) ≤ additiveTupleCount 8 A := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hb := additiveTupleCount_mass_bound 8 A
  simp only [ZMod.card, Nat.reduceMul] at hb
  have hp := pow_le_pow_left₀ (mul_nonneg ha hN.le) hA 16
  apply (mul_le_mul_iff_right₀ hN).mp
  calc
    _ = (alpha * N) ^ (16 : Nat) := by rw [mul_pow]; ring
    _ ≤ (A.card : Real) ^ (16 : Nat) := hp
    _ ≤ _ := by simpa only [mul_comm] using hb

theorem section16_slab_arrangement_density {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hA : theta * N ≤ A.card) :
    section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
      generalArrangementCount 8 (lastProductSet (Finset.univ : Finset (Point N k)) A) := by
  rw [section16_slab_arrangement_count, Nat.cast_mul, Nat.cast_pow]
  have htuple := additiveTupleCount_eight_density A ht.le hA
  calc
    _ ≤ theta ^ (16 : Nat) * (N : Real) ^ (17 * k + 15) :=
      mul_le_mul_of_nonneg_right (section16ThetaOne_le_density_sixteen k ht ht1 hg hg1)
        (by positivity)
    _ = (N : Real) ^ (17 * k) * (theta ^ (16 : Nat) * (N : Real) ^ (15 : Nat)) := by
      rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htuple (by positivity)

theorem section16_face_budget_ge_inv_theta {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    theta⁻¹ ≤ gamma ^ (-(2 : Int)) *
      multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k := by
  let eps := (2 : Real) ^ (-(k + 2 : Real)) * theta
  obtain ⟨heps, heps1⟩ := section16_face_error_range k ht ht1
  have hepsTheta : eps ≤ theta := by
    apply mul_le_of_le_one_left ht.le
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (by positivity))
  have hprod : 0 < eps * gamma := mul_pos heps hg
  have hprod1 : eps * gamma ≤ 1 := mul_le_one₀ heps1 hg.le hg1
  have hb : (1 : Real) ≤ 2 / (eps * gamma) := (le_div_iff₀ hprod).mpr (by linarith)
  have hbase : theta⁻¹ ≤ 2 / (eps * gamma) := by
    rw [← one_div]
    apply (div_le_div_iff₀ ht hprod).mpr
    have hp : eps * gamma ≤ theta := (mul_le_of_le_one_right heps.le hg1).trans hepsTheta
    linarith
  have hS : theta⁻¹ ≤ multipleS eps gamma k :=
    hbase.trans (le_self_pow₀ hb (by positivity))
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  exact hS.trans (le_mul_of_one_le_left (by unfold multipleS; positivity) hginv)

/-- A dense slab with at most theta^-1 values has every source structured
pair field. In particular, the word need not be affine on its last axis. -/
theorem section16_slab_structured_pair {N k : Nat} [NeZero N]
    (hk : 1 ≤ k) (A S : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hf : ∀ x ∈ A, f x ∈ S) {theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hA : theta * N ≤ A.card) (hS : (S.card : Real) ≤ theta⁻¹) :
    Section16StructuredPair theta gamma
      (lastProductSet (Finset.univ : Finset (Point N k)) A) (fun z => f (section16Last z)) := by
  have hb := section16_face_budget_ge_inv_theta k ht ht1 hg hg1
  refine ⟨properCrossSections_of_global_values _ _ S ?_ hg hg1 ?_ (hS.trans hb),
    section16_slab_arrangement_density A ht ht1 hg hg1 hA, ?_⟩
  · intro z hz
    exact hf _ (Finset.mem_filter.mp hz).2.2
  · exact ((one_le_inv₀ ht).mpr ht1).trans hb
  · rw [section16_slab_respected_arrangement_count hk, section16_slab_arrangement_count]
    exact mul_le_of_le_one_left (by positivity) (sub_le_self _ (by positivity))

end LeanProofs.GowersSzemeredi
