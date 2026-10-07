import OAI.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff
import OAI.Combinatorics.Progressions.Fourier.CRTConfigurationTorus
import OAI.Combinatorics.Progressions.Fourier.TorusCellBudget

namespace OAI

section

namespace Erdos3

theorem progression_window_radius_bounds {k : ℕ} (hk : 1 ≤ k) :
    0 < 1 / (16 * (k : ℝ)) ∧ 1 / (16 * (k : ℝ)) ≤ 1 / 16 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨by positivity, one_div_le_one_div_of_le (by norm_num) (by linarith)⟩

theorem residue_base_window_bound {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (x : ZMod N)
    (hx : dist (ZMod.toAddCircle x) ((1 / 4 : ℝ) : UnitAddCircle) ≤ 1 / (16 * (k : ℝ))) :
    2 * x.val < N := by
  obtain ⟨_, hr⟩ := progression_window_radius_bounds hk
  have hc : 1 / (16 * (k : ℝ)) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 - 1 / (16 * (k : ℝ)) := by
    constructor <;> linarith
  have he := residue_fraction_close_to_interior_center x hc hx
  have hfrac : (x.val : ℝ) / N < 1 / 2 := by linarith [(abs_le.mp he).2]
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hmul : 2 * (x.val : ℝ) < N := by linarith [(div_lt_iff₀ hNR).mp hfrac]
  exact_mod_cast hmul

theorem residue_step_window_bounds {N k : ℕ} [NeZero N] (hk : 1 ≤ k)
    (d : ZMod N)
    (hd : dist (ZMod.toAddCircle d) ((1 / (4 * (k : ℝ)) : ℝ) : UnitAddCircle) ≤
      1 / (16 * (k : ℝ))) :
    0 < d.val ∧ 2 * k * d.val < N := by
  obtain ⟨hr0, hr⟩ := progression_window_radius_bounds hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have heq : 1 / (4 * (k : ℝ)) = 4 * (1 / (16 * (k : ℝ))) := by ring
  have hc : 1 / (16 * (k : ℝ)) < 1 / (4 * (k : ℝ)) ∧
      1 / (4 * (k : ℝ)) < 1 - 1 / (16 * (k : ℝ)) := by
    rw [heq]
    constructor <;> linarith
  have he := residue_fraction_close_to_interior_center d hc hd
  have hf0 : 0 < (d.val : ℝ) / N := by rw [heq] at he; linarith [(abs_le.mp he).1]
  have heq' : 1 / (2 * (k : ℝ)) = 8 * (1 / (16 * (k : ℝ))) := by ring
  have hf1 : (d.val : ℝ) / N < 1 / (2 * (k : ℝ)) := by
    rw [heq] at he
    rw [heq']
    linarith [(abs_le.mp he).2]
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  constructor
  · have h := (lt_div_iff₀ hNR).mp hf0
    simpa only [zero_mul, Nat.cast_pos] using h
  · have h := (div_lt_div_iff₀ hNR (by positivity : 0 < 2 * (k : ℝ))).mp hf1
    have hh : 2 * (k : ℝ) * d.val < N := by nlinarith
    exact_mod_cast hh

theorem residue_progression_val_of_windows {N k : ℕ} [NeZero N]
    (x d : ZMod N) (hx : 2 * x.val < N) (hd : 2 * k * d.val < N)
    {i : ℕ} (hi : i < k) :
    (x + (i : ZMod N) * d).val = x.val + i * d.val := by
  have hid : i * d.val ≤ k * d.val := Nat.mul_le_mul_right _ hi.le
  have hsum : x.val + i * d.val < N := by nlinarith
  have he : x + (i : ZMod N) * d = ((x.val + i * d.val : ℕ) : ZMod N) := by simp
  rw [he, ZMod.val_natCast_of_lt hsum]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def progressionTorusCenter {J : Type*} (k : ℕ) : J × Bool → UnitAddCircle :=
  fun t => if t.2 then ((1 / (4 * (k : ℝ)) : ℝ) : UnitAddCircle) else ((1 / 4 : ℝ) : UnitAddCircle)

noncomputable def progressionTorusCutoff {J : Type*} [Fintype J] (k : ℕ)
    (w : J × Bool → UnitAddCircle) : ℝ :=
  centeredTorusTent (64 * k) (progressionTorusCenter k) w

theorem progressionTorusCutoff_range {J : Type*} [Fintype J] (k : ℕ)
    (w : J × Bool → UnitAddCircle) :
    0 ≤ progressionTorusCutoff k w ∧ progressionTorusCutoff k w ≤ 1 :=
  centeredTorusTent_range _ _ _

theorem progressionTorusCutoff_lipschitz {J : Type*} [Fintype J] (k : ℕ) :
    LipschitzWith (((64 * k : ℕ) : ℝ≥0) / 4) (progressionTorusCutoff (J := J) k) :=
  centeredTorusTent_lipschitz _ _

theorem progressionTorusCutoff_residue_support {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] {k : ℕ} (hk : 1 ≤ k)
    (u : (t : J × Bool) → ZMod (N t.1))
    (hu : progressionTorusCutoff k (fun t => ZMod.toAddCircle (u t)) ≠ 0) (j : J) :
    2 * (u (j, false)).val < N j ∧
      0 < (u (j, true)).val ∧ 2 * k * (u (j, true)).val < N j := by
  have hk0 : 0 < 64 * k := by omega
  have hr : 4 / ((64 * k : ℕ) : ℝ) = 1 / (16 * (k : ℝ)) := by push_cast; ring
  have hx := centeredTorusTent_coordinate_support hk0 (progressionTorusCenter k)
    (fun t => ZMod.toAddCircle (u t)) hu (j, false)
  have hd := centeredTorusTent_coordinate_support hk0 (progressionTorusCenter k)
    (fun t => ZMod.toAddCircle (u t)) hu (j, true)
  rw [hr] at hx hd
  simp only [progressionTorusCenter, Bool.false_eq_true, ↓reduceIte] at hx
  simp only [progressionTorusCenter, ↓reduceIte] at hd
  exact ⟨residue_base_window_bound hk _ hx.le, residue_step_window_bounds hk _ hd.le⟩

theorem progressionTorusCutoff_residue_mean {J : Type*} [Fintype J] [DecidableEq J]
    (N : J → ℕ) [∀ j, NeZero (N j)] {k : ℕ} (hk : 1 ≤ k) (hN : ∀ j, 64 * k ≤ N j) :
    1 / (2 * (128 * (k : ℝ)) ^ (Fintype.card J * 2)) ≤
      𝔼 u : (t : J × Bool) → ZMod (N t.1),
        progressionTorusCutoff k (fun t => ZMod.toAddCircle (u t)) := by
  have h := centeredTorusTent_residue_mean (fun t : J × Bool => N t.1)
    (show 0 < 64 * k by omega) (fun t => hN t.1) (progressionTorusCenter k)
  simpa only [progressionTorusCutoff, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul,
    Nat.cast_ofNat, show (2 : ℝ) * (64 * (k : ℝ)) = 128 * k by ring] using h

noncomputable def crtProgressionWeight {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (k : ℕ)
    (z : ZMod (∏ j, N j) × ZMod (∏ j, N j)) : ℝ :=
  progressionTorusCutoff k (crtConfigurationTorus N hN z)

theorem crtProgressionWeight_range {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) (k : ℕ)
    (z : ZMod (∏ j, N j) × ZMod (∏ j, N j)) :
    0 ≤ crtProgressionWeight N hN k z ∧ crtProgressionWeight N hN k z ≤ 1 :=
  progressionTorusCutoff_range _ _

theorem crtProgressionWeight_mean {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] [NeZero (∏ j, N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
    {k : ℕ} (hk : 1 ≤ k) (hsize : ∀ j, 64 * k ≤ N j) :
    1 / (2 * (128 * (k : ℝ)) ^ (Fintype.card J * 2)) ≤
      𝔼 z, crtProgressionWeight N hN k z := by
  classical
  have he := crt_configuration_expect N hN
    (fun u => progressionTorusCutoff k (fun t => ZMod.toAddCircle (u t)))
  change (𝔼 z, crtProgressionWeight N hN k z) = _ at he
  rw [he]
  exact progressionTorusCutoff_residue_mean N hk hsize

theorem crtProgressionWeight_support {J : Type*} [Fintype J] (N : J → ℕ)
    [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) {k : ℕ} (hk : 1 ≤ k)
    (x d : ZMod (∏ j, N j)) (h : crtProgressionWeight N hN k (x, d) ≠ 0) :
    (∀ j, 0 < (ZMod.prodEquivPi N hN d j).val) ∧
    ∀ i : ℕ, i < k → ∀ j,
      (ZMod.prodEquivPi N hN (x + (i : ZMod (∏ j, N j)) * d) j).val =
        (ZMod.prodEquivPi N hN x j).val + i * (ZMod.prodEquivPi N hN d j).val := by
  have hb (j : J) := progressionTorusCutoff_residue_support N hk
    (crtConfigurationEquiv N hN (x, d)) h j
  change ∀ j, 2 * (ZMod.prodEquivPi N hN x j).val < N j ∧
    0 < (ZMod.prodEquivPi N hN d j).val ∧
      2 * k * (ZMod.prodEquivPi N hN d j).val < N j at hb
  refine ⟨fun j => (hb j).2.1, fun i hi j => ?_⟩
  have hv := residue_progression_val_of_windows (ZMod.prodEquivPi N hN x j)
    (ZMod.prodEquivPi N hN d j) (hb j).1 (hb j).2.2 hi
  simpa only [map_add, map_mul, map_natCast, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply] using hv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def IntegerVectorAPFree {J : Type*} (A : Set (J → ℤ)) (k : ℕ) : Prop :=
  ∀ a d : J → ℤ, d ≠ 0 → ∃ i : Fin k, a + (i.val : ℤ) • d ∉ A

noncomputable def residueBoxIntegerPoint {J : Type*} (N : J → ℕ)
    (u : (j : J) → ZMod (N j)) : J → ℤ := fun j => (u j).val

theorem crtProgressionWeight_mul_prod_eq_zero {J : Type*} [Fintype J] [Nonempty J]
    (N : J → ℕ) [∀ j, NeZero (N j)] (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
    {k : ℕ} (hk : 1 ≤ k) (f : ((j : J) → ZMod (N j)) → ℝ)
    (hfree : IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k)
    (x d : ZMod (∏ j, N j)) :
    crtProgressionWeight N hN k (x, d) *
      (∏ i : Fin k, f (ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d))) = 0 := by
  classical
  by_cases hw : crtProgressionWeight N hN k (x, d) = 0
  · rw [hw, zero_mul]
  obtain ⟨hstep, hval⟩ := crtProgressionWeight_support N hN hk x d hw
  let a := residueBoxIntegerPoint N (ZMod.prodEquivPi N hN x)
  let b := residueBoxIntegerPoint N (ZMod.prodEquivPi N hN d)
  have hb : b ≠ 0 := by
    intro h
    let j : J := Classical.choice inferInstance
    have hj : b j = 0 := congrFun h j
    have hpos : (0 : ℤ) < b j := by
      dsimp [b, residueBoxIntegerPoint]
      exact_mod_cast hstep j
    omega
  obtain ⟨i, hi⟩ := hfree a b hb
  have hzero : f (ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d)) = 0 := by
    by_contra h
    apply hi
    refine ⟨ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d), h, ?_⟩
    funext j
    change ((ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d) j).val : ℤ) =
      ((ZMod.prodEquivPi N hN x j).val : ℤ) + (i.val : ℤ) * (ZMod.prodEquivPi N hN d j).val
    exact_mod_cast hval i.val i.isLt j
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, mul_zero]

theorem crtProgressionWeight_product_mean_eq_zero {J : Type*} [Fintype J] [Nonempty J]
    (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
    (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j))) {k : ℕ} (hk : 1 ≤ k)
    (f : ((j : J) → ZMod (N j)) → ℝ)
    (hfree : IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k) :
    (𝔼 x, 𝔼 d, crtProgressionWeight N hN k (x, d) *
      (∏ i : Fin k, f (ZMod.prodEquivPi N hN (x + (i.val : ZMod (∏ j, N j)) * d)))) = 0 := by
  simp only [crtProgressionWeight_mul_prod_eq_zero N hN hk f hfree, Fintype.expect_const]

end Erdos3

end

end OAI
