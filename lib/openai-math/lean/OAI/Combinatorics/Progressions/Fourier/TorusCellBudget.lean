/- Modified for ProveIt: import Lean 4.32 compatibility declarations;
use Isometry.lipschitz and prove the injective sum bound through Finset.image.
The mathematical statements are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FiniteImageCover
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter
import OAI.Combinatorics.Progressions.Lattices.IntegerLiftOffset
import OAI.Combinatorics.Progressions.Linear.PeriodicKernelPartition
import OAI.Combinatorics.Progressions.Linear.WeightedParameterPatchRankPadding
import OAI.Combinatorics.Progressions.Sampling.PositivePartitionScore

namespace OAI

section

namespace Erdos3

noncomputable def torusGridCenter {d : ℕ} (q : ℕ) (a : Fin d → Fin q) : Fin d → ℝ :=
  fun i => (a i).val / (q : ℝ)

theorem fractionalPartBin_center_error {q : ℕ} (hq : 0 < q) (x : ℝ) :
    |((fractionalPartBin q hq x).val : ℝ) / q - Int.fract x| ≤ 1 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo : ((fractionalPartBin q hq x).val : ℝ) ≤ (q : ℝ) * Int.fract x :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg q) (Int.fract_nonneg x))
  have hhi : (q : ℝ) * Int.fract x < ((fractionalPartBin q hq x).val : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hle : ((fractionalPartBin q hq x).val : ℝ) / q ≤ Int.fract x :=
    (div_le_iff₀ hqR).mpr (by simpa only [mul_comm] using hlo)
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  apply (le_div_iff₀ hqR).mpr
  rw [sub_mul, div_mul_cancel₀ _ hqR.ne']
  nlinarith

theorem torusGrid_coordinate_cover {d q : ℕ} (hq : 0 < q) (x : Fin d → ℝ) :
    ∃ (a : Fin d → Fin q) (b : Fin d → ℤ),
      ∀ i, |(b i : ℝ) - (x - torusGridCenter q a) i| ≤ 1 / (q : ℝ) := by
  let a := fun i => fractionalPartBin q hq (x i)
  let b := fun i => Int.floor (x i)
  refine ⟨a, b, ?_⟩
  intro i
  have heq : (b i : ℝ) - (x - torusGridCenter q a) i =
      ((fractionalPartBin q hq (x i)).val : ℝ) / q - Int.fract (x i) := by
    simp only [b, a, Pi.sub_apply, torusGridCenter, Int.fract]
    ring
  rw [heq]
  exact fractionalPartBin_center_error hq (x i)

theorem torusGrid_cover {d q : ℕ} (hq : 0 < q) (x : Fin d → ℝ) :
    ∃ (a : Fin d → Fin q) (b : Fin d → ℤ),
      dist (fun i => (b i : ℝ) - (x - torusGridCenter q a) i) 0 ≤ 1 / (q : ℝ) := by
  obtain ⟨a, b, hab⟩ := torusGrid_coordinate_cover hq x
  refine ⟨a, b, (dist_pi_le_iff (by positivity)).mpr ?_⟩
  intro i
  simpa only [Pi.zero_apply, Real.dist_eq, sub_zero] using hab i

end Erdos3

end

section

namespace Erdos3

open CircleFourier

theorem circle_grid_cover {q : ℕ} (hq : 0 < q) (x : UnitAddCircle) :
    ∃ a : Fin q, dist x (((a.val : ℝ) / q : ℝ) : UnitAddCircle) ≤ 1 / (q : ℝ) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) x
  refine ⟨fractionalPartBin q hq r, ?_⟩
  calc
    _ = ‖((Int.fract r - (fractionalPartBin q hq r).val / (q : ℝ) : ℝ) : UnitAddCircle)‖ := by
      rw [dist_eq_norm, AddCircle.coe_sub, AddCircle.coe_fract]
      rfl
    _ ≤ |Int.fract r - (fractionalPartBin q hq r).val / (q : ℝ)| := by
      exact QuotientAddGroup.norm_mk_le_norm
    _ ≤ 1 / (q : ℝ) := by
      simpa only [abs_sub_comm] using fractionalPartBin_center_error hq r

noncomputable def ambientTorusGrid {J : Type*} (q : ℕ) (a : J → Fin q) : J → UnitAddCircle :=
  fun j => (((a j).val : ℝ) / q : ℝ)

theorem ambientTorusGrid_cover {J : Type*} [Fintype J] {q : ℕ} (hq : 0 < q)
    (x : J → UnitAddCircle) : ∃ a : J → Fin q, dist x (ambientTorusGrid q a) ≤ 1 / (q : ℝ) := by
  choose a ha using fun j => circle_grid_cover hq (x j)
  exact ⟨a, (dist_pi_le_iff (by positivity)).mpr ha⟩

theorem ambientTorus_image_cover {G J : Type*} [Nonempty G] [Fintype J]
    (f : G → J → UnitAddCircle) {q : ℕ} (hq : 0 < q) :
    ∃ a : (J → Fin q) → G, ∀ x, ∃ i, dist (f x) (f (a i)) ≤ 2 / (q : ℝ) := by
  obtain ⟨a, ha⟩ := finite_cover_inside_image f (ambientTorusGrid q)
    (fun x => ambientTorusGrid_cover hq (f x))
  refine ⟨a, fun x => ?_⟩
  simpa only [mul_one_div] using ha x

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped NNReal

noncomputable def ambientTorusTent {J : Type*} [Fintype J] (q : ℕ) (x : J → UnitAddCircle) : ℝ :=
  max 0 (1 - (q : ℝ) / 4 * ‖x‖)

theorem ambientTorusTent_range {J : Type*} [Fintype J] (q : ℕ) (x : J → UnitAddCircle) :
    0 ≤ ambientTorusTent q x ∧ ambientTorusTent q x ≤ 1 := by
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  have h : 0 ≤ (q : ℝ) / 4 * ‖x‖ := by positivity
  linarith

theorem ambientTorusTent_ge_half {J : Type*} [Fintype J] {q : ℕ} (hq : 0 < q)
    (x : J → UnitAddCircle) (hx : ‖x‖ ≤ 2 / (q : ℝ)) : 1 / 2 ≤ ambientTorusTent q x := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have he := (le_div_iff₀ hq').mp hx
  apply le_trans _ (le_max_right _ _)
  nlinarith

theorem ambientTorusTent_support {J : Type*} [Fintype J] {q : ℕ} (hq : 0 < q)
    (x : J → UnitAddCircle) (hx : ambientTorusTent q x ≠ 0) : ‖x‖ < 4 / (q : ℝ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have he : 0 < 1 - (q : ℝ) / 4 * ‖x‖ := by
    by_contra h
    exact hx (max_eq_left (by linarith))
  apply (lt_div_iff₀ hq').mpr
  nlinarith

theorem ambientTorusTent_lipschitz {J : Type*} [Fintype J] (q : ℕ) :
    LipschitzWith ((q : ℝ≥0) / 4) (ambientTorusTent (J := J) q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |max 0 (1 - (q : ℝ) / 4 * ‖x‖) - max 0 (1 - (q : ℝ) / 4 * ‖y‖)| ≤ _
  calc
    _ ≤ |(1 - (q : ℝ) / 4 * ‖x‖) - (1 - (q : ℝ) / 4 * ‖y‖)| := by
      rw [max_comm 0 _, max_comm 0 _]
      exact abs_max_sub_max_le_abs _ _ _
    _ = (q : ℝ) / 4 * |‖x‖ - ‖y‖| := by
      rw [show (1 - (q : ℝ) / 4 * ‖x‖) - (1 - (q : ℝ) / 4 * ‖y‖) =
        -((q : ℝ) / 4) * (‖x‖ - ‖y‖) by ring, abs_mul, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ (q : ℝ) / 4)]
    _ ≤ _ := by
      simpa only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat, dist_eq_norm] using
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by positivity : 0 ≤ (q : ℝ) / 4)

end Erdos3

end

section

namespace Erdos3

theorem residue_quotient_double_bound {N q : ℕ} (hq : 0 < q) (hN : q ≤ N) :
    N ≤ 2 * q * (N / q) := by
  have hpos : 1 ≤ N / q := Nat.le_div_iff_mul_le hq |>.mpr (by simpa using hN)
  have hlt := Nat.lt_mul_div_succ N hq
  nlinarith

theorem exists_residue_circle_neighborhood_embedding {N q : ℕ} [NeZero N]
    (hq : 0 < q) (hN : q ≤ N) (c : UnitAddCircle) :
    ∃ e : Fin (N / q) ↪ ZMod N,
      ∀ a, dist (ZMod.toAddCircle (e a)) c ≤ 2 / (q : ℝ) := by
  obtain ⟨b, hb⟩ := circle_grid_cover (NeZero.pos N) c
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hqN : (q : ℝ) ≤ N := by exact_mod_cast hN
  have hdiv : N / q ≤ N := Nat.div_le_self N q
  let e : Fin (N / q) ↪ ZMod N :=
    ⟨fun a => (b.val : ZMod N) + a.val, by
      intro a a' h
      have hh : (a.val : ZMod N) = a'.val := add_left_cancel h
      have ha : a.val < N := a.isLt.trans_le hdiv
      have ha' : a'.val < N := a'.isLt.trans_le hdiv
      have hv := congrArg ZMod.val hh
      rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt ha'] at hv
      exact Fin.ext hv⟩
  refine ⟨e, fun a => ?_⟩
  have haq : (a.val : ℝ) * q ≤ N := by
    exact_mod_cast (Nat.mul_le_mul_right q a.isLt.le).trans (Nat.div_mul_le_self N q)
  have ha : (a.val : ℝ) / N ≤ 1 / q := by
    apply (div_le_div_iff₀ hNR hqR).mpr
    simpa only [one_mul] using haq
  have hd : dist (ZMod.toAddCircle (e a)) (ZMod.toAddCircle (b.val : ZMod N)) ≤
      (a.val : ℝ) / N := by
    change dist (ZMod.toAddCircle ((b.val : ZMod N) + (a.val : ZMod N))) _ ≤ _
    rw [map_add, dist_eq_norm, add_sub_cancel_left, ZMod.toAddCircle_natCast]
    calc
      _ ≤ ‖(a.val : ℝ) / N‖ := QuotientAddGroup.norm_mk_le_norm
      _ = _ := Real.norm_of_nonneg (by positivity)
  have hb' : dist (ZMod.toAddCircle (b.val : ZMod N)) c ≤ 1 / (N : ℝ) := by
    simpa only [ZMod.toAddCircle_natCast, dist_comm] using hb
  have hi : 1 / (N : ℝ) ≤ 1 / q := one_div_le_one_div_of_le hqR hqN
  exact (dist_triangle _ _ _).trans ((add_le_add (hd.trans ha) (hb'.trans hi)).trans
    (by ring_nf; exact le_rfl))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def centeredTorusTent {J : Type*} [Fintype J] (q : ℕ)
    (c x : J → UnitAddCircle) : ℝ := ambientTorusTent q (x - c)

theorem centeredTorusTent_range {J : Type*} [Fintype J] (q : ℕ)
    (c x : J → UnitAddCircle) : 0 ≤ centeredTorusTent q c x ∧ centeredTorusTent q c x ≤ 1 :=
  ambientTorusTent_range q (x - c)

theorem centeredTorusTent_lipschitz {J : Type*} [Fintype J] (q : ℕ)
    (c : J → UnitAddCircle) : LipschitzWith ((q : ℝ≥0) / 4) (centeredTorusTent q c) := by
  unfold centeredTorusTent
  simpa only [mul_one, Function.comp_def, sub_eq_add_neg] using
    (ambientTorusTent_lipschitz (J := J) q).comp (isometry_add_right (-c)).lipschitz

theorem centeredTorusTent_coordinate_support {J : Type*} [Fintype J] {q : ℕ}
    (hq : 0 < q) (c x : J → UnitAddCircle) (h : centeredTorusTent q c x ≠ 0) (j : J) :
    dist (x j) (c j) < 4 / (q : ℝ) := by
  have hnorm := ambientTorusTent_support hq (x - c) h
  calc
    dist (x j) (c j) = ‖(x - c) j‖ := dist_eq_norm _ _
    _ ≤ ‖x - c‖ := norm_le_pi_norm (x - c) j
    _ < _ := hnorm

theorem centeredTorusTent_residue_mean {J : Type*} [Fintype J] [DecidableEq J] (N : J → ℕ)
    [∀ j, NeZero (N j)] {q : ℕ} (hq : 0 < q) (hN : ∀ j, q ≤ N j)
    (c : J → UnitAddCircle) :
    1 / (2 * (2 * (q : ℝ)) ^ Fintype.card J) ≤
      𝔼 u : (j : J) → ZMod (N j), centeredTorusTent q c (fun j => ZMod.toAddCircle (u j)) := by
  classical
  choose e he using fun j => exists_residue_circle_neighborhood_embedding hq (hN j) (c j)
  let E : ((j : J) → Fin (N j / q)) → ((j : J) → ZMod (N j)) := fun a j => e j (a j)
  have hinj : Function.Injective E := by
    intro a b h
    funext j
    exact (e j).injective (congrFun h j)
  let W : ((j : J) → ZMod (N j)) → ℝ :=
    fun u => centeredTorusTent q c (fun j => ZMod.toAddCircle (u j))
  have hhalf (a : (j : J) → Fin (N j / q)) : 1 / 2 ≤ W (E a) := by
    apply ambientTorusTent_ge_half hq
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    simpa only [Pi.sub_apply, ← dist_eq_norm] using he j (a j)
  have hsum : (Fintype.card ((j : J) → Fin (N j / q)) : ℝ) / 2 ≤ ∑ u, W u := by
    have h : (∑ _ : (j : J) → Fin (N j / q), (1 / 2 : ℝ)) ≤ ∑ u, W u := calc
      _ ≤ ∑ a, W (E a) := Finset.sum_le_sum (fun a _ => hhalf a)
      _ = ∑ u ∈ Finset.univ.image E, W u :=
        (Finset.sum_image (fun a _ b _ hab => hinj hab)).symm
      _ ≤ ∑ u, W u := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun u _ _ => (centeredTorusTent_range q c _).1)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div] using h
  have hcard : (Fintype.card ((j : J) → ZMod (N j)) : ℝ) ≤
      (2 * (q : ℝ)) ^ Fintype.card J * (Fintype.card ((j : J) → Fin (N j / q)) : ℝ) := by
    simp only [Fintype.card_pi, ZMod.card, Fintype.card_fin, Nat.cast_prod]
    calc
      (∏ j, (N j : ℝ)) ≤ ∏ j, 2 * (q : ℝ) * (N j / q : ℕ) := by
        apply Finset.prod_le_prod₀
        · intro j _; positivity
        · intro j _; exact_mod_cast residue_quotient_double_bound hq (hN j)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hd : (0 : ℝ) < Fintype.card ((j : J) → ZMod (N j)) := by
    exact_mod_cast Fintype.card_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Fintype.expect_eq_sum_div_card]
  change 1 / (2 * (2 * (q : ℝ)) ^ Fintype.card J) ≤ (∑ u, W u) / _
  apply (le_div_iff₀ hd).mpr
  calc
    _ = (Fintype.card ((j : J) → ZMod (N j)) : ℝ) /
        (2 * (2 * (q : ℝ)) ^ Fintype.card J) := by ring
    _ ≤ _ := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * (2 * (q : ℝ)) ^ Fintype.card J)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsum
        (by positivity : 0 ≤ 2 * (2 * (q : ℝ)) ^ Fintype.card J)]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem localTent_translateSum_ge_half (d q : ℕ) (hq : 8 ≤ q) (x : Fin d → ℝ) :
    1 / 2 ≤ (localTentKernel d q hq).translateSum (torusGridCenter q) x := by
  obtain ⟨a, b, hab⟩ := torusGrid_cover (show 0 < q by omega) x
  exact (localTentKernel_ge_half hq _ hab).trans
    (((localTentKernel d q hq).kernel_le_periodicValue (x - torusGridCenter q a) b).trans
      ((localTentKernel d q hq).periodicValue_le_translateSum (torusGridCenter q) a x))

noncomputable def torusGridKernel (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) : PatchKernel d :=
  (localTentKernel d q hq).normalizedTranslate (torusGridCenter q) (1 / 2) (by norm_num)
    (fun x => by simpa using localTent_translateSum_ge_half d q hq x) a

theorem torusGridKernel_lip (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) :
    (torusGridKernel d q hq a).lip = (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) := by
  norm_num [torusGridKernel, PatchKernel.normalizedTranslate, localTentKernel]
  ring

theorem torusGridKernel_support (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q)
    (x : Fin d → ℝ) (hx : (torusGridKernel d q hq a).value x ≠ 0) :
    dist x 0 ≤ 2 / (q : ℝ) := by
  apply localTentKernel_support hq
  intro h
  apply hx
  change (localTentKernel d q hq).value x / _ = 0
  rw [h, zero_div]

theorem sum_torusGridKernel_periodicValue (d q : ℕ) (hq : 8 ≤ q) (x : Fin d → ℝ) :
    (∑ a : Fin d → Fin q, (torusGridKernel d q hq a).periodicValue (x - torusGridCenter q a)) = 1 :=
  (localTentKernel d q hq).sum_normalizedTranslate_periodicValue (torusGridCenter q)
    (1 / 2) (by norm_num) (fun x => by simpa using localTent_translateSum_ge_half d q hq x) x

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators NNReal

namespace PolynomialPatch

theorem ofCoordinates_value {σ : Type*} {s d : ℕ} (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i)) (Φ : PatchKernel d)
    (t : σ → ℝ) :
    (ofCoordinates w hw hws hmono P hP Φ).value t = Φ.periodicValue (fun i => aeval t (P i)) := by
  change ((ofCoordinates w hw hws hmono P hP Φ).form.slots t).patchValue Φ =
    (constantSlots (fun i => aeval t (P i))).patchValue Φ
  apply congrArg (fun A : TriangularSlots d => A.patchValue Φ)
  apply TriangularSlots.ext
  intro x i
  exact PolynomialSlots.ofCoordinates_center P hP t x i

end PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def polynomialTorusCell (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) : PolynomialPatch σ s d :=
  PolynomialPatch.ofCoordinates w hw hws hmono (fun i => P i - C (torusGridCenter q a i))
    (fun i => (weightedSupportLE _ _).sub_mem (hP i) (weightedSupportLE_C _ _ _))
    (torusGridKernel d q hq a)

theorem polynomialTorusCell_value (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) (t : σ → ℝ) :
    (polynomialTorusCell w hw hws hmono P hP q hq a).value t =
      (torusGridKernel d q hq a).periodicValue ((fun i => aeval t (P i)) - torusGridCenter q a) := by
  rw [polynomialTorusCell, PolynomialPatch.ofCoordinates_value]
  congr 1
  funext i
  simp

theorem polynomialTorusCell_lip (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) :
    (polynomialTorusCell w hw hws hmono P hP q hq a).kernel.lip =
      (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) := torusGridKernel_lip d q hq a

theorem sum_polynomialTorusCell_value (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i)
    (hws : ∀ i, w i ≤ s) (hmono : Monotone w) (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (t : σ → ℝ) :
    (∑ a : Fin d → Fin q, (polynomialTorusCell w hw hws hmono P hP q hq a).value t) = 1 := by
  simp only [polynomialTorusCell_value]
  exact sum_torusGridKernel_periodicValue d q hq _

theorem exists_polynomialTorusCell_score {Ω : Type*} [Fintype Ω]
    (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i) (hws : ∀ i, w i ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (t : Ω → σ → ℝ) (score : Ω → ℝ) {S : ℝ}
    (hS : S ≤ 𝔼 x, score x) :
    ∃ a : Fin d → Fin q,
      S / (q : ℝ) ^ d ≤ 𝔼 x, score x * (polynomialTorusCell w hw hws hmono P hP q hq a).value (t x) := by
  let : NeZero q := ⟨by omega⟩
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    exists_weighted_partition_score score
      (fun a x => (polynomialTorusCell w hw hws hmono P hP q hq a).value (t x))
      (fun x => sum_polynomialTorusCell_value w hw hws hmono P hP q hq (t x)) hS

end Erdos3

end

section

namespace Erdos3

theorem exists_torusCell_lift_offset {Ω : Type*} {d m q : ℕ}
    (hq : 8 ≤ q) (S : Set Ω) (M : Fin m → Fin d → ℤ) (a : Fin d → Fin q)
    (x : Ω → Fin d → ℝ) (k : Ω → Fin d → ℤ) (β : Ω → Fin m → ℤ) {K : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hmesh : 16 * K ≤ (q : ℝ))
    (hcell : ∀ u ∈ S, (torusGridKernel d q hq a).value
      (fun j => (k u j : ℝ) - (x u - torusGridCenter q a) j) ≠ 0)
    (hβ : ∀ u ∈ S, ∀ i, |(∑ j, (M i j : ℝ) * x u j) - β u i| ≤ 1 / 4) :
    ∃ c : Fin m → ℤ, ∀ u ∈ S, β u = fun i => c i + ∑ j, M i j * k u j := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  apply exists_integer_lift_offset S M (torusGridCenter q a) x k β hM
    (r := 2 / (q : ℝ)) (by positivity) _ _ hβ
  · have hsmall : 4 * K / (q : ℝ) ≤ 1 / 4 :=
      (div_le_iff₀ hqR).mpr (by linarith)
    calc
      2 * K * (2 / (q : ℝ)) + 1 / 2 = 4 * K / (q : ℝ) + 1 / 2 := by ring
      _ < 1 := by linarith
  · intro u hu j
    have h := torusGridKernel_support d q hq a _ (hcell u hu)
    have hc := (dist_le_pi_dist (fun j => (k u j : ℝ) - (x u - torusGridCenter q a) j) 0 j).trans h
    simp only [Real.dist_eq, Pi.zero_apply, sub_zero, Pi.sub_apply] at hc
    have heq : x u j - (k u j : ℝ) - torusGridCenter q a j =
        -((k u j : ℝ) - (x u j - torusGridCenter q a j)) := by ring
    simpa only [heq, abs_neg] using hc

end Erdos3

end

section

namespace Erdos3

namespace PatchKernel

variable {d : ℕ}

noncomputable def integerLift (Φ : PatchKernel d) (x : Fin d → ℝ) : Fin d → ℤ := by
  classical
  exact if h : ∃ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) ≠ 0 then h.choose else 0

theorem periodicValue_eq_integerLift (Φ : PatchKernel d) (x : Fin d → ℝ) :
    Φ.periodicValue x = Φ.value (fun j => (Φ.integerLift x j : ℝ) - x j) := by
  classical
  by_cases h : ∃ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) ≠ 0
  · simp only [integerLift, dite_eq_left h]
    exact (constantSlots x).patchValue_eq_of_nonzero Φ h.choose_spec
  · have hz : ∀ b : Fin d → ℤ, Φ.value (fun j => (b j : ℝ) - x j) = 0 := by simpa using h
    have hp : Φ.periodicValue x = 0 := (constantSlots x).patchValue_eq_zero Φ hz
    simpa only [integerLift, dite_eq_right h, hz] using hp

theorem integerLift_contributes (Φ : PatchKernel d) (x : Fin d → ℝ)
    (hx : Φ.periodicValue x ≠ 0) : Φ.value (fun j => (Φ.integerLift x j : ℝ) - x j) ≠ 0 := by
  rwa [← Φ.periodicValue_eq_integerLift x]

end PatchKernel

theorem exists_torusCell_affine_recovery {Ω : Type*} {d m q : ℕ}
    (hq : 8 ≤ q) (S : Set Ω) (M : Fin m → Fin d → ℤ) (a : Fin d → Fin q)
    (x : Ω → Fin d → ℝ) (β : Ω → Fin m → ℤ) {K : ℝ}
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hmesh : 16 * K ≤ (q : ℝ))
    (hactive : ∀ u ∈ S, (torusGridKernel d q hq a).periodicValue (x u - torusGridCenter q a) ≠ 0)
    (hβ : ∀ u ∈ S, ∀ i, |(∑ j, (M i j : ℝ) * x u j) - β u i| ≤ 1 / 4) :
    ∃ c : Fin m → ℤ, ∀ u ∈ S, β u = fun i => c i + ∑ j, M i j *
      (torusGridKernel d q hq a).integerLift (x u - torusGridCenter q a) j := by
  apply exists_torusCell_lift_offset hq S M a x
    (fun u => (torusGridKernel d q hq a).integerLift (x u - torusGridCenter q a)) β hM hmesh
  · intro u hu
    exact (torusGridKernel d q hq a).integerLift_contributes _ (hactive u hu)
  · exact hβ

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

theorem torusGrid_log_card (d q : ℕ) :
    Real.log (Fintype.card (Fin d → Fin q) : ℝ) = (d : ℝ) * Real.log q := by
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]

theorem torusGridKernel_lip_add_one_le (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) :
    ((torusGridKernel d q hq a).lip : ℝ) + 1 ≤ 4 * (q : ℝ) ^ (d + 1) := by
  rw [torusGridKernel_lip]
  push_cast
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ d := one_le_pow₀ hq1
  have hmul : (q : ℝ) ≤ (q : ℝ) * (q : ℝ) ^ d := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) q) (sub_nonneg.mpr hpow)]
  rw [pow_succ]
  nlinarith

theorem torusGridKernel_log_lip (d q : ℕ) (hq : 8 ≤ q) (a : Fin d → Fin q) :
    Real.log (((torusGridKernel d q hq a).lip : ℝ) + 1) ≤
      Real.log 4 + ((d : ℝ) + 1) * Real.log q := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h := Real.log_le_log (by positivity)
    (torusGridKernel_lip_add_one_le d q hq a)
  simpa only [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero _ hq0),
    Real.log_pow, Nat.cast_add, Nat.cast_one] using h

theorem exists_torus_lift_mesh {K : ℝ} (hK : 0 ≤ K) :
    ∃ q : ℕ, 8 ≤ q ∧ 16 * K ≤ (q : ℝ) ∧ (q : ℝ) ≤ 17 * (K + 1) := by
  let q := ⌈16 * (K + 1)⌉₊
  have hlo : 16 * (K + 1) ≤ (q : ℝ) := Nat.le_ceil _
  have hhi : (q : ℝ) < 16 * (K + 1) + 1 := Nat.ceil_lt_add_one (by positivity)
  refine ⟨q, ?_, by linarith, by linarith⟩
  have hq : (8 : ℝ) ≤ q := by linarith
  exact_mod_cast hq

theorem exists_polynomialTorusCell_exp_score {σ Ω : Type*} [Fintype Ω] {s d : ℕ}
    (w : Fin d → ℕ) (hw : ∀ i, 1 ≤ w i) (hws : ∀ i, w i ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ)
    (hP : ∀ i, P i ∈ weightedSupportLE (fun _ : σ => 1) (w i))
    (q : ℕ) (hq : 8 ≤ q) (t : Ω → σ → ℝ) (score : Ω → ℝ) (p : ℝ)
    (hscore : Real.exp (-p) ≤ 𝔼 x, score x) :
    ∃ a : Fin d → Fin q,
      Real.exp (-(p + (d : ℝ) * Real.log q)) ≤
        𝔼 x, score x * (polynomialTorusCell w hw hws hmono P hP q hq a).value (t x) := by
  obtain ⟨a, ha⟩ := exists_polynomialTorusCell_score w hw hws hmono P hP q hq t score hscore
  refine ⟨a, ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [show -(p + (d : ℝ) * Real.log q) = -p - (d : ℝ) * Real.log q by ring,
    Real.exp_sub, Real.exp_nat_mul, Real.exp_log hq0]
  exact ha

end Erdos3

end

end OAI
