import GowersSzemeredi.Sections08_09
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Bertrand

/-!
# The coloring consequence of the length-four theorem

This module isolates the elementary, but quantitatively delicate, passage
from the cyclic density theorem to the finite coloring formulation.  The
proof embeds a largest color class into a prime cyclic group whose modulus is
larger than four times the interval, so a modular four-term progression lifts
without wraparound.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private noncomputable def coloringClass (N r : Nat)
    (color : Nat → Fin r) (c : Fin r) : Finset Nat :=
  (Finset.Icc 1 N).filter fun x => color x = c

private lemma coloringClass_subset (N r : Nat) (color : Nat → Fin r)
    (c : Fin r) : coloringClass N r color c ⊆ Finset.Icc 1 N :=
  Finset.filter_subset _ _

private lemma exists_large_coloringClass (N r : Nat) (hr : 0 < r)
    (color : Nat → Fin r) :
    ∃ c : Fin r,
      (N : Real) / r ≤ (coloringClass N r color c).card := by
  classical
  letI : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have hmap : ∀ x ∈ Finset.Icc 1 N,
      color x ∈ (Finset.univ : Finset (Fin r)) := by simp
  have hsumNat :
      ∑ c : Fin r, (coloringClass N r color c).card = N := by
    have hfiber := Finset.card_eq_sum_card_fiberwise
      (s := Finset.Icc 1 N) (t := (Finset.univ : Finset (Fin r)))
      (f := color) hmap
    change ∑ c : Fin r,
      ((Finset.Icc 1 N).filter fun x => color x = c).card = N
    rw [← hfiber, Nat.card_Icc]
    omega
  have hsumReal :
      ∑ c : Fin r, ((coloringClass N r color c).card : Real) = N := by
    exact_mod_cast hsumNat
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have hconstant : ∑ _c : Fin r, (N : Real) / r = N := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  have hsumLe :
      ∑ c : Fin r, (N : Real) / r ≤
        ∑ c : Fin r, ((coloringClass N r color c).card : Real) := by
    rw [hconstant, hsumReal]
  obtain ⟨c, _hc, hc⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (Fin r)))
    (f := fun _c => (N : Real) / r)
    (g := fun c => ((coloringClass N r color c).card : Real))
    Finset.univ_nonempty hsumLe
  exact ⟨c, hc⟩

private noncomputable def coloringModSet (p N r : Nat) [NeZero p]
    (color : Nat → Fin r) (c : Fin r) : Finset (ZMod p) :=
  (coloringClass N r color c).image fun x : Nat => (x : ZMod p)

private lemma coloringModSet_card {p N r : Nat} [NeZero p]
    (color : Nat → Fin r) (c : Fin r) (hNp : N < p) :
    (coloringModSet p N r color c).card =
      (coloringClass N r color c).card := by
  classical
  unfold coloringModSet
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have hxN := (Finset.mem_Icc.mp (coloringClass_subset N r color c hx)).2
  have hyN := (Finset.mem_Icc.mp (coloringClass_subset N r color c hy)).2
  have hval := congrArg ZMod.val hxy
  simpa [ZMod.val_natCast_of_lt (hxN.trans_lt hNp),
    ZMod.val_natCast_of_lt (hyN.trans_lt hNp)] using hval

private lemma mem_coloringModSet {p N r : Nat} [NeZero p]
    {color : Nat → Fin r} {c : Fin r} {z : ZMod p} :
    z ∈ coloringModSet p N r color c ↔
      ∃ x ∈ coloringClass N r color c, (x : ZMod p) = z := by
  classical
  simp only [coloringModSet, Finset.mem_image]

private lemma natCast_eq_of_lt {p x y : Nat} [NeZero p]
    (hx : x < p) (hy : y < p) (hxy : (x : ZMod p) = (y : ZMod p)) :
    x = y := by
  have hval := congrArg ZMod.val hxy
  simpa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hval

private theorem monochromatic_of_modular_color_class
    {p N r : Nat} [NeZero p] (color : Nat → Fin r) (c : Fin r)
    (hp : 4 * N < p) (hAP : HasModAP (coloringModSet p N r color c) 4) :
    HasMonochromaticAP N r color 4 := by
  classical
  obtain ⟨a, d, hd, hmem⟩ := hAP
  have hdne : d ≠ 0 := bne_iff_ne.mp hd
  have hpoint (i : Nat) (hi : i < 4) :
      ∃ x : Nat, x ∈ coloringClass N r color c ∧
        (x : ZMod p) = a + (i : Nat) * d := by
    exact mem_coloringModSet.mp (hmem i hi)
  obtain ⟨x0, hx0, hx0eq⟩ := hpoint 0 (by omega)
  obtain ⟨x1, hx1, hx1eq⟩ := hpoint 1 (by omega)
  obtain ⟨x2, hx2, hx2eq⟩ := hpoint 2 (by omega)
  obtain ⟨x3, hx3, hx3eq⟩ := hpoint 3 (by omega)
  have hx0I := coloringClass_subset N r color c hx0
  have hx1I := coloringClass_subset N r color c hx1
  have hx2I := coloringClass_subset N r color c hx2
  have hx3I := coloringClass_subset N r color c hx3
  have hx0N := (Finset.mem_Icc.mp hx0I).2
  have hx1N := (Finset.mem_Icc.mp hx1I).2
  have hx2N := (Finset.mem_Icc.mp hx2I).2
  have hx3N := (Finset.mem_Icc.mp hx3I).2
  have h02cast : ((x0 + x2 : Nat) : ZMod p) =
      ((2 * x1 : Nat) : ZMod p) := by
    push_cast
    rw [hx0eq, hx1eq, hx2eq]
    ring
  have h13cast : ((x1 + x3 : Nat) : ZMod p) =
      ((2 * x2 : Nat) : ZMod p) := by
    push_cast
    rw [hx1eq, hx2eq, hx3eq]
    ring
  have h02 : x0 + x2 = 2 * x1 :=
    natCast_eq_of_lt (by omega) (by omega) h02cast
  have h13 : x1 + x3 = 2 * x2 :=
    natCast_eq_of_lt (by omega) (by omega) h13cast
  have hx01 : x0 ≠ x1 := by
    intro h
    subst x1
    apply hdne
    have heq : a + d = a := by simpa using hx1eq.symm.trans hx0eq
    exact add_eq_left.mp heq
  have hx0data := Finset.mem_filter.mp hx0
  have hx1data := Finset.mem_filter.mp hx1
  have hx2data := Finset.mem_filter.mp hx2
  have hx3data := Finset.mem_filter.mp hx3
  rcases lt_or_gt_of_ne hx01 with hinc | hdec
  · refine ⟨x0, x1 - x0, c, Nat.sub_pos_of_lt hinc, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ⟨Finset.mem_Icc.mp hx0data.1, hx0data.2⟩
    · simpa [Nat.add_sub_of_le hinc.le] using
        ⟨Finset.mem_Icc.mp hx1data.1, hx1data.2⟩
    · have heq : x0 + 2 * (x1 - x0) = x2 := by omega
      simpa [heq] using ⟨Finset.mem_Icc.mp hx2data.1, hx2data.2⟩
    · have heq : x0 + 3 * (x1 - x0) = x3 := by omega
      simpa [heq] using ⟨Finset.mem_Icc.mp hx3data.1, hx3data.2⟩
  · refine ⟨x3, x2 - x3, c, ?_, ?_⟩
    · omega
    · intro i hi
      interval_cases i
      · simpa using ⟨Finset.mem_Icc.mp hx3data.1, hx3data.2⟩
      · have heq : x3 + (x2 - x3) = x2 := by omega
        simpa [heq] using ⟨Finset.mem_Icc.mp hx2data.1, hx2data.2⟩
      · have heq : x3 + 2 * (x2 - x3) = x1 := by omega
        simpa [heq] using ⟨Finset.mem_Icc.mp hx1data.1, hx1data.2⟩
      · have heq : x3 + 3 * (x2 - x3) = x0 := by omega
        simpa [heq] using ⟨Finset.mem_Icc.mp hx0data.1, hx0data.2⟩

/-! ### The logarithmic parameter conversion -/

private lemma coloring_bound_forces_four_le
    {N r : Nat} {c : Real} (hc : 0 < c) (hr : 0 < r)
    (hbound : (r : Real) ≤ (Real.log (Real.log N)) ^ c) :
    4 ≤ N := by
  have hrOne : (1 : Real) ≤ r := by exact_mod_cast hr
  by_contra hN
  have hNle : N ≤ 3 := by omega
  interval_cases N
  · norm_num [Real.zero_rpow hc.ne'] at hbound
    omega
  · norm_num [Real.zero_rpow hc.ne'] at hbound
    omega
  · let u : Real := Real.log (Real.log 2)
    have hlogTwoPos : 0 < Real.log 2 := by positivity
    have hlogTwoHalf : (1 / 2 : Real) < Real.log 2 :=
      (by norm_num : (1 / 2 : Real) < 0.6931471803).trans
        Real.log_two_gt_d9
    have hlogTwoLtOne : Real.log 2 < 1 :=
      Real.log_two_lt_d9.trans (by norm_num)
    have huNeg : u < 0 := by
      exact Real.log_neg hlogTwoPos hlogTwoLtOne
    have hexpNegOne : Real.exp (-1) < Real.log 2 := by
      have hinv : (Real.exp 1)⁻¹ < (1 / 2 : Real) := by
        simpa only [one_div] using
          one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 2)
            Real.exp_one_gt_two
      simpa [Real.exp_neg] using hinv.trans hlogTwoHalf
    have huLower : -1 < u := by
      exact (Real.lt_log_iff_exp_lt hlogTwoPos).2 hexpNegOne
    have habs : |u| < 1 := by rw [abs_of_neg huNeg]; linarith
    have habsPow : |u| ^ c < 1 :=
      Real.rpow_lt_one (abs_nonneg u) habs hc
    have huPow : u ^ c < 1 := by
      calc
        u ^ c ≤ |u ^ c| := le_abs_self _
        _ ≤ |u| ^ c := Real.abs_rpow_le_abs_rpow u c
        _ < 1 := habsPow
    have : (r : Real) < 1 := by
      calc
        (r : Real) ≤ (Real.log (Real.log (2 : Nat))) ^ c := by
          simpa only [Nat.cast_ofNat] using hbound
        _ = u ^ c := rfl
        _ < 1 := huPow
    linarith
  · have hthreePos : (0 : Real) < 3 := by norm_num
    have hlogThreePos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlogThreeLtTwo : Real.log 3 < 2 := by
      apply (Real.log_lt_iff_lt_exp hthreePos).2
      have hsq : (3 : Real) < (Real.exp 1) ^ 2 := by
        nlinarith [Real.exp_one_gt_two]
      simpa [← Real.exp_nat_mul] using hsq
    have hlogThreeLtExpOne : Real.log 3 < Real.exp 1 :=
      hlogThreeLtTwo.trans Real.exp_one_gt_two
    have hloglogThreeLtOne : Real.log (Real.log 3) < 1 := by
      exact (Real.log_lt_iff_lt_exp hlogThreePos).2 hlogThreeLtExpOne
    have hlogThreeGtOne : 1 < Real.log 3 := by
      exact (Real.lt_log_iff_exp_lt hthreePos).2 Real.exp_one_lt_three
    have hloglogThreeNonneg : 0 ≤ Real.log (Real.log 3) :=
      (Real.log_pos hlogThreeGtOne).le
    have hpow : (Real.log (Real.log 3)) ^ c < 1 :=
      Real.rpow_lt_one hloglogThreeNonneg hloglogThreeLtOne hc
    have : (r : Real) < 1 := by
      calc
        (r : Real) ≤ (Real.log (Real.log (3 : Nat))) ^ c := by
          simpa only [Nat.cast_ofNat] using hbound
        _ < 1 := hpow
    linarith

private lemma coloring_loglog_pos {N r : Nat} {c : Real}
    (hc : 0 < c) (hr : 0 < r)
    (hbound : (r : Real) ≤ (Real.log (Real.log N)) ^ c) :
    0 < Real.log (Real.log N) := by
  have hNfour := coloring_bound_forces_four_le hc hr hbound
  have hNpos : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogNGtOne : 1 < Real.log N := by
    exact (Real.lt_log_iff_exp_lt hNpos).2
      (Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 ≤ N by omega)))
  exact Real.log_pos hlogNGtOne

private lemma coloring_parameter_bound
    {C : Real} (hC : 0 < C) {N r : Nat} (hr : 2 ≤ r)
    (hbound : (r : Real) ≤ (Real.log (Real.log N)) ^
      (16 * (C + 1))⁻¹) :
    ((16 : Real) * r) ^ C ≤ Real.log (Real.log N) := by
  let L : Real := Real.log (Real.log N)
  let D : Real := 16 * (C + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < D⁻¹ := inv_pos.mpr hD
  have hL : 0 < L := by
    exact coloring_loglog_pos hc (show 0 < r by omega)
      (by simpa only [L, D] using hbound)
  have hrReal : (0 : Real) < r := by exact_mod_cast (by omega : 0 < r)
  have hrTwo : (2 : Real) ≤ r := by exact_mod_cast hr
  have hLone : 1 < L := by
    by_contra h
    have hLle : L ≤ 1 := le_of_not_gt h
    have hpowLe : L ^ D⁻¹ ≤ 1 := Real.rpow_le_one hL.le hLle hc.le
    linarith
  have hlogr : Real.log r ≤ D⁻¹ * Real.log L := by
    have := Real.log_le_log hrReal (by simpa only [L, D] using hbound)
    rwa [Real.log_rpow hL] at this
  have hlogTwoLe : Real.log 2 ≤ Real.log r :=
    Real.log_le_log (by norm_num) hrTwo
  have hDlogr : D * Real.log r ≤ Real.log L := by
    calc
      D * Real.log r ≤ D * (D⁻¹ * Real.log L) :=
        mul_le_mul_of_nonneg_left hlogr hD.le
      _ = Real.log L := by field_simp
  have hDlogTwo : D * Real.log 2 ≤ Real.log L := by
    exact (mul_le_mul_of_nonneg_left hlogTwoLe hD.le).trans hDlogr
  have hlogL : 0 ≤ Real.log L := (Real.log_pos hLone).le
  have hscaleTwo := mul_le_mul_of_nonneg_left hDlogTwo
    (show (0 : Real) ≤ 4 * C by positivity)
  have hscaleR := mul_le_mul_of_nonneg_left hDlogr hC.le
  have hcoefficient : 5 * C ≤ D := by dsimp [D]; linarith
  have hscaleCoefficient := mul_le_mul_of_nonneg_right hcoefficient hlogL
  have htarget : C * (4 * Real.log 2 + Real.log r) ≤ Real.log L := by
    nlinarith
  apply (Real.log_le_log_iff
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) hrReal) C) hL).mp
  rw [Real.log_rpow (mul_pos (by norm_num) hrReal),
    Real.log_mul (by norm_num : (16 : Real) ≠ 0) hrReal.ne',
    show Real.log (16 : Real) = 4 * Real.log 2 by
      rw [show (16 : Real) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num]
  exact htarget

/-! ### Corollary 8.3 from Theorem 8.2 -/

/-- The cyclic length-four theorem implies the finite coloring formulation.
The explicit exponent chosen here is deliberately conservative: it absorbs
the factor lost when the largest color class is embedded into a prime cyclic
group four times larger than the original interval. -/
theorem corollary_8_3_holds_of_theorem_8_2
    (h82 : theorem_8_2) : corollary_8_3 := by
  obtain ⟨C, hC, hmain⟩ := h82
  let c : Real := (16 * (C + 1))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro N r hr hbound color
  have hNfour : 4 ≤ N := coloring_bound_forces_four_le hc hr hbound
  by_cases hrOne : r = 1
  · subst r
    let col : Fin 1 := 0
    refine ⟨1, 1, col, by omega, ?_⟩
    intro i hi
    have hmem : 1 + i ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      omega
    exact ⟨by simpa using hmem, Subsingleton.elim _ _⟩
  have hrTwo : 2 ≤ r := by omega
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  letI : NeZero p := ⟨hpPrime.ne_zero⟩
  letI : Fact p.Prime := ⟨hpPrime⟩
  obtain ⟨col, hclass⟩ := exists_large_coloringClass N r hr color
  let A : Finset (ZMod p) := coloringModSet p N r color col
  let delta : Real := (A.card : Real) / p
  have hNp : N < p := by omega
  have hAcard : (N : Real) / r ≤ A.card := by
    rw [show A.card = (coloringClass N r color col).card by
      exact coloringModSet_card color col hNp]
    exact hclass
  have hpReal : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have hNReal : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
  have hpUpperNat : p ≤ 8 * N := by omega
  have hpUpperReal : (p : Real) ≤ 8 * N := by exact_mod_cast hpUpperNat
  have hfrac : (p : Real) / (16 * r) ≤ (N : Real) / r := by
    apply (div_le_div_iff₀ (by positivity : (0 : Real) < 16 * r) hrReal).2
    nlinarith
  have hdeltaLower : (1 : Real) / (16 * r) ≤ delta := by
    rw [show delta = (A.card : Real) / p by rfl,
      le_div_iff₀ hpReal]
    calc
      (1 : Real) / (16 * r) * p = (p : Real) / (16 * r) := by ring
      _ ≤ (N : Real) / r := hfrac
      _ ≤ A.card := hAcard
  have hdelta : 0 < delta :=
    (div_pos (by norm_num) (by positivity : (0 : Real) < 16 * r)).trans_le
      hdeltaLower
  have hdeltaCard : (A.card : Real) = delta * p := by
    dsimp only [delta]
    field_simp
  have hinvDelta : (1 : Real) / delta ≤ 16 * r := by
    apply (div_le_iff₀ hdelta).2
    have hscaled := mul_le_mul_of_nonneg_left hdeltaLower
      (show (0 : Real) ≤ 16 * r by positivity)
    have hcancel : (16 : Real) * r * (1 / (16 * r)) = 1 := by
      field_simp
    rw [hcancel] at hscaled
    simpa only [mul_comm] using hscaled
  have hparameter : ((1 : Real) / delta) ^ C ≤
      Real.log (Real.log N) := by
    have hbase : (0 : Real) ≤ 1 / delta := (div_pos (by norm_num) hdelta).le
    have hmono := Real.rpow_le_rpow hbase hinvDelta hC.le
    have hfinal := coloring_parameter_bound hC hrTwo
      (by simpa only [c] using hbound)
    exact hmono.trans hfinal
  have hlogN : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hthresholdN :
      Real.exp (Real.exp (((1 : Real) / delta) ^ C)) ≤ N := by
    calc
      Real.exp (Real.exp (((1 : Real) / delta) ^ C)) ≤
          Real.exp (Real.exp (Real.log (Real.log N))) := by
        exact (Real.exp_le_exp).2 ((Real.exp_le_exp).2 hparameter)
      _ = N := by rw [Real.exp_log hlogN, Real.exp_log hNReal]
  have hthresholdP :
      Real.exp (Real.exp (((1 : Real) / delta) ^ C)) ≤ p :=
    hthresholdN.trans (by exact_mod_cast hNp.le)
  have hmodAP : HasModAP A 4 :=
    hmain p A delta hdelta hdeltaCard hthresholdP
  exact monochromatic_of_modular_color_class color col hpLower hmodAP

end LeanProofs.GowersSzemeredi
