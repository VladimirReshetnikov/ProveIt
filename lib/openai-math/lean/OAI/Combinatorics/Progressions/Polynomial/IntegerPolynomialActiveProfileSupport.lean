/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import OAI.Combinatorics.Progressions.Dynamics.CoefficientProfileBudget
import OAI.Combinatorics.Progressions.Geometry.FixedSupportRawArray
import OAI.Combinatorics.Progressions.Lattices.IntegerAxisPrincipalLaw
import OAI.Combinatorics.Progressions.Lattices.IntegerAxisTailLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def monomialExponentSet {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact Finset.univ.image e

noncomputable def scaledAffinePolynomial {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (H : ℝ) (T : K → ℝ) (c w r : J → ℝ) : MvPolynomial K ℝ :=
  monomialArrayPolynomial e (fun j => H*(c j+w j*r j)/monomialScale T (e j))

theorem scaledAffinePolynomial_support {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (H : ℝ) (T : K → ℝ) (c w r : J → ℝ) :
    (scaledAffinePolynomial e H T c w r).support ⊆ monomialExponentSet e := by
  classical
  intro m hm
  obtain ⟨j, rfl⟩ := monomialArrayPolynomial_support_subset e _ hm
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem scaledAffinePolynomial_coeff {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (he : Function.Injective e) (H : ℝ) (T : K → ℝ) (c w r : J → ℝ) (j : J) :
    (scaledAffinePolynomial e H T c w r).coeff (e j) =
      H*(c j+w j*r j)/monomialScale T (e j) :=
  monomialArrayPolynomial_coeff e he _ j

theorem scaledAffinePolynomial_normalized_coeff {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (he : Function.Injective e) (H : ℝ) (hH : H ≠ 0)
    (T : K → ℝ) (hT : ∀ k, 0 < T k) (c w r : J → ℝ) (j : J) :
    (scaledAffinePolynomial e H T c w r).coeff (e j)*monomialScale T (e j)/H = c j+w j*r j := by
  rw [scaledAffinePolynomial_coeff e he]
  field_simp [(monomialScale_pos T hT (e j)).ne']

theorem fixedNonprincipalExponents_degree {J B K : Type*} [Fintype J] [Fintype B]
    (e : J → K →₀ ℕ) (principal : B → K →₀ ℕ) {degree : ℕ}
    (he : ∀ j, (e j).sum (fun _ n => n) ≤ degree) (m : K →₀ ℕ)
    (hm : m ∈ fixedNonprincipalExponents (monomialExponentSet e) principal) :
    m.sum (fun _ n => n) ≤ degree := by
  classical
  have hmem : m ∈ monomialExponentSet e := (Finset.mem_sdiff.mp hm).1
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
  exact he j

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem monomial_abs_le_scale {K : Type*} (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k)
    (e : K →₀ ℕ) : |∏ k ∈ e.support, x k ^ e k| ≤ monomialScale T e := by
  classical
  rw [Finset.abs_prod]
  change (∏ k ∈ e.support, |x k ^ e k|) ≤ ∏ k ∈ e.support, T k ^ e k
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro k _
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hx k) _

theorem monomialArrayPolynomial_box_bound {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a : J → ℝ) (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤
      ∑ j, |a j| * monomialScale T (e j) := by
  rw [monomialArrayPolynomial_eval]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (monomial_abs_le_scale T x hx (e j)) (abs_nonneg _)

theorem monomialArrayPolynomial_box_budget {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (a B : J → ℝ) (T x : K → ℝ) (hx : ∀ k, |x k| ≤ T k)
    (ha : ∀ j, |a j| * monomialScale T (e j) ≤ B j) :
    |MvPolynomial.eval x (monomialArrayPolynomial e a)| ≤ ∑ j, B j :=
  (monomialArrayPolynomial_box_bound e a T x hx).trans (Finset.sum_le_sum (fun j _ => ha j))

theorem scaledAffinePolynomial_box_bound {J K : Type*} [Fintype J]
    (e : J → K →₀ ℕ) (T : K → ℝ) (hT : ∀ k, 0 < T k) (c w r : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hr : ∀ j, |r j| ≤ 1) (x : K → ℝ) (hx : ∀ k, |x k| ≤ T k) :
    |MvPolynomial.eval x (scaledAffinePolynomial e 1 T c w r)| ≤ ∑ j, (|c j| + w j) := by
  apply monomialArrayPolynomial_box_budget e _ (fun j => |c j| + w j) T x hx
  intro j
  simp only [one_mul, abs_div, abs_of_pos (monomialScale_pos T hT (e j)),
    div_mul_cancel₀ _ (monomialScale_pos T hT (e j)).ne']
  calc
    |c j + w j * r j| ≤ |c j| + |w j * r j| := abs_add_le _ _
    _ ≤ |c j| + w j := by
      rw [abs_mul, abs_of_nonneg (hw j)]
      exact add_le_add le_rfl (mul_le_of_le_one_right (hw j) (hr j))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerMonomialArrayPolynomial {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) : MvPolynomial V ℤ :=
  ∑ j, MvPolynomial.monomial (e j) (a j)

theorem integerMonomialArrayPolynomial_map {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) :
    MvPolynomial.map (Int.castRingHom ℝ) (integerMonomialArrayPolynomial e a) =
      monomialArrayPolynomial e (fun j => (a j : ℝ)) := by
  simp only [integerMonomialArrayPolynomial, monomialArrayPolynomial, map_sum,
    MvPolynomial.map_monomial, Int.coe_castRingHom]

theorem integerMonomialArrayPolynomial_normalized_eval {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) (K : ℝ) (x : V → ℤ) :
    MvPolynomial.eval (fun v => (x v : ℝ)) (monomialArrayPolynomial e (fun j => (a j : ℝ) / K)) =
      (MvPolynomial.eval x (integerMonomialArrayPolynomial e a) : ℝ) / K := by
  classical
  simp only [integerMonomialArrayPolynomial, monomialArrayPolynomial, map_sum,
    MvPolynomial.eval_monomial, Finsupp.prod, Int.cast_sum, Int.cast_mul,
    Int.cast_prod, Int.cast_pow, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integerMonomialArrayPolynomial_degree {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) {s : ℕ} (he : ∀ j, (e j).sum (fun _ n => n) ≤ s) :
    (integerMonomialArrayPolynomial e a).totalDegree ≤ s := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (he j)

end Erdos3

end

section

namespace Erdos3
open MvPolynomial VectorPolynomial
open scoped BigOperators Classical

theorem modularMonomialArrayPolynomial_selected {E K R A : Type*}
    [Fintype E] [Fintype A] [CommRing R] (exponent : E → K →₀ ℕ)
    (slot : A → E) (hinj : Function.Injective slot)
    (fixed : E → R) (c : A → R) :
    (∑ e, MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e)) =
      (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot),
        MvPolynomial.monomial (exponent e) (fixed e)) +
      ∑ a, MvPolynomial.monomial (exponent (slot a)) (c a) := by
  let F : E → MvPolynomial K R :=
    fun e => MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e)
  have himage : Finset.univ.filter (fun e => e ∈ Set.range slot) = Finset.univ.image slot := by
    ext e
    simp
  have hsum := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun e : E => e ∈ Set.range slot) (f := F)
  rw [himage, Finset.sum_image (fun a _ b _ hab => hinj hab)] at hsum
  have hs : (∑ a, F (slot a)) = ∑ a, MvPolynomial.monomial (exponent (slot a)) (c a) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [F, hinj.extend_apply]
  have hu : (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), F e) =
      ∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot),
        MvPolynomial.monomial (exponent e) (fixed e) := by
    apply Finset.sum_congr rfl
    intro e he
    change MvPolynomial.monomial (exponent e) (Function.extend slot c fixed e) = _
    rw [Function.extend_apply' c fixed e (Finset.mem_filter.mp he).2]
  rw [hs, hu] at hsum
  exact hsum.symm.trans (add_comm _ _)

noncomputable def modularBoundedCoefficientPolynomial {K R : Type*}
    [Fintype K] [CommRing R] (h : ℕ)
    (c : BoundedCoefficientExponent K h → R) : MvPolynomial K R :=
  ∑ e, monomial e.val (c e)

theorem modularBoundedCoefficientPolynomial_degree {K R : Type*}
    [Fintype K] [CommRing R] (h : ℕ)
    (c : BoundedCoefficientExponent K h → R) :
    (modularBoundedCoefficientPolynomial h c).totalDegree ≤ h := by
  unfold modularBoundedCoefficientPolynomial
  apply totalDegree_finsetSum_le
  intro e _
  exact (totalDegree_monomial_le e.val (c e)).trans e.property

theorem modularBoundedCoefficientPolynomial_integer_reduce {K : Type*} [Fintype K]
    (h N : ℕ) (c : BoundedCoefficientExponent K h → ℤ) :
    modularBoundedCoefficientPolynomial h (fun e => (c e : ZMod N)) =
      (integerMonomialArrayPolynomial Subtype.val c).map (Int.castRingHom (ZMod N)) := by
  simp only [modularBoundedCoefficientPolynomial, integerMonomialArrayPolynomial,
    map_sum, MvPolynomial.map_monomial, Int.coe_castRingHom]

noncomputable def modularUnselectedCoefficientPolynomial {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h)
    (fixed : BoundedCoefficientExponent K h → R) : MvPolynomial K R :=
  ∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), monomial e.val (fixed e)

theorem modularBoundedCoefficientPolynomial_selected {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h) (hinj : Function.Injective slot)
    (fixed : BoundedCoefficientExponent K h → R) (c : A → R) :
    modularBoundedCoefficientPolynomial h (Function.extend slot c fixed) =
      modularUnselectedCoefficientPolynomial h slot fixed +
        ∑ a, monomial (slot a).val (c a) := by
  let F : BoundedCoefficientExponent K h → MvPolynomial K R :=
    fun e => monomial e.val (Function.extend slot c fixed e)
  have himage : Finset.univ.filter (fun e => e ∈ Set.range slot) = Finset.univ.image slot := by
    ext e
    simp
  have hsum := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun e : BoundedCoefficientExponent K h => e ∈ Set.range slot) (f := F)
  rw [himage, Finset.sum_image (fun a _ b _ hab => hinj hab)] at hsum
  have hselected : (∑ a, F (slot a)) = ∑ a, monomial (slot a).val (c a) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [F, hinj.extend_apply]
  have hunselected : (∑ e ∈ Finset.univ.filter (fun e => e ∉ Set.range slot), F e) =
      modularUnselectedCoefficientPolynomial h slot fixed := by
    apply Finset.sum_congr rfl
    intro e he
    change MvPolynomial.monomial e.val (Function.extend slot c fixed e) = _
    rw [Function.extend_apply' c fixed e (Finset.mem_filter.mp he).2]
  rw [hselected, hunselected] at hsum
  exact hsum.symm.trans (add_comm _ _)

theorem modularBoundedCoefficientPolynomial_selected_top {K R A : Type*}
    [Fintype K] [Fintype A] [CommRing R] (h : ℕ)
    (slot : A → BoundedCoefficientExponent K h) (hinj : Function.Injective slot)
    (hdegree : ∀ a, (slot a).val.degree = h)
    (fixed : BoundedCoefficientExponent K h → R) (c : A → R) :
    homogeneousComponent h (modularBoundedCoefficientPolynomial h (Function.extend slot c fixed)) =
      homogeneousComponent h (modularUnselectedCoefficientPolynomial h slot fixed) +
        ∑ a, monomial (slot a).val (c a) := by
  rw [modularBoundedCoefficientPolynomial_selected h slot hinj fixed c, map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply homogeneousComponent_eq_self
  exact isHomogeneous_monomial (c a) (hdegree a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_integerPolynomial_remainder {J V D : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (c y : J → D → ℝ) {h : ℕ}
    (he : ∀ j, (e j).sum (fun _ k => k) ≤ h)
    (hdiff : ∀ j d, ∃ z : ℤ, c j d - y j d = z) :
    ∃ β : D → MvPolynomial V ℤ, ∀ d,
      monomialArrayPolynomial e (fun j => c j d) = monomialArrayPolynomial e (fun j => y j d) +
        MvPolynomial.map (Int.castRingHom ℝ) (β d) ∧ (β d).totalDegree ≤ h := by
  classical
  choose z hz using hdiff
  refine ⟨fun d => integerMonomialArrayPolynomial e (fun j => z j d), ?_⟩
  intro d
  refine ⟨?_, integerMonomialArrayPolynomial_degree e _ he⟩
  rw [integerMonomialArrayPolynomial_map]
  have hc (j) : c j d = y j d + (z j d : ℝ) := by linarith [hz j d]
  simp only [monomialArrayPolynomial, hc, map_add, Finset.sum_add_distrib]

theorem integerPolynomial_remainder_eval {V : Type*} (c y : MvPolynomial V ℝ)
    (β : MvPolynomial V ℤ) (h : c = y + MvPolynomial.map (Int.castRingHom ℝ) β) (x : V → ℤ) :
    MvPolynomial.eval (fun v => (x v : ℝ)) c =
      MvPolynomial.eval (fun v => (x v : ℝ)) y + (MvPolynomial.eval x β : ℝ) := by
  rw [h, map_add]
  congr 1
  exact (MvPolynomial.map_eval (Int.castRingHom ℝ) x β).symm

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

theorem integerMonomialArrayPolynomial_principal_sum {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (a : J → ℤ) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hzero : ∀ j, j ≠ j₀ → j ∉ P → a j = 0) :
    integerMonomialArrayPolynomial e a =
      MvPolynomial.C (a j₀) + ∑ j ∈ P, MvPolynomial.monomial (e j) (a j) := by
  classical
  have hsum : (∑ j ∈ insert j₀ P, MvPolynomial.monomial (e j) (a j)) =
      ∑ j, MvPolynomial.monomial (e j) (a j) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hne : j ≠ j₀ := fun he => hj (he ▸ Finset.mem_insert_self _ _)
    have hnot : j ∉ P := fun hp => hj (Finset.mem_insert_of_mem hp)
    simp [hzero j hne hnot]
  rw [integerMonomialArrayPolynomial, ← hsum, Finset.sum_insert hj₀, he₀]
  rfl

theorem productBlockExponent_monomial_int {V : Type*} {h : ℕ}
    (principal : Fin h → V) (c : ℤ) :
    MvPolynomial.monomial (productBlockExponent principal) c =
      MvPolynomial.C c * ∏ v, MvPolynomial.X (principal v) := by
  rw [productBlockExponent, MvPolynomial.monomial_sum_index]
  rfl

theorem integerPrincipalPolynomial_eval {D G : Type*} [Fintype D] [Fintype G]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (d : D) (hd : 0 < h d)
    (a : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℤ)
    (hzero : ∀ e, e ≠ constantCoefficientSlot _ _ → e ∉ principalCoefficientSlots h d → a e = 0)
    (x : SamplerTupleIndex G B h → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B d,
        a (principalCoefficientSlot h d b) * ∏ v : Fin (h d), x (.inr ⟨d, b, v⟩) := by
  classical
  rw [integerMonomialArrayPolynomial_principal_sum Subtype.val a
    (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
    (constantCoefficientSlot_not_principal h d hd) rfl hzero]
  simp only [map_add, map_sum, MvPolynomial.eval_C]
  congr 1
  rw [principalCoefficientSlots, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro b _
    change MvPolynomial.eval x
      (MvPolynomial.monomial (productBlockExponent (fun v => .inr ⟨d, b, v⟩)) _) = _
    rw [productBlockExponent_monomial_int]
    simp only [map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  · intro b _ b' _ hb
    exact principalCoefficientSlot_injective h d hd hb

end Erdos3

end

section

namespace Erdos3

theorem small_coordinate_lift_unique {D : Type*} (f y z : D → ℝ)
    (hy : ∀ d, |y d| < 1 / 2) (hz : ∀ d, |z d| < 1 / 2)
    (hfy : ∀ d, ∃ a : ℤ, f d - y d = a) (hfz : ∀ d, ∃ a : ℤ, f d - z d = a) : y = z := by
  funext d
  obtain ⟨a, ha⟩ := hfy d
  obtain ⟨b, hb⟩ := hfz d
  have hlo : (-1 : ℝ) < (b - a : ℤ) := by
    rw [Int.cast_sub]
    linarith [(abs_lt.mp (hy d)).1, (abs_lt.mp (hz d)).2]
  have hhi : ((b - a : ℤ) : ℝ) < 1 := by
    rw [Int.cast_sub]
    linarith [(abs_lt.mp (hy d)).2, (abs_lt.mp (hz d)).1]
  have hlo' : (-1 : ℤ) < b - a := by exact_mod_cast hlo
  have hhi' : b - a < (1 : ℤ) := by exact_mod_cast hhi
  have he : b = a := by omega
  rw [he] at hb
  linarith

theorem integerPolynomial_remainder_identifies_lifts {D V : Type*}
    (f y : D → MvPolynomial V ℝ) (β : D → MvPolynomial V ℤ)
    (h : ∀ d, f d = y d + MvPolynomial.map (Int.castRingHom ℝ) (β d))
    (x : V → ℤ) (z : D → ℝ) (b : D → ℤ)
    (hy : ∀ d, |MvPolynomial.eval (fun v => (x v : ℝ)) (y d)| < 1 / 2)
    (hz : ∀ d, |z d| < 1 / 2)
    (hzβ : ∀ d, MvPolynomial.eval (fun v => (x v : ℝ)) (f d) = z d + (b d : ℝ)) :
    (fun d => MvPolynomial.eval (fun v => (x v : ℝ)) (y d)) = z ∧
      (fun d => MvPolynomial.eval x (β d)) = b := by
  have he (d : D) := integerPolynomial_remainder_eval (f d) (y d) (β d) (h d) x
  have hsmall := small_coordinate_lift_unique
    (fun d => MvPolynomial.eval (fun v => (x v : ℝ)) (f d))
    (fun d => MvPolynomial.eval (fun v => (x v : ℝ)) (y d)) z hy hz
    (fun d => ⟨MvPolynomial.eval x (β d), by linarith [he d]⟩)
    (fun d => ⟨b d, by linarith [hzβ d]⟩)
  refine ⟨hsmall, ?_⟩
  funext d
  apply Int.cast_injective (α := ℝ)
  have hd := congrFun hsmall d
  linarith [he d, hzβ d]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

noncomputable def integerPolynomialCoordinatePMF (j : J) : PMF ℤ := by
  classical
  exact if j = j₀ then constantIntegerPMF K ρ (by exact_mod_cast hK) hρ
    else if j ∈ P then integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap
    else integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL (e j) (he j)

local notation "laws" => integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
  ρ γ ε hρ hγ hε hgap hεL

omit [Fintype J] in
theorem integerPolynomialCoordinatePMF_bound (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (j : J) {k : ℤ} (hk : k ∈ (laws j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤
      |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  by_cases hj : j = j₀
  · subst j
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte] at hk
    have hb := constantIntegerPMF_support K ρ (by exact_mod_cast hK) hρ hk
    simp only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
      he₀, monomialScale_zero, mul_one, abs_zero, zero_add]
    linarith
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisPrincipalPMF_bound hh hK hL hγ hgap hk
      rw [hprincipal j hp]
      have hpos : 0 ≤ 3 * γ / 2 := by positivity
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp,
        ↓reduceIte, abs_of_nonneg hpos]
      linarith
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisTailPMF_support T hT hK hL hTL hε hεL (e j) (he j) hk
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp,
        ↓reduceIte, abs_zero, zero_add]
      linarith

theorem integerPolynomialCoordinatePMF_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (a : J → ℤ) (ha : ∀ j, a j ∈ (laws j).support) (x : V → ℝ) (hx : ∀ v, |x v| ≤ T v) :
    |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤
      ρ + 2 * γ * P.card + ε * Fintype.card J := by
  apply (monomialArrayPolynomial_box_budget e (fun j => (a j : ℝ) / K)
    (fun j => |coefficientProfileCenter P γ j| + coefficientProfileWidth P j₀ ρ γ ε j) T x hx
    (fun j => integerPolynomialCoordinatePMF_bound P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL hj₀ he₀ hprincipal j (ha j))).trans
  exact coefficientProfile_budget P j₀ hj₀ hγ.le hε.le

noncomputable def integerPolynomialLaw : Measure (J → ℤ) :=
  Measure.pi (fun j => (laws j).toMeasure)

theorem integerPolynomialLaw_probability :
    IsProbabilityMeasure (integerPolynomialLaw P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL) := by
  unfold integerPolynomialLaw
  infer_instance

theorem integerPolynomialLaw_density :
    integerPolynomialLaw P j₀ h K L s hh hK hL T hT hTL e he ρ γ ε hρ hγ hε hgap hεL =
      realDensityMeasure (Measure.pi (fun _ : J => (Measure.count : Measure ℤ)))
        (fun a => ∏ j, (laws j (a j)).toReal) :=
  independentIntegerLaw_density laws

theorem integerPolynomialLaw_ae_box (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h) :
    ∀ᵐ a ∂integerPolynomialLaw P j₀ h K L s hh hK hL T hT hTL e he ρ γ ε hρ hγ hε hgap hεL,
      ∀ x : V → ℝ, (∀ v, |x v| ≤ T v) →
        |MvPolynomial.eval x (monomialArrayPolynomial e (fun j => (a j : ℝ) / K))| ≤
          ρ + 2 * γ * P.card + ε * Fintype.card J := by
  classical
  rw [integerPolynomialLaw_density]
  apply realDensityMeasure_ae_of_support _ _ (measurable_of_countable _) _
  intro a ha x hx
  apply integerPolynomialCoordinatePMF_box P j₀ h K L s hh hK hL T hT hTL e he
    ρ γ ε hρ hγ hε hgap hεL hj₀ he₀ hprincipal a _ x hx
  intro j
  have hj := (Finset.prod_ne_zero_iff.mp ha) j (Finset.mem_univ j)
  intro hz
  exact hj (by rw [hz]; exact ENNReal.toReal_zero)

end Erdos3

end

section

namespace Erdos3

variable {J V : Type*}
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

theorem integerPolynomialCoordinatePMF_active_profile_bound
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P,
      monomialScale T (e j) = (integerAxisSideLength h K L γ : ℝ) ^ h)
    (hactive : L ^ h < K) (j : J) {k : ℤ}
    (hk : k ∈ (integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      ρ γ ε hρ hγ hε hgap hεL j).support) :
    |(k : ℝ) / K * monomialScale T (e j) - coefficientProfileCenter P γ j| ≤
      coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  by_cases hj : j = j₀
  · subst j
    simp only [integerPolynomialCoordinatePMF, ↓reduceIte] at hk
    have hb := constantIntegerPMF_support K ρ (by exact_mod_cast hK) hρ hk
    simp only [coefficientProfileCenter, coefficientProfileWidth, hj₀, ↓reduceIte,
      he₀, monomialScale_zero, mul_one, sub_zero]
    linarith
  · by_cases hp : j ∈ P
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisPrincipalPMF_active hh hK hL hγ hgap hactive hk
      have hscale : monomialScale T (e j) = (L : ℝ) ^ h := by
        rw [hprincipal j hp]
        simp only [integerAxisSideLength, hactive, ↓reduceIte]
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte, hscale]
      have heq : (k : ℝ) / K * (L : ℝ) ^ h = (L : ℝ) ^ h * (k : ℝ) / K := by ring
      rw [heq, abs_le]
      constructor <;> linarith [hb.1, hb.2]
    · simp only [integerPolynomialCoordinatePMF, hj, hp, ↓reduceIte] at hk
      have hb := integerAxisTailPMF_support T hT hK hL hTL hε hεL (e j) (he j) hk
      simp only [coefficientProfileCenter, coefficientProfileWidth, hj, hp, ↓reduceIte,
        sub_zero, abs_mul, abs_of_pos (monomialScale_pos T hT (e j))]
      linarith

end Erdos3

end

end OAI
