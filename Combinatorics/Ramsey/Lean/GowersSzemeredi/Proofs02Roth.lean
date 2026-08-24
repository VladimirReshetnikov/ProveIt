import GowersSzemeredi.Proofs02DensityIncrement
import GowersSzemeredi.Proofs01_03
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Bertrand

/-!
# The quantitative Roth theorem

This file proves Theorem 2.6 by the density-increment argument from Gowers's
Section 2.  We work with zero-based finite intervals during the iteration.
At each stage Bertrand's postulate supplies a prime subinterval.  The middle
third of that interval prevents modular three-term progressions from wrapping,
while Corollary 2.5 supplies the density increment in the nonuniform case.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Pulling a set back along a natural-number progression -/

private noncomputable def rothPullback (S : Finset Nat) (P : NatAP) :
    Finset Nat := by
  classical
  exact (Finset.range P.length).filter fun i => P.start + i * P.step ∈ S

private lemma rothPullback_subset_range (S : Finset Nat) (P : NatAP) :
    rothPullback S P ⊆ Finset.range P.length := by
  classical
  exact Finset.filter_subset _ _

private lemma rothProgressionMap_injective (P : NatAP) (hstep : 0 < P.step) :
    Function.Injective fun i : Nat => P.start + i * P.step := by
  intro i j hij
  have hmul : i * P.step = j * P.step := Nat.add_left_cancel hij
  exact Nat.eq_of_mul_eq_mul_right hstep hmul

private lemma rothPullback_image (S : Finset Nat) (P : NatAP) :
    (rothPullback S P).image (fun i => P.start + i * P.step) =
      P.carrier ∩ S := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_filter.mp hi
    refine Finset.mem_inter.mpr ⟨?_, hi'.2⟩
    unfold NatAP.carrier
    rw [Finset.mem_image]
    exact ⟨⟨i, Finset.mem_range.mp hi'.1⟩, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨hxP, hxS⟩ := Finset.mem_inter.mp hx
    unfold NatAP.carrier at hxP
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hxP
    rw [Finset.mem_image]
    refine ⟨i, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hxS⟩

private lemma rothPullback_card (S : Finset Nat) (P : NatAP)
    (hstep : 0 < P.step) :
    (rothPullback S P).card = (P.carrier ∩ S).card := by
  classical
  rw [← rothPullback_image]
  exact (Finset.card_image_of_injective _
    (rothProgressionMap_injective P hstep)).symm

private lemma rothPullback_ap (S : Finset Nat) (P : NatAP)
    (hstep : 0 < P.step) (hAP : HasNatAP (rothPullback S P) 3) :
    HasNatAP S 3 := by
  obtain ⟨a, d, hd, hmem⟩ := hAP
  refine ⟨P.start + a * P.step, d * P.step,
    Nat.mul_pos hd hstep, ?_⟩
  intro i hi
  have hai := hmem i hi
  have himage := (Finset.mem_filter.mp hai).2
  convert himage using 1
  ring

/-! ## Passing between an interval and its prime cyclic model -/

private noncomputable def rothModSet (p : Nat) [NeZero p] (S : Finset Nat) :
    Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun z => z.val ∈ S

@[simp] private lemma mem_rothModSet {p : Nat} [NeZero p]
    {S : Finset Nat} {z : ZMod p} :
    z ∈ rothModSet p S ↔ z.val ∈ S := by
  classical
  simp [rothModSet]

private lemma standardRepresentatives_rothModSet {p : Nat} [NeZero p]
    (S : Finset Nat) (hS : S ⊆ Finset.range p) :
    standardRepresentatives (rothModSet p S) = S := by
  classical
  ext x
  by_cases hx : x < p
  · simp only [standardRepresentatives, Finset.mem_filter, Finset.mem_range,
      mem_rothModSet]
    rw [ZMod.val_natCast_of_lt hx]
    simp [hx]
  · have hxS : x ∉ S := fun h => hx (Finset.mem_range.mp (hS h))
    simp [standardRepresentatives, hx, hxS]

private lemma rothModSet_card {p : Nat} [NeZero p]
    (S : Finset Nat) (hS : S ⊆ Finset.range p) :
    (rothModSet p S).card = S.card := by
  classical
  let e : Finset Nat → Finset (ZMod p) :=
    fun T => T.image fun x : Nat => (x : ZMod p)
  have hinj : Set.InjOn (fun x : Nat => (x : ZMod p)) S := by
    intro x hx y hy hxy
    apply Nat.cast_injective (R := Int)
    have hxlt := Finset.mem_range.mp (hS hx)
    have hylt := Finset.mem_range.mp (hS hy)
    have := congrArg ZMod.val hxy
    simpa [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] using this
  have heq : e S = rothModSet p S := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [mem_rothModSet]
      have hxlt := Finset.mem_range.mp (hS hx)
      simpa [ZMod.val_natCast_of_lt hxlt] using hx
    · intro hz
      have hzS : z.val ∈ S := mem_rothModSet.mp hz
      rw [Finset.mem_image]
      exact ⟨z.val, hzS, ZMod.natCast_zmod_val z⟩
  rw [← heq]
  change (S.image fun x : Nat => (x : ZMod p)).card = S.card
  exact Finset.card_image_of_injOn hinj

/-! ## The middle-third progression count -/

private noncomputable def rothTripleCount {p : Nat} [NeZero p]
    (A B : Finset (ZMod p)) : Nat :=
  countWhere fun q : ZMod p × ZMod p =>
    q.2 ∈ B ∧ q.2 - q.1 ∈ B ∧ q.2 - 2 * q.1 ∈ A

private lemma rothTripleCount_complex {p : Nat} [NeZero p]
    (A B : Finset (ZMod p)) :
    ((rothTripleCount A B : Nat) : Complex) =
      ∑ r : ZMod p, ∑ s : ZMod p,
        indicator B s * indicator B (s - r) * indicator A (s - 2 * r) := by
  classical
  unfold rothTripleCount countWhere
  simp_rw [Finset.cast_card, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [indicator]
  by_cases hs : s ∈ B <;> by_cases hsr : s - r ∈ B <;>
    by_cases hs2r : s - 2 * r ∈ A <;> simp [hs, hsr, hs2r]

private lemma rothTripleCount_split {p : Nat} [NeZero p]
    (A B : Finset (ZMod p)) :
    ((rothTripleCount A B : Nat) : Complex) =
      (density A : Complex) * B.card ^ 2 +
        ∑ r : ZMod p, ∑ s : ZMod p,
          indicator B s * indicator B (s - r) * balanced A (s - 2 * r) := by
  rw [rothTripleCount_complex]
  simp_rw [show indicator A = fun x => (density A : Complex) + balanced A x by
    funext x
    simp [balanced]]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  calc
    (∑ r : ZMod p, ∑ s : ZMod p,
        indicator B s * indicator B (s - r) * (density A : Complex)) =
      (density A : Complex) *
        ∑ s : ZMod p, ∑ r : ZMod p,
          indicator B s * indicator B (s - r) := by
        rw [Finset.mul_sum, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
    _ = (density A : Complex) *
        ∑ s : ZMod p, ∑ t : ZMod p, indicator B s * indicator B t := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      simpa [Equiv.subLeft_apply] using
        (Equiv.sum_comp (Equiv.subLeft s)
          (fun t : ZMod p => indicator B s * indicator B t))
    _ = (density A : Complex) * B.card ^ 2 := by
      rw [show (∑ s : ZMod p, ∑ t : ZMod p,
          indicator B s * indicator B t) =
          (∑ s : ZMod p, indicator B s) *
            ∑ t : ZMod p, indicator B t by
        exact (Fintype.sum_mul_sum (indicator B) (indicator B)).symm]
      simp only [sum_indicator]
      ring

private lemma roth_exponential_add {p : Nat} [NeZero p] (x y : ZMod p) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := p)) x y

private lemma rothError_fourier {p : Nat} [NeZero p]
    (A B : Finset (ZMod p)) :
    (∑ r : ZMod p, ∑ s : ZMod p,
        indicator B s * indicator B (s - r) * balanced A (s - 2 * r)) =
      (p : Complex)⁻¹ * ∑ u : ZMod p,
        fourier (balanced A) u * fourier (indicator B) u *
          fourier (indicator B) (-2 * u) := by
  let f : ZMod p → Complex := balanced A
  let g : ZMod p → Complex := indicator B
  have hchange :
      (∑ r : ZMod p, ∑ s : ZMod p, g s * g (s - r) * f (s - 2 * r)) =
        ∑ s : ZMod p, ∑ y : ZMod p, g s * g y * f (2 * y - s) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    calc
      (∑ r : ZMod p, g s * g (s - r) * f (s - 2 * r)) =
          ∑ y : ZMod p, g s * g y * f (s - 2 * (s - y)) := by
        simpa [Equiv.subLeft_apply] using
          (Equiv.sum_comp (Equiv.subLeft s)
            (fun y : ZMod p => g s * g y * f (s - 2 * (s - y))))
      _ = ∑ y : ZMod p, g s * g y * f (2 * y - s) := by
        apply Finset.sum_congr rfl
        intro y _
        congr 1
        ring
  change (∑ r : ZMod p, ∑ s : ZMod p,
    g s * g (s - r) * f (s - 2 * r)) = _
  rw [hchange]
  calc
    (∑ s : ZMod p, ∑ y : ZMod p, g s * g y * f (2 * y - s)) =
        ∑ s : ZMod p, ∑ y : ZMod p,
          g s * g y * ((p : Complex)⁻¹ * ∑ u : ZMod p,
            fourier f u * exponential (u * (2 * y - s))) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro y _
      rw [identity_2_4_holds p f (2 * y - s)]
    _ = ∑ s : ZMod p, ∑ y : ZMod p, ∑ u : ZMod p,
          (p : Complex)⁻¹ *
            (g s * g y * (fourier f u * exponential (u * (2 * y - s)))) := by
      simp_rw [mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ = ∑ u : ZMod p, ∑ s : ZMod p, ∑ y : ZMod p,
          (p : Complex)⁻¹ *
            (g s * g y * (fourier f u * exponential (u * (2 * y - s)))) := by
      calc
        _ = ∑ s : ZMod p, ∑ u : ZMod p, ∑ y : ZMod p,
            (p : Complex)⁻¹ *
              (g s * g y * (fourier f u * exponential (u * (2 * y - s)))) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = (p : Complex)⁻¹ * ∑ u : ZMod p, ∑ s : ZMod p, ∑ y : ZMod p,
          g s * g y * (fourier f u * exponential (u * (2 * y - s))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
    _ = (p : Complex)⁻¹ * ∑ u : ZMod p,
        fourier f u * fourier g u * fourier g (-2 * u) := by
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      change (∑ s : ZMod p, ∑ y : ZMod p,
          g s * g y * (fourier f u * exponential (u * (2 * y - s)))) =
        fourier f u *
          (∑ s : ZMod p, exponential (-(s * u)) * g s) *
          (∑ y : ZMod p, exponential (-(y * (-2 * u))) * g y)
      rw [Finset.mul_sum]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro y _
      have hphase : exponential (u * (2 * s - y)) =
          exponential (-(y * u)) * exponential (-(s * (-2 * u))) := by
        rw [← roth_exponential_add]
        congr 1
        ring
      rw [hphase]
      ring

@[simp] private lemma roth_fourier_balanced_zero {p : Nat} [NeZero p]
    (A : Finset (ZMod p)) : fourier (balanced A) 0 = 0 := by
  simp [fourier, ZMod.dft_apply]

private lemma roth_fourier_balanced_eq_indicator {p : Nat} [NeZero p]
    (A : Finset (ZMod p)) (u : ZMod p) (hu : u ≠ 0) :
    fourier (balanced A) u = fourier (indicator A) u := by
  rw [fourier, fourier, ZMod.dft_apply, ZMod.dft_apply]
  simp only [balanced, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have hchar :
      (∑ x : ZMod p, exponential (-(x * u))) = 0 := by
    simpa [exponential, mul_comm, hu] using
      AddChar.sum_mulShift (-u) (ZMod.isPrimitive_stdAddChar p)
  have hconst :
      (∑ x : ZMod p, exponential (-(x * u)) * (density A : Complex)) = 0 := by
    rw [← Finset.sum_mul, hchar, zero_mul]
  simpa only [exponential] using sub_eq_self.mpr hconst

private lemma roth_indicator_parseval {p : Nat} [NeZero p]
    (B : Finset (ZMod p)) :
    ∑ u : ZMod p, ‖fourier (indicator B) u‖ ^ 2 =
      (p : Real) * B.card := by
  rw [identity_2_3_holds]
  congr 1
  classical
  calc
    (∑ x : ZMod p, ‖indicator B x‖ ^ 2) =
        ∑ x : ZMod p, if x ∈ B then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ B <;> simp [indicator, hx]
    _ = B.card := by simp

private lemma roth_two_ne_zero {p : Nat} (hp2 : 2 < p) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  have hv2 : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt hp2
  have hv0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  omega

private lemma roth_fourier_mul_two_mass {p : Nat} [NeZero p] [Fact p.Prime]
    (hp2 : 2 < p) (B : Finset (ZMod p)) :
    ∑ u : ZMod p, ‖fourier (indicator B) (-2 * u)‖ ^ 2 =
      (p : Real) * B.card := by
  let e := Equiv.mulLeft₀ (-2 : ZMod p)
    (neg_ne_zero.mpr (roth_two_ne_zero hp2))
  calc
    (∑ u : ZMod p, ‖fourier (indicator B) (-2 * u)‖ ^ 2) =
        ∑ v : ZMod p, ‖fourier (indicator B) v‖ ^ 2 := by
      simpa [e] using (Equiv.sum_comp e fun v : ZMod p =>
        ‖fourier (indicator B) v‖ ^ 2)
    _ = (p : Real) * B.card := roth_indicator_parseval B

private lemma rothError_bound {p : Nat} [NeZero p] [Fact p.Prime]
    (hp2 : 2 < p) (A B : Finset (ZMod p)) (alpha : Real)
    (halpha : 0 ≤ alpha)
    (hsmall : ∀ u : ZMod p, u ≠ 0 →
      ‖fourier (indicator A) u‖ ≤ alpha * p) :
    ‖∑ r : ZMod p, ∑ s : ZMod p,
        indicator B s * indicator B (s - r) * balanced A (s - 2 * r)‖ ≤
      alpha * (p : Real) * B.card := by
  have hp : (0 : Real) < p := by exact_mod_cast lt_trans (by omega : 0 < 2) hp2
  have hbalanced (u : ZMod p) :
      ‖fourier (balanced A) u‖ ≤ alpha * p := by
    by_cases hu : u = 0
    · subst u
      rw [roth_fourier_balanced_zero, norm_zero]
      exact mul_nonneg halpha hp.le
    · rw [roth_fourier_balanced_eq_indicator A u hu]
      exact hsmall u hu
  have hCS :
      (∑ u : ZMod p,
        ‖fourier (indicator B) u‖ *
          ‖fourier (indicator B) (-2 * u)‖) ≤
        (p : Real) * B.card := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt
      (Finset.univ : Finset (ZMod p))
      (fun u => ‖fourier (indicator B) u‖)
      (fun u => ‖fourier (indicator B) (-2 * u)‖)
    rw [roth_indicator_parseval, roth_fourier_mul_two_mass hp2] at h
    have hnonneg : 0 ≤ (p : Real) * B.card := by positivity
    have hsqrt : Real.sqrt ((p : Real) * B.card) *
        Real.sqrt ((p : Real) * B.card) = (p : Real) * B.card := by
      rw [← pow_two, Real.sq_sqrt hnonneg]
    exact h.trans_eq hsqrt
  rw [rothError_fourier]
  calc
    ‖(p : Complex)⁻¹ * ∑ u : ZMod p,
        fourier (balanced A) u * fourier (indicator B) u *
          fourier (indicator B) (-2 * u)‖ =
        (p : Real)⁻¹ * ‖∑ u : ZMod p,
          fourier (balanced A) u * fourier (indicator B) u *
            fourier (indicator B) (-2 * u)‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (p : Real)⁻¹ * ∑ u : ZMod p,
        ‖fourier (balanced A) u‖ * ‖fourier (indicator B) u‖ *
          ‖fourier (indicator B) (-2 * u)‖ := by
      gcongr
      calc
        ‖∑ u : ZMod p, fourier (balanced A) u * fourier (indicator B) u *
            fourier (indicator B) (-2 * u)‖ ≤
            ∑ u : ZMod p, ‖fourier (balanced A) u *
              fourier (indicator B) u * fourier (indicator B) (-2 * u)‖ :=
          norm_sum_le _ _
        _ = _ := by simp only [norm_mul]
    _ ≤ (p : Real)⁻¹ * ((alpha * p) *
        ∑ u : ZMod p, ‖fourier (indicator B) u‖ *
          ‖fourier (indicator B) (-2 * u)‖) := by
      gcongr
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hbalanced u)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (p : Real)⁻¹ * ((alpha * p) * ((p : Real) * B.card)) := by
      gcongr
    _ = alpha * (p : Real) * B.card := by
      field_simp

private lemma roth_modEq_eq_of_close {p a b : Nat} (hp : 0 < p)
    (hab₁ : a < b + p) (hab₂ : b < a + p) (hmod : a ≡ b [MOD p]) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hdvd : p ∣ b - a := (Nat.modEq_iff_dvd' hab.le).mp hmod
    have hple : p ≤ b - a := Nat.le_of_dvd (Nat.sub_pos_of_lt hab) hdvd
    omega
  · exact hab
  · have hdvd : p ∣ a - b :=
      (Nat.modEq_iff_dvd' hab.le).mp hmod.symm
    have hple : p ≤ a - b := Nat.le_of_dvd (Nat.sub_pos_of_lt hab) hdvd
    omega

private lemma rothTripleCount_le_of_no_nat_ap {p : Nat} [NeZero p]
    (A₀ B₀ : Finset Nat) (hA₀ : A₀ ⊆ Finset.range p)
    (hB₀A₀ : B₀ ⊆ A₀)
    (hBmiddle : B₀ ⊆ Finset.Ico (p / 3) (2 * p / 3))
    (hno : ¬ HasNatAP A₀ 3) :
    rothTripleCount (rothModSet p A₀) (rothModSet p B₀) ≤ p := by
  classical
  unfold rothTripleCount countWhere
  rw [Finset.filter_congr_decidable]
  calc
    ((Finset.univ.filter fun q : ZMod p × ZMod p =>
        q.2 ∈ rothModSet p B₀ ∧ q.2 - q.1 ∈ rothModSet p B₀ ∧
          q.2 - 2 * q.1 ∈ rothModSet p A₀).card) ≤
        (Finset.univ.filter fun q : ZMod p × ZMod p => q.1 = 0).card := by
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      by_contra hr
      let x : Nat := q.2.val
      let y : Nat := (q.2 - q.1).val
      let z : Nat := (q.2 - 2 * q.1).val
      have hxB : x ∈ B₀ := mem_rothModSet.mp hq.1
      have hyB : y ∈ B₀ := mem_rothModSet.mp hq.2.1
      have hzA : z ∈ A₀ := mem_rothModSet.mp hq.2.2
      have hxA : x ∈ A₀ := hB₀A₀ hxB
      have hyA : y ∈ A₀ := hB₀A₀ hyB
      have hxmid := Finset.mem_Ico.mp (hBmiddle hxB)
      have hymid := Finset.mem_Ico.mp (hBmiddle hyB)
      have hzlt : z < p := Finset.mem_range.mp (hA₀ hzA)
      have hcast : ((x + z : Nat) : ZMod p) = ((2 * y : Nat) : ZMod p) := by
        dsimp only [x, y, z]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          ZMod.natCast_zmod_val]
        ring
      have hmod : x + z ≡ 2 * y [MOD p] := by
        exact (ZMod.natCast_eq_natCast_iff (x + z) (2 * y) p).mp hcast
      have hclose₁ : x + z < 2 * y + p := by omega
      have hclose₂ : 2 * y < x + z + p := by omega
      have hrel : x + z = 2 * y :=
        roth_modEq_eq_of_close (NeZero.pos p) hclose₁ hclose₂ hmod
      have hxy : x ≠ y := by
        intro hxy
        have hmodEq : q.2 = q.2 - q.1 :=
          ZMod.val_injective p hxy
        apply hr
        exact sub_eq_self.mp hmodEq.symm
      apply hno
      rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
      · refine ⟨x, y - x, Nat.sub_pos_of_lt hxylt, ?_⟩
        intro i hi
        interval_cases i
        · simpa using hxA
        · convert hyA using 1 <;> omega
        · convert hzA using 1 <;> omega
      · refine ⟨z, x - y, ?_, ?_⟩
        · omega
        · intro i hi
          interval_cases i
          · simpa using hzA
          · convert hyA using 1 <;> omega
          · convert hxA using 1 <;> omega
    _ = p := by
      rw [show (Finset.univ.filter fun q : ZMod p × ZMod p => q.1 = 0) =
          ({0} : Finset (ZMod p)) ×ˢ Finset.univ by
        ext q
        rcases q with ⟨r, s⟩
        simp [eq_comm]]
      simp [ZMod.card]

private lemma rothTripleCount_real_lower {p : Nat} [NeZero p] [Fact p.Prime]
    (hp2 : 2 < p) (A B : Finset (ZMod p)) (alpha : Real)
    (halpha : 0 ≤ alpha)
    (hsmall : ∀ u : ZMod p, u ≠ 0 →
      ‖fourier (indicator A) u‖ ≤ alpha * p) :
    density A * (B.card : Real) ^ 2 - alpha * p * B.card ≤
      (rothTripleCount A B : Real) := by
  let E : Complex := ∑ r : ZMod p, ∑ s : ZMod p,
    indicator B s * indicator B (s - r) * balanced A (s - 2 * r)
  have hsplit := rothTripleCount_split A B
  change (rothTripleCount A B : Complex) =
    (density A : Complex) * (B.card : Complex) ^ 2 + E at hsplit
  have hre' := congrArg Complex.re hsplit
  have hre : (rothTripleCount A B : Real) =
      density A * (B.card : Real) ^ 2 + E.re := by
    norm_num at hre' ⊢
    simpa [pow_two, Complex.mul_re] using hre'
  have hE := rothError_bound hp2 A B alpha halpha hsmall
  change ‖E‖ ≤ alpha * (p : Real) * B.card at hE
  have hreLower : -‖E‖ ≤ E.re := by
    exact (neg_le_neg (Complex.abs_re_le_norm E)).trans (neg_abs_le E.re)
  push_cast at hre
  nlinarith

private lemma roth_uniform_case_has_ap {p : Nat} [NeZero p] [Fact p.Prime]
    (hp2 : 2 < p) (delta : Real) (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (A₀ B₀ : Finset Nat)
    (hA₀ : A₀ ⊆ Finset.range p) (hB₀A₀ : B₀ ⊆ A₀)
    (hBmiddle : B₀ ⊆ Finset.Ico (p / 3) (2 * p / 3))
    (hAdensity : delta * (1 - delta / 1000) * p ≤ A₀.card)
    (hBdensity : delta * p / 10 ≤ B₀.card)
    (hscale : 1000 * delta ^ (-3 : Int) ≤ p)
    (hsmall : ∀ u : ZMod p, u ≠ 0 →
      ‖fourier (indicator (rothModSet p A₀)) u‖ ≤
        (delta ^ 2 / 100) * p) :
    HasNatAP A₀ 3 := by
  by_contra hno
  have hupperNat := rothTripleCount_le_of_no_nat_ap A₀ B₀ hA₀
    hB₀A₀ hBmiddle hno
  have hupper : (rothTripleCount (rothModSet p A₀)
      (rothModSet p B₀) : Real) ≤ p := by
    exact_mod_cast hupperNat
  have hAcard := rothModSet_card A₀ hA₀
  have hBsubset : B₀ ⊆ Finset.range p := hB₀A₀.trans hA₀
  have hBcard := rothModSet_card B₀ hBsubset
  have hp : (0 : Real) < p := by exact_mod_cast NeZero.pos p
  have hdensityA : delta * (1 - delta / 1000) ≤
      density (rothModSet p A₀) := by
    unfold density
    rw [hAcard, le_div_iff₀ hp]
    exact hAdensity
  have hlower := rothTripleCount_real_lower hp2 (rothModSet p A₀)
    (rothModSet p B₀) (delta ^ 2 / 100) (by positivity) hsmall
  rw [hBcard] at hlower
  have hB0 : (0 : Real) ≤ B₀.card := Nat.cast_nonneg _
  have hdelta0 : 0 ≤ delta := hdelta.le
  have hdeltaInv : delta ^ (-3 : Int) = (delta ^ 3)⁻¹ := by
    rfl
  rw [hdeltaInv] at hscale
  have hscale' : 1000 ≤ delta ^ 3 * p := by
    have hpow : 0 < delta ^ 3 := pow_pos hdelta _
    have := mul_le_mul_of_nonneg_right hscale hpow.le
    field_simp [ne_of_gt hpow] at this
    nlinarith
  have hmain :
      delta * (1 - delta / 1000) * (B₀.card : Real) ^ 2 -
          delta ^ 2 / 100 * p * B₀.card ≤
        (rothTripleCount (rothModSet p A₀) (rothModSet p B₀) : Real) := by
    exact (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hdensityA (sq_nonneg (B₀.card : Real))) _).trans hlower
  have hB : delta * p / 10 ≤ (B₀.card : Real) := hBdensity
  have hdelta1000 : 0 ≤ 1 - delta / 1000 := by linarith
  have hbig : (p : Real) <
      delta * (1 - delta / 1000) * (B₀.card : Real) ^ 2 -
        delta ^ 2 / 100 * p * B₀.card := by
    have hcoef : delta ^ 2 * p * (89 / 1000 : Real) ≤
        delta * (1 - delta / 1000) * B₀.card - delta ^ 2 / 100 * p := by
      nlinarith [mul_nonneg hdelta0 hB0]
    have hprod := mul_le_mul_of_nonneg_left hcoef hB0
    have hBscaled := mul_le_mul_of_nonneg_left hB (by positivity :
      0 ≤ delta ^ 2 * (89 / 1000 : Real) * p)
    have hcore : 1 < delta ^ 3 * p * (89 / 10000 : Real) := by
      nlinarith
    nlinarith [mul_nonneg hdelta0 hB0, sq_nonneg (B₀.card : Real)]
  linarith

/-! ## Quantitative bookkeeping for a density increment -/

private def rothConstant : Real := 1000000000000

private def rothNextDensity (delta : Real) : Real :=
  delta + delta ^ 2 / 10000

private def rothLengthLoss : Real := 2147483648

private lemma roth_threshold_survives_increment (delta n m : Real)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hn : Real.exp (Real.exp (rothConstant * delta⁻¹)) ≤ n)
    (hm : Real.sqrt (delta ^ 6 * n / rothLengthLoss) ≤ m) :
    Real.exp (Real.exp
      (rothConstant * (rothNextDensity delta)⁻¹)) ≤ m := by
  let t : Real := delta⁻¹
  let delta' : Real := rothNextDensity delta
  let X : Real := rothConstant * t
  let Y : Real := rothConstant * delta'⁻¹
  let E : Real := Real.exp X
  let E' : Real := Real.exp Y
  have ht : 1 ≤ t := by
    dsimp only [t]
    exact (one_le_inv₀ hdelta).mpr hdelta1
  have hdelta' : 0 < delta' := by
    dsimp only [delta', rothNextDensity]
    nlinarith [sq_nonneg delta]
  have hYX : Y + 2 ≤ X := by
    dsimp only [Y, X, t, delta', rothNextDensity, rothConstant]
    field_simp [ne_of_gt hdelta, ne_of_gt hdelta']
    nlinarith [sq_nonneg delta]
  have hexpTwo : (4 : Real) < Real.exp 2 := by
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hE' : 4 * E' ≤ E := by
    have hmono : Real.exp (Y + 2) ≤ Real.exp X :=
      Real.exp_le_exp.mpr hYX
    rw [Real.exp_add] at hmono
    simpa only [E, E', mul_comm] using
      (mul_le_mul_of_nonneg_left hexpTwo.le (Real.exp_nonneg Y)).trans hmono
  have hE'quarter : E' ≤ E / 4 := by linarith
  have hXE : X + 1 ≤ E := Real.add_one_le_exp X
  have hXlarge : (2147483648 : Real) ≤ E / 4 := by
    dsimp only [X, rothConstant] at hXE
    nlinarith
  have hKt : rothLengthLoss ≤ Real.exp (E / 4) := by
    dsimp only [rothLengthLoss]
    calc
      (2147483648 : Real) ≤ E / 4 := hXlarge
      _ ≤ E / 4 + 1 := by norm_num
      _ ≤ Real.exp (E / 4) := Real.add_one_le_exp (E / 4)
  have h6t : 6 * t ≤ E / 4 := by
    dsimp only [X, rothConstant] at hXE
    nlinarith
  have htExp : t ≤ Real.exp t := by
    exact (le_add_of_nonneg_right (by norm_num)).trans (Real.add_one_le_exp t)
  have htPow : t ^ 6 ≤ Real.exp (E / 4) := by
    calc
      t ^ 6 ≤ (Real.exp t) ^ 6 := pow_le_pow_left₀ (by positivity) htExp _
      _ = Real.exp (6 * t) := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ ≤ Real.exp (E / 4) := Real.exp_le_exp.mpr h6t
  have hcoeff : rothLengthLoss * delta⁻¹ ^ 6 ≤ Real.exp (E / 2) := by
    calc
      rothLengthLoss * delta⁻¹ ^ 6 = rothLengthLoss * t ^ 6 := by rfl
      _ ≤ Real.exp (E / 4) * Real.exp (E / 4) :=
        mul_le_mul hKt htPow (by positivity) (by positivity)
      _ = Real.exp (E / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hthresholdSq : (Real.exp E') ^ 2 ≤ Real.exp (E / 2) := by
    calc
      (Real.exp E') ^ 2 = Real.exp (2 * E') := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (E / 2) := by
        apply Real.exp_le_exp.mpr
        linarith
  have hproduct : rothLengthLoss * delta⁻¹ ^ 6 *
      (Real.exp E') ^ 2 ≤ n := by
    calc
      rothLengthLoss * delta⁻¹ ^ 6 * (Real.exp E') ^ 2 ≤
          Real.exp (E / 2) * Real.exp (E / 2) :=
        mul_le_mul hcoeff hthresholdSq (by positivity) (by positivity)
      _ = Real.exp E := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ n := by simpa [E, X, t] using hn
  have hdiv : delta⁻¹ ^ 6 * (Real.exp E') ^ 2 ≤
      n / rothLengthLoss := by
    apply (le_div_iff₀ (by norm_num [rothLengthLoss] :
      (0 : Real) < rothLengthLoss)).mpr
    nlinarith
  have hsquare : (Real.exp E') ^ 2 ≤
      delta ^ 6 * n / rothLengthLoss := by
    have hmul := mul_le_mul_of_nonneg_left hdiv (pow_nonneg hdelta.le 6)
    calc
      (Real.exp E') ^ 2 = delta ^ 6 *
          (delta⁻¹ ^ 6 * (Real.exp E') ^ 2) := by
        field_simp [ne_of_gt hdelta]
      _ ≤ delta ^ 6 * (n / rothLengthLoss) := hmul
      _ = delta ^ 6 * n / rothLengthLoss := by ring
  have hn0 : 0 ≤ n := (Real.exp_pos _).le.trans hn
  have hrad : 0 ≤ delta ^ 6 * n / rothLengthLoss := by
    exact div_nonneg (mul_nonneg (pow_nonneg hdelta.le 6) hn0) (by
      norm_num [rothLengthLoss])
  exact ((Real.le_sqrt (Real.exp_nonneg E') hrad).mpr hsquare).trans hm

/-! ## Elementary interval bookkeeping -/

private def rothInterval (a length : Nat) : NatAP where
  start := a
  step := 1
  length := length

@[simp] private lemma rothInterval_step (a length : Nat) :
    (rothInterval a length).step = 1 := rfl

@[simp] private lemma rothInterval_length (a length : Nat) :
    (rothInterval a length).length = length := rfl

private lemma rothInterval_carrier (a length : Nat) :
    (rothInterval a length).carrier = Finset.Ico a (a + length) := by
  classical
  ext x
  constructor
  · intro hx
    unfold NatAP.carrier at hx
    obtain ⟨i, _hi, hix⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_Ico]
    dsimp only [rothInterval] at hix
    rw [← hix]
    constructor <;> omega
  · intro hx
    have hxi := Finset.mem_Ico.mp hx
    unfold NatAP.carrier
    rw [Finset.mem_image]
    let i : Fin length := ⟨x - a, by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    dsimp only [rothInterval, i]
    omega

private lemma rothInterval_proper (a length : Nat) :
    (rothInterval a length).IsProper := by
  rw [NatAP.IsProper, rothInterval_carrier]
  simp [rothInterval]

private lemma roth_card_split_range (S : Finset Nat) {p n : Nat}
    (hS : S ⊆ Finset.range n) (hpn : p ≤ n) :
    S.card = (S ∩ Finset.range p).card + (S ∩ Finset.Ico p n).card := by
  classical
  have heq : S = (S ∩ Finset.range p) ∪ (S ∩ Finset.Ico p n) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_range,
      Finset.mem_Ico]
    constructor
    · intro hx
      have hxn := Finset.mem_range.mp (hS hx)
      by_cases hxp : x < p
      · exact Or.inl ⟨hx, hxp⟩
      · exact Or.inr ⟨hx, by omega, hxn⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hx
      · exact hx
  have hd : Disjoint (S ∩ Finset.range p) (S ∩ Finset.Ico p n) := by
    rw [Finset.disjoint_left]
    intro x hxL hxR
    simp only [Finset.mem_inter, Finset.mem_range] at hxL
    simp only [Finset.mem_inter, Finset.mem_Ico] at hxR
    omega
  calc
    S.card = ((S ∩ Finset.range p) ∪ (S ∩ Finset.Ico p n)).card :=
      congrArg Finset.card heq
    _ = (S ∩ Finset.range p).card + (S ∩ Finset.Ico p n).card :=
      Finset.card_union_of_disjoint hd

private lemma roth_card_split_thirds (S : Finset Nat) {p : Nat}
    (hS : S ⊆ Finset.range p) :
    S.card = (S ∩ Finset.range (p / 3)).card +
      (S ∩ Finset.Ico (p / 3) (2 * p / 3)).card +
      (S ∩ Finset.Ico (2 * p / 3) p).card := by
  classical
  let L := S ∩ Finset.range (p / 3)
  let M := S ∩ Finset.Ico (p / 3) (2 * p / 3)
  let R := S ∩ Finset.Ico (2 * p / 3) p
  have heq : S = (L ∪ M) ∪ R := by
    ext x
    simp only [L, M, R, Finset.mem_union, Finset.mem_inter,
      Finset.mem_range, Finset.mem_Ico]
    constructor
    · intro hx
      have hxp := Finset.mem_range.mp (hS hx)
      by_cases hxL : x < p / 3
      · exact Or.inl (Or.inl ⟨hx, hxL⟩)
      · by_cases hxM : x < 2 * p / 3
        · exact Or.inl (Or.inr ⟨hx, by omega, hxM⟩)
        · exact Or.inr ⟨hx, by omega, hxp⟩
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩)
      · exact hx
      · exact hx
      · exact hx
  have hLM : Disjoint L M := by
    rw [Finset.disjoint_left]
    intro x hxL hxM
    simp only [L, Finset.mem_inter, Finset.mem_range] at hxL
    simp only [M, Finset.mem_inter, Finset.mem_Ico] at hxM
    omega
  have hLMR : Disjoint (L ∪ M) R := by
    rw [Finset.disjoint_left]
    intro x hxLM hxR
    simp only [Finset.mem_union] at hxLM
    simp only [R, Finset.mem_inter, Finset.mem_Ico] at hxR
    rcases hxLM with hxL | hxM
    · simp only [L, Finset.mem_inter, Finset.mem_range] at hxL
      omega
    · simp only [M, Finset.mem_inter, Finset.mem_Ico] at hxM
      omega
  calc
    S.card = ((L ∪ M) ∪ R).card := congrArg Finset.card heq
    _ = (L ∪ M).card + R.card := Finset.card_union_of_disjoint hLMR
    _ = (L.card + M.card) + R.card := by
      rw [Finset.card_union_of_disjoint hLM]
    _ = _ := rfl

private lemma roth_threshold_nat_large (delta : Real) (n : Nat)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hn : Real.exp (Real.exp (rothConstant * delta⁻¹)) ≤ n) :
    100 ≤ n := by
  have hinv : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta).mpr hdelta1
  have hX : (1000000000000 : Real) ≤ rothConstant * delta⁻¹ := by
    dsimp only [rothConstant]
    nlinarith
  have hE := Real.add_one_le_exp (rothConstant * delta⁻¹)
  have hT := Real.add_one_le_exp (Real.exp (rothConstant * delta⁻¹))
  have hn' : (100 : Real) ≤ n := by linarith
  exact_mod_cast hn'

private lemma roth_linear_length_bound (delta : Real) (n q : Nat)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hn : 1 ≤ n)
    (hq : (n : Real) / 20 ≤ q) :
    Real.sqrt (delta ^ 6 * n / rothLengthLoss) ≤ q := by
  have hn0 : (0 : Real) ≤ n := by positivity
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hd6 : delta ^ 6 ≤ 1 := pow_le_one₀ hdelta.le hdelta1
  have hnum : delta ^ 6 * (n : Real) ≤ n :=
    mul_le_of_le_one_left hn0 hd6
  have hrad : delta ^ 6 * (n : Real) / rothLengthLoss ≤
      ((n : Real) / 20) ^ 2 := by
    calc
      delta ^ 6 * (n : Real) / rothLengthLoss ≤
          (n : Real) / rothLengthLoss :=
        div_le_div_of_nonneg_right hnum (by norm_num [rothLengthLoss])
      _ ≤ (n : Real) / 400 := by
        exact div_le_div_of_nonneg_left hn0 (by norm_num) (by
          norm_num [rothLengthLoss])
      _ ≤ ((n : Real) / 20) ^ 2 := by
        nlinarith [sq_nonneg ((n : Real) - 1)]
  have hsqrt : Real.sqrt (delta ^ 6 * n / rothLengthLoss) ≤
      (n : Real) / 20 := by
    exact Real.sqrt_le_iff.mpr ⟨by positivity, hrad⟩
  exact hsqrt.trans hq

private lemma roth_scale_bound (delta : Real) (n : Nat)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hn : Real.exp (Real.exp (rothConstant * delta⁻¹)) ≤ n) :
    1000 * delta ^ (-3 : Int) ≤ (n : Real) / 20 := by
  let t : Real := delta⁻¹
  let X : Real := rothConstant * t
  let E : Real := Real.exp X
  have ht : 1 ≤ t := by
    exact (one_le_inv₀ hdelta).mpr hdelta1
  have hXE : X + 1 ≤ E := Real.add_one_le_exp X
  have hElarge : (80000 : Real) ≤ E := by
    dsimp only [X, rothConstant] at hXE
    nlinarith
  have htExp : t ^ 3 ≤ E := by
    calc
      t ^ 3 ≤ (Real.exp t) ^ 3 := by
        apply pow_le_pow_left₀ (by positivity)
        exact (le_add_of_nonneg_right (by norm_num)).trans
          (Real.add_one_le_exp t)
      _ = Real.exp (3 * t) := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ ≤ Real.exp X := by
        apply Real.exp_le_exp.mpr
        dsimp only [X, rothConstant]
        nlinarith
      _ = E := rfl
  have hhalf := Real.add_one_le_exp (E / 2)
  have hgrowth : 20000 * E ≤ Real.exp E := by
    rw [show E = E / 2 + E / 2 by ring, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp (E / 2) - (E / 2 + 1))]
  have hpoly : 20000 * t ^ 3 ≤ n := by
    calc
      20000 * t ^ 3 ≤ 20000 * E := by nlinarith
      _ ≤ Real.exp E := hgrowth
      _ ≤ n := by simpa [E, X, t] using hn
  have hzpow : delta ^ (-3 : Int) = t ^ 3 := by
    dsimp only [t]
    change (delta ^ 3)⁻¹ = delta⁻¹ ^ 3
    rw [inv_pow]
  rw [hzpow]
  nlinarith

private lemma roth_tail_density_increment (delta : Real) (n p : Nat)
    (S A T : Finset Nat) (hdelta : 0 < delta) (hpn : p ≤ n)
    (hbalance : S.card = A.card + T.card)
    (hSdensity : delta * n ≤ S.card)
    (hAlow : (A.card : Real) < delta * (1 - delta / 1000) * p)
    (hsize : n - p ≤ 10 * p) :
    rothNextDensity delta * (n - p) ≤ T.card := by
  have hbalance' : (S.card : Real) = A.card + T.card := by
    exact_mod_cast hbalance
  have hsize' : ((n - p : Nat) : Real) ≤ 10 * p := by
    exact_mod_cast hsize
  have hsub : ((n - p : Nat) : Real) = n - p := by
    rw [Nat.cast_sub hpn]
  rw [hsub] at hsize'
  dsimp only [rothNextDensity]
  nlinarith [sq_nonneg delta,
    mul_nonneg (sq_nonneg delta) (sub_nonneg.mpr hsize')]

private lemma roth_outer_density_increment (delta : Real) (p : Nat)
    (A B L R : Finset Nat) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hp4 : 4 ≤ p) (hsplit : A.card = L.card + B.card + R.card)
    (hAdensity : delta * (1 - delta / 1000) * p ≤ A.card)
    (hBlow : (B.card : Real) < delta * p / 10) :
    rothNextDensity delta * ((p / 3 : Nat) : Real) ≤ L.card ∨
      rothNextDensity delta * ((p - 2 * p / 3 : Nat) : Real) ≤ R.card := by
  by_contra h
  push_neg at h
  obtain ⟨hL, hR⟩ := h
  have hsplit' : (A.card : Real) = L.card + B.card + R.card := by
    exact_mod_cast hsplit
  have houtNat : 4 * (p / 3 + (p - 2 * p / 3)) ≤ 3 * p := by
    omega
  have hout : ((p / 3 : Nat) : Real) + (p - 2 * p / 3 : Nat) ≤
      3 * (p : Real) / 4 := by
    have hout' : (4 : Real) *
        (((p / 3 : Nat) : Real) + (p - 2 * p / 3 : Nat)) ≤
        3 * (p : Real) := by
      exact_mod_cast houtNat
    linarith
  have hnext : 0 ≤ rothNextDensity delta := by
    dsimp only [rothNextDensity]
    nlinarith [sq_nonneg delta]
  have hLR : (L.card : Real) + R.card <
      rothNextDensity delta * (3 * (p : Real) / 4) := by
    calc
      (L.card : Real) + R.card < rothNextDensity delta * (p / 3 : Nat) +
          rothNextDensity delta * (p - 2 * p / 3 : Nat) := add_lt_add hL hR
      _ = rothNextDensity delta *
          ((p / 3 : Nat) + (p - 2 * p / 3 : Nat)) := by ring
      _ ≤ rothNextDensity delta * (3 * (p : Real) / 4) :=
        mul_le_mul_of_nonneg_left hout hnext
  dsimp only [rothNextDensity] at hLR
  have hp0 : (0 : Real) ≤ p := by positivity
  nlinarith [mul_nonneg hdelta.le hp0, sq_nonneg delta,
    mul_nonneg (sq_nonneg delta) hp0]

private lemma roth_corollary_length_bound (delta : Real) (n p : Nat)
    (hdelta : 0 < delta) (hnp : n < 4 * p) :
    Real.sqrt (delta ^ 6 * n / rothLengthLoss) ≤
      Real.sqrt ((delta ^ 2 / 100) ^ 3 * p / (128 * Real.pi)) := by
  have hp : (0 : Real) < p := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hnp' : (n : Real) < 4 * p := by exact_mod_cast hnp
  have hden : 4 * (128000000 * Real.pi) < rothLengthLoss := by
    dsimp only [rothLengthLoss]
    nlinarith [Real.pi_lt_four]
  have hcross : (n : Real) * (128000000 * Real.pi) ≤
      (p : Real) * rothLengthLoss := by
    have h₁ := mul_lt_mul_of_pos_right hnp'
      (show (0 : Real) < 128000000 * Real.pi by positivity)
    have h₂ := mul_lt_mul_of_pos_left hden hp
    nlinarith
  have hfrac : (n : Real) / rothLengthLoss ≤
      (p : Real) / (128000000 * Real.pi) := by
    apply (div_le_div_iff₀ (by norm_num [rothLengthLoss]) (by positivity)).mpr
    simpa [mul_comm] using hcross
  have hrad : delta ^ 6 * (n : Real) / rothLengthLoss ≤
      (delta ^ 2 / 100) ^ 3 * (p : Real) / (128 * Real.pi) := by
    have hmul := mul_le_mul_of_nonneg_left hfrac (pow_nonneg hdelta.le 6)
    calc
      delta ^ 6 * (n : Real) / rothLengthLoss =
          delta ^ 6 * ((n : Real) / rothLengthLoss) := by ring
      _ ≤ delta ^ 6 * ((p : Real) / (128000000 * Real.pi)) := hmul
      _ = (delta ^ 2 / 100) ^ 3 * (p : Real) / (128 * Real.pi) := by
        field_simp [ne_of_gt Real.pi_pos]
        ring
  exact Real.sqrt_le_sqrt hrad

/-! ## The density-increment iteration on zero-based intervals -/

private theorem roth_interval_core :
    ∀ n : Nat, ∀ (delta : Real), 0 < delta →
      Real.exp (Real.exp (rothConstant * delta⁻¹)) ≤ n →
      ∀ S : Finset Nat, S ⊆ Finset.range n →
        delta * n ≤ S.card → HasNatAP S 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro delta hdelta hn S hS hSdensity
      have hnposR : (0 : Real) < n := (Real.exp_pos _).trans_le hn
      have hnpos : 0 < n := by exact_mod_cast hnposR
      have hcardleNat : S.card ≤ n := by
        simpa using Finset.card_le_card hS
      have hcardle : (S.card : Real) ≤ n := by exact_mod_cast hcardleNat
      have hdelta1 : delta ≤ 1 := by
        by_contra h
        have hgt : 1 < delta := lt_of_not_ge h
        have := mul_lt_mul_of_pos_right hgt hnposR
        nlinarith
      have hn100 : 100 ≤ n :=
        roth_threshold_nat_large delta n hdelta hdelta1 hn
      obtain ⟨p, hpPrime, hnp, hpn₂⟩ :=
        Nat.exists_prime_lt_and_le_two_mul (n / 4) (by omega)
      have hp0 : 0 < p := hpPrime.pos
      have hp4 : 4 ≤ p := by omega
      have hp2 : 2 < p := by omega
      have hpn : p ≤ n := by omega
      have hpnlt : p < n := by omega
      have hn4p : n < 4 * p := by omega
      letI : NeZero p := ⟨hpPrime.ne_zero⟩
      letI : Fact p.Prime := ⟨hpPrime⟩
      let A₀ : Finset Nat := S ∩ Finset.range p
      have hA₀ : A₀ ⊆ Finset.range p := by
        exact Finset.inter_subset_right
      have hA₀S : A₀ ⊆ S := Finset.inter_subset_left
      by_cases hAdensity :
          delta * (1 - delta / 1000) * p ≤ (A₀.card : Real)
      · let B₀ : Finset Nat := A₀ ∩ Finset.Ico (p / 3) (2 * p / 3)
        have hB₀A₀ : B₀ ⊆ A₀ := Finset.inter_subset_left
        have hBmiddle : B₀ ⊆ Finset.Ico (p / 3) (2 * p / 3) :=
          Finset.inter_subset_right
        by_cases hBdensity : delta * p / 10 ≤ (B₀.card : Real)
        · let Amod : Finset (ZMod p) := rothModSet p A₀
          let alpha : Real := delta ^ 2 / 100
          by_cases hlarge : ∃ r : ZMod p, r ≠ 0 ∧
              alpha * p ≤ ‖fourier (indicator Amod) r‖
          · have hspectrum : ∃ r : ZMod p, r != 0 ∧
                alpha * p ≤ ‖fourier (indicator Amod) r‖ := by
              obtain ⟨r, hr, hrlarge⟩ := hlarge
              exact ⟨r, bne_iff_ne.mpr hr, hrlarge⟩
            obtain ⟨P, hPproper, hPsub, hPlength, hPdensity⟩ :=
              corollary_2_5_holds p Amod alpha (by
                dsimp only [alpha]
                positivity) hspectrum
            have hstd : standardRepresentatives Amod = A₀ := by
              dsimp only [Amod]
              exact standardRepresentatives_rothModSet A₀ hA₀
            rw [hstd] at hPdensity
            have hpR : (0 : Real) < p := by exact_mod_cast hp0
            have hmodcard := rothModSet_card A₀ hA₀
            have hdensityA : delta * (1 - delta / 1000) ≤
                density Amod := by
              dsimp only [Amod]
              unfold density
              rw [hmodcard, le_div_iff₀ hpR]
              exact hAdensity
            have hincrement : rothNextDensity delta ≤
                density Amod + alpha / 8 := by
              dsimp only [rothNextDensity, alpha]
              nlinarith [sq_nonneg delta]
            have hPstep : 0 < P.step := hPproper.1
            have hPcard : (rothPullback S P).card =
                (P.carrier ∩ A₀).card := by
              rw [rothPullback_card S P hPstep]
              congr 1
              ext x
              simp only [Finset.mem_inter, A₀, Finset.mem_range]
              constructor
              · rintro ⟨hxP, hxS⟩
                exact ⟨hxP, hxS, Finset.mem_range.mp (hPsub hxP)⟩
              · rintro ⟨hxP, hxS, _⟩
                exact ⟨hxP, hxS⟩
            have hchildDensity : rothNextDensity delta * P.length ≤
                (rothPullback S P).card := by
              rw [hPcard]
              exact (mul_le_mul_of_nonneg_right hincrement
                (Nat.cast_nonneg P.length)).trans hPdensity
            have hPlenLe : P.length ≤ p := by
              rw [← hPproper.2]
              calc
                P.carrier.card ≤ (Finset.range p).card :=
                  Finset.card_le_card hPsub
                _ = p := Finset.card_range p
            have hPlenLt : P.length < n := hPlenLe.trans_lt hpnlt
            have hbaseLength : Real.sqrt
                (delta ^ 6 * n / rothLengthLoss) ≤ P.length := by
              exact (roth_corollary_length_bound delta n p hdelta hn4p).trans
                (by simpa [alpha] using hPlength)
            have hnextThreshold := roth_threshold_survives_increment
              delta n P.length hdelta hdelta1 hn hbaseLength
            have hrec := ih P.length hPlenLt (rothNextDensity delta) (by
                dsimp only [rothNextDensity]
                nlinarith [sq_nonneg delta]) hnextThreshold
              (rothPullback S P) (rothPullback_subset_range S P) hchildDensity
            exact rothPullback_ap S P hPstep hrec
          · have hsmall : ∀ u : ZMod p, u ≠ 0 →
                ‖fourier (indicator Amod) u‖ ≤ alpha * p := by
              intro u hu
              apply le_of_not_gt
              intro huLarge
              exact hlarge ⟨u, hu, huLarge.le⟩
            have hscaleN := roth_scale_bound delta n hdelta hdelta1 hn
            have hnpReal : (n : Real) / 20 ≤ p := by
              have hn4p' : (n : Real) < 4 * p := by exact_mod_cast hn4p
              have hpR : (0 : Real) ≤ p := by positivity
              nlinarith
            have hscale : 1000 * delta ^ (-3 : Int) ≤ (p : Real) :=
              hscaleN.trans hnpReal
            obtain ⟨a, d, hd, hmem⟩ :=
              roth_uniform_case_has_ap hp2 delta hdelta hdelta1 A₀ B₀
                hA₀ hB₀A₀ hBmiddle hAdensity hBdensity hscale (by
                  simpa only [Amod, alpha] using hsmall)
            exact ⟨a, d, hd, fun i hi => hA₀S (hmem i hi)⟩
        · have hBlow : (B₀.card : Real) < delta * p / 10 :=
            lt_of_not_ge hBdensity
          let L : Finset Nat := A₀ ∩ Finset.range (p / 3)
          let R : Finset Nat := A₀ ∩ Finset.Ico (2 * p / 3) p
          have hsplit : A₀.card = L.card + B₀.card + R.card := by
            simpa only [L, B₀, R] using roth_card_split_thirds A₀ hA₀
          rcases roth_outer_density_increment delta p A₀ B₀ L R hdelta
              hdelta1 hp4 hsplit hAdensity hBlow with hL | hR
          · let P := rothInterval 0 (p / 3)
            have hPstep : 0 < P.step := by simp [P]
            have hPcarrier : P.carrier = Finset.range (p / 3) := by
              change (rothInterval 0 (p / 3)).carrier = _
              rw [rothInterval_carrier]
              simp
            have hchildCard : (rothPullback S P).card = L.card := by
              rw [rothPullback_card S P hPstep, hPcarrier]
              congr 1
              ext x
              simp only [Finset.mem_inter, Finset.mem_range, L, A₀]
              constructor
              · rintro ⟨hxp3, hxS⟩
                exact ⟨⟨hxS, by omega⟩, hxp3⟩
              · rintro ⟨⟨hxS, _hxp⟩, hxp3⟩
                exact ⟨hxp3, hxS⟩
            have hlenNat : n ≤ 20 * (p / 3) := by omega
            have hlenReal : (n : Real) / 20 ≤ (p / 3 : Nat) := by
              have hlenNat' : (n : Real) ≤ 20 * (p / 3 : Nat) := by
                exact_mod_cast hlenNat
              linarith
            have hbaseLength := roth_linear_length_bound delta n (p / 3)
              hdelta hdelta1 (by omega) hlenReal
            have hnextThreshold := roth_threshold_survives_increment delta n
              ((p / 3 : Nat) : Real) hdelta hdelta1 hn hbaseLength
            have hlenLt : p / 3 < n := by omega
            have hrec := ih (p / 3) hlenLt (rothNextDensity delta) (by
                dsimp only [rothNextDensity]
                nlinarith [sq_nonneg delta]) hnextThreshold
              (rothPullback S P) (rothPullback_subset_range S P) (by
                rw [hchildCard]
                exact hL)
            exact rothPullback_ap S P hPstep hrec
          · let P := rothInterval (2 * p / 3) (p - 2 * p / 3)
            have hPstep : 0 < P.step := by simp [P]
            have hPcarrier : P.carrier = Finset.Ico (2 * p / 3) p := by
              change (rothInterval (2 * p / 3)
                (p - 2 * p / 3)).carrier = _
              rw [rothInterval_carrier]
              congr 1
              omega
            have hchildCard : (rothPullback S P).card = R.card := by
              rw [rothPullback_card S P hPstep, hPcarrier]
              congr 1
              ext x
              simp only [Finset.mem_inter, Finset.mem_Ico, R, A₀,
                Finset.mem_range]
              constructor
              · rintro ⟨hxI, hxS⟩
                exact ⟨⟨hxS, hxI.2⟩, hxI⟩
              · rintro ⟨⟨hxS, _hxp⟩, hxI⟩
                exact ⟨hxI, hxS⟩
            have hlenNat : n ≤ 20 * (p - 2 * p / 3) := by omega
            have hlenReal : (n : Real) / 20 ≤
                (p - 2 * p / 3 : Nat) := by
              have hlenNat' : (n : Real) ≤
                  20 * (p - 2 * p / 3 : Nat) := by exact_mod_cast hlenNat
              linarith
            have hbaseLength := roth_linear_length_bound delta n
              (p - 2 * p / 3) hdelta hdelta1 (by omega) hlenReal
            have hnextThreshold := roth_threshold_survives_increment delta n
              ((p - 2 * p / 3 : Nat) : Real) hdelta hdelta1 hn hbaseLength
            have hlenLt : p - 2 * p / 3 < n := by omega
            have hrec := ih (p - 2 * p / 3) hlenLt
              (rothNextDensity delta) (by
                dsimp only [rothNextDensity]
                nlinarith [sq_nonneg delta]) hnextThreshold
              (rothPullback S P) (rothPullback_subset_range S P) (by
                rw [hchildCard]
                exact hR)
            exact rothPullback_ap S P hPstep hrec
      · have hAlow : (A₀.card : Real) <
            delta * (1 - delta / 1000) * p := lt_of_not_ge hAdensity
        let P := rothInterval p (n - p)
        let T := rothPullback S P
        have hPstep : 0 < P.step := by simp [P]
        have hPcarrier : P.carrier = Finset.Ico p n := by
          change (rothInterval p (n - p)).carrier = _
          rw [rothInterval_carrier]
          congr 1
          omega
        have hTcard : T.card = (S ∩ Finset.Ico p n).card := by
          dsimp only [T]
          rw [rothPullback_card S P hPstep, hPcarrier]
          congr 1
          exact Finset.inter_comm _ _
        have hsplit := roth_card_split_range S hS hpn
        rw [← hTcard] at hsplit
        have hTdensity : rothNextDensity delta * ((n - p : Nat) : Real) ≤
            T.card := by
          simpa [Nat.cast_sub hpn] using
            roth_tail_density_increment delta n p S A₀ T hdelta hpn hsplit
              hSdensity hAlow (by omega)
        have hlenNat : n ≤ 2 * (n - p) := by omega
        have hlenReal : (n : Real) / 20 ≤ (n - p : Nat) := by
          have hlenNat' : (n : Real) ≤ 2 * (n - p : Nat) := by
            exact_mod_cast hlenNat
          linarith
        have hbaseLength := roth_linear_length_bound delta n (n - p)
          hdelta hdelta1 (by omega) hlenReal
        have hnextThreshold := roth_threshold_survives_increment delta n
          ((n - p : Nat) : Real) hdelta hdelta1 hn hbaseLength
        have hlenLt : n - p < n := by omega
        have hrec := ih (n - p) hlenLt (rothNextDensity delta) (by
            dsimp only [rothNextDensity]
            nlinarith [sq_nonneg delta]) hnextThreshold T (by
              exact rothPullback_subset_range S P) hTdensity
        exact rothPullback_ap S P hPstep hrec

/-- **Gowers, Theorem 2.6 (Roth).**  A subset of `[1,N]` of density at least
`delta` contains a nonconstant three-term arithmetic progression once `N` is
at least double exponential in `delta⁻¹`. -/
theorem theorem_2_6_holds : theorem_2_6 := by
  refine ⟨rothConstant, by norm_num [rothConstant], ?_⟩
  intro delta N hdelta hN A hA hAdensity
  let P := rothInterval 1 N
  let S := rothPullback A P
  have hPstep : 0 < P.step := by simp [P]
  have hPcarrier : P.carrier = Finset.Icc 1 N := by
    change (rothInterval 1 N).carrier = _
    rw [rothInterval_carrier]
    ext x
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hScard : S.card = A.card := by
    dsimp only [S]
    rw [rothPullback_card A P hPstep, hPcarrier]
    rw [Finset.inter_eq_right.mpr hA]
  have hSdensity : delta * N ≤ S.card := by
    rw [hScard]
    exact hAdensity
  have hSAP := roth_interval_core N delta hdelta hN S
    (rothPullback_subset_range A P) hSdensity
  exact rothPullback_ap A P hPstep hSAP

end LeanProofs.GowersSzemeredi
