import FabiusFunction.BoundedDerivatives
import FabiusFunction.DyadicSpecializations
import FabiusFunction.FabiusInverse
import FabiusFunction.QuadraticCompositionalInverse
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# The Catalan jet of the Fabius inverse at the quarter anchor

Let `G` be the inverse of a bounded Fabius function on the unit interval.  The
quarter value `F(1/4) = 5/72` lies in the smooth interior of `G`, even though
`G` is not analytic there.  This module proves that its full derivative jet is
nevertheless the formal inverse of the quadratic `z + 4z²`:

`D^n (G(5/72 + t) - 1/4)|_(t=0)
  = n! [X^n] QuadraticInverse.inverse 4`.

The mechanism is entirely smooth and formal.  Equation (3) for the bounded
Fabius function gives the exact quarter jet: its derivatives are `5/72`, `1`,
`8`, and then zero.  Faà di Bruno therefore lets one replace the centered
Fabius function by `z + 4z²` inside every derivative of its composition with
the centered inverse.  The inverse identity supplies the identity-function
jet.  After division by factorials, Leibniz's rule becomes precisely the
scalar convolution recurrence consumed by
`QuadraticInverse.seq_succ_of_convolution`.

No local analytic identity is asserted: equality of all jets at this point is
strictly weaker than equality on a neighborhood.
-/

set_option autoImplicit false

open Filter Finset Set
open scoped BigOperators ContDiff

namespace Fabius

noncomputable section

private def centeredFabius (F : BoundedFabius) : ℝ → ℝ :=
  fun z => fabiusReal F (1 / 4 + z) - 5 / 72

private def centeredFabiusInv (F : BoundedFabius) (hF : IsFabius F) : ℝ → ℝ :=
  fun t => fabiusInv F hF (5 / 72 + t) - 1 / 4

private def quarterQuadratic : ℝ → ℝ :=
  fun z => z + 4 * z ^ 2

private def normalizedCenteredInverseJet
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) : ℝ :=
  iteratedDeriv n (centeredFabiusInv F hF) 0 / (n.factorial : ℝ)

private theorem contDiff_centeredFabius
    (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ∞ (centeredFabius F) := by
  change ContDiff ℝ ∞
    (fun z : ℝ => fabiusReal F (1 / 4 + z) - 5 / 72)
  simpa only [Function.comp_def, Pi.add_apply, Pi.sub_apply, id_eq] using
    (hF.contDiff.comp
      ((contDiff_const (c := (1 / 4 : ℝ))).add contDiff_id)).sub
        (contDiff_const (c := (5 / 72 : ℝ)))

private theorem centeredFabiusInv_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    centeredFabiusInv F hF 0 = 0 := by
  rw [centeredFabiusInv, add_zero, ← fabiusReal_one_quarter F hF,
    fabiusInv_fabiusReal F hF (by constructor <;> norm_num)]
  ring

private theorem contDiffAt_centeredFabiusInv
    (F : BoundedFabius) (hF : IsFabius F) :
    ContDiffAt ℝ ∞ (centeredFabiusInv F hF) 0 := by
  have hshift : ContDiffAt ℝ ∞ (fun t : ℝ => 5 / 72 + t) 0 :=
    (contDiffAt_const (c := (5 / 72 : ℝ))).add contDiffAt_id
  have houter : ContDiffAt ℝ ∞ (fabiusInv F hF)
      ((fun t : ℝ => 5 / 72 + t) 0) := by
    simpa only [add_zero] using
      fabiusInv_contDiffAt F hF (y := (5 / 72 : ℝ)) (by norm_num) (by norm_num)
  change ContDiffAt ℝ ∞
    (fun t : ℝ => fabiusInv F hF (5 / 72 + t) - 1 / 4) 0
  simpa only [Function.comp_def, Pi.add_apply, Pi.sub_apply, id_eq] using
    (houter.comp 0 hshift).sub (contDiffAt_const (c := (1 / 4 : ℝ)))

private theorem contDiff_quarterQuadratic :
    ContDiff ℝ ∞ quarterQuadratic := by
  change ContDiff ℝ ∞ (fun z : ℝ => z + 4 * z ^ 2)
  simpa only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq] using
    contDiff_id.add (contDiff_const.mul (contDiff_id.pow 2))

private theorem iteratedDeriv_fabiusReal_quarter
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (fabiusReal F) (1 / 4) =
      if n = 0 then 5 / 72 else if n = 1 then 1 else if n = 2 then 8 else 0 := by
  obtain (_ | _ | _ | n) := n
  · rw [iteratedDeriv_zero, fabiusReal_one_quarter F hF]
    norm_num
  · rw [iteratedDeriv_one, fabius_deriv_quarter F hF]
    norm_num
  · rw [iteratedDeriv_fabiusReal_of_lt_one F hF 2 (by norm_num)]
    rw [show (2 : ℝ) ^ 2 * (1 / 4) = 1 by norm_num, extendedFabius_one F hF]
    norm_num
  · have harg :
        (2 : ℝ) ^ (n + 3) * (1 / 4) = 2 * (((2 ^ n : ℕ) : ℝ)) := by
      calc
        (2 : ℝ) ^ (n + 3) * (1 / 4) = (2 : ℝ) ^ n * 2 := by
          rw [pow_add]
          (norm_num; ring)
        _ = 2 * (((2 ^ n : ℕ) : ℝ)) := by
          (norm_num [Nat.cast_pow]; ring)
    have hzero :
        extendedFabius F ((2 : ℝ) ^ (n + 3) * (1 / 4)) = 0 := by
      rw [harg]
      exact extendedFabius_two_mul_nat F hF (2 ^ n)
    rw [iteratedDeriv_fabiusReal_of_lt_one F hF (n + 3) (by norm_num),
      hzero, mul_zero]
    simp

private theorem iteratedDeriv_centeredFabius_zero_of_pos
    (F : BoundedFabius) (hF : IsFabius F) {n : ℕ} (hn : 0 < n) :
    iteratedDeriv n (centeredFabius F) 0 =
      iteratedDeriv n (fabiusReal F) (1 / 4) := by
  have hshiftInf : ContDiff ℝ ∞ (fun z : ℝ => fabiusReal F (1 / 4 + z)) := by
    simpa only [Function.comp_def, Pi.add_apply, id_eq] using
      hF.contDiff.comp ((contDiff_const (c := (1 / 4 : ℝ))).add contDiff_id)
  have hshift : ContDiffAt ℝ n (fun z : ℝ => fabiusReal F (1 / 4 + z)) 0 :=
    hshiftInf.contDiffAt.of_le (mod_cast le_top)
  have hconst : ContDiffAt ℝ n (fun _ : ℝ => (5 / 72 : ℝ)) 0 :=
    contDiffAt_const
  change iteratedDeriv n
    ((fun z : ℝ => fabiusReal F (1 / 4 + z)) -
      fun _ : ℝ => (5 / 72 : ℝ)) 0 = _
  rw [iteratedDeriv_sub hshift hconst, iteratedDeriv_const, if_neg hn.ne']
  simp only [sub_zero]
  simpa only [add_zero] using
    congrFun (iteratedDeriv_comp_const_add n (fabiusReal F) (1 / 4)) (0 : ℝ)

private theorem iteratedDeriv_centeredFabius_zero
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (centeredFabius F) 0 =
      if n = 1 then 1 else if n = 2 then 8 else 0 := by
  obtain (_ | _ | _ | n) := n
  · rw [iteratedDeriv_zero]
    change fabiusReal F (1 / 4 + 0) - 5 / 72 = 0
    rw [add_zero, fabiusReal_one_quarter F hF]
    ring
  · rw [iteratedDeriv_centeredFabius_zero_of_pos F hF (by omega)]
    simpa using iteratedDeriv_fabiusReal_quarter F hF 1
  · rw [iteratedDeriv_centeredFabius_zero_of_pos F hF (by omega)]
    simpa using iteratedDeriv_fabiusReal_quarter F hF 2
  · rw [iteratedDeriv_centeredFabius_zero_of_pos F hF (by omega)]
    simpa using iteratedDeriv_fabiusReal_quarter F hF (n + 3)

private theorem iteratedDeriv_quarterQuadratic_zero (n : ℕ) :
    iteratedDeriv n quarterQuadratic 0 =
      if n = 1 then 1 else if n = 2 then 8 else 0 := by
  have hid : ContDiffAt ℝ n (fun z : ℝ => z) 0 := contDiffAt_id
  have hquad : ContDiffAt ℝ n (fun z : ℝ => 4 * z ^ 2) 0 :=
    contDiffAt_const.mul (contDiffAt_id.pow 2)
  change iteratedDeriv n
    ((fun z : ℝ => z) + fun z : ℝ => 4 * z ^ 2) 0 = _
  rw [iteratedDeriv_add hid hquad, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  by_cases h1 : n = 1
  · subst n
    norm_num
  by_cases h2 : n = 2
  · subst n
    norm_num
  · simp [h1, h2]

private theorem iteratedDeriv_comp_eq_of_outer_jet_eq
    {g q f : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ ∞ g (f x)) (hq : ContDiffAt ℝ ∞ q (f x))
    (hf : ContDiffAt ℝ ∞ f x)
    (hjet : ∀ k : ℕ, iteratedDeriv k g (f x) = iteratedDeriv k q (f x))
    (n : ℕ) :
    iteratedDeriv n (g ∘ f) x = iteratedDeriv n (q ∘ f) x := by
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hg hf
      (mod_cast le_top),
    iteratedDeriv_comp_eq_sum_orderedFinpartition hq hf
      (mod_cast le_top)]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [hjet c.length]

private theorem centeredFabius_comp_centeredFabiusInv_eventuallyEq
    (F : BoundedFabius) (hF : IsFabius F) :
    centeredFabius F ∘ centeredFabiusInv F hF =ᶠ[nhds 0] fun t : ℝ => t := by
  have hshift : Tendsto (fun t : ℝ => 5 / 72 + t) (nhds 0) (nhds (5 / 72)) := by
    have hshiftContDiff :
        ContDiffAt ℝ ∞ (fun (t : ℝ) => 5 / 72 + t) 0 :=
      by simpa only [Pi.add_apply, id_eq] using contDiffAt_const.add contDiffAt_id
    have hcontinuous := hshiftContDiff.continuousAt
    change Tendsto (fun t : ℝ => 5 / 72 + t) (nhds 0) (nhds (5 / 72 + 0))
      at hcontinuous
    simpa only [add_zero] using hcontinuous
  have hmem : ∀ᶠ t : ℝ in nhds 0, 5 / 72 + t ∈ Ioo (0 : ℝ) 1 :=
    hshift (isOpen_Ioo.mem_nhds (by norm_num))
  filter_upwards [hmem] with t ht
  change fabiusReal F
      (1 / 4 + (fabiusInv F hF (5 / 72 + t) - 1 / 4)) - 5 / 72 = t
  rw [show 1 / 4 + (fabiusInv F hF (5 / 72 + t) - 1 / 4) =
      fabiusInv F hF (5 / 72 + t) by ring,
    fabiusReal_fabiusInv F hF (Ioo_subset_Icc_self ht)]
  ring

private theorem iteratedDeriv_quarterQuadratic_comp_centeredFabiusInv
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (quarterQuadratic ∘ centeredFabiusInv F hF) 0 =
      if n = 1 then 1 else 0 := by
  have hH0 := centeredFabiusInv_zero F hF
  have hA : ContDiffAt ℝ ∞ (centeredFabius F) (centeredFabiusInv F hF 0) := by
    rw [hH0]
    exact (contDiff_centeredFabius F hF).contDiffAt
  have hQ : ContDiffAt ℝ ∞ quarterQuadratic (centeredFabiusInv F hF 0) := by
    rw [hH0]
    exact contDiff_quarterQuadratic.contDiffAt
  have hcomp := iteratedDeriv_comp_eq_of_outer_jet_eq hA hQ
    (contDiffAt_centeredFabiusInv F hF) (fun k => by
      rw [hH0, iteratedDeriv_centeredFabius_zero F hF,
        iteratedDeriv_quarterQuadratic_zero]) n
  have hid :
      iteratedDeriv n (centeredFabius F ∘ centeredFabiusInv F hF) 0 =
        if n = 1 then 1 else 0 :=
    ((centeredFabius_comp_centeredFabiusInv_eventuallyEq F hF).iteratedDeriv_eq n).trans
      iteratedDeriv_fun_id_zero
  exact hcomp.symm.trans hid

private theorem centeredInverseJet_raw_recurrence
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (centeredFabiusInv F hF) 0 +
        4 * ∑ i ∈ range (n + 1),
          (n.choose i : ℝ) * iteratedDeriv i (centeredFabiusInv F hF) 0 *
            iteratedDeriv (n - i) (centeredFabiusInv F hF) 0 =
      if n = 1 then 1 else 0 := by
  have h := iteratedDeriv_quarterQuadratic_comp_centeredFabiusInv F hF n
  simp only [Function.comp_def, quarterQuadratic, pow_two] at h
  have hH : ContDiffAt ℝ n (centeredFabiusInv F hF) 0 :=
    (contDiffAt_centeredFabiusInv F hF).of_le (mod_cast le_top)
  have hscaled : ContDiffAt ℝ n
      (fun t : ℝ => 4 *
        (centeredFabiusInv F hF t * centeredFabiusInv F hF t)) 0 :=
    by simpa only [Pi.mul_apply] using contDiffAt_const.mul (hH.mul hH)
  change iteratedDeriv n
    ((centeredFabiusInv F hF) + fun t : ℝ => 4 *
      (centeredFabiusInv F hF t * centeredFabiusInv F hF t)) 0 = _ at h
  rw [iteratedDeriv_add hH hscaled, iteratedDeriv_const_mul_field] at h
  have hmul := iteratedDeriv_mul hH hH
  change
    iteratedDeriv n
        (fun t : ℝ => centeredFabiusInv F hF t * centeredFabiusInv F hF t) 0 =
      ∑ i ∈ range (n + 1),
        (n.choose i : ℝ) * iteratedDeriv i (centeredFabiusInv F hF) 0 *
          iteratedDeriv (n - i) (centeredFabiusInv F hF) 0 at hmul
  rw [hmul] at h
  exact h

private theorem choose_div_factorial_real {n i : ℕ} (hi : i ≤ n) :
    (n.choose i : ℝ) / (n.factorial : ℝ) =
      1 / ((i.factorial : ℝ) * ((n - i).factorial : ℝ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial hi
  have hcast :
      (n.choose i : ℝ) * (i.factorial : ℝ) * ((n - i).factorial : ℝ) =
        (n.factorial : ℝ) := by
    exact_mod_cast hnat
  have hn : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hi' : (i.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i
  have hni : ((n - i).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - i)
  field_simp [hn, hi', hni]
  exact hcast

private theorem normalizedCenteredInverseJet_convolution
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    normalizedCenteredInverseJet F hF n +
        4 * ∑ p ∈ antidiagonal n,
          normalizedCenteredInverseJet F hF p.1 *
            normalizedCenteredInverseJet F hF p.2 =
      if n = 1 then 1 else 0 := by
  have hraw := centeredInverseJet_raw_recurrence F hF n
  have hdiv := congrArg (fun x : ℝ => x / (n.factorial : ℝ)) hraw
  have hleft :
      (iteratedDeriv n (centeredFabiusInv F hF) 0 +
          4 * ∑ i ∈ range (n + 1),
            (n.choose i : ℝ) * iteratedDeriv i (centeredFabiusInv F hF) 0 *
              iteratedDeriv (n - i) (centeredFabiusInv F hF) 0) /
            (n.factorial : ℝ) =
        normalizedCenteredInverseJet F hF n +
          4 * ∑ i ∈ range (n + 1),
            normalizedCenteredInverseJet F hF i *
              normalizedCenteredInverseJet F hF (n - i) := by
    calc
      (iteratedDeriv n (centeredFabiusInv F hF) 0 +
          4 * ∑ i ∈ range (n + 1),
            (n.choose i : ℝ) * iteratedDeriv i (centeredFabiusInv F hF) 0 *
              iteratedDeriv (n - i) (centeredFabiusInv F hF) 0) /
            (n.factorial : ℝ) =
          normalizedCenteredInverseJet F hF n +
            4 * ∑ i ∈ range (n + 1),
              ((n.choose i : ℝ) * iteratedDeriv i (centeredFabiusInv F hF) 0 *
                iteratedDeriv (n - i) (centeredFabiusInv F hF) 0) /
                  (n.factorial : ℝ) := by
        simp only [normalizedCenteredInverseJet]
        rw [← Finset.sum_div]
        ring
      _ = normalizedCenteredInverseJet F hF n +
          4 * ∑ i ∈ range (n + 1),
            normalizedCenteredInverseJet F hF i *
              normalizedCenteredInverseJet F hF (n - i) := by
        congr 2
        apply Finset.sum_congr rfl
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
        simp only [normalizedCenteredInverseJet]
        calc
          ((n.choose i : ℝ) * iteratedDeriv i (centeredFabiusInv F hF) 0 *
              iteratedDeriv (n - i) (centeredFabiusInv F hF) 0) /
                (n.factorial : ℝ) =
              ((n.choose i : ℝ) / (n.factorial : ℝ)) *
                iteratedDeriv i (centeredFabiusInv F hF) 0 *
                  iteratedDeriv (n - i) (centeredFabiusInv F hF) 0 := by ring
          _ = (1 / ((i.factorial : ℝ) * ((n - i).factorial : ℝ))) *
                iteratedDeriv i (centeredFabiusInv F hF) 0 *
                  iteratedDeriv (n - i) (centeredFabiusInv F hF) 0 := by
              rw [choose_div_factorial_real hin]
          _ = (iteratedDeriv i (centeredFabiusInv F hF) 0 /
                (i.factorial : ℝ)) *
              (iteratedDeriv (n - i) (centeredFabiusInv F hF) 0 /
                ((n - i).factorial : ℝ)) := by
              simp only [div_eq_mul_inv, mul_inv_rev]
              ring
  have hright :
      (if n = 1 then (1 : ℝ) else 0) / (n.factorial : ℝ) =
        if n = 1 then 1 else 0 := by
    by_cases hn : n = 1
    · subst n
      norm_num
    · simp [hn]
  rw [hleft, hright] at hdiv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [Nat.succ_eq_add_one] using hdiv

private theorem normalizedCenteredInverseJet_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    normalizedCenteredInverseJet F hF 0 = 0 := by
  simp [normalizedCenteredInverseJet, iteratedDeriv_zero,
    centeredFabiusInv_zero F hF]

private theorem normalizedCenteredInverseJet_succ
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    normalizedCenteredInverseJet F hF (m + 1) =
      (-4 : ℝ) ^ m * (catalan m : ℝ) := by
  simpa using QuadraticInverse.seq_succ_of_convolution
    (c := (4 : ℝ)) (s := normalizedCenteredInverseJet F hF)
    (normalizedCenteredInverseJet_zero F hF)
    (normalizedCenteredInverseJet_convolution F hF) m

private theorem normalizedCenteredInverseJet_eq_coeff
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    normalizedCenteredInverseJet F hF n =
      PowerSeries.coeff n (QuadraticInverse.inverse (4 : ℝ)) := by
  cases n with
  | zero =>
      rw [normalizedCenteredInverseJet_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        QuadraticInverse.constantCoeff_inverse]
  | succ m =>
      rw [normalizedCenteredInverseJet_succ,
        QuadraticInverse.coeff_succ_inverse]

/-- **The full centered quarter-inverse jet.**  At the exact quarter anchor
`5/72 = F(1/4)`, every derivative of the centered bounded Fabius inverse is
the corresponding exponential coefficient of the reverted quadratic
`X + 4X²`.  This is an equality of jets only; it does not assert local
analyticity. -/
theorem iteratedDeriv_centeredFabiusInv_quarter_eq_quadraticInverse
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    iteratedDeriv n (fun t => fabiusInv F hF (5 / 72 + t) - 1 / 4) 0 =
      (n.factorial : ℝ) *
        PowerSeries.coeff n (QuadraticInverse.inverse (4 : ℝ)) := by
  have hcoeff := normalizedCenteredInverseJet_eq_coeff F hF n
  have hfac : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  change iteratedDeriv n (centeredFabiusInv F hF) 0 = _
  calc
    iteratedDeriv n (centeredFabiusInv F hF) 0 =
        (n.factorial : ℝ) *
          (iteratedDeriv n (centeredFabiusInv F hF) 0 / (n.factorial : ℝ)) :=
      (mul_div_cancel₀ _ hfac).symm
    _ = (n.factorial : ℝ) *
        PowerSeries.coeff n (QuadraticInverse.inverse (4 : ℝ)) := by
      change (n.factorial : ℝ) * normalizedCenteredInverseJet F hF n = _
      rw [hcoeff]

private theorem iteratedDeriv_centeredFabiusInv_zero_of_pos
    (F : BoundedFabius) (hF : IsFabius F) {n : ℕ} (hn : 0 < n) :
    iteratedDeriv n (centeredFabiusInv F hF) 0 =
      iteratedDeriv n (fabiusInv F hF) (5 / 72) := by
  have hshift : ContDiffAt ℝ n (fun t : ℝ => fabiusInv F hF (5 / 72 + t)) 0 := by
    have hfull : ContDiffAt ℝ ∞ (fun t : ℝ => fabiusInv F hF (5 / 72 + t)) 0 := by
      have haffine : ContDiffAt ℝ ∞ (fun t : ℝ => 5 / 72 + t) 0 :=
        (contDiffAt_const (c := (5 / 72 : ℝ))).add contDiffAt_id
      have houter : ContDiffAt ℝ ∞ (fabiusInv F hF)
          ((fun t : ℝ => 5 / 72 + t) 0) := by
        simpa only [add_zero] using
          fabiusInv_contDiffAt F hF (y := (5 / 72 : ℝ))
            (by norm_num) (by norm_num)
      exact houter.fun_comp 0 haffine
    exact hfull.of_le (mod_cast le_top)
  have hconst : ContDiffAt ℝ n (fun _ : ℝ => (1 / 4 : ℝ)) 0 :=
    contDiffAt_const
  change iteratedDeriv n
    ((fun t : ℝ => fabiusInv F hF (5 / 72 + t)) -
      fun _ : ℝ => (1 / 4 : ℝ)) 0 = _
  rw [iteratedDeriv_sub hshift hconst, iteratedDeriv_const, if_neg hn.ne']
  simp only [sub_zero]
  simpa only [add_zero] using
    congrFun (iteratedDeriv_comp_const_add n (fabiusInv F hF) (5 / 72)) (0 : ℝ)

/-- **Catalan formula for the actual bounded Fabius inverse.**  The derivative
of order `m+1` at `5/72` is `(-4)^m C_m` multiplied by `(m+1)!`.  Thus the
jet starts `1, -8, 192, -7680, …`, despite the failure of analyticity at the
quarter anchor. -/
theorem iteratedDeriv_fabiusInv_five_seventy_two_succ
    (F : BoundedFabius) (hF : IsFabius F) (m : ℕ) :
    iteratedDeriv (m + 1) (fabiusInv F hF) (5 / 72) =
      ((m + 1).factorial : ℝ) * (-4 : ℝ) ^ m * (catalan m : ℝ) := by
  have h := iteratedDeriv_centeredFabiusInv_quarter_eq_quadraticInverse
    F hF (m + 1)
  change iteratedDeriv (m + 1) (centeredFabiusInv F hF) 0 = _ at h
  rw [iteratedDeriv_centeredFabiusInv_zero_of_pos F hF (by omega),
    QuadraticInverse.coeff_succ_inverse] at h
  simpa only [mul_assoc] using h

end

end Fabius
