import GowersSzemeredi.Sections08_09
import GowersSzemeredi.Proofs01_03

/-!
# Quadratic bias from a linearly varying Fourier coefficient

This module proves Gowers's Proposition 8.1.  The auxiliary lemmas below keep
the character-orthogonality and finite Cauchy--Schwarz parts separate from the
progression bookkeeping.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod ComplexConjugate
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma prop81_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) :
    exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma prop81_exponential_zero {N : Nat} [NeZero N] :
    exponential (0 : ZMod N) = 1 := by
  exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))

@[simp] private lemma prop81_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact AddChar.norm_apply (ZMod.stdAddChar (N := N)) x

private lemma prop81_sum_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    ∑ r : ZMod N, exponential (x * r) =
      if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private def prop81PairSums {N : Nat} (K : Finset (ZMod N)) :
    Finset (ZMod N) :=
  K.biUnion fun x => K.image fun y => x + y

private lemma prop81_mem_pairSums {N : Nat} {K : Finset (ZMod N)}
    {x y : ZMod N} (hx : x ∈ K) (hy : y ∈ K) :
    x + y ∈ prop81PairSums K := by
  classical
  simp only [prop81PairSums, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨x, hx, y, hy, rfl⟩

private def prop81Orbit {N : Nat} (P : ModAP N) (i : Nat) : ZMod N :=
  P.start + (i : ZMod N) * P.step

private lemma prop81_carrier_eq_image_range {N : Nat} (P : ModAP N) :
    P.carrier = (Finset.range P.length).image (prop81Orbit P) := by
  classical
  ext x
  unfold ModAP.carrier prop81Orbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

private lemma prop81_orbit_mod_order {N : Nat} [NeZero N]
    (P : ModAP N) (i : Nat) :
    prop81Orbit P (i % addOrderOf P.step) = prop81Orbit P i := by
  unfold prop81Orbit
  congr 1
  simpa only [nsmul_eq_mul] using mod_addOrderOf_nsmul P.step i

private lemma prop81_orbit_injOn_order {N : Nat} [NeZero N]
    (P : ModAP N) :
    Set.InjOn (prop81Orbit P) (Set.Iio (addOrderOf P.step)) := by
  intro i hi j hj hij
  have hmul : (i : ZMod N) * P.step = (j : ZMod N) * P.step :=
    add_left_cancel hij
  have hnsmul : i • P.step = j • P.step := by
    simpa only [nsmul_eq_mul] using hmul
  have hmod := ((isOfFinAddOrder_of_finite P.step).nsmul_inj_mod).mp hnsmul
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod

private lemma prop81_carrier_eq_order_range_of_le {N : Nat} [NeZero N]
    (P : ModAP N) (horder : addOrderOf P.step ≤ P.length) :
    P.carrier =
      (Finset.range (addOrderOf P.step)).image (prop81Orbit P) := by
  classical
  rw [prop81_carrier_eq_image_range]
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨i % addOrderOf P.step, ?_, prop81_orbit_mod_order P i⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ (addOrderOf_pos P.step))
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Finset.range_mono horder hi, rfl⟩

private lemma prop81_carrier_card {N : Nat} [NeZero N] (P : ModAP N) :
    P.carrier.card = min P.length (addOrderOf P.step) := by
  classical
  by_cases hlength : P.length ≤ addOrderOf P.step
  · have hinj : Set.InjOn (prop81Orbit P)
        (Finset.range P.length : Set Nat) := by
      intro i hi j hj hij
      apply prop81_orbit_injOn_order P
      · exact lt_of_lt_of_le (Finset.mem_range.mp hi) hlength
      · exact lt_of_lt_of_le (Finset.mem_range.mp hj) hlength
      · exact hij
    rw [min_eq_left hlength, prop81_carrier_eq_image_range,
      Finset.card_image_iff.mpr hinj, Finset.card_range]
  · have horder : addOrderOf P.step ≤ P.length :=
      Nat.le_of_lt (Nat.lt_of_not_ge hlength)
    have hinj : Set.InjOn (prop81Orbit P)
        (Finset.range (addOrderOf P.step) : Set Nat) := by
      intro i hi j hj hij
      exact prop81_orbit_injOn_order P (Finset.mem_range.mp hi)
        (Finset.mem_range.mp hj) hij
    rw [min_eq_right horder, prop81_carrier_eq_order_range_of_le P horder,
      Finset.card_image_iff.mpr hinj, Finset.card_range]

private def prop81NormalizedAP {N : Nat} (P : ModAP N) : ModAP N :=
  { P with length := P.carrier.card }

private lemma prop81_normalized_carrier {N : Nat} [NeZero N] (P : ModAP N) :
    (prop81NormalizedAP P).carrier = P.carrier := by
  classical
  let t := addOrderOf P.step
  have hcard := prop81_carrier_card P
  by_cases hlength : P.length ≤ t
  · have heq : P.carrier.card = P.length := by
      simpa only [t, min_eq_left hlength] using hcard
    simp only [prop81NormalizedAP, heq]
  · have horder : t ≤ P.length := Nat.le_of_lt (Nat.lt_of_not_ge hlength)
    have heq : P.carrier.card = t := by
      simpa only [t, min_eq_right horder] using hcard
    rw [prop81_carrier_eq_order_range_of_le P horder]
    change ({ P with length := P.carrier.card } : ModAP N).carrier = _
    rw [prop81_carrier_eq_image_range, heq]
    rfl

private lemma prop81_pairSums_card_le (N : Nat) [NeZero N] (P : ModAP N) :
    (prop81PairSums P.carrier).card ≤ 2 * P.carrier.card := by
  classical
  let Q := prop81NormalizedAP P
  let cover : Finset (ZMod N) :=
    (Finset.range (2 * P.carrier.card)).image fun (n : Nat) =>
      Q.start + Q.start + (n : ZMod N) * Q.step
  have hQcarrier : Q.carrier = P.carrier := prop81_normalized_carrier P
  have hQlength : Q.length = P.carrier.card := rfl
  have hsubset : prop81PairSums P.carrier ⊆ cover := by
    intro z hz
    simp only [prop81PairSums, Finset.mem_biUnion, Finset.mem_image] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    rw [← hQcarrier, prop81_carrier_eq_image_range] at hx hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, hj, rfl⟩ := hy
    rw [Finset.mem_image]
    refine ⟨i + j, ?_, ?_⟩
    · rw [Finset.mem_range, hQlength] at hi hj
      rw [Finset.mem_range]
      omega
    · unfold prop81Orbit
      push_cast
      ring
  calc
    (prop81PairSums P.carrier).card ≤ cover.card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.range (2 * P.carrier.card)).card := Finset.card_image_le
    _ = 2 * P.carrier.card := Finset.card_range _

@[simp] private lemma prop81_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

@[simp] private lemma prop81_star_balanced {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    star (balanced A x) = balanced A x := by
  classical
  by_cases hx : x ∈ A <;>
    simp [balanced, indicator, density, hx]

private lemma prop81_balanced_norm_le_one {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) : ‖balanced A x‖ ≤ 1 := by
  classical
  have hcard : A.card ≤ N := by
    calc
      A.card ≤ (Finset.univ : Finset (ZMod N)).card :=
        Finset.card_le_card (Finset.subset_univ A)
      _ = N := by simp
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hd0 : (0 : Real) ≤ density A := by
    unfold density
    positivity
  have hd1 : density A ≤ 1 := by
    unfold density
    rw [div_le_one hNpos]
    exact_mod_cast hcard
  by_cases hx : x ∈ A
  · simp only [balanced, indicator, hx, if_true]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hd1)]
    linarith
  · simp only [balanced, indicator, hx, if_false, zero_sub]
    norm_cast
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hd0]
    exact hd1

private lemma prop81_fourier_difference_shifted {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (k r : ZMod N) :
    fourier (difference (balanced A) k) r =
      ∑ s : ZMod N,
        balanced A (s + k) * balanced A s *
          exponential (-((s + k) * r)) := by
  classical
  simp only [fourier, ZMod.dft_apply, smul_eq_mul, difference,
    prop81_star_balanced]
  rw [← (Equiv.addRight k).sum_comp]
  apply Finset.sum_congr rfl
  intro s hs
  change exponential (-((s + k) * r)) *
      (balanced A (s + k) * balanced A ((s + k) - k)) = _
  rw [add_sub_cancel_right]
  ring
  all_goals simp

private lemma prop81_fourier_difference_norm_sq {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (k r : ZMod N) :
    (((‖fourier (difference (balanced A) k) r‖ ^ 2 : Real)) : Complex) =
      ∑ s : ZMod N, ∑ t : ZMod N,
        balanced A (s + k) * balanced A s *
          balanced A (t + k) * balanced A t *
          exponential (-((s - t) * r)) := by
  classical
  rw [prop81_fourier_difference_shifted]
  calc
    (((‖∑ s : ZMod N,
        balanced A (s + k) * balanced A s *
          exponential (-((s + k) * r))‖ ^ 2 : Real)) : Complex) =
      (∑ s : ZMod N,
        balanced A (s + k) * balanced A s *
          exponential (-((s + k) * r))) *
        star (∑ t : ZMod N,
          balanced A (t + k) * balanced A t *
            exponential (-((t + k) * r))) := by
      simpa only [Complex.star_def, ← Complex.ofReal_pow] using
        (Complex.mul_conj' _).symm
    _ = ∑ s : ZMod N, ∑ t : ZMod N,
        balanced A (s + k) * balanced A s *
          balanced A (t + k) * balanced A t *
          exponential (-((s - t) * r)) := by
      conv_rhs => rw [sum_comm]
      simp only [star_sum, star_mul, prop81_star_balanced,
        prop81_star_exponential, neg_neg]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro s hs
      calc
        _ = balanced A (t + k) * balanced A t *
            balanced A (s + k) * balanced A s *
            (exponential (-((s + k) * r)) *
              exponential ((t + k) * r)) := by ring
        _ = balanced A (t + k) * balanced A t *
            balanced A (s + k) * balanced A s *
            exponential (-((s - t) * r)) := by
          rw [← prop81_exponential_add]
          rw [show -((s + k) * r) + (t + k) * r =
              -((s - t) * r) by ring]
        _ = balanced A (s + k) * balanced A s *
            balanced A (t + k) * balanced A t *
            exponential (-((s - t) * r)) := by ac_rfl

private def prop81YEquiv {N : Nat} (s l : ZMod N) : ZMod N ≃ ZMod N where
  toFun y := s - y + l
  invFun y := s - y + l
  left_inv y := by ring
  right_inv y := by ring

private lemma prop81_sum_four_reorder {N : Nat} [NeZero N]
    (K : Finset (ZMod N))
    (F : ZMod N → ZMod N → ZMod N → ZMod N → Complex) :
    (∑ l ∈ K, ∑ k ∈ K, ∑ s : ZMod N, ∑ y : ZMod N, F l k s y) =
      ∑ s : ZMod N, ∑ y : ZMod N,
        ∑ k ∈ K, ∑ l ∈ K, F l k s y := by
  calc
    _ = ∑ l ∈ K, ∑ s : ZMod N,
          ∑ k ∈ K, ∑ y : ZMod N, F l k s y := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [sum_comm]
    _ = ∑ s : ZMod N, ∑ l ∈ K,
          ∑ k ∈ K, ∑ y : ZMod N, F l k s y := by
      rw [sum_comm]
    _ = ∑ s : ZMod N, ∑ l ∈ K, ∑ y : ZMod N,
          ∑ k ∈ K, F l k s y := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro l hl
      rw [sum_comm]
    _ = ∑ s : ZMod N, ∑ y : ZMod N, ∑ l ∈ K,
          ∑ k ∈ K, F l k s y := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro y hy
      rw [sum_comm]

private def prop81BilinearSum {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (f₁ f₂ f₃ : ZMod N → Complex)
    (a b c : ZMod N) : Complex :=
  ∑ i ∈ K, ∑ j ∈ K,
    f₁ i * f₂ j * f₃ (i + j) *
      exponential (-(a * i + b * j - 2 * c * i * j))

private def prop81LocalBilinear {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (K : Finset (ZMod N))
    (lambda mu c s y : ZMod N) : Complex :=
  prop81BilinearSum K
    (fun k => balanced A (s + k))
    (fun l => balanced A (s - y + l))
    (fun u => balanced A (s - y + u))
    (lambda * y) (-mu) c

private lemma prop81_local_phase {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (lambda mu c s y k l : ZMod N)
    (hc : 2 * c = lambda) :
    balanced A (s + k) * balanced A s *
        balanced A (s - y + l + k) * balanced A (s - y + l) *
        exponential (-((y - l) * (lambda * k + mu))) =
      balanced A s * exponential (-(mu * y)) *
        (balanced A (s + k) * balanced A (s - y + l) *
          balanced A (s - y + (k + l)) *
          exponential (-((lambda * y) * k + (-mu) * l - 2 * c * k * l))) := by
  have hphase :
      -((y - l) * (lambda * k + mu)) =
        -(mu * y) +
          -((lambda * y) * k + (-mu) * l - 2 * c * k * l) := by
    rw [hc]
    ring
  conv_lhs =>
    rw [hphase, prop81_exponential_add]
  rw [show s - y + l + k = s - y + (k + l) by ring]
  ring

private lemma prop81_energy_average_identity {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (K : Finset (ZMod N))
    (lambda mu c : ZMod N) (hc : 2 * c = lambda) :
    (K.card : Complex) *
        ((∑ k ∈ K,
          ‖fourier (difference (balanced A) k) (lambda * k + mu)‖ ^ 2 : Real) :
          Complex) =
      ∑ s : ZMod N, balanced A s *
        ∑ y : ZMod N,
          exponential (-(mu * y)) *
            prop81LocalBilinear A K lambda mu c s y := by
  classical
  rw [Complex.ofReal_sum]
  simp_rw [prop81_fourier_difference_norm_sq]
  calc
    (K.card : Complex) *
        ∑ k ∈ K, ∑ s : ZMod N, ∑ t : ZMod N,
          balanced A (s + k) * balanced A s *
            balanced A (t + k) * balanced A t *
            exponential (-((s - t) * (lambda * k + mu))) =
      ∑ l ∈ K, ∑ k ∈ K, ∑ s : ZMod N, ∑ t : ZMod N,
          balanced A (s + k) * balanced A s *
          balanced A (t + k) * balanced A t *
            exponential (-((s - t) * (lambda * k + mu))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ l ∈ K, ∑ k ∈ K, ∑ s : ZMod N, ∑ y : ZMod N,
          balanced A (s + k) * balanced A s *
            balanced A (s - y + l + k) * balanced A (s - y + l) *
            exponential (-((y - l) * (lambda * k + mu))) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro s hs
      rw [← (prop81YEquiv s l).sum_comp]
      apply Finset.sum_congr rfl
      intro y hy
      change balanced A (s + k) * balanced A s *
          balanced A (s - y + l + k) * balanced A (s - y + l) *
          exponential (-((s - (s - y + l)) * (lambda * k + mu))) = _
      rw [show s - (s - y + l) = y - l by ring]
    _ = ∑ s : ZMod N, ∑ y : ZMod N,
          ∑ k ∈ K, ∑ l ∈ K,
            balanced A (s + k) * balanced A s *
              balanced A (s - y + l + k) * balanced A (s - y + l) *
              exponential (-((y - l) * (lambda * k + mu))) := by
      exact prop81_sum_four_reorder K _
    _ = ∑ s : ZMod N, balanced A s *
        ∑ y : ZMod N,
          exponential (-(mu * y)) *
            prop81LocalBilinear A K lambda mu c s y := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [prop81LocalBilinear, prop81BilinearSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      simpa only [add_assoc, add_comm l k, mul_assoc] using
        prop81_local_phase A lambda mu c s y k l hc

private lemma prop81_energy_le_local_norm_sum {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (K : Finset (ZMod N))
    (lambda mu c : ZMod N) (hc : 2 * c = lambda) :
    (K.card : Real) *
        (∑ k ∈ K,
          ‖fourier (difference (balanced A) k) (lambda * k + mu)‖ ^ 2) ≤
      ∑ s : ZMod N, ∑ y : ZMod N,
        ‖prop81LocalBilinear A K lambda mu c s y‖ := by
  classical
  let E : Real := ∑ k ∈ K,
    ‖fourier (difference (balanced A) k) (lambda * k + mu)‖ ^ 2
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hid := prop81_energy_average_identity A K lambda mu c hc
  calc
    (K.card : Real) * E = ‖(K.card : Complex) * (E : Complex)‖ := by
      simp only [norm_mul, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg hE]
    _ = ‖∑ s : ZMod N, balanced A s *
        ∑ y : ZMod N,
          exponential (-(mu * y)) *
            prop81LocalBilinear A K lambda mu c s y‖ := by
      rw [hid]
    _ ≤ ∑ s : ZMod N,
        ‖balanced A s *
          ∑ y : ZMod N,
            exponential (-(mu * y)) *
              prop81LocalBilinear A K lambda mu c s y‖ := norm_sum_le _ _
    _ ≤ ∑ s : ZMod N,
        ‖∑ y : ZMod N,
          exponential (-(mu * y)) *
            prop81LocalBilinear A K lambda mu c s y‖ := by
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (prop81_balanced_norm_le_one A s)
    _ ≤ ∑ s : ZMod N, ∑ y : ZMod N,
        ‖exponential (-(mu * y)) *
          prop81LocalBilinear A K lambda mu c s y‖ := by
      apply Finset.sum_le_sum
      intro s hs
      exact norm_sum_le _ _
    _ = ∑ s : ZMod N, ∑ y : ZMod N,
        ‖prop81LocalBilinear A K lambda mu c s y‖ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro y hy
      rw [norm_mul, prop81_norm_exponential, one_mul]

private def prop81H1 {N : Nat} [NeZero N] (K : Finset (ZMod N))
    (f : ZMod N → Complex) (a c : ZMod N) (x : ZMod N) : Complex :=
  if x ∈ K then f x * exponential (-(a * x + c * x ^ 2)) else 0

private def prop81H3 {N : Nat} [NeZero N] (K : Finset (ZMod N))
    (f : ZMod N → Complex) (c : ZMod N) (x : ZMod N) : Complex :=
  if x ∈ prop81PairSums K then f x * exponential (c * x ^ 2) else 0

private lemma prop81_fourier_H1 {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (f : ZMod N → Complex) (a c r : ZMod N) :
    fourier (prop81H1 K f a c) r =
      ∑ x ∈ K, f x * exponential (-(a * x + c * x ^ 2 + r * x)) := by
  classical
  simp only [fourier, ZMod.dft_apply, smul_eq_mul, prop81H1]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.univ.filter fun x : ZMod N => x ∈ K) = K := by
    ext x
    simp
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro x hx
  change exponential (-(x * r)) *
      (f x * exponential (-(a * x + c * x ^ 2))) = _
  calc
    _ = f x * (exponential (-(x * r)) *
        exponential (-(a * x + c * x ^ 2))) := by ring
    _ = f x * exponential (-(x * r) + -(a * x + c * x ^ 2)) := by
      rw [prop81_exponential_add]
    _ = _ := by
      congr 2
      ring

private lemma prop81_fourier_H3_neg {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (f : ZMod N → Complex) (c r : ZMod N) :
    fourier (prop81H3 K f c) (-r) =
      ∑ x ∈ prop81PairSums K,
        f x * exponential (c * x ^ 2 + r * x) := by
  classical
  simp only [fourier, ZMod.dft_apply, smul_eq_mul, prop81H3]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hfilter :
      (Finset.univ.filter fun x : ZMod N => x ∈ prop81PairSums K) =
        prop81PairSums K := by
    ext x
    simp
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro x hx
  change exponential (-(x * -r)) *
      (f x * exponential (c * x ^ 2)) = _
  calc
    _ = f x * (exponential (-(x * -r)) *
        exponential (c * x ^ 2)) := by ring
    _ = f x * exponential (-(x * -r) + c * x ^ 2) := by
      rw [prop81_exponential_add]
    _ = _ := by
      congr 2
      ring

private lemma prop81_triple_orthogonality {N : Nat} [NeZero N]
    (f₁ f₂ f₃ : ZMod N → Complex) (a b c i j u : ZMod N) :
    (∑ r : ZMod N,
        (f₁ i * exponential (-(a * i + c * i ^ 2 + r * i))) *
          (f₂ j * exponential (-(b * j + c * j ^ 2 + r * j))) *
          (f₃ u * exponential (c * u ^ 2 + r * u))) =
      if u = i + j then
        (N : Complex) *
          (f₁ i * f₂ j * f₃ u *
            exponential (-(a * i + b * j - 2 * c * i * j)))
      else 0 := by
  classical
  let base : Complex := f₁ i * f₂ j * f₃ u *
    exponential (-(a * i + c * i ^ 2) - (b * j + c * j ^ 2) + c * u ^ 2)
  have hterm (r : ZMod N) :
      (f₁ i * exponential (-(a * i + c * i ^ 2 + r * i))) *
          (f₂ j * exponential (-(b * j + c * j ^ 2 + r * j))) *
          (f₃ u * exponential (c * u ^ 2 + r * u)) =
        base * exponential ((u - i - j) * r) := by
    calc
      _ = f₁ i * f₂ j * f₃ u *
          (exponential (-(a * i + c * i ^ 2 + r * i)) *
            exponential (-(b * j + c * j ^ 2 + r * j)) *
            exponential (c * u ^ 2 + r * u)) := by ring
      _ = f₁ i * f₂ j * f₃ u *
          exponential (-(a * i + c * i ^ 2 + r * i) +
            -(b * j + c * j ^ 2 + r * j) + (c * u ^ 2 + r * u)) := by
        congr 1
        rw [← prop81_exponential_add, ← prop81_exponential_add]
      _ = f₁ i * f₂ j * f₃ u *
          exponential ((-(a * i + c * i ^ 2) - (b * j + c * j ^ 2) +
            c * u ^ 2) +
            (u - i - j) * r) := by
        congr 2
        ring
      _ = base * exponential ((u - i - j) * r) := by
        rw [prop81_exponential_add]
        dsimp only [base]
        ring
  calc
    (∑ r : ZMod N,
        (f₁ i * exponential (-(a * i + c * i ^ 2 + r * i))) *
          (f₂ j * exponential (-(b * j + c * j ^ 2 + r * j))) *
          (f₃ u * exponential (c * u ^ 2 + r * u))) =
        ∑ r : ZMod N, base * exponential ((u - i - j) * r) := by
      apply Finset.sum_congr rfl
      intro r _
      exact hterm r
    _ = base * ∑ r : ZMod N, exponential ((u - i - j) * r) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [prop81_sum_exponential_mul]
      by_cases h : u = i + j
      · rw [if_pos h]
        have hz : u - i - j = 0 := by rw [h]; ring
        rw [if_pos hz]
        dsimp only [base]
        rw [h]
        have hphase :
            exponential (-(a * i + c * i ^ 2) - (b * j + c * j ^ 2) +
                c * (i + j) ^ 2) =
              exponential (-(a * i + b * j - 2 * c * i * j)) := by
          congr 1
          ring
        rw [hphase]
        ring
      · rw [if_neg h]
        have hnz : u - i - j ≠ 0 := by
          intro hz
          apply h
          linear_combination hz
        rw [if_neg hnz, mul_zero]

private lemma prop81_fourier_triple {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (f₁ f₂ f₃ : ZMod N → Complex)
    (a b c : ZMod N) :
    (∑ r : ZMod N,
        fourier (prop81H1 K f₁ a c) r *
          fourier (prop81H1 K f₂ b c) r *
          fourier (prop81H3 K f₃ c) (-r)) =
      (N : Complex) * prop81BilinearSum K f₁ f₂ f₃ a b c := by
  classical
  simp_rw [prop81_fourier_H1, prop81_fourier_H3_neg]
  calc
    (∑ r : ZMod N,
        (∑ i ∈ K, f₁ i * exponential (-(a * i + c * i ^ 2 + r * i))) *
          (∑ j ∈ K, f₂ j * exponential (-(b * j + c * j ^ 2 + r * j))) *
          (∑ u ∈ prop81PairSums K,
            f₃ u * exponential (c * u ^ 2 + r * u))) =
        ∑ r : ZMod N, ∑ i ∈ K, ∑ j ∈ K,
          ∑ u ∈ prop81PairSums K,
            (f₁ i * exponential (-(a * i + c * i ^ 2 + r * i))) *
              (f₂ j * exponential (-(b * j + c * j ^ 2 + r * j))) *
              (f₃ u * exponential (c * u ^ 2 + r * u)) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [sum_comm]
      rw [sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = ∑ i ∈ K, ∑ j ∈ K, ∑ u ∈ prop81PairSums K,
          ∑ r : ZMod N,
            (f₁ i * exponential (-(a * i + c * i ^ 2 + r * i))) *
              (f₂ j * exponential (-(b * j + c * j ^ 2 + r * j))) *
              (f₃ u * exponential (c * u ^ 2 + r * u)) := by
      rw [sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_comm]
    _ = (N : Complex) * prop81BilinearSum K f₁ f₂ f₃ a b c := by
      simp_rw [prop81_triple_orthogonality]
      simp only [prop81BilinearSum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_eq_single (i + j)]
      · simp
      · intro u hu hne
        rw [if_neg hne]
      · intro hnot
        exact (hnot (prop81_mem_pairSums hi hj)).elim

private lemma prop81_H1_fourier_energy_le {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (f : ZMod N → Complex) (a c : ZMod N)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    (∑ r : ZMod N, ‖fourier (prop81H1 K f a c) r‖ ^ 2) ≤
      (N : Real) * K.card := by
  classical
  rw [identity_2_3_holds]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ x : ZMod N, ‖prop81H1 K f a c x‖ ^ 2) =
        ∑ x : ZMod N, if x ∈ K then ‖f x‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxK : x ∈ K <;> simp [prop81H1, hxK]
    _ = ∑ x ∈ K, ‖f x‖ ^ 2 := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
      have hfilter : (Finset.univ.filter fun x : ZMod N => x ∈ K) = K := by
        ext x
        simp
      rw [hfilter]
    _ ≤ ∑ _x ∈ K, (1 : Real) := by
      apply Finset.sum_le_sum
      intro x hx
      nlinarith [norm_nonneg (f x), hf x]
    _ = K.card := by simp

private lemma prop81_H3_fourier_energy_le {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (f : ZMod N → Complex) (c : ZMod N)
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (hcard : (prop81PairSums K).card ≤ 2 * K.card) :
    (∑ r : ZMod N, ‖fourier (prop81H3 K f c) (-r)‖ ^ 2) ≤
      (N : Real) * (2 * K.card) := by
  classical
  have hneg :
      (∑ r : ZMod N, ‖fourier (prop81H3 K f c) (-r)‖ ^ 2) =
        ∑ r : ZMod N, ‖fourier (prop81H3 K f c) r‖ ^ 2 := by
    exact Fintype.sum_equiv (Equiv.neg (ZMod N))
      (fun r => ‖fourier (prop81H3 K f c) (-r)‖ ^ 2)
      (fun r => ‖fourier (prop81H3 K f c) r‖ ^ 2) (fun _ => rfl)
  rw [hneg, identity_2_3_holds]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ x : ZMod N, ‖prop81H3 K f c x‖ ^ 2) =
        ∑ x : ZMod N,
          if x ∈ prop81PairSums K then ‖f x‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxK : x ∈ prop81PairSums K <;>
        simp [prop81H3, hxK]
    _ = ∑ x ∈ prop81PairSums K, ‖f x‖ ^ 2 := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
      have hfilter :
          (Finset.univ.filter fun x : ZMod N => x ∈ prop81PairSums K) =
            prop81PairSums K := by
        ext x
        simp
      rw [hfilter]
    _ ≤ ∑ _x ∈ prop81PairSums K, (1 : Real) := by
      apply Finset.sum_le_sum
      intro x hx
      nlinarith [norm_nonneg (f x), hf x]
    _ = (prop81PairSums K).card := by simp
    _ ≤ 2 * K.card := by exact_mod_cast hcard

private lemma prop81_quadratic_extraction {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (f₁ f₂ f₃ : ZMod N → Complex)
    (a b c : ZMod N) (gamma : Real)
    (hf₂ : ∀ x, ‖f₂ x‖ ≤ 1) (hf₃ : ∀ x, ‖f₃ x‖ ≤ 1)
    (hcard : (prop81PairSums K).card ≤ 2 * K.card)
    (hlarge : gamma * (K.card : Real) ^ 2 ≤
      ‖prop81BilinearSum K f₁ f₂ f₃ a b c‖) :
    ∃ r : ZMod N,
      gamma * K.card / Real.sqrt 2 ≤
        ‖∑ x ∈ K,
          f₁ x * exponential (-(a * x + c * x ^ 2 + r * x))‖ := by
  classical
  obtain ⟨r₀, hr₀mem, hr₀⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ZMod N))
    (fun r => ‖fourier (prop81H1 K f₁ a c) r‖)
    ⟨0, Finset.mem_univ 0⟩
  refine ⟨r₀, ?_⟩
  rw [← prop81_fourier_H1]
  by_cases hK : K.card = 0
  · simp [hK]
  by_cases hgamma : gamma ≤ 0
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hgamma (Nat.cast_nonneg _))
      (Real.sqrt_nonneg 2)).trans (norm_nonneg _)
  have hgammaPos : 0 < gamma := lt_of_not_ge hgamma
  have hTpos : (0 : Real) < K.card := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let g₁ : ZMod N → Complex := fun r => fourier (prop81H1 K f₁ a c) r
  let g₂ : ZMod N → Complex := fun r => fourier (prop81H1 K f₂ b c) r
  let g₃ : ZMod N → Complex := fun r => fourier (prop81H3 K f₃ c) (-r)
  let E₂ : Real := ∑ r : ZMod N, ‖g₂ r‖ ^ 2
  let E₃ : Real := ∑ r : ZMod N, ‖g₃ r‖ ^ 2
  let M₁ : Real := ‖g₁ r₀‖
  have hmax (r : ZMod N) : ‖g₁ r‖ ≤ M₁ := by
    exact hr₀ r (Finset.mem_univ r)
  have hE₂ : E₂ ≤ (N : Real) * K.card := by
    simpa only [E₂, g₂] using prop81_H1_fourier_energy_le K f₂ b c hf₂
  have hE₃ : E₃ ≤ (N : Real) * (2 * K.card) := by
    simpa only [E₃, g₃] using prop81_H3_fourier_energy_le K f₃ c hf₃ hcard
  have hE₂nonneg : 0 ≤ E₂ := by
    dsimp only [E₂]
    positivity
  have hE₃nonneg : 0 ≤ E₃ := by
    dsimp only [E₃]
    positivity
  have hCS :
      (∑ r : ZMod N, ‖g₂ r‖ * ‖g₃ r‖) ≤
        Real.sqrt E₂ * Real.sqrt E₃ := by
    simpa only [E₂, E₃] using Real.sum_mul_le_sqrt_mul_sqrt
      (Finset.univ : Finset (ZMod N)) (fun r => ‖g₂ r‖) (fun r => ‖g₃ r‖)
  have hsqrtBound :
      Real.sqrt E₂ * Real.sqrt E₃ ≤
        Real.sqrt 2 * ((N : Real) * K.card) := by
    calc
      Real.sqrt E₂ * Real.sqrt E₃ ≤
          Real.sqrt ((N : Real) * K.card) *
            Real.sqrt ((N : Real) * (2 * K.card)) := by
        exact mul_le_mul (Real.sqrt_le_sqrt hE₂) (Real.sqrt_le_sqrt hE₃)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt 2 * ((N : Real) * K.card) := by
        have hNT : 0 ≤ (N : Real) * K.card := by positivity
        rw [show (N : Real) * (2 * K.card) =
            2 * ((N : Real) * K.card) by ring,
          Real.sqrt_mul (show 0 ≤ (2 : Real) by norm_num)]
        calc
          Real.sqrt ((N : Real) * K.card) *
              (Real.sqrt 2 * Real.sqrt ((N : Real) * K.card)) =
              Real.sqrt 2 *
                (Real.sqrt ((N : Real) * K.card) *
                  Real.sqrt ((N : Real) * K.card)) := by ring
          _ = Real.sqrt 2 * ((N : Real) * K.card) := by
            rw [Real.mul_self_sqrt hNT]
  have hsumMax :
      (∑ r : ZMod N, ‖g₁ r‖ * ‖g₂ r‖ * ‖g₃ r‖) ≤
        M₁ * (Real.sqrt 2 * ((N : Real) * K.card)) := by
    calc
      _ ≤ ∑ r : ZMod N, M₁ * (‖g₂ r‖ * ‖g₃ r‖) := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          ‖g₁ r‖ * ‖g₂ r‖ * ‖g₃ r‖ =
              ‖g₁ r‖ * (‖g₂ r‖ * ‖g₃ r‖) := by ring
          _ ≤ M₁ * (‖g₂ r‖ * ‖g₃ r‖) :=
            mul_le_mul_of_nonneg_right (hmax r)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = M₁ * ∑ r : ZMod N, ‖g₂ r‖ * ‖g₃ r‖ := by
        rw [Finset.mul_sum]
      _ ≤ M₁ * (Real.sqrt E₂ * Real.sqrt E₃) := by gcongr
      _ ≤ M₁ * (Real.sqrt 2 * ((N : Real) * K.card)) := by gcongr
  have htriple :
      (N : Real) * ‖prop81BilinearSum K f₁ f₂ f₃ a b c‖ ≤
        ∑ r : ZMod N, ‖g₁ r‖ * ‖g₂ r‖ * ‖g₃ r‖ := by
    calc
      (N : Real) * ‖prop81BilinearSum K f₁ f₂ f₃ a b c‖ =
          ‖(N : Complex) * prop81BilinearSum K f₁ f₂ f₃ a b c‖ := by
        simp
      _ = ‖∑ r : ZMod N, g₁ r * g₂ r * g₃ r‖ := by
        rw [prop81_fourier_triple]
      _ ≤ ∑ r : ZMod N, ‖g₁ r * g₂ r * g₃ r‖ := norm_sum_le _ _
      _ = ∑ r : ZMod N, ‖g₁ r‖ * ‖g₂ r‖ * ‖g₃ r‖ := by
        apply Finset.sum_congr rfl
        intro r hr
        simp
  have hchain :
      (N : Real) * (gamma * (K.card : Real) ^ 2) ≤
        M₁ * (Real.sqrt 2 * ((N : Real) * K.card)) := by
    calc
      _ ≤ (N : Real) * ‖prop81BilinearSum K f₁ f₂ f₃ a b c‖ := by gcongr
      _ ≤ ∑ r : ZMod N, ‖g₁ r‖ * ‖g₂ r‖ * ‖g₃ r‖ := htriple
      _ ≤ _ := hsumMax
  have hcancel : gamma * K.card ≤ M₁ * Real.sqrt 2 := by
    apply le_of_mul_le_mul_left
      (a := (N : Real) * K.card) _ (mul_pos hNpos hTpos)
    calc
      ((N : Real) * K.card) * (gamma * K.card) =
          (N : Real) * (gamma * (K.card : Real) ^ 2) := by ring
      _ ≤ M₁ * (Real.sqrt 2 * ((N : Real) * K.card)) := hchain
      _ = ((N : Real) * K.card) * (M₁ * Real.sqrt 2) := by ring
  exact (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2))).2
    (by simpa [mul_comm] using hcancel)

private lemma prop81_local_extraction {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (K : Finset (ZMod N))
    (lambda mu c s y : ZMod N)
    (hcard : (prop81PairSums K).card ≤ 2 * K.card) :
    ∃ r : ZMod N,
      ‖prop81LocalBilinear A K lambda mu c s y‖ ≤
        Real.sqrt 2 * K.card *
          ‖∑ k ∈ K, balanced A (s + k) *
            exponential (-((lambda * y) * k + c * k ^ 2 + r * k))‖ := by
  classical
  by_cases hK : K.card = 0
  · have hKempty : K = ∅ := Finset.card_eq_zero.mp hK
    refine ⟨0, ?_⟩
    simp [prop81LocalBilinear, prop81BilinearSum, hKempty]
  · have hTpos : (0 : Real) < K.card := by
      exact_mod_cast Nat.pos_of_ne_zero hK
    let gamma : Real :=
      ‖prop81LocalBilinear A K lambda mu c s y‖ / (K.card : Real) ^ 2
    have hlarge :
        gamma * (K.card : Real) ^ 2 ≤
          ‖prop81LocalBilinear A K lambda mu c s y‖ := by
      dsimp only [gamma]
      field_simp
      exact le_rfl
    obtain ⟨r, hr⟩ := prop81_quadratic_extraction K
      (fun k => balanced A (s + k))
      (fun l => balanced A (s - y + l))
      (fun u => balanced A (s - y + u))
      (lambda * y) (-mu) c gamma
      (fun x => prop81_balanced_norm_le_one A _)
      (fun x => prop81_balanced_norm_le_one A _) hcard hlarge
    refine ⟨r, ?_⟩
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hTne : (K.card : Real) ≠ 0 := ne_of_gt hTpos
    have hr' :
        ‖prop81LocalBilinear A K lambda mu c s y‖ /
            ((K.card : Real) * Real.sqrt 2) ≤
          ‖∑ k ∈ K, balanced A (s + k) *
            exponential (-((lambda * y) * k + c * k ^ 2 + r * k))‖ := by
      convert hr using 1
      dsimp only [gamma]
      symm
      rw [pow_two, ← div_div, div_mul_cancel₀ _ hTne]
      rw [div_div]
    have := (div_le_iff₀ (mul_pos hTpos hsqrt)).mp hr'
    nlinarith [norm_nonneg
      (∑ k ∈ K, balanced A (s + k) *
        exponential (-((lambda * y) * k + c * k ^ 2 + r * k)))]

private def prop81Phase {N : Nat} (c q s z : ZMod N) : ZMod N :=
  c * (z - s) ^ 2 + q * (z - s)

private lemma prop81_phase_polynomial {N : Nat} [NeZero N]
    (c q s : ZMod N) :
    PolynomialOn 2 Finset.univ (prop81Phase c q s) := by
  classical
  refine ⟨![c * s ^ 2 - q * s, q - 2 * c * s, c], ?_⟩
  intro z hz
  simp [prop81Phase, Fin.sum_univ_succ]
  ring_nf

private lemma prop81_translate_correlation {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (K : Finset (ZMod N)) (c q s : ZMod N) :
    (∑ z ∈ translate K s,
        balanced A z * exponential (-(prop81Phase c q s z))) =
      ∑ k ∈ K,
        balanced A (s + k) * exponential (-(q * k + c * k ^ 2)) := by
  classical
  unfold translate
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [prop81Phase]
    rw [show k + s - s = k by ring]
    congr 1
    · congr 1
      ring
    · ring_nf
  · intro x hx y hy hxy
    exact add_right_cancel hxy

private theorem prop81_of_half {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (P : ModAP N) (beta : Real)
    (lambda mu c : ZMod N) (hc : 2 * c = lambda)
    (hpremise : beta * (N : Real) ^ 2 * P.carrier.card ≤
      ∑ k ∈ P.carrier,
        ‖fourier (difference (balanced A) k) (lambda * k + mu)‖ ^ 2) :
    ∃ psi : ZMod N → ZMod N → ZMod N,
      (∀ s, PolynomialOn 2 Finset.univ (psi s)) ∧
      beta * N * P.carrier.card / Real.sqrt 2 ≤
        ∑ s : ZMod N,
          ‖∑ z ∈ translate P.carrier s,
            balanced A z * exponential (-(psi s z))‖ := by
  classical
  let K := P.carrier
  let E : Real := ∑ k ∈ K,
    ‖fourier (difference (balanced A) k) (lambda * k + mu)‖ ^ 2
  by_cases hK : K.card = 0
  · have hKempty : K = ∅ := Finset.card_eq_zero.mp hK
    refine ⟨fun _ _ => 0, ?_, ?_⟩
    · intro s
      refine ⟨0, ?_⟩
      intro x hx
      simp
    · simp [K, hK]
      positivity
  have hTpos : (0 : Real) < K.card := by
    exact_mod_cast Nat.pos_of_ne_zero hK
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hpremise' : beta * (N : Real) ^ 2 * K.card ≤ E := by
    simpa only [K, E] using hpremise
  have hlocal := prop81_energy_le_local_norm_sum A K lambda mu c hc
  have hlower :
      beta * (N : Real) ^ 2 * (K.card : Real) ^ 2 ≤
        ∑ s : ZMod N, ∑ y : ZMod N,
          ‖prop81LocalBilinear A K lambda mu c s y‖ := by
    calc
      _ = (K.card : Real) *
          (beta * (N : Real) ^ 2 * K.card) := by ring
      _ ≤ (K.card : Real) * E := by gcongr
      _ ≤ _ := hlocal
  have hyExists (s : ZMod N) :
      ∃ y ∈ (Finset.univ : Finset (ZMod N)),
        ∀ y' ∈ (Finset.univ : Finset (ZMod N)),
          ‖prop81LocalBilinear A K lambda mu c s y'‖ ≤
            ‖prop81LocalBilinear A K lambda mu c s y‖ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod N))
      (fun y => ‖prop81LocalBilinear A K lambda mu c s y‖)
      ⟨0, Finset.mem_univ 0⟩
  let yChoice : ZMod N → ZMod N := fun s => Classical.choose (hyExists s)
  have hyMax (s y : ZMod N) :
      ‖prop81LocalBilinear A K lambda mu c s y‖ ≤
        ‖prop81LocalBilinear A K lambda mu c s (yChoice s)‖ := by
    exact (Classical.choose_spec (hyExists s)).2 y
      (Finset.mem_univ y)
  have hrExists (s : ZMod N) :
      ∃ r : ZMod N,
        ‖prop81LocalBilinear A K lambda mu c s (yChoice s)‖ ≤
          Real.sqrt 2 * K.card *
            ‖∑ k ∈ K, balanced A (s + k) *
              exponential (-((lambda * yChoice s) * k + c * k ^ 2 + r * k))‖ :=
    prop81_local_extraction A K lambda mu c s (yChoice s)
      (by simpa only [K] using prop81_pairSums_card_le N P)
  let rChoice : ZMod N → ZMod N := fun s => Classical.choose (hrExists s)
  let Corr : ZMod N → Real := fun s =>
    ‖∑ k ∈ K, balanced A (s + k) *
      exponential (-((lambda * yChoice s) * k + c * k ^ 2 + rChoice s * k))‖
  have hrBound (s : ZMod N) :
      ‖prop81LocalBilinear A K lambda mu c s (yChoice s)‖ ≤
        Real.sqrt 2 * K.card * Corr s := by
    simpa only [rChoice, Corr] using Classical.choose_spec (hrExists s)
  have htotalUpper :
      (∑ s : ZMod N, ∑ y : ZMod N,
          ‖prop81LocalBilinear A K lambda mu c s y‖) ≤
        (N : Real) * (Real.sqrt 2 * K.card) * ∑ s : ZMod N, Corr s := by
    calc
      _ ≤ ∑ s : ZMod N, ∑ _y : ZMod N,
          ‖prop81LocalBilinear A K lambda mu c s (yChoice s)‖ := by
        apply Finset.sum_le_sum
        intro s hs
        apply Finset.sum_le_sum
        intro y hy
        exact hyMax s y
      _ = ∑ s : ZMod N,
          (N : Real) *
            ‖prop81LocalBilinear A K lambda mu c s (yChoice s)‖ := by
        simp
      _ ≤ ∑ s : ZMod N,
          (N : Real) * (Real.sqrt 2 * K.card * Corr s) := by
        apply Finset.sum_le_sum
        intro s hs
        exact mul_le_mul_of_nonneg_left (hrBound s) hNpos.le
      _ = (N : Real) * (Real.sqrt 2 * K.card) *
          ∑ s : ZMod N, Corr s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        ring
  have hcancel :
      beta * (N : Real) * K.card ≤
        Real.sqrt 2 * ∑ s : ZMod N, Corr s := by
    apply le_of_mul_le_mul_left
      (a := (N : Real) * K.card) _ (mul_pos hNpos hTpos)
    calc
      ((N : Real) * K.card) * (beta * (N : Real) * K.card) =
          beta * (N : Real) ^ 2 * (K.card : Real) ^ 2 := by ring
      _ ≤ ∑ s : ZMod N, ∑ y : ZMod N,
          ‖prop81LocalBilinear A K lambda mu c s y‖ := hlower
      _ ≤ (N : Real) * (Real.sqrt 2 * K.card) *
          ∑ s : ZMod N, Corr s := htotalUpper
      _ = ((N : Real) * K.card) *
          (Real.sqrt 2 * ∑ s : ZMod N, Corr s) := by ring
  let psi : ZMod N → ZMod N → ZMod N := fun s =>
    prop81Phase c (lambda * yChoice s + rChoice s) s
  refine ⟨psi, fun s => prop81_phase_polynomial c _ s, ?_⟩
  have hcorr (s : ZMod N) :
      ‖∑ z ∈ translate K s,
          balanced A z * exponential (-(psi s z))‖ = Corr s := by
    rw [prop81_translate_correlation]
    dsimp only [psi, Corr]
    apply congrArg norm
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    congr 1
    ring
  rw [show P.carrier = K by rfl]
  simp_rw [hcorr]
  exact (div_le_iff₀ hsqrt).2 (by simpa [mul_comm] using hcancel)

/-- **Gowers, Proposition 8.1.**  The paper's completing-square argument uses
that multiplication by two is invertible.  The statement records the minimal
odd-modulus hypothesis; no primality or properness assumption is needed. -/
theorem proposition_8_1_holds : proposition_8_1 := by
  intro N _ hNodd A P beta
  rintro ⟨lambda, mu, hpremise⟩
  have hunit : IsUnit (2 : ZMod N) :=
    (ZMod.isUnit_iff_coprime 2 N).2 hNodd.coprime_two_left
  obtain ⟨c, hc⟩ := Even.of_isUnit_two hunit lambda
  apply prop81_of_half A P beta lambda mu c
  · simpa only [two_mul] using hc.symm
  · exact hpremise

end LeanProofs.GowersSzemeredi
