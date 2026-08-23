import IntegerPoints.GKBProcessAux
import IntegerPoints.IwaniecMozzochiDyadicPartition
import IntegerPoints.IwaniecMozzochiHalfBlock
import IntegerPoints.IwaniecMozzochiSawtooth
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Iwaniec--Mozzochi Section 3: the dyadic Fourier decomposition

This file proves the corrected Section 3 decomposition.  The scale
`H = 1 / 2` is kept separate: it supplies the first Fourier mode, which is
not present in the blocks `H = 2^j`, `j : Nat`.

If `n = ceil (logb 2 y)` and `n > 0`, put `Q = 2^(n - 1)`.  The finite block
sum is *exactly* the sharp Fourier sum through `2 Q`, followed by one smooth
shell:

```
psiH chi (1 / 2) t + sum_{j < n} psiH chi (2^j) t
  = sum_{1 <= h <= 2 Q} sin (2 pi h t) / (pi h)
      + sum_{2 Q < h <= 4 Q} chi (h / Q) sin (2 pi h t) / (pi h).
```

The identity is proved by a finite induction.  At every step the recurrence
`chi u + chi (2 u) = 1` fills the preceding shell and creates the next one.
This is the finite-frequency form of `iwaniecMozzochi_eq31_holds`; spelling it
out avoids silently interchanging a `finsum` with a finite sum.

The remaining shell is estimated by Abel summation.  Every prefix of
`sum e(h t)` is bounded by Kuzmin--Landau, while smoothness of `chi` gives a
uniform bound for the total variation of `chi (h / Q) / h`.  The endpoint
`n = 0` (which, under `1 <= y`, means `y = 1`) is treated separately.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace IMPsiDecomposition

private noncomputable def sineCoeff (t : Real) (h : Nat) : Real :=
  Real.sin (2 * Real.pi * (h : Real) * t) / (Real.pi * (h : Real))

private noncomputable def sharpFourier (N : Nat) (t : Real) : Real :=
  ∑ h ∈ Finset.Icc 1 N, sineCoeff t h

/-- The one smooth frequency shell left after the sharp modes have been
filled.  The endpoint `h = 4 Q` is harmless because `chi 4 = 0`. -/
private noncomputable def smoothTail (chi : Real → Real) (Q : Nat) (t : Real) : Real :=
  ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q), chi (h / (Q : Real)) * sineCoeff t h

private noncomputable def complexTail (chi : Real → Real) (Q : Nat) (t : Real) : Complex :=
  ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
    ((chi (h / (Q : Real)) / h : Real) : Complex) * e (h * t)

/-! ## Exact finite block bookkeeping -/

/-- The support axioms turn the `finsum` defining `psiH` at an integral
positive scale into a literal finite interval. -/
private theorem psiH_nat_eq_Ioc {chi : Real → Real} (hchi : IsDyadicPartition chi)
    (Q : Nat) (hQ : 0 < Q) (t : Real) :
    psiH chi (Q : Real) t =
      ∑ h ∈ Finset.Ioc Q (4 * Q), chi (h / (Q : Real)) * sineCoeff t h := by
  have hQreal : 0 < (Q : Real) := by exact_mod_cast hQ
  let f : Nat → Real := fun h ↦
    chi ((h : Real) / (Q : Real)) *
      Real.sin (2 * Real.pi * (h : Real) * t) / (Real.pi * (h : Real))
  have hsupp : Function.support f ⊆
      (↑(Finset.Ioc Q (4 * Q)) : Set Nat) := by
    intro h hh
    have hchine : chi (h / (Q : Real)) ≠ 0 := by
      intro hz
      apply hh
      simp [f, hz]
    have hlower : Q < h := by
      by_contra hnlt
      have hhQ : h ≤ Q := Nat.le_of_not_gt hnlt
      have hhQreal : (h : Real) ≤ Q := by exact_mod_cast hhQ
      have harg : (h : Real) / Q ≤ 1 := (div_le_one hQreal).2 hhQreal
      exact hchine (hchi.2.2.2.2 _ harg)
    have hupper : h ≤ 4 * Q := by
      by_contra hnle
      have hfourQ : 4 * Q < h := Nat.lt_of_not_ge hnle
      have hfourQreal : (4 : Real) * Q ≤ h := by exact_mod_cast hfourQ.le
      have harg : (4 : Real) ≤ (h : Real) / Q := by
        rw [le_div_iff₀ hQreal]
        simpa [mul_comm] using hfourQreal
      exact hchine (hchi.2.1 _ harg)
    simpa only [Finset.mem_coe, Finset.mem_Ioc] using And.intro hlower hupper
  unfold psiH
  change ∑ᶠ h : Nat, f h = _
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp only [f, sineCoeff]
  ring

private theorem sharpFourier_add_annulus (Q : Nat) (hQ : 0 < Q) (t : Real) :
    sharpFourier (2 * Q) t + ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q), sineCoeff t h =
      sharpFourier (4 * Q) t := by
  have hone : 1 ≤ 2 * Q := by omega
  have hunion :
      Finset.Icc 1 (2 * Q) ∪ Finset.Ioc (2 * Q) (4 * Q) =
        Finset.Icc 1 (4 * Q) := by
    ext h
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisjoint :
      Disjoint (Finset.Icc 1 (2 * Q)) (Finset.Ioc (2 * Q) (4 * Q)) := by
    rw [Finset.disjoint_left]
    intro h hh htail
    simp only [Finset.mem_Icc] at hh
    simp only [Finset.mem_Ioc] at htail
    omega
  unfold sharpFourier
  rw [← Finset.sum_union hdisjoint, hunion]

/-- The first positive integral block fills frequency `2` and leaves the
shell `(2,4]`. -/
private theorem half_add_first_block {chi : Real → Real}
    (hchi : IsDyadicPartition chi) (t : Real) :
    psiH chi (1 / 2 : Real) t + psiH chi 1 t =
      sharpFourier 2 t + smoothTail chi 1 t := by
  have hpsi :
      psiH chi (1 : Real) t =
        ∑ h ∈ (Finset.Ioc 1 4 : Finset Nat), chi (h : Real) * sineCoeff t h := by
    simpa only [Nat.cast_one, Nat.mul_one, div_one] using
      psiH_nat_eq_Ioc hchi 1 (by omega) t
  have hsplit :
      Finset.Ioc 1 4 = Finset.Ioc 1 2 ∪ Finset.Ioc 2 4 :=
    (Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)).symm
  have hdisjoint : Disjoint (Finset.Ioc 1 2) (Finset.Ioc 2 4) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hlower :
      ∑ h ∈ (Finset.Ioc 1 2 : Finset Nat), chi (h : Real) * sineCoeff t h =
        ∑ h ∈ (Finset.Ioc 1 2 : Finset Nat), sineCoeff t h := by
    refine Finset.sum_congr rfl fun h hh ↦ ?_
    simp only [Finset.mem_Ioc] at hh
    have : h = 2 := by omega
    subst h
    norm_num only [Nat.cast_ofNat]
    rw [IMHalfBlock.chi_two_eq_one hchi]
    simp
  have hsharp :
      sharpFourier 2 t = sineCoeff t 1 + ∑ h ∈ Finset.Ioc 1 2, sineCoeff t h := by
    unfold sharpFourier
    rw [Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
  rw [IMHalfBlock.psiH_half_eq hchi, hpsi, hsplit, Finset.sum_union hdisjoint, hlower,
    hsharp]
  unfold smoothTail sineCoeff
  simp only [Nat.cast_one, div_one]
  ring

/-- Adding the next dyadic block fills the old shell and creates a shell at
twice the scale. -/
private theorem sharp_tail_add_next_block {chi : Real → Real}
    (hchi : IsDyadicPartition chi) (Q : Nat) (hQ : 0 < Q) (t : Real) :
    sharpFourier (2 * Q) t + smoothTail chi Q t + psiH chi (2 * Q : Nat) t =
      sharpFourier (4 * Q) t + smoothTail chi (2 * Q) t := by
  have h2Q : 0 < 2 * Q := by omega
  have hpsi :
      psiH chi (2 * Q : Nat) t =
        ∑ h ∈ Finset.Ioc (2 * Q) (8 * Q),
          chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h := by
    have h8 : 4 * (2 * Q) = 8 * Q := by omega
    simpa only [h8] using psiH_nat_eq_Ioc hchi (2 * Q) h2Q t
  have hsplit :
      Finset.Ioc (2 * Q) (8 * Q) =
        Finset.Ioc (2 * Q) (4 * Q) ∪ Finset.Ioc (4 * Q) (8 * Q) := by
    simpa [mul_assoc] using
      (Finset.Ioc_union_Ioc_eq_Ioc (a := 2 * Q) (b := 4 * Q) (c := 8 * Q)
        (by omega) (by omega)).symm
  have hdisjoint :
      Disjoint (Finset.Ioc (2 * Q) (4 * Q)) (Finset.Ioc (4 * Q) (8 * Q)) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hfill :
      ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
          (chi (h / (Q : Real)) * sineCoeff t h +
            chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h) =
        ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q), sineCoeff t h := by
    refine Finset.sum_congr rfl fun h hh ↦ ?_
    simp only [Finset.mem_Ioc] at hh
    have hQreal : 0 < (Q : Real) := by exact_mod_cast hQ
    have hlower : (1 : Real) < (h : Real) / (2 * Q : Nat) := by
      rw [one_lt_div₀ (by positivity)]
      exact_mod_cast hh.1
    have hupper : (h : Real) / (2 * Q : Nat) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      calc
        (h : Real) ≤ ((4 * Q : Nat) : Real) := by exact_mod_cast hh.2
        _ = 2 * ((2 * Q : Nat) : Real) := by push_cast; ring
    have hscale :
        (2 : Real) * ((h : Real) / (2 * Q : Nat)) = (h : Real) / Q := by
      push_cast
      field_simp [hQreal.ne']
    rw [hchi.2.2.2.1 _ hlower hupper, hscale]
    ring
  have hpsiSplit :
      psiH chi (2 * Q : Nat) t =
          ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
            chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h +
          ∑ h ∈ Finset.Ioc (4 * Q) (8 * Q),
            chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h := by
    rw [hpsi, hsplit, Finset.sum_union hdisjoint]
  have hnewTail :
      ∑ h ∈ Finset.Ioc (4 * Q) (8 * Q),
          chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h =
        smoothTail chi (2 * Q) t := by
    unfold smoothTail
    have h4 : 2 * (2 * Q) = 4 * Q := by omega
    have h8 : 4 * (2 * Q) = 8 * Q := by omega
    simp only [h4, h8]
  rw [hpsiSplit]
  unfold smoothTail
  calc
    sharpFourier (2 * Q) t +
          ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
            chi (h / (Q : Real)) * sineCoeff t h +
        (∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
              chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h +
          ∑ h ∈ Finset.Ioc (4 * Q) (8 * Q),
              chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h) =
        sharpFourier (2 * Q) t +
          (∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
              (chi (h / (Q : Real)) * sineCoeff t h +
                chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h)) +
          ∑ h ∈ Finset.Ioc (4 * Q) (8 * Q),
              chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h := by
      rw [Finset.sum_add_distrib]
      ring
    _ = sharpFourier (2 * Q) t +
          (∑ h ∈ Finset.Ioc (2 * Q) (4 * Q), sineCoeff t h) +
          ∑ h ∈ Finset.Ioc (4 * Q) (8 * Q),
              chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h := by
      rw [hfill]
    _ = sharpFourier (4 * Q) t +
          ∑ h ∈ Finset.Ioc (4 * Q) (8 * Q),
              chi (h / ((2 * Q : Nat) : Real)) * sineCoeff t h := by
      rw [sharpFourier_add_annulus Q hQ t]
    _ = sharpFourier (4 * Q) t + smoothTail chi (2 * Q) t := by rw [hnewTail]

/-- Exact finite reconstruction through the last completed sharp cutoff. -/
private theorem blocks_eq_sharp_add_tail {chi : Real → Real}
    (hchi : IsDyadicPartition chi) (n : Nat) (t : Real) :
    psiH chi (1 / 2 : Real) t +
        ∑ j ∈ Finset.range (n + 1), psiH chi ((2 : Real) ^ j) t =
      sharpFourier (2 ^ (n + 1)) t + smoothTail chi (2 ^ n) t := by
  induction n with
  | zero =>
      simpa using half_add_first_block hchi t
  | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      have hstep := sharp_tail_add_next_block hchi (2 ^ n) (by positivity) t
      have hpowNat : (2 : Nat) ^ (n + 1) = 2 * 2 ^ n := by
        rw [pow_succ]
        ring
      have hpowNatTwo : (2 : Nat) ^ (n + 2) = 4 * 2 ^ n := by
        calc
          (2 : Nat) ^ (n + 2) = 2 ^ (n + 1) * 2 := by
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
          _ = (2 * 2 ^ n) * 2 := by rw [hpowNat]
          _ = 4 * 2 ^ n := by ring
      have hpowReal :
          (2 : Real) ^ (n + 1) = ((2 * 2 ^ n : Nat) : Real) := by
        exact_mod_cast hpowNat
      rw [hpowNatTwo, hpowNat, hpowReal]
      exact hstep

/-! ## Abel summation for the final smooth shell -/

/-- Abel's identity with absolute values of all weight drops.  Unlike the
antitone specialization in `GKBProcessAux`, this form applies to the arbitrary
smooth partition function used here. -/
private theorem norm_weighted_range_le_variation (a : Nat → Complex)
    (w : Nat → Real) (K : Nat) (M : Real)
    (hprefix : ∀ i, i ≤ K → ‖GKB.prefixSum a i‖ ≤ M) :
    ‖∑ i ∈ Finset.range (K + 1), (w i : Complex) * a i‖ ≤
      M * (|w K| + ∑ i ∈ Finset.range K, |w i - w (i + 1)|) := by
  rw [GKB.weighted_sum_eq_last_prefix_add_sum_drops]
  calc
    ‖(w K : Complex) * GKB.prefixSum a K +
        ∑ i ∈ Finset.range K,
          ((w i - w (i + 1) : Real) : Complex) * GKB.prefixSum a i‖ ≤
        ‖(w K : Complex) * GKB.prefixSum a K‖ +
          ‖∑ i ∈ Finset.range K,
            ((w i - w (i + 1) : Real) : Complex) * GKB.prefixSum a i‖ :=
      norm_add_le _ _
    _ ≤ |w K| * M +
        ∑ i ∈ Finset.range K,
          |w i - w (i + 1)| * M := by
      gcongr
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) (abs_nonneg _)
      · refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hprefix i (Nat.le_of_lt (Finset.mem_range.1 hi))) (abs_nonneg _)
    _ = M * (|w K| + ∑ i ∈ Finset.range K, |w i - w (i + 1)|) := by
      rw [← Finset.sum_mul]
      ring

private theorem chi_abs_le_one {chi : Real → Real} (hchi : IsDyadicPartition chi)
    {u : Real} (hu2 : 2 ≤ u) (hu4 : u ≤ 4) : |chi u| ≤ 1 := by
  rcases lt_or_eq_of_le hu4 with hu4lt | rfl
  · have hu := hchi.2.2.1 u hu2 hu4lt
    rw [abs_of_pos hu.1]
    exact hu.2
  · rw [hchi.2.1 4 le_rfl]
    norm_num

/-- A single discrete derivative of `chi (h/Q) / h`. -/
private theorem weight_step_le {chi : Real → Real} (hchi : IsDyadicPartition chi)
    (D : Real) (hD0 : 0 ≤ D)
    (hD : ∀ u ∈ Set.Icc (2 : Real) 4, |deriv chi u| ≤ D)
    (Q h : Nat) (hQ : 0 < Q) (hlower : 2 * Q ≤ h) (hupper : h + 1 ≤ 4 * Q) :
    |chi (h / (Q : Real)) / h - chi ((h + 1) / (Q : Real)) / (h + 1)| ≤
      (D + 1) / (Q : Real) ^ 2 := by
  let q : Real := Q
  let x : Real := h
  let u : Real := x / q
  let v : Real := (x + 1) / q
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast hQ
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2 * Q) hlower)
  have hxlower : 2 * q ≤ x := by
    dsimp [q, x]
    exact_mod_cast hlower
  have hxupper : x + 1 ≤ 4 * q := by
    dsimp [q, x]
    exact_mod_cast hupper
  have hu : u ∈ Set.Icc (2 : Real) 4 := by
    constructor
    · dsimp [u]
      rw [le_div_iff₀ hq]
      exact hxlower
    · dsimp [u]
      rw [div_le_iff₀ hq]
      linarith
  have hv : v ∈ Set.Icc (2 : Real) 4 := by
    constructor
    · dsimp [v]
      rw [le_div_iff₀ hq]
      linarith
    · dsimp [v]
      rw [div_le_iff₀ hq]
      exact hxupper
  have hdiff : ∀ z ∈ Set.Icc (2 : Real) 4, DifferentiableAt Real chi z := by
    intro z _
    exact hchi.1.differentiable (by simp) z
  have hlip : |chi v - chi u| ≤ D / q := by
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := Real) (f := chi) (s := Set.Icc (2 : Real) 4)
      (x := u) (y := v) (C := D)
      hdiff (fun z hz ↦ by simpa only [Real.norm_eq_abs] using hD z hz)
      (convex_Icc (2 : Real) 4) hu hv
    have huv : ‖v - u‖ = 1 / q := by
      rw [Real.norm_eq_abs, abs_of_pos]
      · dsimp [u, v]
        field_simp [hq.ne']
        ring
      · dsimp [u, v]
        have hsub : (x + 1) / q - x / q = 1 / q := by
          field_simp [hq.ne']
          ring
        rw [hsub]
        positivity
    simpa [Real.norm_eq_abs, huv, div_eq_mul_inv] using hmvt
  have hchiu : |chi u| ≤ 1 := chi_abs_le_one hchi hu.1 hu.2
  have hxp : 0 < x + 1 := by positivity
  have hrecip : |1 / x - 1 / (x + 1)| = 1 / (x * (x + 1)) := by
    rw [abs_of_pos]
    · field_simp [hx.ne', hxp.ne']
      ring
    · rw [sub_pos]
      exact one_div_lt_one_div_of_lt hx (by linarith)
  have hdecomp :
      chi u / x - chi v / (x + 1) =
        (chi u - chi v) / (x + 1) + chi u * (1 / x - 1 / (x + 1)) := by
    field_simp [hx.ne', hxp.ne']
    ring
  suffices hmain : |chi u / x - chi v / (x + 1)| ≤ (D + 1) / q ^ 2 by
    simpa [q, x, u, v, Nat.cast_add, Nat.cast_one] using hmain
  rw [hdecomp]
  calc
    |(chi u - chi v) / (x + 1) + chi u * (1 / x - 1 / (x + 1))| ≤
        |chi u - chi v| / (x + 1) + |chi u| / (x * (x + 1)) := by
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_div, abs_of_pos hxp, abs_mul, hrecip]
      simp only [div_eq_mul_inv, one_mul]
    _ ≤ (D / q) / (2 * q) + 1 / ((2 * q) * (2 * q)) := by
      have hxu : |chi u - chi v| ≤ D / q := by
        simpa [abs_sub_comm] using hlip
      have h2qpos : 0 < 2 * q := by positivity
      have hterm1 : |chi u - chi v| / (x + 1) ≤ (D / q) / (2 * q) := by
        exact div_le_div₀ (by positivity) hxu h2qpos (by linarith)
      have hden : (2 * q) * (2 * q) ≤ x * (x + 1) :=
        mul_le_mul hxlower (by linarith) (by positivity) (by positivity)
      have hterm2 : |chi u| / (x * (x + 1)) ≤ 1 / ((2 * q) * (2 * q)) := by
        exact div_le_div₀ zero_le_one hchiu (by positivity) hden
      exact add_le_add hterm1 hterm2
    _ ≤ (D + 1) / q ^ 2 := by
      field_simp [hq.ne']
      nlinarith

private theorem complexTail_trivial {chi : Real → Real}
    (hchi : IsDyadicPartition chi) (Q : Nat) (hQ : 0 < Q) (t : Real) :
    ‖complexTail chi Q t‖ ≤ 1 := by
  have hq : 0 < (Q : Real) := by exact_mod_cast hQ
  have hterm : ∀ h ∈ Finset.Ioc (2 * Q) (4 * Q),
      ‖((chi (h / (Q : Real)) / h : Real) : Complex) * e (h * t)‖ ≤
        1 / (2 * (Q : Real)) := by
    intro h hh
    simp only [Finset.mem_Ioc] at hh
    have hhNat : 0 < h := by omega
    have hhpos : 0 < (h : Real) := by exact_mod_cast hhNat
    have hu2 : (2 : Real) ≤ (h : Real) / Q := by
      rw [le_div_iff₀ hq]
      exact_mod_cast hh.1.le
    have hu4 : (h : Real) / Q ≤ 4 := by
      rw [div_le_iff₀ hq]
      exact_mod_cast hh.2
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hhpos]
    calc
      |chi ((h : Real) / Q)| / h ≤ 1 / h :=
        div_le_div_of_nonneg_right (chi_abs_le_one hchi hu2 hu4) hhpos.le
      _ ≤ 1 / (2 * (Q : Real)) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast hh.1.le
  unfold complexTail
  calc
    ‖∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
        ((chi (h / (Q : Real)) / h : Real) : Complex) * e (h * t)‖ ≤
        ∑ h ∈ Finset.Ioc (2 * Q) (4 * Q),
          ‖((chi (h / (Q : Real)) / h : Real) : Complex) * e (h * t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _h ∈ Finset.Ioc (2 * Q) (4 * Q), 1 / (2 * (Q : Real)) :=
      Finset.sum_le_sum hterm
    _ = 1 := by
      have hcard : #(Finset.Ioc (2 * Q) (4 * Q)) = 2 * Q := by
        simp only [Nat.card_Ioc]
        omega
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      push_cast
      field_simp [hq.ne']

private theorem complexTail_large {chi : Real → Real}
    (hchi : IsDyadicPartition chi) (D : Real) (hD0 : 0 ≤ D)
    (hD : ∀ u ∈ Set.Icc (2 : Real) 4, |deriv chi u| ≤ D)
    (Q : Nat) (hQ : 0 < Q) (t : Real)
    (hdQ : 1 < nearestIntDist t * Q) :
    ‖complexTail chi Q t‖ ≤
      8 * (D + 1) / (nearestIntDist t * Q) := by
  let d := nearestIntDist t
  let A := 2 * Q
  let K := 2 * Q - 1
  let a : Nat → Complex := fun i ↦ e ((A + 1 + i : Nat) * t)
  let w : Nat → Real := fun i ↦
    chi ((A + 1 + i : Nat) / (Q : Real)) / (A + 1 + i : Nat)
  have hq : 0 < (Q : Real) := by exact_mod_cast hQ
  have hd : 0 < d := by
    by_contra hdnot
    have hdle : d ≤ 0 := le_of_not_gt hdnot
    have : d * (Q : Real) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hdle hq.le
    nlinarith
  have hdhalf : d ≤ 1 / 2 := by
    dsimp [d]
    simpa [nearestIntDist] using abs_sub_round t
  have hlength : 4 * Q - A = K + 1 := by
    dsimp [A, K]
    omega
  have htailRange :
      complexTail chi Q t =
        ∑ i ∈ Finset.range (K + 1), (w i : Complex) * a i := by
    unfold complexTail
    rw [KL.sum_Ioc_eq_sum_range, hlength]
  have hprefix : ∀ i, i ≤ K → ‖GKB.prefixSum a i‖ ≤ 4 / d := by
    intro i hi
    have hprefixEq :
        GKB.prefixSum a i = ∑ h ∈ Finset.Ioc A (A + 1 + i), e (t * h) := by
      rw [KL.sum_Ioc_eq_sum_range]
      simp only [GKB.prefixSum, a]
      rw [show A + 1 + i - A = i + 1 by omega]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      congr 1
      ring
    rw [hprefixEq]
    exact KL.kuzmin_landau (fun x : Real ↦ t * x) A (A + 1 + i) d hd hdhalf
      (contDiff_const.mul contDiff_id)
      (Or.inl (by
        intro x hx y hy hxy
        simp only [deriv_const_mul_id]
        exact le_rfl))
      (by
        intro x hx
        dsimp [d]
        simp only [deriv_const_mul_id]
        exact le_rfl)
  have hwlast : w K = 0 := by
    have hindex : A + 1 + K = 4 * Q := by
      dsimp [A, K]
      omega
    dsimp only [w]
    rw [hindex]
    have hratio : ((4 * Q : Nat) : Real) / Q = 4 := by
      push_cast
      field_simp [hq.ne']
    rw [hratio, hchi.2.1 4 le_rfl]
    simp
  have hdrop : ∀ i ∈ Finset.range K,
      |w i - w (i + 1)| ≤ (D + 1) / (Q : Real) ^ 2 := by
    intro i hi
    have hiK : i < K := Finset.mem_range.1 hi
    have hlower : 2 * Q ≤ A + 1 + i := by
      dsimp [A]
      omega
    have hupper : A + 1 + i + 1 ≤ 4 * Q := by
      dsimp [A, K] at hiK ⊢
      omega
    have hsucc : A + 1 + (i + 1) = (A + 1 + i) + 1 := by omega
    dsimp only [w]
    rw [hsucc]
    simpa only [Nat.cast_add, Nat.cast_one] using
      weight_step_le hchi D hD0 hD Q (A + 1 + i) hQ hlower hupper
  have hdropSum :
      ∑ i ∈ Finset.range K, |w i - w (i + 1)| ≤
        (2 * (Q : Real)) * ((D + 1) / (Q : Real) ^ 2) := by
    calc
      ∑ i ∈ Finset.range K, |w i - w (i + 1)| ≤
          ∑ _i ∈ Finset.range K, (D + 1) / (Q : Real) ^ 2 :=
        Finset.sum_le_sum hdrop
      _ = (K : Real) * ((D + 1) / (Q : Real) ^ 2) := by simp
      _ ≤ (2 * (Q : Real)) * ((D + 1) / (Q : Real) ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (show K ≤ 2 * Q by dsimp [K]; omega)
        · positivity
  rw [htailRange]
  have hAbel := norm_weighted_range_le_variation a w K (4 / d) hprefix
  calc
    ‖∑ i ∈ Finset.range (K + 1), (w i : Complex) * a i‖ ≤
        (4 / d) * (|w K| + ∑ i ∈ Finset.range K, |w i - w (i + 1)|) := hAbel
    _ ≤ (4 / d) *
        (2 * (Q : Real) * ((D + 1) / (Q : Real) ^ 2)) := by
      rw [hwlast, abs_zero, zero_add]
      exact mul_le_mul_of_nonneg_left hdropSum (by positivity)
    _ = 8 * (D + 1) / (d * Q) := by
      field_simp [hd.ne', hq.ne']
      ring

private theorem smoothTail_eq_im {chi : Real → Real} (Q : Nat) (t : Real) :
    smoothTail chi Q t = (complexTail chi Q t).im / Real.pi := by
  unfold smoothTail complexTail sineCoeff
  rw [Complex.im_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, IMHalfBlock.e_im]
  by_cases hh : h = 0
  · subst h
    simp
  · field_simp [hh, Real.pi_ne_zero]
    ring

private theorem abs_smoothTail_le_norm {chi : Real → Real} (Q : Nat) (t : Real) :
    |smoothTail chi Q t| ≤ ‖complexTail chi Q t‖ := by
  rw [smoothTail_eq_im, abs_div, abs_of_pos Real.pi_pos]
  calc
    |(complexTail chi Q t).im| / Real.pi ≤ ‖complexTail chi Q t‖ / Real.pi :=
      div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) Real.pi_pos.le
    _ ≤ ‖complexTail chi Q t‖ := by
      apply div_le_self (norm_nonneg _)
      exact one_le_two.trans Real.two_le_pi

/-- Uniform shell estimate at any positive integral scale `Q`, provided the
target cutoff is at most `2 Q`. -/
private theorem smoothTail_bound {chi : Real → Real}
    (hchi : IsDyadicPartition chi) (D : Real) (hD0 : 0 ≤ D)
    (hD : ∀ u ∈ Set.Icc (2 : Real) 4, |deriv chi u| ≤ D)
    (Q : Nat) (hQ : 0 < Q) (t y : Real) (hy : 1 ≤ y)
    (hyQ : y ≤ 2 * Q) :
    |smoothTail chi Q t| ≤
      max 6 (24 * (D + 1)) * (1 + nearestIntDist t * y)⁻¹ := by
  let d := nearestIntDist t
  have hd0 : 0 ≤ d := by
    dsimp [d, nearestIntDist]
    positivity
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hden : 0 < 1 + d * y := by positivity
  have hq : 0 < (Q : Real) := by exact_mod_cast hQ
  rcases le_or_gt (d * Q) 1 with hsmall | hlarge
  · have htail : |smoothTail chi Q t| ≤ 1 :=
      (abs_smoothTail_le_norm Q t).trans (complexTail_trivial hchi Q hQ t)
    have hdy : d * y ≤ 2 := by
      calc
        d * y ≤ d * (2 * Q) := mul_le_mul_of_nonneg_left hyQ hd0
        _ = 2 * (d * Q) := by ring
        _ ≤ 2 := by linarith
    calc
      |smoothTail chi Q t| ≤ 1 := htail
      _ ≤ 6 * (1 + d * y)⁻¹ := by
        rw [← div_eq_mul_inv]
        apply (le_div_iff₀ hden).2
        nlinarith
      _ ≤ max 6 (24 * (D + 1)) * (1 + d * y)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 hden.le)
  · have hcomplex := complexTail_large hchi D hD0 hD Q hQ t hlarge
    have htail : |smoothTail chi Q t| ≤ 8 * (D + 1) / (d * Q) :=
      (abs_smoothTail_le_norm Q t).trans hcomplex
    have hdq : 0 < d * (Q : Real) := by nlinarith
    have hdenUpper : 1 + d * y ≤ 3 * (d * Q) := by
      have hdy : d * y ≤ 2 * (d * Q) := by
        calc
          d * y ≤ d * (2 * Q) := mul_le_mul_of_nonneg_left hyQ hd0
          _ = 2 * (d * Q) := by ring
      nlinarith
    have hinv : 1 / (d * Q) ≤ 3 / (1 + d * y) := by
      rw [div_le_div_iff₀ hdq hden]
      nlinarith
    calc
      |smoothTail chi Q t| ≤ 8 * (D + 1) / (d * Q) := htail
      _ ≤ 24 * (D + 1) * (1 + d * y)⁻¹ := by
        calc
          8 * (D + 1) / (d * Q) = 8 * (D + 1) * (1 / (d * Q)) := by ring
          _ ≤ 8 * (D + 1) * (3 / (1 + d * y)) := by
            exact mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = 24 * (D + 1) * (1 + d * y)⁻¹ := by ring
      _ ≤ max 6 (24 * (D + 1)) * (1 + d * y)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.2 hden.le)

end IMPsiDecomposition

open IMPsiDecomposition

/-- The corrected Iwaniec--Mozzochi Section 3 decomposition, including the
separate `H = 1 / 2` Fourier block. -/
theorem iwaniecMozzochi_section3_psiDecomposition_holds :
    iwaniecMozzochi_section3_psiDecomposition := by
  intro chi hchi
  -- Record the full partition theorem whose finite-frequency incarnation is
  -- the block induction above.
  have _hpartition := iwaniecMozzochi_eq31_holds chi hchi
  obtain ⟨C₀, hfourier⟩ := sawtooth_fourierExpansion_holds
  obtain ⟨c, hc, hcmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by norm_num : (2 : Real) ≤ 4))
    ((hchi.1.continuous_deriv (by simp)).norm.continuousOn)
  let D := |deriv chi c|
  have hD0 : 0 ≤ D := abs_nonneg _
  have hD : ∀ u ∈ Set.Icc (2 : Real) 4, |deriv chi u| ≤ D := by
    intro u hu
    simpa [D, Real.norm_eq_abs] using hcmax hu
  let K := max 6 (24 * (D + 1))
  refine ⟨max C₀ 0 + K, ?_⟩
  intro t y hy
  let d := nearestIntDist t
  have hd0 : 0 ≤ d := by
    dsimp [d, nearestIntDist]
    positivity
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  by_cases hyone : y = 1
  · subst y
    have hhalf : psiH chi (1 / 2 : Real) t = sharpFourier 1 t := by
      rw [IMHalfBlock.psiH_half_eq hchi]
      simp [sharpFourier, sineCoeff]
    have hbase := hfourier t 1 (le_rfl : (1 : Real) ≤ 1)
    rw [Real.logb_one, Nat.ceil_zero, Finset.range_zero, Finset.sum_empty, add_zero,
      hhalf, mul_one]
    change |sawtooth t + sharpFourier 1 t| ≤
      (max C₀ 0 + K) * (1 + d)⁻¹
    have hbase' :
        |sawtooth t + sharpFourier 1 t| ≤ C₀ * (1 + d)⁻¹ := by
      simpa [upTo, sharpFourier, sineCoeff, d] using hbase
    calc
      |sawtooth t + sharpFourier 1 t| ≤ C₀ * (1 + d)⁻¹ := hbase'
      _ ≤ max C₀ 0 * (1 + d)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (by positivity))
      _ ≤ (max C₀ 0 + K) * (1 + d)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 (by positivity))
        dsimp [K]
        have : 0 ≤ max 6 (24 * (D + 1)) := le_max_of_le_left (by norm_num)
        linarith
  · have hyone' : 1 < y := lt_of_le_of_ne hy (Ne.symm hyone)
    let n := ⌈Real.logb 2 y⌉₊
    have hn : 0 < n := by
      dsimp [n]
      rw [Nat.ceil_pos]
      exact Real.logb_pos (by norm_num) hyone'
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hycutRpow : y ≤ (2 : Real) ^ (n : Real) := by
      rw [← Real.logb_le_iff_le_rpow (by norm_num : (1 : Real) < 2) hy0]
      exact Nat.le_ceil (Real.logb 2 y)
    have hycut : y ≤ (2 ^ n : Nat) := by
      simpa [Real.rpow_natCast] using hycutRpow
    have hpow : (2 : Nat) ^ n = 2 * (2 : Nat) ^ k := by
      rw [hk, pow_succ]
      ring
    have hyQ : y ≤ 2 * (2 ^ k : Nat) := by simpa [hpow] using hycut
    have hblocks := blocks_eq_sharp_add_tail hchi k t
    have hpowoneNat : 1 ≤ (2 : Nat) ^ n := by
      exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hpowone : (1 : Real) ≤ ((2 : Nat) ^ n : Nat) := by
      exact_mod_cast hpowoneNat
    have hsharpRaw := hfourier t (2 ^ n : Nat) hpowone
    have hupToPow :
        upTo (((2 : Nat) ^ n : Nat) : Real) = Finset.Icc 1 ((2 : Nat) ^ n) := by
      simp only [upTo, Nat.floor_natCast]
    rw [hupToPow] at hsharpRaw
    have hsharp :
        |sawtooth t + sharpFourier (2 ^ n) t| ≤
          max C₀ 0 * (1 + d * y)⁻¹ := by
      have hraw :
          |sawtooth t + sharpFourier (2 ^ n) t| ≤
            C₀ * (1 + d * (2 ^ n : Nat))⁻¹ := by
        simpa only [sharpFourier, sineCoeff, d] using hsharpRaw
      have hinv : (1 + d * (2 ^ n : Nat))⁻¹ ≤ (1 + d * y)⁻¹ := by
        have hdenOrder : 1 + d * y ≤ 1 + d * (2 ^ n : Nat) := by
          linarith [mul_le_mul_of_nonneg_left hycut hd0]
        exact inv_anti₀ (by positivity) hdenOrder
      calc
        |sawtooth t + sharpFourier (2 ^ n) t| ≤
            C₀ * (1 + d * (2 ^ n : Nat))⁻¹ := hraw
        _ ≤ max C₀ 0 * (1 + d * (2 ^ n : Nat))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 (by positivity))
        _ ≤ max C₀ 0 * (1 + d * y)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (le_max_right _ _)
    have htail :
        |smoothTail chi (2 ^ k) t| ≤ K * (1 + d * y)⁻¹ := by
      simpa [K, d] using smoothTail_bound hchi D hD0 hD (2 ^ k) (by positivity) t y hy hyQ
    have hblocksN :
        psiH chi (1 / 2 : Real) t +
            ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) t =
          sharpFourier (2 ^ n) t + smoothTail chi (2 ^ k) t := by
      simpa [hk] using hblocks
    have hexact :
        sawtooth t + psiH chi (1 / 2 : Real) t +
            ∑ j ∈ Finset.range ⌈Real.logb 2 y⌉₊, psiH chi ((2 : Real) ^ j) t =
          sawtooth t + (sharpFourier (2 ^ n) t + smoothTail chi (2 ^ k) t) := by
      change sawtooth t + psiH chi (1 / 2 : Real) t +
          ∑ j ∈ Finset.range n, psiH chi ((2 : Real) ^ j) t = _
      rw [add_assoc, hblocksN]
    rw [hexact]
    calc
      |sawtooth t + (sharpFourier (2 ^ n) t + smoothTail chi (2 ^ k) t)| ≤
          |sawtooth t + sharpFourier (2 ^ n) t| +
            |smoothTail chi (2 ^ k) t| := by
        simpa only [add_assoc] using
          abs_add_le (sawtooth t + sharpFourier (2 ^ n) t) (smoothTail chi (2 ^ k) t)
      _ ≤ max C₀ 0 * (1 + d * y)⁻¹ + K * (1 + d * y)⁻¹ :=
        add_le_add hsharp htail
      _ = (max C₀ 0 + K) * (1 + d * y)⁻¹ := by ring

end LeanProofs.IntegerPoints
