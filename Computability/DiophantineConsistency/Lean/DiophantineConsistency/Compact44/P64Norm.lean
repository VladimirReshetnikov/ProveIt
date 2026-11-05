import DiophantineConsistency.Compact44.P64Root
import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! # Package 64's local norm minimum

A zero of package 64's equation makes `A0² + M² + W² + Na² + Lt² = 1`. In every
model of `𝗜𝚺₁` this forces `A0 = M = W = Lt = 0` and `Na = 1`:

* `Na ≠ 0`. Write `Na = A(x² − y²) + y²`, where `A = Δ(f²−1)`, `x = |V|` and
  `y = |V + e|` with `e > 0`. If `f = 1` then `A = 0` and `W = (ic²)² ≥ 81`,
  which is too large. If `f ≥ 2` then `A ≥ 2`, and `Na = 0` would make
  `A(A−1)` a square, but it lies strictly between `(A−1)²` and `A²`
  (`na_ne_zero`, via integral square roots);
* so `Na² ≥ 1` by discreteness, the other four squares vanish and `Na = ±1`;
* `Na = −1` is impossible modulo four (`na_ne_neg`).

`V` is used only through some representation `ι P − ι N`, so neither the rank
nor the transport is needed here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P64Norm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveQuotients2011 P64Graph P64Root
open ArithmeticAdaptiveFactorUnits2011 (residue residue_add residue_mul residue_nat)
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem absdiff_eq_zero {a b : V} (h : absdiff a b = 0) : a = b := by
  have h2 := ι_absdiff_sq a b
  rw [h, map_zero, mul_zero] at h2
  have h3 : ι a - ι b = 0 := mul_self_eq_zero.mp h2.symm
  exact ι_injective (sub_eq_zero.mp h3)

/-- `A(A−1)` is not a square: no zero of the auxiliary form when `A ≥ 2`. -/
theorem na_ne_zero (A P N e : V) (hA : 2 ≤ A) (he : 0 < e) :
    A * (absdiff P N * absdiff P N) + absdiff (P + e) N * absdiff (P + e) N ≠
      A * (absdiff (P + e) N * absdiff (P + e) N) := by
  intro h
  set x := absdiff P N with hx
  set y := absdiff (P + e) N with hy
  obtain ⟨B, hB⟩ : ∃ B, A = B + 1 := ⟨A - 1, (tsub_add_cancel_of_le (le_trans (by norm_num) hA)).symm⟩
  have hB1 : 1 ≤ B := by
    have : 1 + 1 ≤ B + 1 := by rw [← hB]; simpa [one_add_one_eq_two] using hA
    exact (add_le_add_iff_right 1).mp this
  rw [hB] at h
  have h1 : (B + 1) * (x * x) = B * (y * y) := by
    have : (B + 1) * (x * x) + y * y = B * (y * y) + y * y := by rw [h]; ring
    exact add_right_cancel this
  have hy0 : 0 < y := by
    rcases (Arithmetic.zero_le y).lt_or_eq with hy' | hy'
    · exact hy'
    · exfalso
      rw [← hy', mul_zero, mul_zero] at h1
      have hxx : x * x = 0 := by
        rcases mul_eq_zero.mp h1 with h' | h'
        · exact absurd h' (ne_of_gt (lt_of_lt_of_le (by norm_num) le_add_self))
        · exact h'
      have hx0 : x = 0 := mul_self_eq_zero.mp hxx
      have hPN : P = N := absdiff_eq_zero hx0
      have hPeN : P + e = N := absdiff_eq_zero hy'.symm
      rw [← hPN] at hPeN
      exact (ne_of_gt he) (add_left_cancel (hPeN.trans (add_zero P).symm))
  have h2 : ((B + 1) * x) * ((B + 1) * x) = y * y * ((B + 1) * B) := by
    calc ((B + 1) * x) * ((B + 1) * x) = (B + 1) * ((B + 1) * (x * x)) := by ring
      _ = (B + 1) * (B * (y * y)) := by rw [h1]
      _ = y * y * ((B + 1) * B) := by ring
  obtain ⟨t, _, ht⟩ := scaled_quotient y ((B + 1) * x) ((B + 1) * B) hy0 h2
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB1
  have hlo : B * B < t * t := by
    rw [ht]
    calc B * B < B * B + B := lt_add_of_pos_right _ hB0
      _ = (B + 1) * B := by ring
  have hhi : t * t < (B + 1) * (B + 1) := by
    rw [ht]; exact mul_lt_mul_of_pos_left (lt_add_one B) (lt_of_lt_of_le hB0 le_self_add)
  have hBt : B < t := by
    by_contra hle
    have h' : t ≤ B := le_of_not_gt hle
    exact absurd hlo (not_lt_of_ge (mul_le_mul h' h' (Arithmetic.zero_le _) (Arithmetic.zero_le _)))
  have htB : t < B + 1 := by
    by_contra hle
    have h' : B + 1 ≤ t := le_of_not_gt hle
    exact absurd hhi (not_lt_of_ge (mul_le_mul h' h' (Arithmetic.zero_le _) (Arithmetic.zero_le _)))
  exact absurd (lt_iff_succ_le.mp hBt) (not_le_of_gt htB)

private theorem r1 : residue (V := V) 1 = 1 := by simpa using residue_nat (V := V) 1
private theorem r3 : residue (V := V) 3 = 3 := by simpa using residue_nat (V := V) 3
private theorem r4 : residue (V := V) 4 = 4 := by simpa using residue_nat (V := V) 4

private theorem aux_bad : ∀ a f g x y : ZMod 4, g + 1 = f * f →
    (a * a + (4 * a + 3)) * g * (x * x) + y * y + 1 ≠ (a * a + (4 * a + 3)) * g * (y * y) := by
  decide

/-- The auxiliary form never takes the value `−1`. -/
theorem na_ne_neg (a f x y : V) (hf : 1 ≤ f * f) :
    (a * a + (4 * a + 3)) * (f * f - 1) * (x * x) + y * y + 1 ≠
      (a * a + (4 * a + 3)) * (f * f - 1) * (y * y) := by
  intro h
  have hr := congrArg (residue (V := V)) h
  have hg : residue (f * f - 1) + 1 = residue f * residue f := by
    rw [← r1 (V := V), ← residue_add, tsub_add_cancel_of_le hf, residue_mul]
  simp only [residue_add, residue_mul, r1, r3, r4] at hr
  exact aux_bad _ _ _ _ _ hg hr

/-- Five squares summing to one, with the fourth nonzero. -/
theorem sq_split {a m w n l : DiffRing V} (h : a * a + m * m + w * w + n * n + l * l = 1)
    (hn : n ≠ 0) : a = 0 ∧ m = 0 ∧ w = 0 ∧ (n = 1 ∨ n = -1) ∧ l = 0 := by
  have h1 : 1 ≤ |n| := DiscreteOrderedRingFacts.abs_ge_one ModelArithmetic.model_discrete hn
  have hn2 : 1 ≤ n * n := by
    have := abs_mul_abs_self n
    nlinarith [abs_nonneg n]
  have ha := mul_self_nonneg a
  have hm := mul_self_nonneg m
  have hw := mul_self_nonneg w
  have hl := mul_self_nonneg l
  have hnn : n * n = 1 := by linarith
  refine ⟨mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith),
    mul_self_eq_zero.mp (by linarith), ?_, mul_self_eq_zero.mp (by linarith)⟩
  exact DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete hnn

/-- A positive zero is a common zero of `A0`, `M`, `W` and `Lt`, with `Na = 1`. -/
theorem residuals (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).output v) :
    InternalZero (graph (fun j => (p j : ℤ))).A0 v ∧ InternalZero (graph (fun j => (p j : ℤ))).M v ∧
      InternalZero (graph (fun j => (p j : ℤ))).W v ∧
      (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) = 1 ∧
      InternalZero (graph (fun j => (p j : ℤ))).Lt v := by
  have hs := (zero_iff _ v).mp hz
  dsimp only at hs
  -- the V-values
  set q : V := (p 0 : V) * v 0 + 1 with hq
  set cV : V := (v 10 + v 11) * v 7 + v 10 with hcV
  set aV : V := (v 8 * q) * v 7 + v 7 with haV
  set ΔV : V := aV * aV + (4 * aV + 3) with hΔV
  have hf1 : 1 ≤ v 4 * v 4 := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp (hv 4)) (pos_iff_one_le.mp (hv 4))
  set A : V := ΔV * (v 4 * v 4 - 1) with hA
  have cA : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux = ι A := by
    rw [c_Aaux, c_Delta, hA, map_mul, ι_tsub hf1, map_mul, map_one]
  obtain ⟨P0, N0, hPN⟩ := exists_mk (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).V
  rw [mk_eq_sub] at hPN
  set x : V := absdiff P0 N0 with hx
  set y : V := absdiff (P0 + v 12) N0 with hy
  have hna : (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) =
      ι A * (ι x * ι x - ι y * ι y) + ι y * ι y := by
    rw [Na_eval, c_y, cA, hPN, hx, hy, ι_absdiff_sq, ι_absdiff_sq, map_add]; ring
  -- Na ≠ 0
  have hn : (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) ≠ 0 := by
    intro h0
    rcases (pos_iff_one_le.mp (hv 4)).lt_or_eq with hf2 | hf1'
    · -- f ≥ 2: A ≥ 2
      have hA2 : 2 ≤ A := by
        have hΔ3 : 3 ≤ ΔV := le_add_self.trans' (le_add_self)
        have hff : 4 ≤ v 4 * v 4 := by
          have h2 : 2 ≤ v 4 := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hf2
          calc (4 : V) = 2 * 2 := by norm_num
            _ ≤ v 4 * v 4 := mul_le_mul h2 h2 (by norm_num) (Arithmetic.zero_le _)
        have hf3 : 3 ≤ v 4 * v 4 - 1 := by
          apply (add_le_add_iff_right (1 : V)).mp
          rw [tsub_add_cancel_of_le hf1]
          calc (3 : V) + 1 = 4 := by norm_num
            _ ≤ v 4 * v 4 := hff
        calc (2 : V) ≤ 3 * 3 := by norm_num
          _ ≤ ΔV * (v 4 * v 4 - 1) := mul_le_mul hΔ3 hf3 (by norm_num) (Arithmetic.zero_le _)
      apply na_ne_zero A P0 N0 (v 12) hA2 (hv 12)
      apply ι_injective
      simp only [map_add, map_mul]
      rw [hna] at h0
      linear_combination h0
    · -- f = 1: W is too large
      have hA0 : A = 0 := by rw [hA, ← hf1', mul_one, tsub_self, mul_zero]
      have hc3 : (3 : V) ≤ cV := by
        have hk2 : 2 ≤ v 10 + v 11 := by
          simpa [one_add_one_eq_two] using add_le_add (pos_iff_one_le.mp (hv 10)) (pos_iff_one_le.mp (hv 11))
        calc (3 : V) = 2 * 1 + 1 := by norm_num
          _ ≤ (v 10 + v 11) * v 7 + v 10 := add_le_add (mul_le_mul hk2 (pos_iff_one_le.mp (hv 7))
              (by norm_num) (Arithmetic.zero_le _)) (pos_iff_one_le.mp (hv 10))
      have hI : (9 : V) ≤ v 5 * (cV * cV) := by
        calc (9 : V) = 1 * (3 * 3) := by norm_num
          _ ≤ v 5 * (cV * cV) := mul_le_mul (pos_iff_one_le.mp (hv 5))
              (mul_le_mul hc3 hc3 (by norm_num) (Arithmetic.zero_le _)) (by norm_num) (Arithmetic.zero_le _)
      have hW : (graph (fun j => (p j : ℤ))).W.evalRing (fun j => ι (v j)) =
          ι (v 5 * (cV * cV)) * ι (v 5 * (cV * cV)) := by
        rw [W_eval, cA, hA0, map_zero, _root_.sub_zero, c_c]; simp only [map_mul]; rfl
      have hI' : (9 : DiffRing V) ≤ ι (v 5 * (cV * cV)) := by
        have h := (ι_le_ι (V := V)).mpr hI; rwa [map_ofNat] at h
      rw [hW, h0] at hs
      set I : DiffRing V := ι (v 5 * (cV * cV)) with hIdef
      have hII : (81 : DiffRing V) ≤ I * I := by nlinarith
      have hIIII : (6561 : DiffRing V) ≤ I * I * (I * I) := by nlinarith
      have := mul_self_nonneg ((graph (fun j => (p j : ℤ))).A0.evalRing (fun j => ι (v j)))
      have := mul_self_nonneg ((graph (fun j => (p j : ℤ))).M.evalRing (fun j => ι (v j)))
      have := mul_self_nonneg ((graph (fun j => (p j : ℤ))).Lt.evalRing (fun j => ι (v j)))
      linarith
  obtain ⟨h0, hm, hw, hn1, hl⟩ := sq_split hs hn
  refine ⟨(internalZero_iff _ _).mpr h0, (internalZero_iff _ _).mpr hm, (internalZero_iff _ _).mpr hw,
    ?_, (internalZero_iff _ _).mpr hl⟩
  rcases hn1 with h1 | hneg
  · exact h1
  · exfalso
    apply na_ne_neg aV (v 4) x y hf1
    rw [← hΔV, ← hA]
    apply ι_injective
    rw [hna] at hneg
    simp only [map_add, map_mul, map_one]
    linear_combination hneg

end P64Norm

#print axioms P64Norm.na_ne_zero
#print axioms P64Norm.na_ne_neg
#print axioms P64Norm.sq_split
#print axioms P64Norm.residuals
