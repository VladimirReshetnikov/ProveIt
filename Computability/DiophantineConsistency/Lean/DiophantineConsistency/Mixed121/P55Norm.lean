import DiophantineConsistency.Mixed121.P55Root
import DiophantineConsistency.Compact44.P64Norm

/-! # Package 55's local norm minimum and unit split

A zero of package 55's equation makes `M² + W² + Na² + (N0·Nt − 1)² = 1`. In
every model of `𝗜𝚺₁`, at a positive valuation with `0 < β`, this forces
`M = W = 0` and `Na = N0 = Nt = 1`:

* `Na ≠ 0`, by P64's argument (`P64Norm.na_ne_zero`). If `f = 1` then
  `Aaux = 0` and `W = (ic²)² ≥ 81`, which is too large. If `f ≥ 2`, then
  `Aaux(Aaux − 1)` would be a square strictly between `(Aaux − 1)²` and
  `Aaux²`;
* so `Na² ≥ 1` by discreteness, the other three squares vanish, and `Na = ±1`.
  `Na = −1` is impossible modulo four (`P64Norm.na_ne_neg`);
* `N0·Nt = 1` makes `N0 = ±1`. With `n = XY² ≥ 2` and `ℓ = nk`,
  `N0 = τ² − n(n+1)k²`, so `N0 = −1` is the excluded consecutive-product
  negative Pell equation (`ModelArithmetic.consecutive_ne_neg_one`). Hence
  `N0 = Nt = 1`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P55Norm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open P55Graph P55Root
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Four squares summing to one, with the third nonzero. -/
theorem sq_split {m w n l : DiffRing V} (h : m * m + w * w + n * n + l * l = 1)
    (hn : n ≠ 0) : m = 0 ∧ w = 0 ∧ (n = 1 ∨ n = -1) ∧ l = 0 := by
  have h1 : 1 ≤ |n| := DiscreteOrderedRingFacts.abs_ge_one ModelArithmetic.model_discrete hn
  have hn2 : 1 ≤ n * n := by
    have := abs_mul_abs_self n
    nlinarith [abs_nonneg n]
  have hm := mul_self_nonneg m
  have hw := mul_self_nonneg w
  have hl := mul_self_nonneg l
  have hnn : n * n = 1 := by linarith
  refine ⟨mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith), ?_,
    mul_self_eq_zero.mp (by linarith)⟩
  exact DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete hnn

/-- A positive zero is a common zero of `M` and `W`, with `Na = N0 = Nt = 1`. -/
theorem residuals (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (hz : InternalZero (graph (fun j => (p j : ℤ))).output v) :
    InternalZero (graph (fun j => (p j : ℤ))).M v ∧ InternalZero (graph (fun j => (p j : ℤ))).W v ∧
      (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) = 1 ∧
      (graph (fun j => (p j : ℤ))).N0.evalRing (fun j => ι (v j)) = 1 ∧
      (graph (fun j => (p j : ℤ))).Nt.evalRing (fun j => ι (v j)) = 1 := by
  have hs := (zero_iff _ v).mp hz
  dsimp only at hs
  have hf1 : 1 ≤ v 4 * v 4 :=
    one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp (hv 4)) (pos_iff_one_le.mp (hv 4))
  have hq2 : (2 : V) ≤ qV p v := by
    have h1 : 1 ≤ (p 0 : V) * v 0 :=
      one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    simpa [qV, one_add_one_eq_two] using (add_le_add_iff_right (1 : V)).mpr h1
  have hq0 : 0 < qV p v := lt_of_lt_of_le (by norm_num) hq2
  have hY0 : 0 < YV p v := mul_pos (hv 7) (mul_pos (mul_pos hq0 hq0) hq0)
  set A : V := ΔV p v * (v 4 * v 4 - 1) with hA
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
        have hΔ3 : 3 ≤ ΔV p v := by
          show 3 ≤ aV p v * aV p v + (4 * aV p v + 3)
          exact le_add_self.trans' le_add_self
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
          _ ≤ ΔV p v * (v 4 * v 4 - 1) := mul_le_mul hΔ3 hf3 (by norm_num) (Arithmetic.zero_le _)
      apply P64Norm.na_ne_zero A P0 N0 (v 12) hA2 (hv 12)
      apply ι_injective
      simp only [map_add, map_mul]
      rw [hna] at h0
      linear_combination h0
    · -- f = 1: W is too large
      have hA0 : A = 0 := by rw [hA, ← hf1', mul_one, tsub_self, mul_zero]
      have hc3 : (3 : V) ≤ cV p v := by
        have hk2 : 2 ≤ kV v := by
          simpa [kV, one_add_one_eq_two] using
            add_le_add (pos_iff_one_le.mp (hv 10)) (pos_iff_one_le.mp (hv 11))
        calc (3 : V) = 2 * 1 + 1 := by norm_num
          _ ≤ kV v * YV p v + v 10 := add_le_add (mul_le_mul hk2 (pos_iff_one_le.mp hY0)
              (by norm_num) (Arithmetic.zero_le _)) (pos_iff_one_le.mp (hv 10))
      have hI : (9 : V) ≤ v 5 * (cV p v * cV p v) := by
        calc (9 : V) = 1 * (3 * 3) := by norm_num
          _ ≤ v 5 * (cV p v * cV p v) := mul_le_mul (pos_iff_one_le.mp (hv 5))
              (mul_le_mul hc3 hc3 (by norm_num) (Arithmetic.zero_le _)) (by norm_num) (Arithmetic.zero_le _)
      have hW : (graph (fun j => (p j : ℤ))).W.evalRing (fun j => ι (v j)) =
          ι (v 5 * (cV p v * cV p v)) * ι (v 5 * (cV p v * cV p v)) := by
        rw [W_eval, cA, hA0, map_zero, _root_.sub_zero, c_c]; simp only [map_mul]
      have hI' : (9 : DiffRing V) ≤ ι (v 5 * (cV p v * cV p v)) := by
        have h := (ι_le_ι (V := V)).mpr hI; rwa [map_ofNat] at h
      rw [hW, h0] at hs
      set I : DiffRing V := ι (v 5 * (cV p v * cV p v)) with hIdef
      have hII : (81 : DiffRing V) ≤ I * I := by nlinarith
      have hIIII : (6561 : DiffRing V) ≤ I * I * (I * I) := by nlinarith
      have := mul_self_nonneg ((graph (fun j => (p j : ℤ))).M.evalRing (fun j => ι (v j)))
      have := mul_self_nonneg ((graph (fun j => (p j : ℤ))).N0.evalRing (fun j => ι (v j)) *
        (graph (fun j => (p j : ℤ))).Nt.evalRing (fun j => ι (v j)) - 1)
      linarith
  obtain ⟨hm, hw, hn1, hl⟩ := sq_split hs hn
  -- Na = 1
  have hNa : (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) = 1 := by
    rcases hn1 with h1 | hneg
    · exact h1
    · exfalso
      apply P64Norm.na_ne_neg (aV p v) (v 4) x y hf1
      have hΔ : aV p v * aV p v + (4 * aV p v + 3) = ΔV p v := rfl
      rw [hΔ, ← hA]
      apply ι_injective
      rw [hna] at hneg
      simp only [map_add, map_mul, map_one]
      linear_combination hneg
  -- N0 · Nt = 1, and N0 ≠ −1
  set n0 := (graph (fun j => (p j : ℤ))).N0.evalRing (fun j => ι (v j)) with hn0
  set nt := (graph (fun j => (p j : ℤ))).Nt.evalRing (fun j => ι (v j)) with hnt
  have hprod : n0 * nt = 1 := sub_eq_zero.mp hl
  have hu := DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one ModelArithmetic.model_discrete hprod
  have hN01 : n0 = 1 := by
    rcases hu with h1 | hneg
    · exact h1
    · exfalso
      have hX2 : 2 ≤ XV p v :=
        le_trans hq2 (le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 8)))
      have hn2 : (2 : V) ≤ EV p v * YV p v := by
        show 2 ≤ XV p v * YV p v * YV p v
        rw [mul_assoc]
        exact le_trans hX2 (le_mul_of_one_le_right (Arithmetic.zero_le _)
          (one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hY0) (pos_iff_one_le.mp hY0)))
      have hn2' : (2 : DiffRing V) ≤ ι (EV p v * YV p v) := ModelArithmetic.two_le_ι hn2
      apply ModelArithmetic.consecutive_ne_neg_one (ι (EV p v * YV p v)) (ι (v 9)) (ι (kV v)) hn2'
      rw [hn0, N0_eval, c_ell, c_k] at hneg
      have hell : ι (ellV p v) = ι (EV p v * YV p v) * ι (kV v) := by
        simp only [ellV, map_mul]; ring
      rw [hell] at hneg
      linear_combination hneg
  have hNt1 : nt = 1 := by rw [hN01, one_mul] at hprod; exact hprod
  exact ⟨(internalZero_iff _ _).mpr hm, (internalZero_iff _ _).mpr hw, hNa, hN01, hNt1⟩

end P55Norm

#print axioms P55Norm.sq_split
#print axioms P55Norm.residuals
