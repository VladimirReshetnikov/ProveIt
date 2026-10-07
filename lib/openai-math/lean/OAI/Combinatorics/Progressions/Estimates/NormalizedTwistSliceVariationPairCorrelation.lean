/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.NormalizedTwistAffineCells

namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {A K X : Type*} [Fintype A] [Fintype K] [DecidableEq K] [Fintype X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

omit [Fintype K] [DecidableEq K] in
theorem modulus_product_bound
    (W : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    {v : ℝ} (hv : periodCap ≤ Real.exp v) :
    ((∏ a, (W a).modulus : ℕ) : ℝ) ≤ Real.exp (Fintype.card A * v) := by
  rw [Nat.cast_prod]
  calc
    _ ≤ ∏ _a : A, Real.exp v :=
      Finset.prod_le_prod₀ (fun a _ => Nat.cast_nonneg _) (fun a _ => (W a).modulus_bound.trans hv)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

theorem exists_common_local_parameter_freezing [IsEmpty (Σ j, J j)]
    (W : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (P : K → ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hperiod : ((∏ a, (W a).modulus : ℕ) : ℝ) ≤ Real.exp p)
    (hP : ∀ k, Real.exp (3 * p + 16) ≤ (P k : ℝ)) :
    ∃ Q : ∀ k, FiniteProgressionPartition (P k),
      (∀ k c, (Q k).step c = ∏ a, (W a).modulus) ∧
      (∀ k c, 0 < (Q k).length c) ∧
      (∀ k c, (P k : ℝ) * Real.exp (-(3 * p + 16)) ≤ (Q k).length c) ∧
      (Fintype.card (∀ k, (Q k).Label) : ℝ) ≤
        Real.exp (Fintype.card K * (3 * p + 16)) ∧
      ∀ (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (frame : A → Option K × X → ℤ) (C : A → K → ℝ),
        (∀ a k, 0 ≤ C a k) →
        (∀ a k x, |(frame a (some k, x) : ℝ) / N x| * P k ≤ C a k) →
        ∃ coefficient : A → (∀ k, (Q k).Label) → ℂ,
          (∀ a c, ‖coefficient a c‖ ≤ 1) ∧
          ∀ a c (t : ∀ k, Fin ((Q k).length (c k))),
            ‖(W a).eval N poly (integerPhysicalSite
              (fun k => (((Q k).point (c k) (t k)).val : ℤ)) (frame a)) -
              coefficient a c‖ ≤
            (L : ℝ) * (Real.exp (-(2 * p)) / 4) * ∑ k, C a k := by
  let q := ∏ a, (W a).modulus
  have hq : 0 < q := Finset.prod_pos (fun a _ => (W a).modulus_pos)
  obtain ⟨Q, hstep, hlength, hlower, hnear, _, _, hcard⟩ :=
    exists_normalizedTwist_parameter_partition P q p hp hq hperiod hP
  refine ⟨Q, hstep, hlength, hlower, hcard, ?_⟩
  intro N poly frame C hC hslope
  let coefficient := fun a (c : ∀ k, (Q k).Label) =>
    (W a).eval N poly (integerPhysicalSite (fun k => ((Q k).start (c k) : ℤ)) (frame a))
  refine ⟨coefficient, fun a c => (W a).norm_eval_le N poly _, ?_⟩
  intro a c t
  have hqzero : (q : ZMod (W a).modulus) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Finset.dvd_prod_of_mem _ (Finset.mem_univ a))
  apply eval_local_parameter_freezing (W a) N P
    (fun k => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hP k)))
    poly (frame a) _ _ (C a) (hC a) (by positivity) (hslope a)
  · intro k
    simpa only [Int.cast_natCast] using hnear k (c k) (t k)
  · intro k
    simp only [FiniteProgressionPartition.point_val, hstep, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, hqzero, zero_mul, add_zero]

theorem exists_common_local_parameter_cells_with_correlation [IsEmpty (Σ j, J j)]
    (W : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (P : K → ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hperiod : ((∏ a, (W a).modulus : ℕ) : ℝ) ≤ Real.exp p)
    (hP : ∀ k, Real.exp (3 * p + 16) ≤ (P k : ℝ)) :
    ∃ Q : ∀ k, FiniteProgressionPartition (P k),
      (∀ k c, (Q k).step c = ∏ a, (W a).modulus) ∧
      (∀ k c, 0 < (Q k).length c) ∧
      (∀ k c, (P k : ℝ) * Real.exp (-(3 * p + 16)) ≤ (Q k).length c) ∧
      (Fintype.card (∀ k, (Q k).Label) : ℝ) ≤
        Real.exp (Fintype.card K * (3 * p + 16)) ∧
      ∀ (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (frame : A → Option K × X → ℤ) (C : A → K → ℝ),
        (∀ a k, 0 ≤ C a k) →
        (∀ a k x, |(frame a (some k, x) : ℝ) / N x| * P k ≤ C a k) →
        ∀ (a : A) (μ : FiniteProbabilityWeights (∀ k, Fin (P k)))
          (signal : (∀ k, Fin (P k)) → ℂ) (δ : ℝ),
          0 < δ → (∀ t, ‖signal t‖ ≤ 1) →
          δ ≤ ‖μ.complexMean (fun t => star ((W a).eval N poly
            (integerPhysicalSite (fun k => ((t k).val : ℤ)) (frame a))) * signal t)‖ →
          ∃ (c : ∀ k, (Q k).Label)
            (hc : 0 < μ.mass (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c))),
            δ / (2 * Fintype.card (∀ k, (Q k).Label)) ≤
              μ.mass (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c)) ∧
            δ / 2 - (L : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, C a k) ≤
              ‖(μ.condition (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c))
                hc).complexMean signal‖ := by
  obtain ⟨Q, hstep, hlength, hlower, hcard, hfreeze⟩ :=
    exists_common_local_parameter_freezing W P p hp hperiod hP
  refine ⟨Q, hstep, hlength, hlower, hcard, ?_⟩
  intro N poly frame C hC hslope a μ signal δ hδ hsignal hbias
  obtain ⟨coefficient, hcoefficient, herr⟩ := hfreeze N poly frame C hC hslope
  let label := BoxProgressionPartition.cell Q
  let twist := fun t : ∀ k, Fin (P k) =>
    (W a).eval N poly (integerPhysicalSite (fun k => ((t k).val : ℤ)) (frame a))
  let : Nonempty (∀ k, (Q k).Label) := ⟨fun k => (Q k).cell
    ⟨0, Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hP k))⟩⟩
  obtain ⟨c, hc, hmass, hb⟩ := μ.exists_large_correlating_fiber label
    (fun t => star (twist t) * signal t) hδ (fun t => by
      rw [norm_mul, norm_star]
      exact (mul_le_mul ((W a).norm_eval_le N poly _) (hsignal t)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) hbias
  refine ⟨c, hc, hmass, ?_⟩
  let ν := μ.condition (Finset.univ.filter (fun t => label t = c)) hc
  apply correlation_after_freezing ν twist signal (coefficient a c)
    (hcoefficient a c) hsignal ?_ hb
  intro t ht
  have htc : label t = c := by
    by_contra hn
    exact ht (by simp only [ν, FiniteProbabilityWeights.condition,
      Finset.mem_filter, Finset.mem_univ, true_and, hn, ite_false, zero_div])
  have he := herr a (label t) (fun k => (Q k).offset (t k))
  simpa only [label, BoxProgressionPartition.cell, FiniteProgressionPartition.point_cell_offset,
    htc] using he

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_untwisted_subrectangle_of_fullSliceLaw
    {A K X : Type*} [Fintype A] [Fintype K] [DecidableEq K] [Fintype X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] [IsEmpty (Σ j, J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    (hperiod : ((∏ a, (W a).modulus : ℕ) : ℝ) ≤ Real.exp p)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (frame : A → Option K × X → ℤ) (C : A → K → ℝ)
    (hC : ∀ a k, 0 ≤ C a k)
    (hslope : ∀ a k x, |(frame a (some k, x) : ℝ) / N x| * P k ≤ C a k)
    (a : A) (signal : integerBox P → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsignal : ∀ t, ‖signal t‖ ≤ 1)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
      star ((W a).eval N poly (integerPhysicalSite t.val (frame a))) * signal t)‖) :
    ∃ T : ResidueBoxSlice P (q * ∏ a, (W a).modulus),
      0 < q * ∏ a, (W a).modulus ∧
      (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - 2 * (L : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, C a k) ≤
        ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ := by
  have hSL : ∀ k, Real.exp (3 * p + 16) ≤ (S.length k : ℝ) :=
    fun k => S.length_large_of_cost hS hP k
  have htwo : ∀ k, 2 ≤ S.length k := by
    intro k
    have he := Real.add_one_le_exp (3 * p + 16)
    have hh := hSL k
    have : (2 : ℝ) ≤ S.length k := by linarith
    exact_mod_cast this
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  obtain ⟨Q, hstep, hlength, hlower, hcard, hlocal⟩ :=
    exists_common_local_parameter_cells_with_correlation W S.length p hp hperiod hSL
  let newframe := fun a => S.pullbackIntegerFrame (frame a)
  have hnew : ∀ a k x,
      |(newframe a (some k, x) : ℝ) / N x| * S.length k ≤ 2 * C a k :=
    fun a k x => S.pullback_normalized_slope_bound htwo (frame a) N (C a) (hslope a) k x
  have hsite (a : A) (u : ∀ k, Fin (S.length k)) :
      integerPhysicalSite (fun k => ((u k).val : ℤ)) (newframe a) =
        integerPhysicalSite (S.fullSlicePointInIntegerBox u).val (frame a) := by
    rw [ResidueBoxSlice.integerPhysicalSite_pullback]
    congr 1
  let μ := FiniteProbabilityWeights.uniform (∀ k, Fin (S.length k))
  have hbound : δ ≤ ‖μ.complexMean (fun u => star ((W a).eval N poly
      (integerPhysicalSite (fun k => ((u k).val : ℤ)) (newframe a))) *
        signal (S.fullSlicePointInIntegerBox u))‖ := by
    rw [S.fullSliceLaw_complexMean] at hbias
    simpa only [μ, FiniteProbabilityWeights.uniform_complexMean, hsite] using hbias
  obtain ⟨c, hc, hmass, hcorr⟩ := hlocal N poly newframe (fun a k => 2 * C a k)
    (fun a k => mul_nonneg (by norm_num) (hC a k)) hnew a μ
    (fun u => signal (S.fullSlicePointInIntegerBox u)) δ hδ
    (fun u => hsignal _) hbound
  let T₀ := ResidueBoxSlice.parameterCell Q hstep c
  let T := S.composeSlice T₀
  have heval (u : ∀ k, Fin ((Q k).length (c k))) :
      T.fullSlicePointInIntegerBox u =
        S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u) := by
    apply Subtype.ext
    funext k
    change ((S.start k + q * (Q k).start (c k) +
      (q * ∏ a, (W a).modulus) * (u k).val : ℕ) : ℤ) =
        ((S.start k + q * ((Q k).point (c k) (u k)).val : ℕ) : ℤ)
    rw [FiniteProgressionPartition.point_val, hstep]
    push_cast
    ring
  refine ⟨T, mul_pos hq (Finset.prod_pos (fun a _ => (W a).modulus_pos)),
    fun k => hlength k (c k), ?_, ?_⟩
  · intro k
    exact S.composeSlice_length_lower T₀ hS (fun k => hlower k (c k)) k
  · have hmean : (μ.condition
        (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c)) hc).complexMean
          (fun u => signal (S.fullSlicePointInIntegerBox u)) =
        𝔼 u, signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      rw [FiniteProbabilityWeights.uniform_condition_complexMean]
      have hset : Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c) =
          partitionCell (BoxProgressionPartition.cell Q) c := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_partitionCell]
      rw [hset, BoxProgressionPartition.expect_cell_complex]
    rw [hmean] at hcorr
    have hexpect : (𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)) =
        𝔼 u : (∀ k, Fin ((Q k).length (c k))),
          signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      change (𝔼 t : (∀ k, Fin ((Q k).length (c k))), signal (T.fullSlicePointInIntegerBox t)) = _
      apply Finset.expect_congr rfl
      intro t _
      rw [heval]
    rw [hexpect]
    have herror : (L : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, 2 * C a k) =
        2 * (L : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, C a k) := by
      rw [← Finset.mul_sum]
      ring
    rw [herror] at hcorr
    exact hcorr

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {A K X : Type*} [Fintype A] [Fintype K] [DecidableEq K] [Fintype X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem exists_trimmed_local_parameter_cells_with_correlation [IsEmpty (Σ j, J j)]
    (W : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (P : K → ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hperiod : ((∏ a, (W a).modulus : ℕ) : ℝ) ≤ Real.exp p)
    (hP : ∀ k, Real.exp (3 * p + 16) ≤ (P k : ℝ)) :
    ∃ Q : ∀ k, FiniteProgressionPartition (P k),
      (∀ k c, (Q k).step c = ∏ a, (W a).modulus) ∧
      (∀ k c, 0 < (Q k).length c) ∧
      (∀ k c, (P k : ℝ) * Real.exp (-(3 * p + 16)) ≤ (Q k).length c) ∧
      (Fintype.card (∀ k, (Q k).Label) : ℝ) ≤
        Real.exp (Fintype.card K * (3 * p + 16)) ∧
      ∀ (N : X → ℕ), (∀ x, 0 < N x) →
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (B τ : ℝ),
        0 ≤ B → 0 ≤ τ → (∑ k, (P k : ℝ)) ≤ B →
        ∀ (z : A → rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1)
          (a : A) (μ : FiniteProbabilityWeights (∀ k, Fin (P k)))
          (signal : (∀ k, Fin (P k)) → ℂ) (δ : ℝ),
          0 < δ → (∀ t, ‖signal t‖ ≤ 1) →
          δ ≤ ‖μ.complexMean (fun t => star ((W a).eval N poly
            (centeredIntegerPhysicalSite (fun k => ((t k).val : ℤ)) N (z a).val)) * signal t)‖ →
          ∃ (c : ∀ k, (Q k).Label)
            (hc : 0 < μ.mass (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c))),
            δ / (2 * Fintype.card (∀ k, (Q k).Label)) ≤
              μ.mass (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c)) ∧
            δ / 2 - (L : ℝ) * Real.exp (-(2 * p)) * τ / 32 ≤
              ‖(μ.condition (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c))
                hc).complexMean signal‖ := by
  obtain ⟨Q, hstep, hlength, hlower, hcard, hfreeze⟩ :=
    exists_common_local_parameter_cells_with_correlation W P p hp hperiod hP
  refine ⟨Q, hstep, hlength, hlower, hcard, ?_⟩
  intro N hN poly B τ hB hτ hPB z a μ signal δ hδ hsignal hbias
  let frame := fun a => baseArrayJoin (fun k : K × X => (z a).val (some k.1, k.2))
    (fun x => integerBoxCenter N x + (z a).val (none, x))
  have heval (a : A) (u : K → ℤ) : integerPhysicalSite u (frame a) =
      centeredIntegerPhysicalSite u N (z a).val := by
    funext x
    simp only [frame, integerPhysicalSite, baseArrayJoin, centeredIntegerPhysicalSite, Pi.add_apply]
    ring
  let C : A → K → ℝ := fun _ k => τ * (P k : ℝ) / (8 * (1 + B))
  have hC : ∀ a k, 0 ≤ C a k := by intro a k; dsimp only [C]; positivity
  have hslope : ∀ a k x, |(frame a (some k, x) : ℝ) / N x| * P k ≤ C a k :=
    fun a k x => trimmedSpatial_normalized_parameter_slope P N hN hB hτ (z a) k x
  have hsum : (∑ k, C a k) ≤ τ / 8 := by
    have hb : 0 < 8 * (1 + B) := by positivity
    calc
      _ = τ * (∑ k, (P k : ℝ)) / (8 * (1 + B)) := by
        simp only [C, ← Finset.sum_div, Finset.mul_sum]
      _ ≤ τ * B / (8 * (1 + B)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPB hτ) hb.le
      _ ≤ τ / 8 := by
        apply (div_le_iff₀ hb).mpr
        nlinarith
  obtain ⟨c, hc, hmass, hcorr⟩ := hfreeze N poly frame C hC hslope a μ signal δ hδ hsignal
    (by simpa only [heval] using hbias)
  refine ⟨c, hc, hmass, ?_⟩
  have herr : (L : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, C a k) ≤
      (L : ℝ) * Real.exp (-(2 * p)) * τ / 32 := by
    exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)
  linarith

omit [Fintype A] [Fintype K] [DecidableEq K] [Fintype X] [∀ j, Fintype (J j)] in

theorem trimmed_local_freezing_error_le_quarter {p δ τ : ℝ}
    (hδ : 0 < δ) (hL : (L : ℝ) ≤ Real.exp p) (hδinv : δ⁻¹ ≤ Real.exp p)
    (hτ : 0 ≤ τ) (hτone : τ ≤ 1) :
    (L : ℝ) * Real.exp (-(2 * p)) * τ / 32 ≤ δ / 4 := by
  have he : Real.exp (-p) ≤ δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos p) hδ).mpr hδinv
  have hprod : (L : ℝ) * Real.exp (-(2 * p)) * τ ≤ δ := by
    calc
      _ ≤ Real.exp p * Real.exp (-(2 * p)) * 1 := by gcongr
      _ = Real.exp (-p) := by rw [mul_one, ← Real.exp_add]; congr 1; ring
      _ ≤ δ := he
  linarith

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3

open scoped BigOperators Classical TensorProduct NNReal

namespace ResidueBoxSlice

theorem fin_mean_eq_translated_zero {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (T : ResidueBoxSlice P q) (f : (K → ℤ) → ℂ) :
    (𝔼 t : (∀ k, Fin (T.length k)), f (T.fullSlicePointInIntegerBox t).val) =
      𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
        f (fun k => (q : ℤ) * x k + T.start k) := by
  have hzero : translatedIntegerBox (0 : K → ℤ) T.length = integerBox T.length := by
    ext x
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  rw [hzero, integerBox_expect_eq_fin]
  apply Finset.expect_congr rfl
  intro t _
  congr 1
  funext k
  simp only [fullSlicePointInIntegerBox, point, Nat.cast_add, Nat.cast_mul, add_comm]

end ResidueBoxSlice

namespace VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel

theorem exists_niltest_pair_correlation_subrectangle
    {A K X : Type*} [Fintype A] [Fintype K] [DecidableEq K] [Fintype X]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] [IsEmpty (Σ j, J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (twists : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    (hperiod : ((∏ a, (twists a).modulus : ℕ) : ℝ) ≤ Real.exp p)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (frame : A → Option K × X → ℤ) (C : A → K → ℝ)
    (hC : ∀ a k, 0 ≤ C a k)
    (hslope : ∀ a k x, |(frame a (some k, x) : ℝ) / N x| * P k ≤ C a k)
    {LG MG : Type*} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    {D : RationalFilteredNilmanifold LG s d} {E : RationalFilteredNilmanifold MG s e}
    (V : D.Niltest (fun _ : K => 1)) (Wlocal : E.Niltest (fun _ : K => 1))
    {pLocal : ℝ} (hV : V.ComplexityLE pLocal) (hW : Wlocal.normBound ≤ 1)
    (a : A) {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
      star ((twists a).eval N poly (integerPhysicalSite t.val (frame a))) *
        (V.eval t.val * Wlocal.eval t.val))‖) :
    ∃ T : ResidueBoxSlice P (q * ∏ a, (twists a).modulus),
      0 < q * ∏ a, (twists a).modulus ∧
      (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - Real.exp pLocal *
          (2 * (Lip : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, C a k)) ≤
        ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
          V.eval (fun k => ((q * ∏ a, (twists a).modulus : ℕ) : ℤ) * x k + T.start k) *
          Wlocal.eval (fun k => ((q * ∏ a, (twists a).modulus : ℕ) : ℤ) * x k + T.start k)‖ := by
  let signal : integerBox P → ℂ := fun t =>
    (Real.exp (-pLocal) : ℂ) * (V.eval t.val * Wlocal.eval t.val)
  have hsignal : ∀ t, ‖signal t‖ ≤ 1 := by
    intro t
    have hpartner : ‖Wlocal.eval t.val‖ ≤ 1 :=
      (Wlocal.norm_eval_le _).trans (by exact_mod_cast hW)
    have hprod : ‖V.eval t.val * Wlocal.eval t.val‖ ≤ Real.exp pLocal := by
      rw [norm_mul]
      exact (mul_le_mul (V.eval_budget hV _) hpartner (norm_nonneg _)
        (Real.exp_nonneg _)).trans_eq (mul_one _)
    dsimp only [signal]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (-pLocal) * Real.exp pLocal :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscaled : Real.exp (-pLocal) * δ ≤ ‖(S.fullSliceLaw hlen).complexMean
      (fun t => star ((twists a).eval N poly (integerPhysicalSite t.val (frame a))) * signal t)‖ := by
    have heq : (S.fullSliceLaw hlen).complexMean
        (fun t => star ((twists a).eval N poly (integerPhysicalSite t.val (frame a))) * signal t) =
        (Real.exp (-pLocal) : ℂ) * (S.fullSliceLaw hlen).complexMean (fun t =>
          star ((twists a).eval N poly (integerPhysicalSite t.val (frame a))) *
            (V.eval t.val * Wlocal.eval t.val)) := by
      rw [← FiniteProbabilityWeights.complexMean_mul_left]
      congr 1
      funext t
      dsimp only [signal]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left hbias (Real.exp_nonneg _)
  obtain ⟨T, hTq, hTlen, hTlength, hc⟩ := exists_untwisted_subrectangle_of_fullSliceLaw
    twists S hq hlen hp hS hP hperiod N poly frame C hC hslope a signal
    (mul_pos (Real.exp_pos _) hδ) hsignal hscaled
  have hmean : ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ =
      Real.exp (-pLocal) *
        ‖𝔼 t : (∀ k, Fin (T.length k)),
          V.eval (T.fullSlicePointInIntegerBox t).val * Wlocal.eval (T.fullSlicePointInIntegerBox t).val‖ := by
    simp only [signal, ← Finset.mul_expect, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
  rw [hmean] at hc
  have he : Real.exp pLocal * Real.exp (-pLocal) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hrestore := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg pLocal)
  have hlhs : Real.exp pLocal * (Real.exp (-pLocal) * δ / 2 -
      2 * (Lip : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, C a k)) =
      δ / 2 - Real.exp pLocal *
        (2 * (Lip : ℝ) * (Real.exp (-(2 * p)) / 4) * (∑ k, C a k)) := by
    rw [mul_sub, ← mul_div_assoc, ← mul_assoc, he, one_mul]
  have hcancel (x : ℝ) : Real.exp pLocal * (Real.exp (-pLocal) * x) = x := by
    rw [← mul_assoc, he, one_mul]
  rw [hlhs, hcancel] at hrestore
  refine ⟨T, hTq, hTlen, hTlength, ?_⟩
  rwa [T.fin_mean_eq_translated_zero (fun x => V.eval x * Wlocal.eval x)] at hrestore

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

namespace ResidueBoxSlice

theorem fullSlicePoint_normalized_distance_le
    {K : Type*} [Fintype K] [DecidableEq K] {P : K → ℕ} {q : ℕ}
    (S : ResidueBoxSlice P q) (htwo : ∀ k, 2 ≤ S.length k)
    (u v : ∀ k, Fin (S.length k)) {η : ℝ}
    (hnear : ∀ k, |((u k).val : ℝ) / S.length k -
      ((v k).val : ℝ) / S.length k| ≤ η) (k : K) :
    |((S.fullSlicePointInIntegerBox u).val k : ℝ) / P k -
      ((S.fullSlicePointInIntegerBox v).val k : ℝ) / P k| ≤ 2 * η := by
  have htwoK := htwo k
  have hlen : (0 : ℝ) < S.length k := by exact_mod_cast (by omega : 0 < S.length k)
  have hP : (0 : ℝ) < P k := by
    have h := S.inside k 0 (by omega)
    exact_mod_cast (show 0 < P k by omega)
  have hspan : (q : ℝ) * S.length k ≤ 2 * (P k : ℝ) := by
    exact_mod_cast S.stride_mul_length_le_twice k (htwo k)
  have hfac : (q : ℝ) * S.length k / P k ≤ 2 := (div_le_iff₀ hP).mpr hspan
  have hfac0 : 0 ≤ (q : ℝ) * S.length k / P k := by positivity
  have heq : ((S.fullSlicePointInIntegerBox u).val k : ℝ) / P k -
      ((S.fullSlicePointInIntegerBox v).val k : ℝ) / P k =
      ((q : ℝ) * S.length k / P k) *
        (((u k).val : ℝ) / S.length k - ((v k).val : ℝ) / S.length k) := by
    simp only [fullSlicePointInIntegerBox, point, Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp
    ring
  rw [heq, abs_mul, abs_of_nonneg hfac0]
  exact mul_le_mul hfac (hnear k) (abs_nonneg _) (by norm_num)

end ResidueBoxSlice

namespace VectorPolynomial.NormalizedPolynomialTwist

theorem exists_untwisted_subrectangle_of_fullSliceLaw_of_variation
    {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    {M : ℕ} (hM : 0 < M) (hMexp : (M : ℝ) ≤ Real.exp p)
    (twist : integerBox P → ℂ) (htwist : ∀ t, ‖twist t‖ ≤ 1)
    {ε : ℝ}
    (hvariation : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * p)) / 4)) → ‖twist u - twist v‖ ≤ ε)
    (signal : integerBox P → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsignal : ∀ t, ‖signal t‖ ≤ 1)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean
      (fun t => star (twist t) * signal t)‖) :
    ∃ T : ResidueBoxSlice P (q * M),
      0 < q * M ∧ (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - ε ≤
        ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ := by
  have hSL : ∀ k, Real.exp (3 * p + 16) ≤ (S.length k : ℝ) :=
    fun k => S.length_large_of_cost hS hP k
  have htwo : ∀ k, 2 ≤ S.length k := by
    intro k
    have he := Real.add_one_le_exp (3 * p + 16)
    have hh := hSL k
    have : (2 : ℝ) ≤ S.length k := by linarith
    exact_mod_cast this
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  obtain ⟨Q, hstep, hlength, hlower, _, hnear, _, _⟩ :=
    exists_normalizedTwist_parameter_partition S.length M p hp hM hMexp hSL
  let label := BoxProgressionPartition.cell Q
  let base := fun (c : ∀ k, (Q k).Label) =>
    BoxProgressionPartition.point Q c (fun k => ⟨0, hlength k (c k)⟩)
  let coefficient := fun c => twist (S.fullSlicePointInIntegerBox (base c))
  have herr (c : ∀ k, (Q k).Label) (t : ∀ k, Fin ((Q k).length (c k))) :
      ‖twist (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c t)) -
        coefficient c‖ ≤ ε := by
    apply hvariation
    · intro k
      simp only [ResidueBoxSlice.fullSlicePointInIntegerBox, ResidueBoxSlice.point,
        BoxProgressionPartition.point, FiniteProgressionPartition.point_val, hstep, base,
        Nat.cast_add, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, Nat.cast_zero,
        zero_mul, add_zero]
    · exact S.fullSlicePoint_normalized_distance_le htwo _ _
        (fun k => hnear k (c k) (t k) ⟨0, hlength k (c k)⟩)
  let μ := FiniteProbabilityWeights.uniform (∀ k, Fin (S.length k))
  let pulledTwist := fun u => twist (S.fullSlicePointInIntegerBox u)
  let pulledSignal := fun u => signal (S.fullSlicePointInIntegerBox u)
  have hbound : δ ≤ ‖μ.complexMean (fun u => star (pulledTwist u) * pulledSignal u)‖ := by
    rw [S.fullSliceLaw_complexMean] at hbias
    simpa only [μ, pulledTwist, pulledSignal, FiniteProbabilityWeights.uniform_complexMean] using hbias
  let : Nonempty (∀ k, (Q k).Label) := ⟨fun k => (Q k).cell ⟨0, hlen k⟩⟩
  obtain ⟨c, hc, _, hb⟩ := μ.exists_large_correlating_fiber label
    (fun t => star (pulledTwist t) * pulledSignal t) hδ (fun t => by
      rw [norm_mul, norm_star]
      exact (mul_le_mul (htwist _) (hsignal _) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul 1)) hbound
  let ν := μ.condition (Finset.univ.filter (fun t => label t = c)) hc
  have hcorr : δ / 2 - ε ≤ ‖ν.complexMean pulledSignal‖ := by
    apply correlation_after_freezing ν pulledTwist pulledSignal (coefficient c)
      (htwist _) (fun t => hsignal _) ?_ hb
    intro t ht
    have htc : label t = c := by
      by_contra hn
      exact ht (by simp only [ν, FiniteProbabilityWeights.condition,
        Finset.mem_filter, Finset.mem_univ, true_and, hn, ite_false, zero_div])
    have he := herr (label t) (fun k => (Q k).offset (t k))
    have hpoint : BoxProgressionPartition.point Q (label t)
        (fun k => (Q k).offset (t k)) = t := by
      funext k
      exact (Q k).point_cell_offset (t k)
    rw [hpoint, htc] at he
    exact he
  let T₀ := ResidueBoxSlice.parameterCell Q hstep c
  let T := S.composeSlice T₀
  have heval (u : ∀ k, Fin ((Q k).length (c k))) :
      T.fullSlicePointInIntegerBox u =
        S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u) := by
    apply Subtype.ext
    funext k
    change ((S.start k + q * (Q k).start (c k) +
      (q * M) * (u k).val : ℕ) : ℤ) =
        ((S.start k + q * ((Q k).point (c k) (u k)).val : ℕ) : ℤ)
    rw [FiniteProgressionPartition.point_val, hstep]
    push_cast
    ring
  refine ⟨T, mul_pos hq hM, fun k => hlength k (c k), ?_, ?_⟩
  · exact fun k => S.composeSlice_length_lower T₀ hS (fun k => hlower k (c k)) k
  · have hmean : ν.complexMean pulledSignal =
        𝔼 u, signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      dsimp only [ν, μ, pulledSignal]
      rw [FiniteProbabilityWeights.uniform_condition_complexMean]
      have hset : Finset.univ.filter (fun t => label t = c) =
          partitionCell (BoxProgressionPartition.cell Q) c := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_partitionCell, label]
      rw [hset, BoxProgressionPartition.expect_cell_complex]
    rw [hmean] at hcorr
    have hexpect : (𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)) =
        𝔼 u : (∀ k, Fin ((Q k).length (c k))),
          signal (S.fullSlicePointInIntegerBox (BoxProgressionPartition.point Q c u)) := by
      change (𝔼 t : (∀ k, Fin ((Q k).length (c k))), signal (T.fullSlicePointInIntegerBox t)) = _
      apply Finset.expect_congr rfl
      intro t _
      rw [heval]
    rwa [hexpect]

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical TensorProduct NNReal

namespace VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel

theorem exists_niltest_pair_correlation_subrectangle_of_variation
    {K : Type*} [Fintype K] [DecidableEq K]
    {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (hq : 0 < q)
    (hlen : ∀ k, 0 < S.length k) {cost p : ℝ} (hp : 0 ≤ p)
    (hS : ∀ k, Real.exp (-cost) * (P k : ℝ) ≤ S.length k)
    (hP : ∀ k, Real.exp (cost + (3 * p + 16)) ≤ (P k : ℝ))
    {M : ℕ} (hM : 0 < M) (hMexp : (M : ℝ) ≤ Real.exp p)
    (twist : integerBox P → ℂ) (htwist : ∀ t, ‖twist t‖ ≤ 1)
    {ε : ℝ}
    (hvariation : ∀ u v : integerBox P,
      (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
      (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤
        2 * (Real.exp (-(2 * p)) / 4)) → ‖twist u - twist v‖ ≤ ε)
    {LG MG : Type*} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
    {s d e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    {D : RationalFilteredNilmanifold LG s d} {E : RationalFilteredNilmanifold MG s e}
    (V : D.Niltest (fun _ : K => 1)) (Wlocal : E.Niltest (fun _ : K => 1))
    {pLocal : ℝ} (hV : V.ComplexityLE pLocal) (hW : Wlocal.normBound ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
      star (twist t) *
        (V.eval t.val * Wlocal.eval t.val))‖) :
    ∃ T : ResidueBoxSlice P (q * M),
      0 < q * M ∧
      (∀ k, 0 < T.length k) ∧
      (∀ k, Real.exp (-(cost + (3 * p + 16))) * (P k : ℝ) ≤ T.length k) ∧
      δ / 2 - Real.exp pLocal *
          ε ≤
        ‖𝔼 x ∈ translatedIntegerBox (0 : K → ℤ) T.length,
          V.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k) *
          Wlocal.eval (fun k => ((q * M : ℕ) : ℤ) * x k + T.start k)‖ := by
  let signal : integerBox P → ℂ := fun t =>
    (Real.exp (-pLocal) : ℂ) * (V.eval t.val * Wlocal.eval t.val)
  have hsignal : ∀ t, ‖signal t‖ ≤ 1 := by
    intro t
    have hpartner : ‖Wlocal.eval t.val‖ ≤ 1 :=
      (Wlocal.norm_eval_le _).trans (by exact_mod_cast hW)
    have hprod : ‖V.eval t.val * Wlocal.eval t.val‖ ≤ Real.exp pLocal := by
      rw [norm_mul]
      exact (mul_le_mul (V.eval_budget hV _) hpartner (norm_nonneg _)
        (Real.exp_nonneg _)).trans_eq (mul_one _)
    dsimp only [signal]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ Real.exp (-pLocal) * Real.exp pLocal :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscaled : Real.exp (-pLocal) * δ ≤ ‖(S.fullSliceLaw hlen).complexMean
      (fun t => star (twist t) * signal t)‖ := by
    have heq : (S.fullSliceLaw hlen).complexMean
        (fun t => star (twist t) * signal t) =
        (Real.exp (-pLocal) : ℂ) * (S.fullSliceLaw hlen).complexMean (fun t =>
          star (twist t) *
            (V.eval t.val * Wlocal.eval t.val)) := by
      rw [← FiniteProbabilityWeights.complexMean_mul_left]
      congr 1
      funext t
      dsimp only [signal]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left hbias (Real.exp_nonneg _)
  obtain ⟨T, hTq, hTlen, hTlength, hc⟩ := exists_untwisted_subrectangle_of_fullSliceLaw_of_variation
    S hq hlen hp hS hP hM hMexp twist htwist hvariation signal
    (mul_pos (Real.exp_pos _) hδ) hsignal hscaled
  have hmean : ‖𝔼 t : (∀ k, Fin (T.length k)), signal (T.fullSlicePointInIntegerBox t)‖ =
      Real.exp (-pLocal) *
        ‖𝔼 t : (∀ k, Fin (T.length k)),
          V.eval (T.fullSlicePointInIntegerBox t).val * Wlocal.eval (T.fullSlicePointInIntegerBox t).val‖ := by
    simp only [signal, ← Finset.mul_expect, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
  rw [hmean] at hc
  have he : Real.exp pLocal * Real.exp (-pLocal) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hrestore := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg pLocal)
  have hlhs : Real.exp pLocal * (Real.exp (-pLocal) * δ / 2 -
      ε) =
      δ / 2 - Real.exp pLocal *
        ε := by
    rw [mul_sub, ← mul_div_assoc, ← mul_assoc, he, one_mul]
  have hcancel (x : ℝ) : Real.exp pLocal * (Real.exp (-pLocal) * x) = x := by
    rw [← mul_assoc, he, one_mul]
  rw [hlhs, hcancel] at hrestore
  refine ⟨T, hTq, hTlen, hTlength, ?_⟩
  rwa [T.fin_mean_eq_translated_zero (fun x => V.eval x * Wlocal.eval x)] at hrestore

end VectorPolynomial.NormalizedPolynomialTwist
end Erdos3

end

end OAI
