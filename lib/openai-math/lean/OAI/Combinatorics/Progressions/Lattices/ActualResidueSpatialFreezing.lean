import OAI.Combinatorics.Progressions.Geometry.NormalizedTwistSpatialPartition

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlated_residue_progression_box {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) (f : (I → ℕ) → ℂ) :
    ∃ start length : I → ℕ,
      (∀ i, 0 < length i) ∧
      (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
      (∀ i (j : Fin (length i)), start i + q * j.val < N i) ∧
      (∀ i (j : Fin (length i)), (start i + q * j.val) % q = start i % q) ∧
      (∀ i (j : Fin (length i)),
        |((start i + q * j.val : ℕ) : ℝ) / N i - (start i : ℝ) / N i| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ i (j k : Fin (length i)),
        |((start i + q * j.val : ℕ) : ℝ) / N i -
          ((start i + q * k.val : ℕ) : ℝ) / N i| ≤ Real.exp (-(2 * p)) / 4) ∧
      ‖𝔼 x : (∀ i, Fin (N i)), f (fun i => (x i).val)‖ ≤
        ‖𝔼 j : (∀ i, Fin (length i)), f (fun i => start i + q * (j i).val)‖ := by
  classical
  let H : I → ℕ := fun i => exponentialProgressionScale (N i) q p
  have hscale (i : I) := exponentialProgressionScale_bounds (N i) q p hp hq hqexp (hN i)
  let P : ∀ i, FiniteProgressionPartition (N i) := fun i =>
    FiniteProgressionPartition.comparableResidueProgressions (N i) q (H i) hq
      (hscale i).1 (hscale i).2.1
  have hstep (i : I) (a : (P i).Label) : (P i).step a = q :=
    FiniteProgressionPartition.comparableResidueProgressions_step _ _ _ _ _ _ _
  have hlength (i : I) (a : (P i).Label) :
      H i ≤ (P i).length a ∧ (P i).length a < 2 * H i :=
    FiniteProgressionPartition.comparableResidueProgressions_length_bounds _ _ _ _ _ _ _
  have hNpos (i : I) : 0 < N i := by
    have : (0 : ℝ) < N i := (Real.exp_pos _).trans_le (hN i)
    exact_mod_cast this
  obtain ⟨a, hpositive, hmean⟩ :=
    BoxProgressionPartition.exists_positive_box_norm_mean_le P hNpos f
  refine ⟨fun i => (P i).start (a i), fun i => (P i).length (a i), hpositive,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hscale i).2.2.1.trans (by exact_mod_cast (hlength i (a i)).1)
  · intro i j
    simpa only [hstep] using (P i).point_lt (a i) j.isLt
  · intro i j
    exact Nat.add_mul_mod_self_left _ _ _
  · intro i j
    simpa only [FiniteProgressionPartition.point_val, hstep] using
      (P i).normalized_point_sub_start_le_of_bound (a i) (hstep i (a i))
        (hlength i (a i)).2 (hNpos i) (hscale i).2.2.2 j
  · intro i j k
    simpa only [FiniteProgressionPartition.point_val, hstep] using
      (P i).normalized_point_sub_point_le_of_bound (a i) (hstep i (a i))
        (hlength i (a i)).2 (hNpos i) (hscale i).2.2.2 j k
  · simpa only [hstep] using hmean

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_correlated_integer_residue_box {I : Type*} [Fintype I]
    [DecidableEq I] (N : I → ℕ) (q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hq : 0 < q) (hqexp : (q : ℝ) ≤ Real.exp p)
    (hN : ∀ i, Real.exp (3 * p + 16) ≤ (N i : ℝ)) (f : (I → ℤ) → ℂ) :
    ∃ start length : I → ℕ,
      (∀ i, 0 < length i) ∧
      (∀ i, (N i : ℝ) * Real.exp (-(3 * p + 16)) ≤ length i) ∧
      (∀ i, (N i : ℝ) ≤ Real.exp (3 * p + 16) * q * length i) ∧
      (∀ v ∈ integerBox length,
        (fun i => (start i : ℤ) + (q : ℤ) * v i) ∈ integerBox N) ∧
      (∀ v ∈ integerBox length, ∀ i,
        ((start i : ℤ) + (q : ℤ) * v i) % q = (start i : ℤ) % q) ∧
      (∀ v ∈ integerBox length, ∀ i,
        |((start i : ℝ) + (q : ℝ) * v i) / N i - (start i : ℝ) / N i| ≤
          Real.exp (-(2 * p)) / 4) ∧
      (∀ v ∈ integerBox length, ∀ w ∈ integerBox length, ∀ i,
        |((start i : ℝ) + (q : ℝ) * v i) / N i -
          ((start i : ℝ) + (q : ℝ) * w i) / N i| ≤ Real.exp (-(2 * p)) / 4) ∧
      ‖𝔼 u ∈ integerBox N, f u‖ ≤
        ‖𝔼 v ∈ integerBox length, f (fun i => (start i : ℤ) + (q : ℤ) * v i)‖ := by
  obtain ⟨start, length, hpos, hlength, hinside, _, hdiam, hpair, hmean⟩ :=
    exists_correlated_residue_progression_box N q p hp hq hqexp hN
      (fun u => f (fun i => (u i : ℤ)))
  have hrepr (v : I → ℤ) (hv : v ∈ integerBox length) :
      ∃ j : ∀ i, Fin (length i), ∀ i, ((j i).val : ℤ) = v i := by
    have hb := (mem_integerBox length v).mp hv
    refine ⟨fun i => ⟨(v i).toNat, by have := hb i; omega⟩, ?_⟩
    exact fun i => Int.toNat_of_nonneg (hb i).1
  refine ⟨start, length, hpos, hlength, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hbase : (N i : ℝ) ≤ (length i : ℝ) * Real.exp (3 * p + 16) := by
      apply (div_le_iff₀ (Real.exp_pos _)).mp
      simpa only [Real.exp_neg, div_eq_mul_inv] using hlength i
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc
      (N i : ℝ) ≤ Real.exp (3 * p + 16) * length i := by simpa only [mul_comm] using hbase
      _ ≤ Real.exp (3 * p + 16) * q * length i := by
        gcongr
        exact le_mul_of_one_le_right (Real.exp_pos _).le hqone
  · intro v hv
    obtain ⟨j, hj⟩ := hrepr v hv
    rw [mem_integerBox]
    intro i
    rw [← hj i]
    constructor
    · positivity
    · exact_mod_cast hinside i (j i)
  · intro v _ i
    exact Int.add_mul_emod_self_left _ _ _
  · intro v hv i
    obtain ⟨j, hj⟩ := hrepr v hv
    have hjR : ((j i).val : ℝ) = v i := by exact_mod_cast hj i
    simpa only [Nat.cast_add, Nat.cast_mul, hjR] using hdiam i (j i)
  · intro v hv w hw i
    obtain ⟨j, hj⟩ := hrepr v hv
    obtain ⟨k, hk⟩ := hrepr w hw
    have hjR : ((j i).val : ℝ) = v i := by exact_mod_cast hj i
    have hkR : ((k i).val : ℝ) = w i := by exact_mod_cast hk i
    simpa only [Nat.cast_add, Nat.cast_mul, hjR, hkR] using hpair i (j i) (k i)
  · rw [integerBox_expect_eq_fin, integerBox_expect_eq_fin]
    simpa only [Nat.cast_add, Nat.cast_mul] using hmean

end Erdos3

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped NNReal BigOperators

variable {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*}
  [∀ j, Fintype (J j)] {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem eval_affine_sub_frozenTorus
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (r v : X → ℤ) (p : ℝ) (hL : (L : ℝ) ≤ Real.exp p)
    (hspatial : ∀ i,
      |((r i + W.modulus * v i : ℤ) : ℝ) / N i - (r i : ℝ) / N i| ≤
        Real.exp (-(2 * p)) / 4) :
    ‖W.eval N poly (fun i => r i + W.modulus * v i) -
      W.frozenTorus (fun i => (r i : ZMod W.modulus))
        (fun i => (r i : ℝ) / N i)
        (physicalGridFactorInput W.cover poly
          (fun i => ((r i + W.modulus * v i : ℤ) : ℝ)))‖ ≤
      Real.exp (-p) / 4 := by
  have hresidue : (fun i => ((r i + W.modulus * v i : ℤ) : ZMod W.modulus)) =
      (fun i => (r i : ZMod W.modulus)) := by
    funext i
    simp
  have hdist : dist
      (fun i => ((r i + W.modulus * v i : ℤ) : ℝ) / N i)
      (fun i => (r i : ℝ) / N i) ≤ Real.exp (-(2 * p)) / 4 :=
    (dist_pi_le_iff (by positivity)).mpr (fun i => by
      simpa only [Real.dist_eq] using hspatial i)
  have herr := W.eval_sub_frozenSpatialEval N (fun i => (r i : ℝ) / N i) poly
    (fun i => r i + W.modulus * v i)
  simp only [frozenSpatialEval, hresidue] at herr
  refine herr.trans ?_
  calc
    (L : ℝ) * dist _ _ ≤ Real.exp p * (Real.exp (-(2 * p)) / 4) :=
      mul_le_mul hL hdist dist_nonneg (Real.exp_nonneg _)
    _ = Real.exp (-p) / 4 := by rw [← mul_div_assoc, ← Real.exp_add]; congr 2; ring

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
