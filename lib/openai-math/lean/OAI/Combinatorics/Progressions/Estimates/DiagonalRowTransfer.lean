import OAI.Combinatorics.Progressions.Estimates.CorrelatingVerticalPair
import OAI.Combinatorics.Progressions.Estimates.OriginalDiagonalComparison
import OAI.Combinatorics.Progressions.Linear.AntisymmetricPairProjectionBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_common_factor_products :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K : Type*} [Fintype K] {w : σ → ℕ} {s : ℕ} {p : ℝ},
      0 ≤ p → (Fintype.card K : ℝ) ≤ Real.exp p →
      ∀ (F : J → K → (σ → ℤ) → ℂ) (U : K → (σ → ℤ) → ℂ),
        (∀ j k, Nonempty (NativeIntegerExpansion w s p (F j k))) →
        (∀ a b, Nonempty (NativeIntegerExpansion w s p
          (fun x => U a x * star (U b x)))) →
        ∀ i j, Nonempty (NativeIntegerExpansion w s ((p + C) ^ C)
          (fun x => (∑ a, F i a x * U a x) * star (∑ b, F j b x * U b x))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C A) ^ A + 2 * X)
  refine ⟨C, hC, ?_⟩
  intro σ J K _ w s p hp hK F U hF hU i j
  classical
  let r := p + (p + A) ^ A + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by
    have : 0 ≤ (p + A) ^ A := by positivity
    dsimp [r]
    linarith
  have har : (p + A) ^ A ≤ r := by dsimp [r]; linarith
  have hcost : (r + A) ^ A + 2 * p ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hterm (a b : K) : Nonempty (NativeIntegerExpansion w s ((r + A) ^ A)
      (fun x => (F i a x * star (F j b x)) * (U a x * star (U b x)))) := by
    obtain ⟨E⟩ := hmul hp (Classical.choice (hF i a)) (Classical.choice (hF j b)).conjugate
    exact hmul hr (E.mono har) ((Classical.choice (hU a b)).mono hpr)
  have hcount : (Fintype.card (K × K) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul, two_mul, Real.exp_add]
    exact mul_le_mul hK hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hcoeff : (∑ _ : K × K, ‖(1 : ℂ)‖) ≤ Real.exp (2 * p) := by simpa using hcount
  let E := (NativeIntegerExpansion.weightedSum
    (fun ab : K × K => Classical.choice (hterm ab.1 ab.2)) (fun _ => (1 : ℂ))
    (by positivity : 0 ≤ 2 * p) hcount hcoeff).mono hcost
  have heq : (fun x => ∑ ab : K × K,
      (1 : ℂ) * ((F i ab.1 x * star (F j ab.2 x)) * (U ab.1 x * star (U ab.2 x)))) =
      (fun x => (∑ a, F i a x * U a x) * star (∑ b, F j b x * U b x)) := by
    funext x
    simp only [one_mul, Fintype.sum_prod_type, star_sum, star_mul]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  exact ⟨heq ▸ E⟩

theorem norm_mul_star_sub_mul_star_le_of_le_one {a b c d : ℂ}
    (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    ‖a * star b - c * star d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  calc
    _ = ‖(a - c) * star b + c * star (b - d)‖ := by
      congr 1
      simp only [star_sub]
      ring
    _ ≤ ‖(a - c) * star b‖ + ‖c * star (b - d)‖ := norm_add_le _ _
    _ = ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by simp only [norm_mul, norm_star]
    _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) hb)
      (mul_le_of_le_one_left (norm_nonneg _) hc)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff
  NativePairPartition.finite

theorem NativePairPartition.partition_sum_norm {p q r b ε : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
    {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
    {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
      Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
      (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
    {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
      V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
      (fun _ : Fin 2 => (N : ℝ)) r}
    (P : NativePairPartition R b ε) (k : Fin 2) (out : Fin W.outputDim)
    (x : Fin 2 → ZMod N) :
    ‖∑ cell, ((∏ z, P.weight (cell z) (x z) : ℝ) : ℂ) *
      R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
        (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
  classical
  exact norm_positive_partition_sum_le_one
    (fun cell : Fin 2 → P.I => ∏ z, P.weight (cell z) (x z))
    (fun cell => R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
      (fun z => ((x z).val : ℤ)))
    (fun cell => Finset.prod_nonneg (fun z _ => ((P.positive (cell z)).unit_interval (x z)).1))
    (sum_productPartitionWeight (fun (_ : Fin 2) a x => P.weight a x) (fun _ => P.total) x)
    (fun cell => R.pairAnchoredVector_norm _ _ _ _)

theorem exists_global_pair_comparison :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u b ε : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ u → 0 ≤ b → R.HasOuterValueControl u →
      NativePairPartition R b ε →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ out₀ out₁, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + u + b + C) ^ C) (G out₀ out₁))) ∧
        (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a b, (𝔼 x : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
            G a b (fun z => ((x z).val : ℤ))‖) ≤ 2 * ε) := by
  obtain ⟨A, _, hcommon⟩ := exists_common_anchor_approximation
  obtain ⟨B, _, hanchor⟩ := exists_antisymmetric_anchor_equivalence
  obtain ⟨D, _, hproducts⟩ := exists_native_common_factor_products
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p q r u b ε W N _ i j V R hr hu hb houter P
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u + b
  let t := v + (v + A) ^ A + (v + B) ^ B + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : 0 ≤ (v + A) ^ A := by positivity
  have hB : 0 ≤ (v + B) ^ B := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hAt : (p + q + r + u + b + A) ^ A ≤ t := by change (v + A) ^ A ≤ t; dsimp [t]; linarith
  have hBt : (p + q + r + u + B) ^ B ≤ t := by
    calc
      _ ≤ (v + B) ^ B := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [v]
        linarith
      _ ≤ t := by dsimp [t]; linarith
  have hcost : (t + D) ^ D ≤ (p + q + r + u + b + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzero (k : Fin 2) : |((0 : Fin 2 → ℤ) k : ℝ)| ≤ (N : ℝ) := by simp
  obtain ⟨F, hF, _, hrepr, herr⟩ := hcommon R hr hu hb houter P 0 hzero 0
  let U := R.pairAnchoredVector 0 0
  let Q (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) := ∑ a, F k out a x * U a x
  let G (a b : Fin W.outputDim) (x : Fin 2 → ℤ) := Q 1 b x * star (Q 0 a x)
  have hU := (hanchor R hr hu houter 0 0 hzero hzero 0 0).mono hBt
  have hG (out₀ out₁ : Fin W.outputDim) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((p + q + r + u + b + C) ^ C) (G out₀ out₁)) := by
    obtain ⟨E⟩ := hproducts ht
      (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpt))
      (fun k : Fin 2 × Fin W.outputDim => F k.1 k.2) U
      (fun k a => ⟨(Classical.choice (hF k.1 k.2 a)).mono hAt⟩)
      hU.expansion (1, out₁) (0, out₀)
    exact ⟨E.mono hcost⟩
  have hQcap (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      ‖Q k out (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
    have heq := hrepr k out x
    change Q k out (fun z => ((x z).val : ℤ)) = _ at heq
    rw [heq]
    exact P.partition_sum_norm k out x
  refine ⟨G, hG, ?_, ?_⟩
  · intro a b x
    dsimp only [G]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hQcap 1 b x)).trans (hQcap 0 a x)
  · intro a b
    have hpoint (x : Fin 2 → ZMod N) :
        ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G a b (fun z => ((x z).val : ℤ))‖ ≤
        ‖W.eval b (correlationInput ((x 1).val : ℤ) ((x 0).val : ℤ)) -
          Q 1 b (fun z => ((x z).val : ℤ))‖ +
        ‖W.eval a (correlationInput ((x 0).val : ℤ) ((x 1).val : ℤ)) -
          Q 0 a (fun z => ((x z).val : ℤ))‖ := by
      dsimp only [NativeMultidegreeNilcharacter.antisymmetricKernel, G]
      rw [mul_comm (star _) (W.eval b _)]
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval a _) (hQcap 1 b x)
    have hmean := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
    rw [Finset.expect_add_distrib] at hmean
    have hfirst := herr 1 b
    have hsecond := herr 0 a
    change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval b (correlationInput ((x 1).val : ℤ) ((x 0).val : ℤ)) -
        Q 1 b (fun z => ((x z).val : ℤ))‖) ≤ ε at hfirst
    change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (correlationInput ((x 0).val : ℤ) ((x 1).val : ℤ)) -
        Q 0 a (fun z => ((x z).val : ℤ))‖) ≤ ε at hsecond
    linarith

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_precise_global_pair_comparison :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (_R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + e + C) ^ C) (G a b))) ∧
        (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a b, (𝔼 x : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
            G a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hlocal⟩ := exists_antisymmetric_pair_local_approximation
  obtain ⟨B, _, hfrozen⟩ := exists_antisymmetric_pair_frozen_reduction
  obtain ⟨D, _, hpartition⟩ := exists_antisymmetric_pair_precise_partition
  obtain ⟨E, _, hglobal⟩ := exists_global_pair_comparison
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C A) ^ A
  let K := (X + Polynomial.C B) ^ B
  let T := L + K + X + 2
  let Z := (T + (X + 1) + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Z + (X + K + Z + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + e
  let b := (v + A) ^ A
  let c := (v + B) ^ B
  let t := b + c + v + 2
  let z := (t + (e + 1) + D) ^ D
  let zmax := (t + (v + 1) + D) ^ D
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hev : e ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzmax : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hct : c ≤ t := by dsimp [t]; linarith
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (v + c + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    simpa [X, L, K, T, Z, b, c, t, zmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : zmax ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hGC : (v + c + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_left hzmax).trans hsum
  have hloc : R.HasPairLocalApproximation b :=
    R.hasPairLocalApproximation_mono (hlocal R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  have hred : R.HasPairFrozenReduction c :=
    R.hasPairFrozenReduction_mono (hfrozen R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  obtain ⟨P⟩ := hpartition R hloc hred ht (by linarith : 0 ≤ e + 1) hbt hct
    ((Real.exp_le_exp.mpr (hzz.trans hzC)).trans hN)
  obtain ⟨u, hu, huc, houter, _⟩ := hred
  obtain ⟨G, hG, hcap, herr⟩ := hglobal R hr hu hz houter P
  have hcost : (p + q + r + u + z + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    apply le_trans _ hGC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  refine ⟨G, ?_, hcap, ?_⟩
  · intro a b
    exact ⟨(Classical.choice (hG a b)).mono hcost⟩
  · intro a b
    apply (herr a b).trans
    have hh := exp_sub_one_le_half_exp (-e)
    have hid : -(e + 1) = -e - 1 := by ring
    rw [hid]
    linarith

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quadratic_pair_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  Nonempty (NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
                    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
                    (fun _ : Fin 2 => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨A, _, hdrop⟩ := exists_quadratic_pair_step_drop
  obtain ⟨B, _, horbit⟩ := exists_antisymmetric_pair_orbit_factors
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (3 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (3 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, r, hq, hqt, hr, hrt, H, hH, hdense, M, i, hderiv, i', j', V, ⟨F⟩⟩ :=
    hdrop hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  have hbound : (q + r + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + r + t + B ≤ 3 * t + B
    linarith
  obtain ⟨R⟩ := horbit F ht ((Real.exp_le_exp.mpr hbound).trans hN)
  exact ⟨q, r, hq, hqt.trans htC, hr, hrt.trans htC, H, hH, hdense, M, i, hderiv, i', j', V,
    ⟨R.mono hbound (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_global_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ G : Fin M.outputDim → Fin M.outputDim → (Fin 2 → ℤ) → ℂ,
                (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (G a b))) ∧
                (∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
                (∀ a b, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
                    G a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hpair⟩ := exists_quadratic_pair_orbit_factors
  obtain ⟨B, _, hcomparison⟩ := exists_precise_global_pair_comparison
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let t := (p + e + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbase : (p + A) ^ A ≤ t := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hsum : t + (3 * t + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
  have htC : t ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (3 * t + (p + e) + B) ^ B ≤ (p + e + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hbaseC : (p + A) ^ A ≤ (p + C) ^ C := by
    have hh : (p + A) ^ A + (3 * (p + A) ^ A + p + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, T, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right (by positivity)).trans hh
  obtain ⟨q, r, hq, hqt, hr, hrt, H, hH, hdense, M, i, hderiv, i', j', V, ⟨R⟩⟩ :=
    hpair hp ((Real.exp_le_exp.mpr (hbase.trans htC)).trans hN) f hf hGowers
  have hcost : (q + r + (p + A) ^ A + e + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    have hq' := hqt.trans hbase
    have hr' := hrt.trans hbase
    linarith
  obtain ⟨G, hG, hcap, herr⟩ := hcomparison R
    (by positivity : 0 ≤ (p + A) ^ A) he ((Real.exp_le_exp.mpr hcost).trans hN)
  refine ⟨q, hq, hqt.trans hbaseC, H, hH, hdense, M, i, hderiv, G, ?_, hcap, herr⟩
  intro a b
  exact ⟨(Classical.choice (hG a b)).mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quadratic_pair_projected_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r u : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  ∃ R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
                    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
                    (fun _ : Fin 2 => (N : ℝ)) u,
                    R.HasPairProjectionControl ((p + C) ^ C) := by
  obtain ⟨A, _, horbit⟩ := exists_quadratic_pair_orbit_factors
  obtain ⟨B, _, hcontrol⟩ := exists_antisymmetric_pair_projection_control
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (3 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (3 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, r, hq, hqt, hr, hrt, H, hH, hdense, M, i, hderiv, i', j', V, ⟨R⟩⟩ :=
    horbit hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  have hbound : (q + r + t + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + r + t + B ≤ 3 * t + B
    linarith
  have hproj : R.HasPairProjectionControl ((q + r + t + B) ^ B) := hcontrol R ht
  exact ⟨q, r, t, hq, hqt.trans htC, hr, hrt.trans htC, ht, htC, H, hH, hdense,
    M, i, hderiv, i', j', V, R, R.hasPairProjectionControl_mono hproj hbound⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_approximate_integration :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ F : (Fin M.outputDim × Fin M.outputDim) →
                  (Fin M.outputDim × Fin M.outputDim × Fin M.outputDim) → (Fin 2 → ℤ) → ℂ,
                (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (F a b))) ∧
                (∀ a b (x : Fin 2 → ZMod N), ‖F a b (fun z => ((x z).val : ℤ))‖ ≤ M.outputDim) ∧
                (∀ a b, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
                      star (M.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
                    F a b (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hglobal⟩ := exists_quadratic_global_exchange
  obtain ⟨B, _, hcompare⟩ := NativeMultidegreeNilcharacter.exists_quadratic_diagonal_square_comparison
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + U + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + T + (U + T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let u := (p + A) ^ A
  let v := p + e
  let umax := (v + A) ^ A
  let t := (p + (e + u) + A) ^ A
  let tmax := (v + umax + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsum : umax + tmax + (umax + tmax + B) ^ B ≤ (p + e + C) ^ C := by
    simpa [X, U, T, umax, tmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have htC : tmax ≤ (p + e + C) ^ C := by
    have : 0 ≤ (umax + tmax + B) ^ B := by positivity
    linarith
  have hcompareC : (umax + tmax + B) ^ B ≤ (p + e + C) ^ C := by linarith
  have hqu : u ≤ (p + C) ^ C := by
    have hh : u + (p + u + A) ^ A + (u + (p + u + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, U, T, u, Polynomial.eval₂_pow] using hbudget p hp
    have h₁ : 0 ≤ (p + u + A) ^ A := by positivity
    have h₂ : 0 ≤ (u + (p + u + A) ^ A + B) ^ B := by positivity
    linarith
  have hu_le : u ≤ umax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have ht_le : t ≤ tmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨q, hq, hqb, H, hH, hdense, M, i, hderiv, G, hG, hcap, herr⟩ :=
    hglobal hp (add_nonneg he hu) ((Real.exp_le_exp.mpr (ht_le.trans htC)).trans hN) f hf hGowers
  obtain ⟨F, hF, hnorm, herror⟩ := hcompare M G ht hG hcap herr
  have hcost : (q + t + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hcompareC
    apply pow_le_pow_left₀ (by positivity)
    change q + t + B ≤ umax + tmax + B
    have hqmax := hqb.trans hu_le
    linarith
  have herrorC : (M.outputDim : ℝ) * Real.exp (-(e + u)) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp q * Real.exp (-(e + u)) :=
        mul_le_mul_of_nonneg_right M.output_bound (Real.exp_nonneg _)
      _ = Real.exp (q - (e + u)) := by rw [← Real.exp_add]; rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by change q ≤ u at hqb; linarith)
  refine ⟨q, hq, hqb.trans hqu, H, hH, hdense, M, i, hderiv, F, ?_, hnorm, ?_⟩
  · intro a b
    exact ⟨(Classical.choice (hF a b)).mono hcost⟩
  · intro a b
    exact (herror a b).trans herrorC

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem quadratic_original_error_bound {d u e N : ℝ} (hd : 0 ≤ d) (hu : 0 ≤ u)
    (hdu : d ≤ Real.exp u) (hN : Real.exp (e + 4 * u + 40) ≤ N) :
    d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40))))) +
        12 * Real.exp (-(e + 4 * u + 40)) + 2 / N) ≤ Real.exp (-e) := by
  have hp (n : ℕ) : d ^ n ≤ Real.exp ((n : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hd hdu n
  have h2 : d ^ 2 + 1 ≤ 2 * Real.exp (2 * u) := by
    have hh := hp 2
    norm_num only [Nat.cast_ofNat] at hh
    linarith [Real.one_le_exp (show 0 ≤ 2 * u by positivity)]
  have hplus : (d ^ 2 + 1) ^ 2 ≤ 4 * Real.exp (4 * u) := by
    calc
      _ ≤ (2 * Real.exp (2 * u)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = 4 * Real.exp (4 * u) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
        ring_nf
  have hcoef : 4 * d ^ 8 * (d ^ 2 + 1) ^ 2 ≤ 16 * Real.exp (12 * u) := by
    calc
      _ ≤ 4 * Real.exp (8 * u) * (4 * Real.exp (4 * u)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_ofNat] using hp 8)
          (by norm_num)) hplus (by positivity) (by positivity)
      _ = _ := by rw [show 4 * Real.exp (8 * u) * (4 * Real.exp (4 * u)) =
        16 * (Real.exp (8 * u) * Real.exp (4 * u)) by ring, ← Real.exp_add]; congr 2; ring
  have hfirst : d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40)))))) ≤ 16 * Real.exp (-(e + 40)) := by
    calc
      _ = (4 * d ^ 8 * (d ^ 2 + 1) ^ 2) * Real.exp (-(e + 12 * u + 40)) := by ring
      _ ≤ (16 * Real.exp (12 * u)) * Real.exp (-(e + 12 * u + 40)) :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hfour : d ^ 4 ≤ Real.exp (4 * u) := by simpa only [Nat.cast_ofNat] using hp 4
  have hscaled : d ^ 4 * Real.exp (-(e + 4 * u + 40)) ≤ Real.exp (-(e + 40)) := by
    calc
      _ ≤ Real.exp (4 * u) * Real.exp (-(e + 4 * u + 40)) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hrecip : 1 / N ≤ Real.exp (-(e + 4 * u + 40)) := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos _) hN
    simpa only [one_div, ← Real.exp_neg] using hh
  have hthird : d ^ 4 * (2 / N) ≤ 2 * Real.exp (-(e + 40)) := by
    have hh := (mul_le_mul_of_nonneg_left hrecip (pow_nonneg hd 4)).trans hscaled
    calc
      _ = 2 * (d ^ 4 * (1 / N)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)
  have hsum : d ^ 4 * ((d ^ 2 + 1) * (d ^ 2 * ((1 + d ^ 2) *
      (4 * d ^ 2 * Real.exp (-(e + 12 * u + 40))))) +
        12 * Real.exp (-(e + 4 * u + 40)) + 2 / N) ≤ 30 * Real.exp (-(e + 40)) := by
    nlinarith
  apply hsum.trans
  calc
    _ ≤ Real.exp 40 * Real.exp (-(e + 40)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (40 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_quadratic_original_integration :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ K : (Fin M.quadraticRoot.outputDim × Fin M.quadraticRoot.outputDim) →
                  Fin M.outputDim → Fin M.quadraticRoot.outputDim → (Fin 2 → ℤ) → ℂ,
                (∀ a j c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                  ((p + e + C) ^ C) (K a j c))) ∧
                (∀ a j c, (𝔼 x : Fin 2 → ZMod N,
                  ‖M.quadraticRoot.cyclicDiagonalDerivative a x *
                      (M.eval j (fun k => ((x k).val : ℤ)) *
                        M.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
                    K a j c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hglobal⟩ := exists_quadratic_global_exchange
  obtain ⟨B, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_rootCyclicCorrection_expansion
  obtain ⟨D, _, horiginal⟩ := NativeMultidegreeNilcharacter.exists_originalDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + 12 * U + 40 + Polynomial.C A) ^ A
  let S := (U + T + X + 4 * U + 40 + Polynomial.C B) ^ B
  let R := (U + S + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + 4 * U + 40 + S + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + A) ^ A
  let umax := (v + A) ^ A
  let t := (p + (e + 12 * u + 40) + A) ^ A
  let tmax := (v + 12 * umax + 40 + A) ^ A
  let b := e + 4 * u + 40
  let smax := (umax + tmax + v + 4 * umax + 40 + B) ^ B
  let rmax := (umax + smax + D) ^ D
  let δ : ℝ≥0 := ⟨Real.exp (-b), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-b) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hrmax : 0 ≤ rmax := by dsimp [rmax]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp b := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + 4 * umax + 40 + smax + rmax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, R, umax, tmax, smax, rmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have hrC : rmax ≤ (p + e + C) ^ C := by linarith
  have hbC : b ≤ (p + e + C) ^ C := by dsimp [b, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 +
        (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B +
        (u + (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B + D) ^ D ≤ (p + C) ^ C := by
      simpa [X, U, T, S, R, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + 12 * u + 40 + A) ^ A := by positivity
    have h2 : 0 ≤ (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B := by positivity
    have h3 : 0 ≤ (u + (u + (p + 12 * u + 40 + A) ^ A + p + 4 * u + 40 + B) ^ B + D) ^ D := by positivity
    linarith
  obtain ⟨q, hq, hqu, H, hH, hdense, M, i, hderiv, G, hG, hcap, herr⟩ :=
    hglobal hp (by positivity : 0 ≤ e + 12 * u + 40)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax := hqu.trans hum
  have hs : (q + t + b + B) ^ B ≤ smax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [b, v]
    linarith
  have hF (a c) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 smax
      (M.rootCyclicCorrection N δ G a c)) :=
    ⟨(Classical.choice (hroot M N δ hδ ht hb hinv G hG a c)).mono hs⟩
  have hfinal : (q + smax + D) ^ D ≤ (p + e + C) ^ C := by
    apply le_trans _ hrC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have herror := quadratic_original_error_bound (Nat.cast_nonneg M.outputDim) hu
    (M.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  have hrootError := M.rootCyclicCorrection_mean_error δ hδ G hcap herr
  refine ⟨q, hq, hqu.trans huC, H, hH, hdense, M, i, hderiv,
    M.originalDiagonalCorrection (M.rootCyclicCorrection N δ G), ?_, ?_⟩
  · intro a j c
    exact ⟨(Classical.choice (horiginal M hsmax (M.rootCyclicCorrection N δ G) hF a j c)).mono hfinal⟩
  · intro a j c
    apply (M.originalDiagonalCorrection_mean_error (M.rootCyclicCorrection N δ G) hrootError a j c).trans
    have hdim : M.quadraticRoot.outputDim = M.outputDim ^ 2 := rfl
    simp only [hdim, Nat.cast_pow, hδval]
    dsimp [b] at *
    simpa only [← pow_mul, Nat.reduceMul] using herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem unit_row_correlation_bound {H X I J : Type*}
    [Fintype H] [Fintype X] [Fintype I] [Fintype J]
    (f q : H → X → ℂ) (u : I → H → X → ℂ) (v : J → H → ℂ)
    (K : I → J → H → X → ℂ)
    (hf : ∀ h x, ‖f h x‖ ≤ 1)
    (hu : ∀ h x, ∑ i, ‖u i h x‖ ^ 2 = 1) (hv : ∀ h, ∑ j, ‖v j h‖ ^ 2 = 1)
    (huc : ∀ i h x, ‖u i h x‖ ≤ 1) (hvc : ∀ j h, ‖v j h‖ ≤ 1)
    {ε : ℝ} (herr : ∀ i j, (𝔼 h, 𝔼 x, ‖q h x * (u i h x * v j h) - K i j h x‖) ≤ ε) :
    (𝔼 h, ‖𝔼 x, f h x * star (q h x)‖) ≤
      (∑ ij : I × J, 𝔼 h, ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖) +
        Fintype.card (I × J) * ε := by
  let z (ij : I × J) (h : H) (x : X) := u ij.1 h x * v ij.2 h
  have hz (h : H) (x : X) : ∑ ij : I × J, ‖z ij h x‖ ^ 2 = 1 := by
    simp only [z, Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, hv, mul_one, hu]
  have hzc (ij : I × J) (h : H) (x : X) : ‖z ij h x‖ ≤ 1 := by
    dsimp only [z]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (huc _ _ _)).trans (hvc _ _)
  let t (ij : I × J) (h : H) (x : X) := star (z ij h x) * K ij.1 ij.2 h x
  have he (h : H) (x : X) : ‖q h x - ∑ ij, t ij h x‖ ≤
      ∑ ij : I × J, ‖q h x * z ij h x - K ij.1 ij.2 h x‖ := by
    have hh := norm_unit_vector_exchange_error (fun ij => star (z ij h x))
      (by simpa only [norm_star] using hz h x)
      (fun ij => by simpa only [norm_star] using hzc ij h x)
      (q h x) (fun ij => star (K ij.1 ij.2 h x))
    simpa only [t, star_star, ← star_mul, ← star_sub, norm_star, mul_comm] using hh
  have hterm (ij : I × J) (h : H) :
      ‖𝔼 x, f h x * star (t ij h x)‖ ≤ ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖ := by
    have heq : (𝔼 x, f h x * star (t ij h x)) =
        v ij.2 h * (𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [t, z, star_mul, star_star]
      ring
    rw [heq, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hvc _ _)
  have hp (h : H) : ‖𝔼 x, f h x * star (q h x)‖ ≤
      (∑ ij : I × J, ‖𝔼 x, f h x * u ij.1 h x * star (K ij.1 ij.2 h x)‖) +
        (𝔼 x, ∑ ij : I × J, ‖q h x * z ij h x - K ij.1 ij.2 h x‖) := by
    apply (norm_correlation_partition_bound (f h) (q h) (fun ij => t ij h) (hf h)).trans
    exact add_le_add (Finset.sum_le_sum (fun ij _ => hterm ij h))
      (Finset.expect_le_expect (fun x _ => he h x))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hp h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm] at hm
  apply hm.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _ij : I × J, ε := Finset.sum_le_sum (fun ij _ => herr ij.1 ij.2)
    _ = _ := by simp

namespace NativeMultidegreeNilcharacter

theorem cyclicDiagonalDerivative_unit {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.cyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [cyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem cyclicDiagonalDerivative_norm {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [cyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem original_diagonal_row_correlation_bound {p ε : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (i : Fin W.outputDim)
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (K : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) →
      Fin W.quadraticRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
        (W.eval i (fun k => ((x k).val : ℤ)) * W.quadraticRoot.eval c (fun _ => ((x 0).val : ℤ))) -
        K a c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (W.evalCyclic N i (correlationInput h n))‖) ≤
      (∑ ac : (Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) × Fin W.quadraticRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
          W.quadraticRoot.cyclicDiagonalDerivative ac.1 ![h, n] *
            star (K ac.1 ac.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
        (W.quadraticRoot.outputDim : ℝ) ^ 3 * ε := by
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : W.evalCyclic N i (correlationInput h n) = W.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hh := unit_row_correlation_bound (multiplicativeDerivative f)
    (fun h n => W.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun a h n => W.quadraticRoot.cyclicDiagonalDerivative a ![h, n])
    (fun c h => W.quadraticRoot.eval c (fun _ => (h.val : ℤ)))
    (fun a c h n => K a c ![(h.val : ℤ), (n.val : ℤ)])
    (fun h => multiplicativeDerivative_norm_le_one f hf h)
    (fun h n => W.quadraticRoot.cyclicDiagonalDerivative_unit ![h, n])
    (fun h => W.quadraticRoot.unit_eval _) (fun a h n => W.quadraticRoot.cyclicDiagonalDerivative_norm a ![h, n])
    (fun c h => W.quadraticRoot.norm_eval _ _) (ε := ε) (by
      intro a c
      have he := herr a c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hc : (Fintype.card ((Fin W.quadraticRoot.outputDim × Fin W.quadraticRoot.outputDim) × Fin W.quadraticRoot.outputDim) : ℝ) =
      (W.quadraticRoot.outputDim : ℝ) ^ 3 := by simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]; ring
  simpa only [heval, hc] using hh

end NativeMultidegreeNilcharacter
end Erdos3

end

end OAI
