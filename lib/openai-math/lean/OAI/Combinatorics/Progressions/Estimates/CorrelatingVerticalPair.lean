import OAI.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

theorem exists_weighted_common_factor :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} {I J K : Type*}
      [Fintype σ] [Fintype I] [Fintype K] {s N : ℕ} [NeZero N] {p : ℝ},
      2 ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ (w : I → σ → ZMod N → ℝ) (v : I → J → (σ → ℤ) → ℂ)
        (u : K → (σ → ℤ) → ℂ),
        (∀ i a, PositiveCyclicNiltest.{0} s N p (w i a)) →
        (∀ x : σ → ZMod N, ∑ i, ∏ a, w i a (x a) = 1) →
        (∀ i j (x : σ → ZMod N), ‖v i j (fun a => ((x a).val : ℤ))‖ ≤ 1) →
        (∀ k (x : σ → ZMod N), ‖u k (fun a => ((x a).val : ℤ))‖ ≤ 1) →
        (∀ x : σ → ZMod N, ∑ k, ‖u k (fun a => ((x a).val : ℤ))‖ ^ 2 = 1) →
        (∀ i j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
          (fun x => v i j x * star (u k x)))) →
        ∃ F : J → K → (σ → ℤ) → ℂ,
          (∀ j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j k))) ∧
          (∀ j k (x : σ → ZMod N), F j k (fun a => ((x a).val : ℤ)) =
            (∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) *
              star (u k (fun a => ((x a).val : ℤ)))) ∧
          (∀ j k (x : σ → ZMod N), ‖F j k (fun a => ((x a).val : ℤ))‖ ≤ 1) ∧
          (∀ j (x : σ → ZMod N),
            ∑ k, F j k (fun a => ((x a).val : ℤ)) * u k (fun a => ((x a).val : ℤ)) =
            ∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  obtain ⟨B, _, hproduct⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 2) ^ 2 + 3
  let R := (Y + Polynomial.C B) ^ B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro σ I J K _ _ _ s N _ p hp hσ hI w v u hw htotal hv hu hunit hexp
  classical
  have hp0 : 0 ≤ p := by linarith
  have hy : 0 ≤ raisedNiltestBudget p := hp0.trans (le_raisedNiltestBudget p)
  let r := (raisedNiltestBudget p + B) ^ B + p + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; linarith [pow_nonneg (by positivity : 0 ≤ raisedNiltestBudget p + B) B]
  have hwr : productNiltestBudget (raisedNiltestBudget p) ≤ r :=
    (hproduct _ hy).trans (by dsimp [r]; linarith)
  have hcost : (r + A) ^ A + p ≤ (p + C) ^ C := by
    simpa [X, Y, R, r, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp0
  have hweights (i : I) := exists_positive_coordinate_product hp0 hσ (hw i)
  choose g hgExpansion hg using hweights
  have hproducts (i : I) (j : J) (k : K) :
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((r + A) ^ A)
        (fun x => g i x * (v i j x * star (u k x)))) :=
    hmul hr ((Classical.choice (hgExpansion i)).mono hwr)
      ((Classical.choice (hexp i j k)).mono hpr)
  let E (i : I) (j : J) (k : K) := Classical.choice (hproducts i j k)
  let F (j : J) (k : K) (x : σ → ℤ) := ∑ i, g i x * (v i j x * star (u k x))
  have hF (j : J) (k : K) :
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j k)) := by
    have hc : (∑ _ : I, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hI
    have H := (NativeIntegerExpansion.weightedSum (fun i => E i j k)
      (fun _ => (1 : ℂ)) hp0 hI hc).mono hcost
    exact ⟨by simpa only [one_mul] using H⟩
  have heq (j : J) (k : K) (x : σ → ZMod N) : F j k (fun a => ((x a).val : ℤ)) =
      (∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) * v i j (fun a => ((x a).val : ℤ))) *
        star (u k (fun a => ((x a).val : ℤ))) := by
    simp only [F, hg, Complex.ofReal_prod, Finset.sum_mul, mul_assoc]
  refine ⟨F, hF, heq, ?_, ?_⟩
  · intro j k x
    rw [heq, norm_mul, norm_star]
    have hsum : ‖∑ i, ((∏ a, w i a (x a) : ℝ) : ℂ) *
        v i j (fun a => ((x a).val : ℤ))‖ ≤ 1 :=
      norm_positive_partition_sum_le_one (fun i => ∏ a, w i a (x a))
        (fun i => v i j (fun a => ((x a).val : ℤ)))
        (fun i => Finset.prod_nonneg (fun a _ => ((hw i a).unit_interval (x a)).1))
        (htotal x) (fun i => hv i j x)
    exact (mul_le_of_le_one_left (norm_nonneg _) hsum).trans (hu k x)
  · intro j x
    simp_rw [heq]
    exact (complex_unit_vector_resolution (fun k => u k (fun a => ((x a).val : ℤ)))
      (hunit x) _).symm

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

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

structure NativePairPartition
    (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
      V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
      (fun _ : Fin 2 => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin 2 → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin 2 → I) → (Fin 2 → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence 1 b
    (R.pairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.pairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
        ∑ j, ((∏ l, weight (j l) (x l) : ℝ) : ℂ) * R.pairAnchoredVector
          (fun l => ((anchor j l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativePairPartition.finite

noncomputable def NativePairPartition.mono
    {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
      V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
      (fun _ : Fin 2 => (N : ℝ)) r} {a b ε δ : ℝ}
    (P : NativePairPartition R a ε) (hab : a ≤ b) (hεδ : ε ≤ δ) : NativePairPartition R b δ :=
  { P with
    card_bound := P.card_bound.trans (Real.exp_le_exp.mpr hab)
    positive := fun j => (P.positive j).mono le_rfl hab
    equivalence := fun j => (P.equivalence j).mono hab
    approximation := fun k out => (P.approximation k out).trans hεδ }

end Data

theorem exists_antisymmetric_pair_precise_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      R.HasPairLocalApproximation b → R.HasPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativePairPartition R ((t + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨A, _, hpartition⟩ := exists_antisymmetric_pair_local_partition 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [T, X, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
  have hcost : (u + A) ^ A ≤ (t + e + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + e + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨P, hP, hPb, n, hn, hcard, weight, hpositive, htotal, anchor, hequiv, herr⟩ :=
    hpartition R hlocal hred hu (hbt.trans (by dsimp [u]; linarith))
      (hct.trans (by dsimp [u]; linarith)) hρ hprec
  let : NeZero P := ⟨hP.ne'⟩
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  have herror : Real.exp (u + 40) * (ρ + 1 / N) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp (u + 40) * (2 * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
      _ = 2 * Real.exp (40 - u) := by
        dsimp [ρ]
        rw [← mul_assoc, mul_comm (Real.exp (u + 40)) 2, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * (Real.exp (-e) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply (Real.exp_le_exp.mpr (show 40 - u ≤ -e - 1 by dsimp [u]; linarith)).trans
        exact exp_sub_one_le_half_exp (-e)
      _ = _ := by ring
  exact ⟨{
    I := Fin n × ZMod P
    card_bound := hcard.trans (Real.exp_le_exp.mpr hcost)
    weight := weight
    positive := fun j => (hpositive j).mono le_rfl hcost
    total := htotal
    anchor := anchor
    equivalence := fun j => (hequiv j).mono hcost
    approximation := fun k out => (herr k out).trans herror }⟩

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

section Data

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  {R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r}

theorem NativePairPartition.exists_correlating_anchor {b ε η : ℝ}
    (P : NativePairPartition R b ε) (out : Fin W.outputDim) (f : ZMod N → ℂ)
    (H : Finset (ZMod N)) (hf : ∀ n, ‖f n‖ ≤ 1) (hη : 0 < η)
    (hmass : η ≤ 𝔼 h : ZMod N, if h ∈ H then
      ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (W.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ else 0)
    (hε : ε ≤ η / 2) :
    ∃ j : Fin 2 → P.I, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
      η / (4 * Real.exp b) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, η / (4 * Real.exp b) ≤
        ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
          star ((P.weight (j 1) n : ℂ) * R.pairAnchoredVector
            (fun k => ((P.anchor j k).val : ℤ)) 0 out ![(h.val : ℤ), (n.val : ℤ)])‖ := by
  classical
  let C := fun (j : Fin 2 → P.I) (h n : ZMod N) => R.pairAnchoredVector
    (fun k => ((P.anchor j k).val : ℤ)) 0 out ![(h.val : ℤ), (n.val : ℤ)]
  let v := fun (j : Fin 2 → P.I) (h n : ZMod N) =>
    (P.weight (j 0) h : ℂ) * ((P.weight (j 1) n : ℂ) * C j h n)
  have hw (i : P.I) (n : ZMod N) : ‖(P.weight i n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((P.positive i).unit_interval n).1]
    exact ((P.positive i).unit_interval n).2
  have hv (j : Fin 2 → P.I) (h n : ZMod N) : ‖v j h n‖ ≤ 1 := by
    dsimp [v]
    rw [norm_mul, norm_mul]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (hw _ _)).trans ((mul_le_of_le_one_left (norm_nonneg _) (hw _ _)).trans
        (R.pairAnchoredVector_norm _ _ _ _))
  have heval (h n : ZMod N) :
      (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have herr : (𝔼 h : ZMod N, 𝔼 n : ZMod N,
      ‖W.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)) - ∑ j, v j h n‖) ≤ η / 2 := by
    have h := (P.approximation 0 out).trans hε
    rw [expect_fin_two] at h
    have hrev : (0 : Fin 2).rev = 1 := by decide
    simpa only [Fin.prod_univ_two, heval, Complex.ofReal_mul, v, C, mul_assoc,
      hrev, Matrix.cons_val_zero, Matrix.cons_val_one] using h
  obtain ⟨j, S, hSH, hS, hsize, hcorr⟩ := exists_dense_row_partition_correlation H
    (multiplicativeDerivative f)
    (fun h n => W.eval out (correlationInput (h.val : ℤ) (n.val : ℤ))) v hη
    (Real.exp_pos b) P.card_bound (multiplicativeDerivative_norm_le_one f hf) hv hmass herr
  refine ⟨j, S, hSH, hS, by simpa only [ZMod.card] using hsize, ?_⟩
  intro h hh
  have hrow : (𝔼 n : ZMod N, multiplicativeDerivative f h n * star (v j h n)) =
      (P.weight (j 0) h : ℂ) *
        (𝔼 n : ZMod N, multiplicativeDerivative f h n * star ((P.weight (j 1) n : ℂ) * C j h n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    simp only [v, star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  apply (hcorr h hh).trans
  rw [hrow, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw _ _)

namespace NativePolynomialOrbitFactors

def HasCorrelatingAnchor (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r) (f : ZMod N → ℂ) (H : Finset (ZMod N))
    (out : Fin W.outputDim) (b : ℝ) : Prop :=
  ∃ y : Fin 2 → ZMod N, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
    Real.exp (-b) * N ≤ (S.card : ℝ) ∧ ∃ w : ZMod N → ℝ,
      PositiveCyclicNiltest.{0} 1 N b w ∧
      NativeIntegerVectorEquivalence 1 b
        (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 0)
        (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 1) ∧
      ∀ h ∈ S, Real.exp (-b) ≤
        ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
          star ((w n : ℂ) * R.pairAnchoredVector (fun k => ((y k).val : ℤ))
            0 out ![(h.val : ℤ), (n.val : ℤ)])‖

theorem hasCorrelatingAnchor_mono {f : ZMod N → ℂ} {H : Finset (ZMod N)}
    {out : Fin W.outputDim} {a b : ℝ} (h : R.HasCorrelatingAnchor f H out a) (hab : a ≤ b) :
    R.HasCorrelatingAnchor f H out b := by
  obtain ⟨y, S, hSH, hS, hsize, w, hw, hequiv, hcorr⟩ := h
  have he : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (neg_le_neg hab)
  exact ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg N)).trans hsize,
    w, hw.mono le_rfl hab, hequiv.mono hab, fun h hh => he.trans (hcorr h hh)⟩

end NativePolynomialOrbitFactors

end Data

theorem exists_antisymmetric_pair_correlating_anchor :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r),
      R.HasPairLocalApproximation b → R.HasPairFrozenReduction c →
      0 ≤ t → p ≤ t → b ≤ t → c ≤ t → Real.exp ((t + C) ^ C) ≤ (N : ℝ) →
      ∀ (f : ZMod N → ℂ) (H : Finset (ZMod N)) (out : Fin W.outputDim),
        (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) * N ≤ (H.card : ℝ) →
        (∀ h ∈ H, Real.exp (-p) ≤
          ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
            star (W.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)))‖) →
        R.HasCorrelatingAnchor f H out ((t + C) ^ C) := by
  obtain ⟨A, _, hpartition⟩ := exists_antisymmetric_pair_precise_partition
  let X : Polynomial ℕ := Polynomial.X
  let B := (3 * X + 1 + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (B + 2 * X + 4)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j V R hlocal hred ht hpt hbt hct hN f H out hf hsize hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let d := (3 * t + 1 + A) ^ A
  have htotal : d + 2 * t + 4 ≤ (t + C) ^ C := by
    simpa [B, X, d, Polynomial.eval₂_pow] using hbudget t ht
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hdC : d ≤ (t + C) ^ C := by linarith
  have heq : t + (2 * t + 1) + (A : ℝ) = 3 * t + 1 + A := by ring
  obtain ⟨P⟩ := hpartition R hlocal hred ht (by linarith : 0 ≤ 2 * t + 1) hbt hct
    (by simpa only [heq] using (Real.exp_le_exp.mpr hdC).trans hN)
  have hP : NativePairPartition R d (Real.exp (-(2 * t + 1))) := by
    simpa only [heq] using P
  let η := Real.exp (-(2 * p))
  have hmass : η ≤ 𝔼 h : ZMod N, if h ∈ H then
      ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (W.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ else 0 := by
    have hind : (𝔼 h : ZMod N, if h ∈ H then Real.exp (-p) else 0) =
        (H.card : ℝ) * Real.exp (-p) / N := by
      rw [Fintype.expect_eq_sum_div_card]
      simp only [ZMod.card]
      simp
    calc
      η = Real.exp (-p) * Real.exp (-p) := by dsimp [η]; rw [← Real.exp_add]; congr 1; ring
      _ ≤ (H.card : ℝ) * Real.exp (-p) / N := by
        apply (le_div_iff₀ (Nat.cast_pos.mpr (NeZero.pos N))).mpr
        nlinarith [mul_le_mul_of_nonneg_right hsize (Real.exp_nonneg (-p))]
      _ = _ := hind.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact le_rfl
  have herror : Real.exp (-(2 * t + 1)) ≤ η / 2 := by
    apply (Real.exp_le_exp.mpr (show -(2 * t + 1) ≤ -(2 * p) - 1 by linarith)).trans
    exact exp_sub_one_le_half_exp _
  obtain ⟨j, S, hSH, hS, hSsize, hScorr⟩ :=
    hP.exists_correlating_anchor out f H hf (Real.exp_pos _) hmass herror
  have hlower : Real.exp (-((t + C) ^ C)) ≤ η / (4 * Real.exp d) := by
    have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.exp d)).mpr
    calc
      _ ≤ Real.exp (-((t + C) ^ C)) * (Real.exp 4 * Real.exp d) := by gcongr
      _ = Real.exp (-((t + C) ^ C) + (4 + d)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ η := Real.exp_le_exp.mpr (by linarith)
  exact ⟨hP.anchor j, S, hSH, hS,
    (mul_le_mul_of_nonneg_right hlower (Nat.cast_nonneg N)).trans hSsize,
    hP.weight (j 1), (hP.positive (j 1)).mono le_rfl hdC, (hP.equivalence j).mono hdC,
    fun h hh => hlower.trans (hScorr h hh)⟩

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

theorem exists_common_anchor_approximation :
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
      (P : NativePairPartition R b ε) →
      ∀ (y : Fin 2 → ℤ), (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) → ∀ l : Fin 2,
      ∃ F : Fin 2 → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ k out a, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + r + u + b + C) ^ C) (F k out a))) ∧
        (∀ k out a (x : Fin 2 → ZMod N),
          ‖F k out a (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ k out (x : Fin 2 → ZMod N),
          ∑ a, F k out a (fun z => ((x z).val : ℤ)) *
            R.pairAnchoredVector y l a (fun z => ((x z).val : ℤ)) =
          ∑ cell, ((∏ z, P.weight (cell z) (x z) : ℝ) : ℂ) *
            R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k out
              (fun z => ((x z).val : ℤ))) ∧
        (∀ k out,
          (𝔼 x : Fin 2 → ZMod N,
            ‖W.eval out (correlationInput ((x k).val : ℤ) ((x k.rev).val : ℤ)) -
              ∑ a, F k out a (fun z => ((x z).val : ℤ)) *
                R.pairAnchoredVector y l a (fun z => ((x z).val : ℤ))‖) ≤ ε) := by
  obtain ⟨A, _, hanchor⟩ := exists_antisymmetric_anchor_equivalence
  obtain ⟨B, _, hcommon⟩ := exists_weighted_common_factor
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r u b ε W N _ i j V R hr hu hb houter P y hy l
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + u + b
  let t := v + (v + A) ^ A + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 2 ≤ t := by
    have ha : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t]
    linarith
  have hbt : b ≤ t := by
    have ha : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v]
    linarith
  have hat : (p + q + r + u + A) ^ A ≤ t := by
    calc
      _ ≤ (v + A) ^ A := by
        apply pow_le_pow_left₀ (by positivity)
        dsimp [v]
        linarith
      _ ≤ t := by dsimp [t]; linarith
  have hcost : (t + B) ^ B ≤ (p + q + r + u + b + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  let coords (cell : Fin 2 → P.I) (k : Fin 2 × Fin W.outputDim) :=
    R.pairAnchoredVector (fun z => ((P.anchor cell z).val : ℤ)) k.1 k.2
  have hbox (x : Fin 2 → ZMod N) (z : Fin 2) : |(((x z).val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x z).val))]
    exact Nat.cast_le.mpr (x z).val_lt.le
  have hcross (cell : Fin 2 → P.I) (k : Fin 2 × Fin W.outputDim) (a : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
        (fun x => coords cell k x * star (R.pairAnchoredVector y l a x))) :=
    ((hanchor R hr hu houter (fun z => ((P.anchor cell z).val : ℤ)) y
      (hbox (P.anchor cell)) hy k.1 l).mono hat).expansion k.2 a
  obtain ⟨F, hF, _, hnorm, hrepr⟩ := hcommon ht
    (by simpa using ht : (Fintype.card (Fin 2) : ℝ) ≤ t)
    (P.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell z => P.weight (cell z)) coords (R.pairAnchoredVector y l)
    (fun cell z => (P.positive (cell z)).mono le_rfl hbt)
    (sum_productPartitionWeight (fun (_ : Fin 2) a x => P.weight a x) (fun _ => P.total))
    (fun cell k x => R.pairAnchoredVector_norm _ _ _ _)
    (fun a x => R.pairAnchoredVector_norm _ _ _ _)
    (fun x => R.pairFrozenVector_unit l (R.slowValue y) (R.rationalValue y) _)
    hcross
  refine ⟨fun k out => F (k, out), ?_, ?_, ?_, ?_⟩
  · intro k out a
    exact ⟨(Classical.choice (hF (k, out) a)).mono hcost⟩
  · intro k out a x
    exact hnorm (k, out) a x
  · intro k out x
    exact hrepr (k, out) x
  · intro k out
    simpa only [hrepr] using P.approximation k out

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]

def HasVerticalCorrelatingAnchor (f : ZMod N → ℂ) (H : Finset (ZMod N))
    (out : Fin W.outputDim) (b : ℝ) : Prop :=
  ∃ y : Fin 2 → ZMod N, ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
    Real.exp (-b) * N ≤ (S.card : ℝ) ∧ ∃ w : ZMod N → ℝ,
      PositiveCyclicNiltest.{0} 1 N b w ∧
      ∃ M : R.FrozenMiddleRealization
          (R.slowValue (fun k => ((y k).val : ℤ)))
          (R.rationalValue (fun k => ((y k).val : ℤ))) b,
        ∃ U : Fin 2 → M.model.UnitVerticalObservable
            (M.model.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
            (Fin W.outputDim) b,
          (∀ k, (U k).frequency = R.pairMiddleFrequency) ∧
          (∀ k l x, (U k).observable l (QuotientGroup.mk
            (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M.orbit)) =
              R.pairAnchoredVector (fun k => ((y k).val : ℤ)) k l x) ∧
          NativeIntegerVectorEquivalence 1 b
            (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 0)
            (R.pairAnchoredVector (fun k => ((y k).val : ℤ)) 1) ∧
          ∀ h ∈ S, Real.exp (-b) ≤
            ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
              star ((w n : ℂ) * (U 0).observable out (QuotientGroup.mk
                (M.model.filtration.realification.polynomialOrbitEval (fun _ => 1)
                  ![(h.val : ℤ), (n.val : ℤ)] M.orbit)))‖

end NativePolynomialOrbitFactors

theorem exists_correlating_vertical_pair :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ]
        (pi V.antisymmetricPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      0 ≤ r → 0 ≤ b → R.HasPairFrozenReduction b →
      ∀ (f : ZMod N → ℂ) (H : Finset (ZMod N)) (out : Fin W.outputDim),
        R.HasCorrelatingAnchor f H out b →
        R.HasVerticalCorrelatingAnchor f H out ((p + q + r + b + C) ^ C) := by
  obtain ⟨A, _, hmodel⟩ := exists_antisymmetric_pair_middle_model
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let D := (X + Polynomial.C A) ^ A
  let P := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + D + (P + D + 4 + (X + D + 2) ^ 4))
  refine ⟨C, hC, ?_⟩
  intro p q r b W N _ i j V R _ _ _ _ _ _ _ _ hr hb hred f H out hanchor
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + b
  let B₀ := v + raisedNiltestBudget v + 4
  let d := (v + A) ^ A
  let z := productNiltestBudget B₀ + d + 4 + (v + d + 2) ^ 4
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hB : 0 ≤ B₀ := by dsimp [B₀, raisedNiltestBudget]; positivity
  have hz : 0 ≤ z := by
    dsimp [z]
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hsum : v + d + z ≤ (p + q + r + b + C) ^ C := by
    simpa [X, B, D, P, v, B₀, d, z, raisedNiltestBudget,
      productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have hbC : b ≤ (p + q + r + b + C) ^ C := by dsimp [v] at hsum; linarith
  have hdC : d ≤ (p + q + r + b + C) ^ C := by linarith
  have hzC : z ≤ (p + q + r + b + C) ^ C := by linarith
  obtain ⟨u, hu, hub, houter, _hfreeze⟩ := hred
  obtain ⟨y, S, hSH, hS, hdensity, w, hw, hequiv, hcorr⟩ := hanchor
  have hy : ∀ k : Fin 2, |(((y k).val : ℤ) : ℝ)| ≤ (N : ℝ) := by
    intro k
    change |((y k).val : ℝ)| ≤ (N : ℝ)
    rw [abs_of_nonneg (Nat.cast_nonneg ((y k).val))]
    exact Nat.cast_le.mpr (y k).val_lt.le
  obtain ⟨M, _hMc, _hMe⟩ := hmodel R hr hu houter (fun k => ((y k).val : ℤ)) hy
  let c := (p + q + r + u + A) ^ A
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcd : c ≤ d := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hpv : p ≤ v := by dsimp [v]; linarith
  have hpair : antisymmetricPairBudget p q ≤ B₀ := by
    dsimp [antisymmetricPairBudget, B₀, raisedNiltestBudget]
    gcongr
  have hpair0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprod : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget B₀ := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have hvcost : pairMiddleVerticalBudget p q c ≤ z := by
    dsimp [pairMiddleVerticalBudget, z]
    gcongr
  let M' := M.mono (hcd.trans hdC)
  let U : Fin 2 → M'.model.UnitVerticalObservable
      (M'.model.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
      (Fin W.outputDim) ((p + q + r + b + C) ^ C) :=
    fun k => (M.pairMiddleVertical hc k).mono (hvcost.trans hzC)
  have heval (k l x) : (U k).observable l (QuotientGroup.mk
      (M'.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x M'.orbit)) =
      R.pairAnchoredVector (fun k => ((y k).val : ℤ)) k l x :=
    M.pairMiddleVertical_eval hc k l x
  have hexp : Real.exp (-((p + q + r + b + C) ^ C)) ≤ Real.exp (-b) :=
    Real.exp_le_exp.mpr (neg_le_neg hbC)
  refine ⟨y, S, hSH, hS, (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg N)).trans hdensity,
    w, hw.mono le_rfl hbC, M', U, fun _ => rfl, heval, hequiv.mono hbC, ?_⟩
  intro h hh
  apply hexp.trans
  simpa only [heval] using hcorr h hh

end Erdos3

end

end OAI
