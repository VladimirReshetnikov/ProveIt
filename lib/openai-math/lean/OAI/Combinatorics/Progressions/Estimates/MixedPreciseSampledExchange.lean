import OAI.Combinatorics.Progressions.Linear.MixedPairPartitionKernel

namespace OAI

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

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}

structure NativeMixedPointwisePartition
    (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r) (b δ β : ℝ) where
  partition : NativeMixedPairPartition R b (δ + 2 * ((n + 2 : ℕ) : ℝ) * β)
  error_nonneg : 0 ≤ δ
  density_nonneg : 0 ≤ β
  bad : Finset (ZMod N)
  bad_density : (bad.card : ℝ) / N ≤ β
  pointwise : ∀ a x, (∀ l, x l ∉ bad) → 0 < partition.cellWeight a x →
    ∀ (k : Fin 2) (out : Fin W.outputDim),
      ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - partition.cellVector a k out x‖ ≤ δ

namespace NativeMixedPointwisePartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b δ β : ℝ} (P : NativeMixedPointwisePartition R b δ β)

noncomputable def mono {b' δ' β' : ℝ} (hb : b ≤ b') (hδ : δ ≤ δ') (hβ : β ≤ β') :
    NativeMixedPointwisePartition R b' δ' β' where
  partition := P.partition.mono hb (add_le_add hδ
    (mul_le_mul_of_nonneg_left hβ (by positivity)))
  error_nonneg := P.error_nonneg.trans hδ
  density_nonneg := P.density_nonneg.trans hβ
  bad := P.bad
  bad_density := P.bad_density.trans hβ
  pointwise := fun a x hx hax k out => (P.pointwise a x hx hax k out).trans hδ

theorem sampled_error {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin (n + 2) → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ∑ a, P.partition.cellWeight a (sample x) *
      ‖W.eval out (mixedSlotInput ((sample x (![0, 1] k)).val : ℤ) ((sample x (![1, 0] k)).val : ℤ) (fun l => ((sample x l.succ.succ).val : ℤ))) - P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  exact weighted_partition_mean_error E
    (fun a x => P.partition.cellWeight a (sample x))
    (fun a x => P.partition.cellVector a k out (sample x)) _ P.error_nonneg
    (fun a x => P.partition.cellWeight_nonneg a (sample x))
    (fun x => P.partition.cellWeight_total (sample x))
    (fun a x => P.partition.cellVector_norm a k out (sample x))
    (fun x => W.norm_eval out _) (fun a x hx hax => P.pointwise a (sample x) (hE x hx) hax k out)

theorem sampled_approximation {X : Type*} [Fintype X] [Nonempty X]
    (sample : X → Fin (n + 2) → ZMod N) (E : Finset X)
    (hE : ∀ x, x ∉ E → ∀ l, sample x l ∉ P.bad) (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x, ‖W.eval out (mixedSlotInput ((sample x (![0, 1] k)).val : ℤ) ((sample x (![1, 0] k)).val : ℤ) (fun l => ((sample x l.succ.succ).val : ℤ))) -
      ∑ a, (P.partition.cellWeight a (sample x) : ℂ) * P.partition.cellVector a k out (sample x)‖) ≤
      δ + 2 * (E.card : ℝ) / Fintype.card X := by
  apply le_trans _ (P.sampled_error sample E hE k out)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (sample x))
    (fun a => P.partition.cellVector a k out (sample x)) _
    (fun a => P.partition.cellWeight_nonneg a (sample x)) (P.partition.cellWeight_total (sample x)))

end NativeMixedPointwisePartition
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

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem select_mixed_pointwise_partition {b c : ℝ}
    (hlocal : R.HasMixedPairLocalApproximation b) (hred : R.HasMixedPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin (n + 2) → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin (n + 2) → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence (n + 1) c
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ a x, (∀ l, x l ∉ B) → 0 < A a x →
            ∀ (k : Fin 2) (out : Fin W.outputDim),
              ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) -
                R.mixedPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
                  (fun l => ((x l).val : ℤ))‖ ≤ Real.exp b * ρ := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) => ((x i).val : ℤ)
  have hv (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin (n + 2) → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.mixedPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro a x hx hax k out
  obtain ⟨hy', hAy⟩ := hy a x hx hax
  obtain ⟨hres, hnear⟩ := hcells a x (y a) hx hy' hax hAy
  exact hmodel (v (y a)) (hv (y a)) k out (v x) ρ hρ (hv x) hres
    (by simpa only [v, Int.cast_natCast] using hnear)

end NativePolynomialOrbitFactors

theorem exists_mixed_pointwise_partition (n a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      Nonempty (NativeMixedPointwisePartition R ((t + C) ^ C)
        (Real.exp t * ρ) (6 * ρ + 3 / N)) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 60 + Polynomial.C (n + 2) * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t m W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_mixed_pointwise_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨cells, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 60 + ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have hdim : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hmul : 0 ≤ ((n + 2 : ℕ) : ℝ) * (t + B) ^ B := mul_nonneg (by linarith) hpow
  have htC : t ≤ (t + C) ^ C := by linarith
  have hdimCost : ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C :=
    (le_mul_of_one_le_left hpow hdim).trans hdimCost
  let w := productPartitionWeight (fun _ : Fin (n + 2) => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin (n + 2) => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, hpoint⟩ := hselect E w hρ.le hw hwSum hcells
  let δ := Real.exp t * ρ
  let β := 6 * ρ + 3 / (N : ℝ)
  have hδ : 0 ≤ δ := mul_nonneg (Real.exp_nonneg _) hρ.le
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hbad : (E.card : ℝ) / N ≤ β := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
  have hcard' : (Fintype.card (Fin (n + 2) → Fin cells × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ (n + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard (n + 2)
      _ = Real.exp (((n + 2 : ℕ) : ℝ) * (t + B) ^ B) := (Real.exp_nat_mul _ (n + 2)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimCost
  have hpoint' (a) (x) (hx : ∀ l, x l ∉ E) (hax : 0 < w a x) (k : Fin 2) (out : Fin W.outputDim) :
      ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - R.mixedPairAnchoredVector
        (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖ ≤ δ :=
    (hpoint a x hx hax k out).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbt) hρ.le)
  have herr (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin (n + 2) → ZMod N, ∑ a, w a x *
        ‖W.eval out (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ) (fun l => ((x l.succ.succ).val : ℤ))) - R.mixedPairAnchoredVector
          (fun l => ((y a l).val : ℤ)) k out (fun l => ((x l).val : ℤ))‖) ≤ δ + 2 * ((n + 2 : ℕ) : ℝ) * β := by
    have h := weighted_partition_mean_error (coordinateExceptional E) w
      (fun a x => R.mixedPairAnchoredVector (fun l => ((y a l).val : ℤ)) k out
        (fun l => ((x l).val : ℤ))) _ hδ hw hwSum
      (fun a x => R.mixedPairAnchoredVector_norm _ _ _ _)
      (fun x => W.norm_eval out _) (fun a x hx hax =>
        hpoint' a x ((not_mem_coordinateExceptional E x).mp hx) hax k out)
    have hd : ((coordinateExceptional (ι := Fin (n + 2)) E).card : ℝ) / Fintype.card (Fin (n + 2) → ZMod N) ≤
        ((n + 2 : ℕ) : ℝ) * ((E.card : ℝ) / N) := by
      simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] using
        coordinateExceptional_density_le (ι := Fin (n + 2)) E
    have hbad' : ((n + 2 : ℕ) : ℝ) * ((E.card : ℝ) / N) ≤ ((n + 2 : ℕ) : ℝ) * β :=
      mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg _)
    have hsmall := hd.trans hbad'
    rw [mul_div_assoc] at h
    linarith
  let core : NativeMixedPairPartition R ((t + C) ^ C) (δ + 2 * ((n + 2 : ℕ) : ℝ) * β) := {
    I := Fin cells × ZMod P
    card_bound := hcard'
    weight := A
    positive := fun j => (hA j).mono le_rfl hcost
    total := hsum
    anchor := y
    equivalence := fun j => (hequiv j).mono (hct.trans htC)
    weighted_approximation := herr }
  exact ⟨{
    partition := core
    error_nonneg := hδ
    density_nonneg := hβ
    bad := E
    bad_density := hbad
    pointwise := hpoint' }⟩

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

def mixedDiagonalSample {n : ℕ} {X : Type*} (x : Fin 2 → X) : Fin (n + 2) → X :=
  Fin.cases (x 0) (fun _ => x 1)

theorem mixedDiagonalSample_avoids {n : ℕ} {X : Type*} (B : Set X) (x : Fin 2 → X)
    (hx : ∀ k, x k ∉ B) : ∀ l, mixedDiagonalSample (n := n) x l ∉ B := by
  intro l
  refine Fin.cases ?_ ?_ l
  · exact hx 0
  · intro _
    exact hx 1

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}

namespace NativeMixedPointwisePartition

attribute [local instance] NativeMixedPairPartition.finite

variable {b δ β : ℝ} (P : NativeMixedPointwisePartition R b δ β)

theorem weighted_diagonal_error (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (mixedDiagonalSample (n := n) x) *
      ‖W.eval out (mixedSlotInput ((x 0).val : ℤ) ((x 1).val : ℤ) (fun _ => ((x 1).val : ℤ))) -
        P.partition.cellVector a 0 out (mixedDiagonalSample (n := n) x)‖) ≤ δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error (mixedDiagonalSample (n := n)) E (fun x hx =>
    mixedDiagonalSample_avoids (n := n) (P.bad : Set (ZMod N)) x ((not_mem_coordinateExceptional P.bad x).mp hx)) 0 out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  change (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (mixedDiagonalSample (n := n) x) *
      ‖W.eval out (mixedSlotInput ((x 0).val : ℤ) ((x 1).val : ℤ) (fun _ => ((x 1).val : ℤ))) -
        P.partition.cellVector a 0 out (mixedDiagonalSample (n := n) x)‖) ≤
    δ + 2 * (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) at h
  rw [mul_div_assoc] at h
  linarith

theorem diagonal_approximation (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out (mixedSlotInput ((x 0).val : ℤ) ((x 1).val : ℤ) (fun _ => ((x 1).val : ℤ))) -
        ∑ a, (P.partition.cellWeight a (mixedDiagonalSample (n := n) x) : ℂ) *
          P.partition.cellVector a 0 out (mixedDiagonalSample (n := n) x)‖) ≤ δ + 4 * β := by
  apply le_trans _ (P.weighted_diagonal_error out)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (mixedDiagonalSample (n := n) x))
    (fun a => P.partition.cellVector a 0 out (mixedDiagonalSample (n := n) x)) _
    (fun a => P.partition.cellWeight_nonneg a (mixedDiagonalSample (n := n) x))
    (P.partition.cellWeight_total (mixedDiagonalSample (n := n) x)))

end NativeMixedPointwisePartition

theorem exists_mixed_diagonal_partition (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      ∃ δ β : ℝ, ∃ _P : NativeMixedPointwisePartition R ((t + e + C) ^ C) δ β,
        δ + 4 * β ≤ Real.exp (-e) := by
  obtain ⟨A, _, hpartition⟩ := exists_mixed_pointwise_partition n 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e m W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [X, T, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
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
  obtain ⟨P⟩ := hpartition R hlocal hred hu
    (hbt.trans (by dsimp [u]; linarith)) (hct.trans (by dsimp [u]; linarith)) hρ hprec
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using h
  have hρle : ρ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hthree : (3 : ℝ) / N ≤ 3 * ρ := by
    calc
      _ = 3 * (1 / (N : ℝ)) := by ring
      _ ≤ 3 * ρ := mul_le_mul_of_nonneg_left hrecip (by norm_num)
  have hδ : Real.exp u * ρ = Real.exp (-u) := by
    dsimp [ρ]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨Real.exp u * ρ, 6 * ρ + 3 / N, P.mono hcost le_rfl le_rfl, ?_⟩
  calc
    _ ≤ 37 * Real.exp (-u) := by rw [hδ]; linarith
    _ ≤ Real.exp 100 * Real.exp (-u) := by
      gcongr
      linarith [Real.add_one_le_exp (100 : ℝ)]
    _ = Real.exp (100 - u) := by simp only [← Real.exp_add, sub_eq_add_neg]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [u]; linarith)

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
  NativeMixedPairPartition.finite

namespace NativeMixedPointwisePartition

variable {n m : ℕ} {p q r b δ β : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r}
  (P : NativeMixedPointwisePartition R b δ β)

theorem weighted_two_variable_error (π : Fin (n + 2) → Fin 2)
    (k : Fin 2) (out : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out (mixedSlotInput ((x (π (![0, 1] k))).val : ℤ) ((x (π (![1, 0] k))).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) -
        P.partition.cellVector a k out (fun l => x (π l))‖) ≤ δ + 4 * β := by
  let E := coordinateExceptional (ι := Fin 2) P.bad
  have h := P.sampled_error (fun x l => x (π l)) E
    (fun x hx l => (not_mem_coordinateExceptional P.bad x).mp hx (π l)) k out
  have hd : (E.card : ℝ) / Fintype.card (Fin 2 → ZMod N) ≤ 2 * β := by
    have hD := coordinateExceptional_density_le (ι := Fin 2) P.bad
    simp only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat, mul_div_assoc] at hD
    exact hD.trans (mul_le_mul_of_nonneg_left P.bad_density (by norm_num))
  rw [mul_div_assoc] at h
  linarith

theorem weighted_two_variable_exchange_error (π : Fin (n + 2) → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
      ‖W.eval out₀ (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
          star (W.eval out₁ (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
        P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
          star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))‖) ≤ 2 * (δ + 4 * β) := by
  let err := fun (k : Fin 2) (out : Fin W.outputDim) (a : Fin (n + 2) → P.partition.I)
      (x : Fin 2 → ZMod N) =>
    ‖W.eval out (mixedSlotInput ((x (π (![0, 1] k))).val : ℤ) ((x (π (![1, 0] k))).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) -
      P.partition.cellVector a k out (fun l => x (π l))‖
  have hbound (k : Fin 2) (out : Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err k out a x) ≤
        δ + 4 * β := P.weighted_two_variable_error π k out
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) *
        (err 0 out₀ a x + err 1 out₁ a x) := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (P.partition.cellWeight_nonneg _ _)
      exact norm_mul_star_sub_mul_star_le_of_le_one (W.norm_eval out₁ _)
        (P.partition.cellVector_norm a 0 out₀ _)
    _ = (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 0 out₀ a x) +
        (𝔼 x : Fin 2 → ZMod N, ∑ a, P.partition.cellWeight a (fun l => x (π l)) * err 1 out₁ a x) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.expect_add_distrib]
    _ ≤ _ := by linarith [hbound 0 out₀, hbound 1 out₁]

theorem two_variable_exchange_approximation (π : Fin (n + 2) → Fin 2) (out₀ out₁ : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval out₀ (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
          star (W.eval out₁ (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
        ∑ a, (P.partition.cellWeight a (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
            star (P.partition.cellVector a 1 out₁ (fun l => x (π l))))‖) ≤ 2 * (δ + 4 * β) := by
  apply le_trans _ (P.weighted_two_variable_exchange_error π out₀ out₁)
  exact Finset.expect_le_expect (fun x _ => norm_sub_positive_sum_le_weighted
    (fun a => P.partition.cellWeight a (fun l => x (π l)))
    (fun a => P.partition.cellVector a 0 out₀ (fun l => x (π l)) *
      star (P.partition.cellVector a 1 out₁ (fun l => x (π l)))) _
    (fun a => P.partition.cellWeight_nonneg a _) (P.partition.cellWeight_total _))

end NativeMixedPointwisePartition
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
  NativeMixedPairPartition.finite

theorem exists_mixed_sampled_exchange (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b δ β : ℝ} {m N : ℕ} [NeZero N]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r}
      (P : NativeMixedPointwisePartition R b δ β), 0 ≤ b →
      ∃ G : (Fin (n + 2) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1)
          ((b + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), G π a c (fun z => ((x z).val : ℤ)) =
          ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
            (P.partition.cellVector cell 0 a (fun l => x (π l)) *
              star (P.partition.cellVector cell 1 c (fun l => x (π l))))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
              star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ 2 * (δ + 4 * β)) := by
  obtain ⟨A, _, hpartition⟩ := exists_positive_partition_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C (n + 2) + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p q r b δ β m N _ W i j V R P hb
  classical
  let t := b + ((n + 2 : ℕ) : ℝ)
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hσ : (Fintype.card (Fin (n + 2)) : ℝ) ≤ t := by simp only [Fintype.card_fin]; dsimp [t]; linarith
  let v := fun (cell : Fin (n + 2) → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim)
      (x : Fin (n + 2) → ℤ) =>
    R.mixedPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 0 ac.1 x *
      star (R.mixedPairAnchoredVector (fun k => ((P.partition.anchor cell k).val : ℤ)) 1 ac.2 x)
  have hv (cell : Fin (n + 2) → P.partition.I) (ac : Fin W.outputDim × Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) t (v cell ac)) :=
    ((P.partition.equivalence cell).mono hbt).expansion ac.1 ac.2
  obtain ⟨F, hF, hFeval⟩ := hpartition ht hσ
    (P.partition.card_bound.trans (Real.exp_le_exp.mpr hbt))
    (fun cell k => P.partition.weight (cell k)) v
    (fun cell k => (P.partition.positive (cell k)).mono (by omega : 1 ≤ n + 1) hbt) hv
  let G := fun (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ℤ) =>
    F (a, c) (fun l => x (π l))
  have hcost : (t + A) ^ A ≤ (b + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget b hb
  have hexp (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1) ((b + C) ^ C) (G π a c)) := by
    let f : Fin (n + 2) → ((Fin 2 → ℤ) →+ ℤ) :=
      fun k => ⟨⟨fun x => x (π k), rfl⟩, fun _ _ => rfl⟩
    exact ⟨((Classical.choice (hF (a, c))).linearPullbackHom f).mono hcost⟩
  have heval (π : Fin (n + 2) → Fin 2) (a c : Fin W.outputDim) (x : Fin 2 → ZMod N) :
      G π a c (fun z => ((x z).val : ℤ)) =
        ∑ cell, (P.partition.cellWeight cell (fun l => x (π l)) : ℂ) *
          (P.partition.cellVector cell 0 a (fun l => x (π l)) *
            star (P.partition.cellVector cell 1 c (fun l => x (π l)))) :=
    hFeval (a, c) (fun l => x (π l))
  refine ⟨G, hexp, heval, ?_, ?_⟩
  · intro π a c x
    rw [heval]
    apply norm_positive_partition_sum_le_one
      (fun cell => P.partition.cellWeight cell (fun l => x (π l)))
      (fun cell => P.partition.cellVector cell 0 a (fun l => x (π l)) *
        star (P.partition.cellVector cell 1 c (fun l => x (π l))))
      (fun cell => P.partition.cellWeight_nonneg cell _) (P.partition.cellWeight_total _)
    intro cell
    rw [norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (P.partition.cellVector_norm cell 0 a _)
      (norm_nonneg _)).trans (by
        simpa only [one_mul] using P.partition.cellVector_norm cell 1 c _)
  · intro π a c
    simpa only [heval] using P.two_variable_exchange_approximation π a c

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

theorem exists_mixed_precise_sampled_exchange (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (_R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((tensorPowerBudget m p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : (Fin (n + 2) → Fin 2) → Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ π a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (n + 1)
          ((tensorPowerBudget m p + q + r + e + C) ^ C) (G π a c))) ∧
        (∀ π a c (x : Fin 2 → ZMod N), ‖G π a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ π a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (mixedSlotInput ((x (π 0)).val : ℤ) ((x (π 1)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ))) *
              star (W.eval c (mixedSlotInput ((x (π 1)).val : ℤ) ((x (π 0)).val : ℤ) (fun l => ((x (π l.succ.succ)).val : ℤ)))) -
            G π a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨a, _, hlocal⟩ := exists_mixed_pair_local_approximation n
  obtain ⟨b, _, hfrozen⟩ := exists_mixed_pair_frozen_reduction n
  obtain ⟨d, _, hpartition⟩ := exists_mixed_diagonal_partition n
  obtain ⟨c, _, hexchange⟩ := exists_mixed_sampled_exchange n
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b
  let Z := (T + X + 1 + Polynomial.C d) ^ d
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z + (Z + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q r e m _ W N _ i j V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hk : 0 ≤ tensorPowerBudget m p := hp.trans (tensorPowerBudget_bounds m hp).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget m p + q + r + e
  let t := (v + a) ^ a + (v + b) ^ b
  let z := (t + (e + 1) + d) ^ d
  let zmax := (t + v + 1 + d) ^ d
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzm : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (zmax + c) ^ c ≤ (v + C) ^ C := by
    simpa [X, T, Z, zmax, t, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : z ≤ (v + C) ^ C :=
    hzz.trans ((le_add_of_nonneg_right (by positivity)).trans hsum)
  have hcost : (z + c) ^ c ≤ (v + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by linarith : z + c ≤ zmax + c) c).trans
      ((le_add_of_nonneg_left hzm).trans hsum)
  have ha : (tensorPowerBudget m p + q + r + a) ^ a ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hb : (tensorPowerBudget m p + q + r + b) ^ b ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨δ, β, P, herr⟩ := hpartition R (hlocal (W := W) R hr) (hfrozen (W := W) R hr)
    ht (by positivity : 0 ≤ e + 1) ha hb ((Real.exp_le_exp.mpr hzC).trans hN)
  obtain ⟨G, hG, _, hcap, herror⟩ := hexchange P hz
  refine ⟨G, fun π a c => ⟨(Classical.choice (hG π a c)).mono hcost⟩, hcap, ?_⟩
  intro π a c
  apply (herror π a c).trans
  have hhalf := exp_sub_one_le_half_exp (-e)
  have hid : -(e + 1) = -e - 1 := by ring
  rw [← hid] at hhalf
  linarith

end Erdos3

end

end OAI
