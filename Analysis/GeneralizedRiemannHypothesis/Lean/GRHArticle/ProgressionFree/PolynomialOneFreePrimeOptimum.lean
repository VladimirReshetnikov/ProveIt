import GRHArticle.ProgressionFree.PolynomialGreedyCofactorDensity
import GRHArticle.ProgressionFree.PolynomialOneFreePrimeCount

/-!
# The optimum upper density with one free linear prime

The uniform fiber bound is a Roth number. Choosing a maximizer for
each cofactor at the first stage that sees it attains the limiting
sum along cofinal degree balls.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F]

/-- The limiting optimum for assignments at the designated linear prime. -/
noncomputable def polynomialOneFreePrimeOptimum (P : F[X]) : ℝ :=
  let z := (Fintype.card F : ℝ)⁻¹
  (1-z) * greedyPrimeAvoidingDensity {P} *
    ∑' t : ℕ, (rothNumberNat (t+1) : ℝ) * z^t

theorem summable_roth_oneFreePrime_weight {z : ℝ} (h₀ : 0 ≤ z) (h₁ : z < 1) :
    Summable (fun t : ℕ ↦ (rothNumberNat (t+1) : ℝ) * z^t) := by
  have hn : ‖z‖ < 1 := by rwa [Real.norm_of_nonneg h₀]
  have hs : Summable (fun t : ℕ ↦ ((t:ℝ)+1)*z^t) := by
    simpa only [pow_one, add_mul, one_mul] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hn).add (summable_geometric_of_lt_one h₀ h₁)
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun t ↦ ?_) hs
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg h₀ _)
  exact_mod_cast rothNumberNat_le (t+1)

theorem oneFreePrime_field_inv_bounds : (Fintype.card F : ℝ)⁻¹ ∈ Set.Ioo 0 1 := by
  have hq : 1 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F)
  exact ⟨inv_pos.mpr (zero_lt_one.trans hq), inv_lt_one_of_one_lt₀ hq⟩

theorem tendsto_oneFreePrimeCofactorLayer {P : F[X]} (hm : P.Monic) (hi : Irreducible P) :
    Tendsto (fun n ↦ ((oneFreePrimeCofactorLayer P n).card : ℝ) / (Fintype.card F : ℝ)^n)
      atTop (𝓝 (greedyPrimeAvoidingDensity {P})) := by
  simp_rw [← greedyPrimeAvoidingLayer_singleton]
  exact tendsto_greedyPrimeAvoidingLayer_card_div_pow {P} (by simpa using And.intro hm hi)

theorem oneFreePrimeCofactorLayer_card_div_pow_mem_Icc (P : F[X]) (n : ℕ) :
    ((oneFreePrimeCofactorLayer P n).card : ℝ) / (Fintype.card F : ℝ)^n ∈ Set.Icc 0 1 := by
  have hcard := card_greedyPrimeAvoidingLayer_le ({P} : Finset F[X]) n
  rw [greedyPrimeAvoidingLayer_singleton] at hcard
  refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
  exact_mod_cast hcard

/-- Every rational-function-ratio admissible cofactor assignment is bounded
by the same value. -/
theorem limsup_oneFreePrimeFamily_le_optimum
    {P : F[X]} (hm : P.Monic) (hi : Irreducible P) (hP : P.natDegree = 1)
    {H : F[X] → Set ℕ} (hH : ∀ g, ThreeAPFree (H g)) :
    limsup (polynomialBallProportion (oneFreePrimeFamily P H)) atTop ≤
      polynomialOneFreePrimeOptimum P := by
  let q := (Fintype.card F : ℝ)
  let z := q⁻¹
  let r (n : ℕ) := (oneFreePrimeCofactorLayer P n).card
  let w (t : ℕ) := (rothNumberNat (t+1) : ℝ)*z^t
  have hz := oneFreePrime_field_inv_bounds (F := F)
  have hs : Summable w := summable_roth_oneFreePrime_weight hz.1.le hz.2
  let B (N : ℕ) := (1-z)*∑ t ∈ Finset.range (N+1), (r (N-t) : ℝ)/q^(N-t)*w t
  have hlim : Tendsto B atTop (𝓝 (polynomialOneFreePrimeOptimum P)) := by
    simpa only [polynomialOneFreePrimeOptimum, mul_assoc] using
      (tendsto_weighted_rough_convolution w hs (fun _ ↦ by dsimp [w]; positivity)
        (oneFreePrimeCofactorLayer_card_div_pow_mem_Icc P)
        (tendsto_oneFreePrimeCofactorLayer hm hi)).const_mul (1-z)
  have hb (N : ℕ) : polynomialBallProportion (oneFreePrimeFamily P H) N ≤ B N := by
    unfold polynomialBallProportion
    calc
      _ ≤ (((Fintype.card F-1) * ∑ t ∈ Finset.range (N+1), r (N-t)*rothNumberNat (t+1) : ℕ) : ℝ) /
          q^(N+1) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast card_polynomialDegreeLTFinset_oneFreePrimeFamily_le hm hi hP hH N
      _ = B N := polynomial_weighted_convolution_scale F N r (fun t ↦ rothNumberNat (t+1))
  exact (limsup_le_limsup (Eventually.of_forall hb)
    (isCoboundedUnder_le_of_le _ (polynomialBallProportion_nonneg _)) hlim.isBoundedUnder_le).trans_eq
    hlim.limsup_eq

private noncomputable def bestPrefix (t : ℕ) : Finset ℕ :=
  (rothNumberNat_spec (t+1)).choose

private theorem bestPrefix_spec (t : ℕ) :
    bestPrefix t ⊆ Finset.range (t+1) ∧ (bestPrefix t).card = rothNumberNat (t+1) ∧
      ThreeAPFree (bestPrefix t : Set ℕ) :=
  (rothNumberNat_spec (t+1)).choose_spec

private def stageCutoff (j : ℕ) : ℕ := j*(j+1)

private theorem stageCutoff_ge (j : ℕ) : j ≤ stageCutoff j :=
  Nat.le_mul_of_pos_right _ (by omega)

private theorem stageCutoff_strictMono : StrictMono stageCutoff :=
  strictMono_nat_of_lt_succ fun j ↦ by
    dsimp [stageCutoff]
    nlinarith

private theorem exists_stageCutoff (n : ℕ) : ∃ j, n ≤ stageCutoff j :=
  ⟨n, stageCutoff_ge n⟩

private noncomputable def stageOfDegree (n : ℕ) : ℕ :=
  Nat.find (exists_stageCutoff n)

private theorem stageOfDegree_eq {j t : ℕ} (hj : 0 < j) (ht : t < 2*j) :
    stageOfDegree (stageCutoff j-t) = j := by
  have hseq : stageCutoff j = stageCutoff (j-1)+2*j := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    simp only [stageCutoff, Nat.succ_sub_one, Nat.succ_eq_add_one]
    ring
  have hle₀ : stageOfDegree (stageCutoff j-t) ≤ j :=
    Nat.find_min' (exists_stageCutoff (stageCutoff j-t))
      (show stageCutoff j-t ≤ stageCutoff j from Nat.sub_le _ _)
  apply le_antisymm hle₀
  by_contra! h
  have hmin := Nat.find_spec (exists_stageCutoff (stageCutoff j-t))
  change stageCutoff j-t ≤ stageCutoff (stageOfDegree (stageCutoff j-t)) at hmin
  have hle : stageOfDegree (stageCutoff j-t) ≤ j-1 := by omega
  have hgap := hmin.trans (stageCutoff_strictMono.monotone hle)
  omega

private noncomputable def optimalAssignment (g : F[X]) : Set ℕ :=
  bestPrefix (stageCutoff (stageOfDegree g.natDegree)-g.natDegree)

omit [Fintype F] in
private theorem prefix_optimalAssignment {g : F[X]} {j t : ℕ}
    (hj : 0 < j) (ht : t < 2*j) (htj : t ≤ stageCutoff j)
    (hg : g.natDegree = stageCutoff j-t) :
    oneFreePrimeExponentPrefix optimalAssignment g t = bestPrefix t := by
  have hstage : stageOfDegree (stageCutoff j-t) = j := stageOfDegree_eq hj ht
  have hsum : stageCutoff j-(stageCutoff j-t)=t := by omega
  ext e
  simp only [oneFreePrimeExponentPrefix, optimalAssignment, Finset.mem_filter, hg, hstage,
    hsum, Finset.mem_coe]
  exact ⟨And.right, fun he ↦ ⟨(bestPrefix_spec t).1 he, he⟩⟩

/-- A single cofactor assignment attains the exact optimum density. -/
theorem exists_oneFreePrime_optimalAssignment
    {P : F[X]} (hm : P.Monic) (hi : Irreducible P) (hP : P.natDegree = 1) :
    ∃ H : F[X] → Set ℕ, (∀ g, ThreeAPFree (H g)) ∧
      limsup (polynomialBallProportion (oneFreePrimeFamily P H)) atTop =
        polynomialOneFreePrimeOptimum P := by
  let H : F[X] → Set ℕ := optimalAssignment
  have hH (g : F[X]) : ThreeAPFree (H g) := (bestPrefix_spec _).2.2
  refine ⟨H,hH,le_antisymm (limsup_oneFreePrimeFamily_le_optimum hm hi hP hH) ?_⟩
  let z := (Fintype.card F : ℝ)⁻¹
  let r (n : ℕ) := ((oneFreePrimeCofactorLayer P n).card : ℝ) / (Fintype.card F : ℝ)^n
  let c := greedyPrimeAvoidingDensity ({P} : Finset F[X])
  let w (t : ℕ) := (rothNumberNat (t+1) : ℝ)*z^t
  have hz := oneFreePrime_field_inv_bounds (F := F)
  have hs : Summable w := summable_roth_oneFreePrime_weight hz.1.le hz.2
  have hPfin (K : ℕ) :
      (1-z)*c*(∑ t ∈ Finset.range K, w t) ≤
        limsup (polynomialBallProportion (oneFreePrimeFamily P H)) atTop := by
    apply le_limsup_of_le ⟨1, eventually_map.mpr (Eventually.of_forall (polynomialBallProportion_le_one _))⟩
    intro b hb
    have hT (t : ℕ) : Tendsto (fun j ↦ r (stageCutoff j-t)*w t) atTop (𝓝 (c*w t)) := by
      have ht := (tendsto_oneFreePrimeCofactorLayer hm hi).comp (tendsto_sub_atTop_nat t)
      exact (ht.comp stageCutoff_strictMono.tendsto_atTop).mul_const _
    have hlim : Tendsto (fun j ↦ (1-z)*∑ t ∈ Finset.range K, r (stageCutoff j-t)*w t)
        atTop (𝓝 ((1-z)*c*(∑ t ∈ Finset.range K, w t))) := by
      simpa only [← Finset.mul_sum, mul_assoc] using
        (tendsto_finsetSum (Finset.range K) (fun t _ ↦ hT t)).const_mul (1-z)
    apply le_of_tendsto hlim
    filter_upwards [stageCutoff_strictMono.tendsto_atTop.eventually hb, eventually_ge_atTop (K+1)]
      with j hj hJK
    refine le_trans ?_ hj
    rw [polynomialBallProportion_oneFreePrimeFamily hm hi hP]
    have hsub : Finset.range K ⊆ Finset.range (stageCutoff j+1) :=
      Finset.range_mono (by have := stageCutoff_ge j; omega)
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hz.2.le)
    calc
      _ = ∑ t ∈ Finset.range K,
          (((∑ g ∈ oneFreePrimeCofactorLayer P (stageCutoff j-t),
            (oneFreePrimeExponentPrefix H g t).card : ℕ) : ℝ) /
            (Fintype.card F : ℝ)^(stageCutoff j-t))*z^t := by
          apply Finset.sum_congr rfl
          intro t ht
          have htk := Finset.mem_range.mp ht
          have htj : t ≤ stageCutoff j := by have := stageCutoff_ge j; omega
          have hEq (g : F[X]) (hg : g ∈ oneFreePrimeCofactorLayer P (stageCutoff j-t)) :
              (oneFreePrimeExponentPrefix H g t).card = rothNumberNat (t+1) := by
            change (oneFreePrimeExponentPrefix optimalAssignment g t).card = _
            rw [prefix_optimalAssignment (by omega) (by omega) htj (mem_oneFreePrimeCofactorLayer.mp hg).1]
            exact (bestPrefix_spec t).2.1
          rw [Finset.sum_congr rfl hEq]
          simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul, Nat.cast_id, r,w]
          ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun t _ _ ↦
        mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
          (pow_nonneg hz.1.le t)
  have htarget := hs.hasSum.tendsto_sum_nat.const_mul ((1-z)*c)
  exact le_of_tendsto htarget (Eventually.of_forall hPfin)

/-- Exact maximum over the article's one-free-prime family, including
rational-ratio progression-freeness of every admissible assignment. -/
theorem isGreatest_oneFreePrime_family_upperDensity
    {P : F[X]} (hm : P.Monic) (hi : Irreducible P) (hP : P.natDegree = 1) :
    IsGreatest {d : ℝ | ∃ H : F[X] → Set ℕ, (∀ g, ThreeAPFree (H g)) ∧
      d = limsup (polynomialBallProportion (oneFreePrimeFamily P H)) atTop}
      (polynomialOneFreePrimeOptimum P) := by
  obtain ⟨H,hH,he⟩ := exists_oneFreePrime_optimalAssignment hm hi hP
  refine ⟨⟨H,hH,he.symm⟩,?_⟩
  rintro d ⟨G,hG,rfl⟩
  exact limsup_oneFreePrimeFamily_le_optimum hm hi hP hG

end GRHArticle.ProgressionFree
