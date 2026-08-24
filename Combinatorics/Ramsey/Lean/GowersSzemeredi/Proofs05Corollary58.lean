import GowersSzemeredi.Proofs05Lemma14

/-!
# The scale issue in Corollary 5.8

The printed proof of Corollary 5.8 chooses one common target length for the
Corollary 5.7 refinements of all input progressions.  The live statement only
assumes that those progressions are disjoint, comparable, and cover `A`.
Those hypotheses give the required upper size bound, but they do not supply
the lower size and large-scale hypotheses needed by Corollary 5.7.

This module isolates the missing condition and proves the resulting minimally
repaired statement from `corollary_5_6`.  No lower-size or threshold condition
is silently inferred from the original hypotheses.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The common-target scale condition used, but not stated, in the printed
proof of Corollary 5.8. -/
def Corollary58Scale {N k M : Nat} (P : Fin M → ModAP N)
    (alpha : Real) : Prop :=
  ∃ v : Nat,
    1 ≤ v ∧
    ((N : Real) / M) ^ (polynomialPartitionConstant k : Real)⁻¹ / 8 ≤
      ((v - 1 : Nat) : Real) ∧
    (∀ i, max (polynomialPartitionThreshold k : Real)
      ((4 * Real.pi / alpha) ^ polynomialPartitionConstant k) <
        (P i).carrier.card) ∧
    ∀ i, (v : Real) ≤
      ((P i).carrier.card : Real) ^
        (polynomialPartitionConstant k : Real)⁻¹

/-- Corollary 5.8 with the common-target scale condition from its proof made
explicit. -/
def corollary_5_8_with_scale : Prop :=
  forall (N k M : Nat) [NeZero N] (A : Finset (ZMod N))
      (P : Fin M → ModAP N) (phi : Fin M → ZMod N → ZMod N)
      (delta alpha : Real),
    1 ≤ k → 0 < M → 0 < alpha → (A.card : Real) = delta * N →
    (forall i, (P i).IsProper ∧ PolynomialOn k Finset.univ (phi i)) →
    (forall x, x ∈ A → exists i, x ∈ (P i).carrier) →
    (forall i j, i != j → Disjoint (P i).carrier (P j).carrier) →
    (forall i j, (P i).carrier.card ≤ 2 * (P j).carrier.card) →
    alpha * N ≤ ∑ i, ‖∑ s ∈ (P i).carrier,
      balanced A s * exponential (-(phi i s))‖ →
    Corollary58Scale (k := k) P alpha →
      exists Q : ModAP N, Q.IsProper ∧
        ((N : Real) / M) ^ (polynomialPartitionConstant k : Real)⁻¹ / 8 ≤
          Q.carrier.card ∧
        (delta + alpha / 16) * Q.carrier.card ≤ (A ∩ Q.carrier).card

private def cor58BalancedReal {N : Nat} (A : Finset (ZMod N))
    (delta : Real) (x : ZMod N) : Real :=
  (if x ∈ A then 1 else 0) - delta

private lemma cor58_density_eq {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (delta : Real)
    (hcard : (A.card : Real) = delta * N) : density A = delta := by
  have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold density
  rw [hcard]
  field_simp

private lemma cor58_balanced_eq_real {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (delta : Real)
    (hcard : (A.card : Real) = delta * N) (x : ZMod N) :
    balanced A x = (cor58BalancedReal A delta x : Complex) := by
  classical
  unfold balanced
  rw [show density A = delta from cor58_density_eq A delta hcard]
  by_cases hx : x ∈ A <;>
    simp [indicator, cor58BalancedReal, hx]

private lemma cor58_balanced_discValued {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : DiscValued (balanced A) := by
  intro x
  classical
  have hd0 : 0 ≤ density A := density_nonneg A
  have hd1 : density A ≤ 1 := density_le_one A
  by_cases hx : x ∈ A
  · simp only [balanced, indicator, hx, if_true]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hd1)]
    linarith
  · simp only [balanced, indicator, hx, if_false, zero_sub]
    norm_cast
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hd0]
    exact hd1

private lemma cor58_sum_partition {X R : Type*} [DecidableEq X]
    {m : Nat} [AddCommMonoid R] (P : Fin m → Finset X) (S : Finset X)
    (hpartition : IsPartition P S) (g : X → R) :
    ∑ j, ∑ x ∈ P j, g x = ∑ x ∈ S, g x := by
  classical
  have hpair :
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _hi j _hj hij
    exact hpartition.2 i j (bne_iff_ne.mpr hij)
  have hunion : (Finset.univ : Finset (Fin m)).biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hpartition.1 x).symm
  rw [show (∑ j, ∑ x ∈ P j, g x) =
      ∑ j ∈ (Finset.univ : Finset (Fin m)), ∑ x ∈ P j, g x by simp]
  rw [← Finset.sum_biUnion hpair, hunion]

private lemma cor58_sum_abs_positive {I : Type*} [Fintype I]
    (g : I → Real) (hsigned : 0 ≤ ∑ z, g z)
    {c : Real} (habs : c ≤ ∑ z, |g z|) :
    c / 2 ≤ ∑ z, max (g z) 0 := by
  have hpoint (x : Real) : |x| = 2 * max x 0 - x := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_left hx]
      ring
    · have hx' : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hx', max_eq_right hx']
      ring
  simp_rw [hpoint] at habs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at habs
  linarith

private lemma cor58_inter_formula {N : Nat} (A S : Finset (ZMod N))
    (delta : Real) :
    ∑ x ∈ S, cor58BalancedReal A delta x =
      ((A ∩ S).card : Real) - delta * S.card := by
  classical
  simp only [cor58BalancedReal, Finset.sum_sub_distrib]
  have hindicator :
      (∑ x ∈ S, if x ∈ A then (1 : Real) else 0) =
        ((A ∩ S).card : Real) := by
    rw [← Finset.sum_filter]
    have hfilter : S.filter (fun x ↦ x ∈ A) = A ∩ S := by
      ext x
      simp [and_comm]
    rw [hfilter]
    simp
  rw [hindicator]
  simp [mul_comm]

/-- The minimally repaired Corollary 5.8 follows from Corollary 5.6. -/
theorem corollary_5_8_with_scale_holds_of_corollary_5_6
    (h56 : corollary_5_6) : corollary_5_8_with_scale := by
  classical
  intro N k M _inst A P phi delta alpha hk hM halpha hAcard hdata
    hcover hdisjoint _hcomparable hphase hscale
  obtain ⟨v, hv, hvlower, hlarge, hvupper⟩ := hscale
  choose L R hRpart hRshape hRerror using fun i : Fin M ↦
    section5_local_phase_refinement_of_corollary_5_6 (v := v)
      h56 (P i) (phi i) alpha (hdata i).1 hk (hdata i).2 halpha
      (by
        have hcardLength : (P i).carrier.card = (P i).length := (hdata i).1
        rw [← hcardLength]
        exact hlarge i) hv
      (by
        have hcardLength : (P i).carrier.card = (P i).length := (hdata i).1
        rw [← hcardLength]
        exact hvupper i)
  let I := Σ i : Fin M, Fin (L i)
  let U : Finset (ZMod N) :=
    (Finset.univ : Finset (Fin M)).biUnion fun i ↦ (P i).carrier
  let g : I → Real := fun z ↦
    ∑ s ∈ (R z.1 z.2).carrier, cor58BalancedReal A delta s
  let card : I → Real := fun z ↦ ((R z.1 z.2).carrier.card : Real)
  have hparentPair :
      ((Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint
        (fun i ↦ (P i).carrier) := by
    intro i _hi j _hj hij
    exact hdisjoint i j (bne_iff_ne.mpr hij)
  have hUcardNat : ∑ i, (P i).carrier.card = U.card := by
    dsimp only [U]
    simpa using (Finset.card_biUnion hparentPair).symm
  have hUcardReal :
      ∑ i, ((P i).carrier.card : Real) = (U.card : Real) := by
    exact_mod_cast hUcardNat
  have hUcardLeNat : U.card ≤ N := by
    calc
      U.card ≤ (Finset.univ : Finset (ZMod N)).card :=
        Finset.card_le_card (Finset.subset_univ U)
      _ = N := by simp
  have hUcardLe : (U.card : Real) ≤ N := by exact_mod_cast hUcardLeNat
  have hAsubU : A ⊆ U := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    change x ∈ (Finset.univ : Finset (Fin M)).biUnion
      (fun i ↦ (P i).carrier)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hdelta : 0 ≤ delta := by
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hcardNonneg : (0 : Real) ≤ A.card := by positivity
    nlinarith
  have hsignedU :
      0 ≤ ∑ s ∈ U, cor58BalancedReal A delta s := by
    have hformula :
        ∑ s ∈ U, cor58BalancedReal A delta s =
          (A.card : Real) - delta * U.card := by
      rw [cor58_inter_formula]
      have hinter : A ∩ U = A := Finset.inter_eq_left.mpr hAsubU
      rw [hinter]
    rw [hformula, hAcard]
    simpa only [mul_sub] using
      mul_nonneg hdelta (sub_nonneg.mpr hUcardLe)
  have hsigned : 0 ≤ ∑ z : I, g z := by
    rw [Fintype.sum_sigma]
    calc
      0 ≤ ∑ s ∈ U, cor58BalancedReal A delta s := hsignedU
      _ = ∑ i, ∑ s ∈ (P i).carrier,
          cor58BalancedReal A delta s := by
        dsimp only [U]
        rw [show (∑ i, ∑ s ∈ (P i).carrier,
            cor58BalancedReal A delta s) =
          ∑ i ∈ (Finset.univ : Finset (Fin M)),
            ∑ s ∈ (P i).carrier, cor58BalancedReal A delta s by simp]
        rw [← Finset.sum_biUnion hparentPair]
      _ = ∑ i, ∑ j, g ⟨i, j⟩ := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (cor58_sum_partition (fun j ↦ (R i j).carrier)
          (P i).carrier (hRpart i) (cor58BalancedReal A delta)).symm
  have hdisc : DiscValued (balanced A) := cor58_balanced_discValued A
  have hlocalError (i : Fin M) :
      ‖∑ s ∈ (P i).carrier,
          balanced A s * exponential (-(phi i s))‖ ≤
        (∑ j, |∑ s ∈ (R i j).carrier,
          cor58BalancedReal A delta s|) +
          alpha / 2 * (P i).carrier.card := by
    have hnorm (j : Fin (L i)) :
        ‖∑ s ∈ (R i j).carrier, balanced A s‖ =
          |∑ s ∈ (R i j).carrier, cor58BalancedReal A delta s| := by
      have hcast :
          (∑ s ∈ (R i j).carrier, balanced A s) =
            ((∑ s ∈ (R i j).carrier,
              cor58BalancedReal A delta s : Real) : Complex) := by
        calc
          _ = ∑ s ∈ (R i j).carrier,
              (cor58BalancedReal A delta s : Complex) := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact cor58_balanced_eq_real A delta hAcard s
          _ = _ := (Complex.ofReal_sum (R i j).carrier
            (cor58BalancedReal A delta)).symm
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    simpa only [hnorm] using hRerror i (balanced A) hdisc
  have hplain :
      (alpha / 2) * N ≤ ∑ z : I, |g z| := by
    have hphaseUpper :
        ∑ i, ‖∑ s ∈ (P i).carrier,
            balanced A s * exponential (-(phi i s))‖ ≤
          (∑ i, ∑ j, |∑ s ∈ (R i j).carrier,
            cor58BalancedReal A delta s|) +
            alpha / 2 * U.card := by
      calc
        ∑ i, ‖∑ s ∈ (P i).carrier,
              balanced A s * exponential (-(phi i s))‖ ≤
            ∑ i, ((∑ j, |∑ s ∈ (R i j).carrier,
              cor58BalancedReal A delta s|) +
              alpha / 2 * (P i).carrier.card) :=
          Finset.sum_le_sum fun i _hi ↦ hlocalError i
        _ = (∑ i, ∑ j, |∑ s ∈ (R i j).carrier,
              cor58BalancedReal A delta s|) +
              alpha / 2 * U.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hUcardReal]
    rw [Fintype.sum_sigma]
    have herrorN :
        (∑ i, ∑ j, |∑ s ∈ (R i j).carrier,
            cor58BalancedReal A delta s|) + alpha / 2 * U.card ≤
          (∑ i, ∑ j, |∑ s ∈ (R i j).carrier,
            cor58BalancedReal A delta s|) + alpha / 2 * N := by
      gcongr
    nlinarith
  have hpositive :
      (alpha / 4) * N ≤ ∑ z : I, max (g z) 0 := by
    have hpos := cor58_sum_abs_positive g hsigned
      (c := (alpha / 2) * N) hplain
    convert hpos using 1
    ring
  have hchildCards : ∑ z : I, card z = (U.card : Real) := by
    rw [Fintype.sum_sigma]
    calc
      ∑ i, ∑ j, card ⟨i, j⟩ =
          ∑ i, ((P i).carrier.card : Real) := by
        apply Finset.sum_congr rfl
        intro i _hi
        change (∑ j, ((R i j).carrier.card : Real)) =
          ((P i).carrier.card : Real)
        exact_mod_cast (IsPartition.sum_card (hRpart i))
      _ = (U.card : Real) := by exact_mod_cast hUcardNat
  have hweighted :
      ∑ z : I, (alpha / 16) * card z ≤
        ∑ z : I, max (g z) 0 := by
    calc
      ∑ z : I, (alpha / 16) * card z =
          (alpha / 16) * U.card := by rw [← Finset.mul_sum, hchildCards]
      _ ≤ (alpha / 16) * N := by gcongr
      _ ≤ (alpha / 4) * N := by
        have hprod : 0 ≤ alpha * (N : Real) := by positivity
        nlinarith
      _ ≤ ∑ z : I, max (g z) 0 := hpositive
  have hindex : (Finset.univ : Finset I).Nonempty := by
    by_contra hempty
    have hempty' : (Finset.univ : Finset I) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : (∑ z : I, max (g z) 0) = 0 := by
      rw [hempty']
      simp
    rw [hzero] at hpositive
    have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    nlinarith
  obtain ⟨z, _hz, hz⟩ := Finset.exists_le_of_sum_le hindex hweighted
  have hcellLower :
      ((N : Real) / M) ^ (polynomialPartitionConstant k : Real)⁻¹ / 8 ≤
        (R z.1 z.2).carrier.card := by
    rw [(hRshape z.1 z.2).1]
    rcases (hRshape z.1 z.2).2.2 with hlen | hlen
    · rw [hlen]
      exact hvlower
    · rw [hlen]
      exact hvlower.trans (by exact_mod_cast Nat.sub_le v 1)
  have hcardPos : 0 < card z := by
    dsimp only [card]
    have hscalePos :
        0 < ((N : Real) / M) ^
          (polynomialPartitionConstant k : Real)⁻¹ / 8 := by
      have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      have hMpos : (0 : Real) < M := by exact_mod_cast hM
      positivity
    exact hscalePos.trans_le hcellLower
  have hthresholdPos : 0 < (alpha / 16) * card z := by positivity
  have hgpos : 0 < g z := by
    by_contra hnot
    have hnonpos : g z ≤ 0 := le_of_not_gt hnot
    rw [max_eq_right hnonpos] at hz
    exact (not_le_of_gt hthresholdPos) hz
  have hz' : (alpha / 16) * card z ≤ g z := by
    simpa only [max_eq_left hgpos.le] using hz
  refine ⟨R z.1 z.2, (hRshape z.1 z.2).1, hcellLower, ?_⟩
  have hformula := cor58_inter_formula A (R z.1 z.2).carrier delta
  dsimp only [g, card] at hz'
  rw [hformula] at hz'
  nlinarith

end LeanProofs.GowersSzemeredi
