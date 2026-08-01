import PolynomialFormulas.AbelRuffini
import Mathlib.RingTheory.Polynomial.Morse
import Mathlib.RingTheory.Polynomial.Selmer
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# The rational Selmer family and an all-roots Abel--Ruffini theorem

For every `n ≥ 5`, the rational polynomial `X ^ n - X - 1` is monic of
exact degree `n`, has `n` distinct complex roots, and none of those roots is
solvable by radicals over `ℚ`.  Selmer irreducibility, Morse's inertia
criterion, and the nonsolvability of the symmetric group supply the Galois
obstruction.  The collision and inertia arguments are exposed as reusable
lemmas rather than repeated inside the final theorem.
-/

open scoped NumberField Polynomial
open NumberField Polynomial

noncomputable section

namespace LeanProofs.PolynomialFormulas.SelmerAbelRuffini

def selmer (R : Type*) [Ring R] (n : ℕ) : R[X] := X ^ n - X - 1

@[simp] lemma map_selmer {R K : Type*} [Ring R] [Ring K]
    (φ : R →+* K) (n : ℕ) : (selmer R n).map φ = selmer K n := by
  simp [selmer]

@[simp] lemma selmer_monic {R : Type*} [Ring R] [Nontrivial R]
    {n : ℕ} (hn : 2 ≤ n) : (selmer R n).Monic := by
  rw [selmer, sub_sub]
  apply monic_X_pow_sub
  calc
    degree (X + 1 : R[X]) ≤ max (degree (X : R[X])) (degree (1 : R[X])) := degree_add_le _ _
    _ = 1 := by simp
    _ < n := by exact_mod_cast (show 1 < n by omega)

lemma selmer_natDegree {R : Type*} [Ring R] [Nontrivial R]
    {n : ℕ} (hn : 2 ≤ n) : (selmer R n).natDegree = n := by
  rw [selmer, sub_sub]
  have hq : (X + 1 : R[X]).natDegree = 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · simp
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simpa [hq] using (show 1 < n by omega)

lemma multiple_root_linear {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {x : K} (hx : 1 < (selmer K n).rootMultiplicity x) :
    ((n - 1 : ℕ) : K) * x + (n : K) = 0 := by
  have hp0 : selmer K n ≠ 0 := (selmer_monic hn).ne_zero
  obtain ⟨hx0, hx1⟩ := (one_lt_rootMultiplicity_iff_isRoot hp0).mp hx
  rw [IsRoot, selmer] at hx0
  rw [IsRoot, selmer, derivative_sub, derivative_sub, derivative_X_pow,
    derivative_X, derivative_one] at hx1
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, eval_C, sub_zero]
    at hx0 hx1
  have hxpow : x * x ^ (n - 1) = x ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have hx1mul : (n : K) * x ^ n - x = 0 := by
    calc
      (n : K) * x ^ n - x = (n : K) * (x * x ^ (n - 1)) - x := by rw [hxpow]
      _ = x * ((n : K) * x ^ (n - 1) - 1) := by ring
      _ = 0 := by rw [hx1, mul_zero]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  linear_combination -(n : K) * hx0 + hx1mul

lemma multiple_roots_eq {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    {x y : K} (hx : 1 < (selmer K n).rootMultiplicity x)
    (hy : 1 < (selmer K n).rootMultiplicity y) : x = y := by
  have hxlin := multiple_root_linear hn hx
  have hylin := multiple_root_linear hn hy
  have hn1 : ((n - 1 : ℕ) : K) ≠ 0 := by
    intro hn1
    have hncast : (n : K) = 1 := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.cast_add, hn1, zero_add,
        Nat.cast_one]
    simp [hn1, hncast] at hxlin
  apply (mul_left_cancel₀ hn1)
  linear_combination hxlin - hylin

lemma rootMultiplicity_le_two {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n)
    (x : K) : (selmer K n).rootMultiplicity x ≤ 2 := by
  by_contra! hx
  have hp0 : selmer K n ≠ 0 := (selmer_monic hn).ne_zero
  have hxmult : 1 < (selmer K n).rootMultiplicity x := by omega
  obtain ⟨hx0, hx1⟩ := (one_lt_rootMultiplicity_iff_isRoot hp0).mp hxmult
  have hx0' := hx0
  have hx1' := hx1
  rw [IsRoot, selmer] at hx0'
  rw [IsRoot, selmer, derivative_sub, derivative_sub, derivative_X_pow,
    derivative_X, derivative_one] at hx1'
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_mul, eval_C, sub_zero]
    at hx0' hx1'
  have hxn : (n : K) ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_sub] at hx1'
    exact one_ne_zero (neg_eq_zero.mp hx1')
  have hxne : x ≠ 0 := by
    intro h
    subst x
    simp [show n ≠ 0 by omega] at hx0'
  have hn1 : ((n - 1 : ℕ) : K) ≠ 0 := by
    intro hn1
    have hncast : (n : K) = 1 := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.cast_add, hn1, zero_add,
        Nat.cast_one]
    have hlin := multiple_root_linear hn hxmult
    simp [hn1, hncast] at hlin
  have hx2 := isRoot_iterate_derivative_of_lt_rootMultiplicity (n := 2) hx
  rw [IsRoot, selmer, iterate_derivative_sub, iterate_derivative_sub,
    iterate_derivative_X_pow_eq_natCast_mul, iterate_derivative_X (by norm_num),
    iterate_derivative_one (by norm_num)] at hx2
  simp only [sub_zero, eval_mul, eval_natCast, eval_pow, eval_X] at hx2
  rw [Nat.cast_descFactorial_two] at hx2
  have hn1' : (n : K) - 1 ≠ 0 := by
    simpa [Nat.cast_sub (by omega : 1 ≤ n)] using hn1
  exact (mul_ne_zero (mul_ne_zero hxn hn1') (pow_ne_zero _ hxne)) hx2

abbrev pZ (n : ℕ) : ℤ[X] := selmer ℤ n
abbrev pQ (n : ℕ) : ℚ[X] := selmer ℚ n
abbrev splittingField (n : ℕ) := (pQ n).SplittingField

/-- Selmer's irreducibility theorem, specialized once for the rational family. -/
lemma pQ_irreducible {n : ℕ} (hn : n ≠ 1) : Irreducible (pQ n) := by
  simpa [pQ, selmer] using
    (Polynomial.X_pow_sub_X_sub_one_irreducible_rat (n := n) hn)

instance splittingField_numberField (n : ℕ) : NumberField (splittingField n) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- The Selmer polynomial has exactly its degree many splitting-field roots. -/
theorem pQ_rootSet_splittingField_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card ((pQ n).rootSet (splittingField n)) = n := by
  classical
  change Fintype.card ((pQ n).rootSet ((pQ n).SplittingField)) = n
  have hirr := pQ_irreducible (n := n) (by omega)
  exact (card_rootSet_eq_natDegree hirr.separable
    (SplittingField.splits (pQ n))).trans (selmer_natDegree (R := ℚ) hn)

lemma pZ_map_rat (n : ℕ) :
    (pZ n).map (algebraMap ℤ ℚ) = pQ n := by
  simp [pZ, pQ, selmer]

lemma pZ_map_splittingField_eq (n : ℕ) :
    (pZ n).map (algebraMap ℤ (splittingField n)) =
      (pQ n).map (algebraMap ℚ (splittingField n)) := by
  have hrat := congrArg
    (fun q : ℚ[X] => q.map (algebraMap ℚ (splittingField n))) (pZ_map_rat n)
  rwa [map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ (splittingField n)] at hrat

/-- The integral and rational Selmer models define the same roots in the
splitting field. -/
lemma pZ_rootSet_splittingField_eq (n : ℕ) :
    (pZ n).rootSet (splittingField n) =
      (pQ n).rootSet (splittingField n) := by
  classical
  rw [rootSet_def, rootSet_def, aroots, aroots, pZ_map_splittingField_eq n]

lemma pZ_splits_ringOfIntegers {n : ℕ} (hn : 2 ≤ n) :
    ((pZ n).map (algebraMap ℤ (𝓞 (splittingField n)))).Splits := by
  let i : (𝓞 (splittingField n)) →+* splittingField n := algebraMap _ _
  apply Polynomial.Splits.of_splits_map_of_injective
    (i := i) (FaithfulSMul.algebraMap_injective _ _)
  · have hrat := pZ_map_splittingField_eq n
    have hgoal :
        ((pZ n).map (algebraMap ℤ (𝓞 (splittingField n)))).map i =
          (pQ n).map (algebraMap ℚ (splittingField n)) := by
      dsimp [i]
      have hcomp :
          (algebraMap (𝓞 (splittingField n)) (splittingField n)).comp
              (Int.castRingHom (𝓞 (splittingField n))) =
            algebraMap ℤ (splittingField n) :=
        (IsScalarTower.algebraMap_eq ℤ (𝓞 (splittingField n)) (splittingField n)).symm
      rw [map_map, hcomp]
      exact hrat
    rw [hgoal]
    exact SplittingField.splits (pQ n)
  · intro a ha
    have ha' : a ∈ (pZ n).aroots (splittingField n) := by
      simpa [Polynomial.aroots, i, pZ, selmer] using ha
    exact ⟨⟨a, roots_mem_integralClosure
      (selmer_monic (R := ℤ) hn) ha'⟩, rfl⟩

lemma Multiset.card_le_toFinset_card_add_one {α : Type*} [DecidableEq α]
    (s : Multiset α)
    (hunique : ∀ ⦃x y⦄, 1 < s.count x → 1 < s.count y → x = y)
    (hatMostTwo : ∀ x, s.count x ≤ 2) :
    s.card ≤ s.toFinset.card + 1 := by
  by_cases hs : s.Nodup
  · rw [s.toFinset_card_of_nodup hs]
    omega
  · rw [Multiset.nodup_iff_count_le_one] at hs
    simp only [not_forall, not_le] at hs
    obtain ⟨x, hx⟩ := hs
    have hxmem : x ∈ s := Multiset.count_pos.mp (by omega)
    have herase : (s.erase x).Nodup := by
      rw [Multiset.nodup_iff_count_le_one]
      intro y
      by_cases hyx : y = x
      · subst y
        rw [Multiset.count_erase_self]
        have := hatMostTwo x
        omega
      · rw [Multiset.count_erase_of_ne hyx]
        by_contra! hy
        exact hyx (hunique hy hx)
    have hxmemerase : x ∈ s.erase x := by
      rw [← Multiset.count_pos, Multiset.count_erase_self]
      omega
    have hfin : (s.erase x).toFinset = s.toFinset := by
      ext y
      simp only [Multiset.mem_toFinset]
      by_cases hyx : y = x
      · subst y
        exact iff_of_true hxmemerase hxmem
      · exact Multiset.mem_erase_of_ne hyx
    rw [← hfin, Multiset.toFinset_card_of_nodup herase,
      Multiset.card_erase_add_one hxmem]

theorem selmer_natDegree_le_ncard_rootSet_add_one {K : Type*} [Field K]
    {n : ℕ} (hn : 2 ≤ n) (hsplit : (selmer K n).Splits) :
    (selmer K n).natDegree ≤ ((selmer K n).rootSet K).ncard + 1 := by
  classical
  let f := selmer K n
  have hcard : f.roots.card ≤ f.roots.toFinset.card + 1 :=
    Multiset.card_le_toFinset_card_add_one f.roots
      (fun {x y} hx hy => multiple_roots_eq (K := K) (n := n) hn
        (by simpa [f, count_roots] using hx)
        (by simpa [f, count_roots] using hy))
      (fun x => by simpa [f, count_roots] using
        rootMultiplicity_le_two (K := K) (n := n) hn x)
  rw [hsplit.natDegree_eq_card_roots]
  simpa [f, rootSet_def, aroots_def] using hcard

theorem selmer_natDegree_le_ncard_rootSet_add_one_of_splits_map
    {R K : Type*} [CommRing R] [Nontrivial R] [Field K] [Algebra R K]
    {n : ℕ} (hn : 2 ≤ n)
    (hsplit : ((selmer R n).map (algebraMap R K)).Splits) :
    (selmer R n).natDegree ≤ ((selmer R n).rootSet K).ncard + 1 := by
  have hsplitK : (selmer K n).Splits := by simpa using hsplit
  have h := selmer_natDegree_le_ncard_rootSet_add_one (K := K) hn hsplitK
  have hroot : (selmer R n).rootSet K = (selmer K n).rootSet K := by
    classical
    rw [rootSet_def, rootSet_def, aroots_def, aroots_def, map_selmer,
      Algebra.algebraMap_self, map_id]
  rw [selmer_natDegree hn]
  rw [selmer_natDegree hn] at h
  rwa [hroot]

lemma pZ_rootSet_ringOfIntegers_ncard {n : ℕ} (hn : 2 ≤ n) :
    ((pZ n).rootSet (𝓞 (splittingField n))).ncard = n := by
  classical
  have hsplitsO := pZ_splits_ringOfIntegers hn
  have himage := hsplitsO.image_rootSet_algebraMap
    (B := splittingField n)
  have hroots := pZ_rootSet_splittingField_eq n
  have hcardQ := pQ_rootSet_splittingField_card hn
  calc
    ((pZ n).rootSet (𝓞 (splittingField n))).ncard =
        ((algebraMap (𝓞 (splittingField n)) (splittingField n)) ''
          (pZ n).rootSet (𝓞 (splittingField n))).ncard :=
      (Set.ncard_image_of_injective _
        (FaithfulSMul.algebraMap_injective (𝓞 (splittingField n))
          (splittingField n))).symm
    _ = ((pZ n).rootSet (splittingField n)).ncard := by rw [himage]
    _ = ((pQ n).rootSet (splittingField n)).ncard := by rw [hroots]
    _ = n := by rw [← Set.fintypeCard_eq_ncard, hcardQ]

theorem iSup_inertia_eq_top
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L] :
    (⨆ m : MaximalSpectrum (𝓞 L), m.asIdeal.inertia Gal(L/ℚ)) = ⊤ := by
  classical
  let G := Gal(L/ℚ)
  haveI : IsGaloisGroup G ℚ L := by
    dsimp [G]
    exact IsGaloisGroup.of_isGalois ℚ L
  haveI : IsGaloisGroup G ℤ (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing G ℤ (𝓞 L) ℚ L
  let H : Subgroup G :=
    ⨆ m : MaximalSpectrum (𝓞 L), m.asIdeal.inertia G
  change H = ⊤
  by_contra hH
  let F : IntermediateField ℚ L := FixedPoints.intermediateField H
  letI : Module ℚ F := Algebra.toModule
  haveI : IsGaloisGroup H F L := IsGaloisGroup.subgroup G ℚ L H
  haveI : IsGaloisGroup H (𝓞 F) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing H (𝓞 F) (𝓞 L) F L
  have hF : Module.finrank ℚ F ≠ 1 := by
    intro h
    have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h
    have hFbot : F = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [IntermediateField.mem_bot]
      obtain ⟨a, ha⟩ := hbij.2 ⟨x, hx⟩
      refine ⟨a, ?_⟩
      have ha' := congrArg (algebraMap F L) ha
      simpa only [IsScalarTower.algebraMap_apply ℚ F L,
        IntermediateField.algebraMap_apply] using ha'
    have hfixed :
        FixedPoints.intermediateField H = (⊥ : IntermediateField ℚ L) := by
      simpa only [F] using hFbot
    apply hH
    rw [← IsGaloisGroup.fixingSubgroup_fixedPoints G ℚ L H, hfixed,
      IsGaloisGroup.fixingSubgroup_bot]
  obtain ⟨q, hqmax, hqram⟩ :=
    NumberField.exists_not_isUnramifiedAt_int (K := F) (𝒪 := 𝓞 F) hF
  letI : q.IsMaximal := hqmax
  letI : q.IsPrime := hqmax.isPrime
  obtain ⟨P, hPmax, hPq⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := 𝓞 F) (S := 𝓞 L) q
  letI : P.IsMaximal := hPmax
  letI : P.IsPrime := hPmax.isPrime
  letI : P.LiesOver q := hPq
  haveI : Module.Finite ℤ (𝓞 L) :=
    IsIntegralClosure.finite ℤ ℚ L (𝓞 L)
  haveI : Module.Finite (𝓞 F) (𝓞 L) :=
    IsIntegralClosure.finite (𝓞 F) F L (𝓞 L)
  have hIP : P.inertia G ≤ H := by
    exact le_iSup
      (fun m : MaximalSpectrum (𝓞 L) => m.asIdeal.inertia G) ⟨P, hPmax⟩
  have hcard : Nat.card (P.inertia H) = Nat.card (P.inertia G) := by
    calc
      Nat.card (P.inertia H) =
          Nat.card ((P.inertia H).map H.subtype) :=
        (Subgroup.card_map_of_injective H.subtype_injective).symm
      _ = Nat.card (P.inertia G) := by
        rw [AddSubgroup.inertia_map_subtype, inf_eq_left.mpr hIP]
  have hGcard : Nat.card (P.inertia G) = P.ramificationIdx ℤ := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P.under ℤ) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G]
  have hHcard : Nat.card (P.inertia H) = P.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := H) q P,
      Ideal.ramificationIdxIn_eq_ramificationIdx q P H]
  have hram : P.ramificationIdx ℤ = P.ramificationIdx (𝓞 F) :=
    hGcard.symm.trans (hcard.symm.trans hHcard)
  have hqidx : q.ramificationIdx ℤ = 1 := by
    apply (right_eq_mul₀ (P.ramificationIdx_pos (𝓞 F)).ne').mp
    exact hram.symm.trans (Ideal.ramificationIdx_tower (R := ℤ) q P)
  have hqunram : Algebra.IsUnramifiedAt ℤ q :=
    Ideal.ramificationIdx_eq_one_iff.mp hqidx
  exact hqram hqunram

theorem splittingField_isGalois {n : ℕ} (hn : 2 ≤ n) :
    IsGalois ℚ (splittingField n) := by
  change IsGalois ℚ (pQ n).SplittingField
  letI : IsSplittingField ℚ (pQ n).SplittingField (pQ n) :=
    Polynomial.IsSplittingField.splittingField (pQ n)
  have hirr := pQ_irreducible (n := n) (by omega)
  exact IsGalois.of_separable_splitting_field hirr.separable

theorem pZ_rootSet_isPretransitive {n : ℕ} (hn : 2 ≤ n) :
    MulAction.IsPretransitive (pQ n).Gal
      ((pZ n).rootSet (𝓞 (splittingField n))) := by
  classical
  letI : IsGalois ℚ (splittingField n) := splittingField_isGalois hn
  have hsplitsO := pZ_splits_ringOfIntegers hn
  have himage := hsplitsO.image_rootSet_algebraMap
    (B := splittingField n)
  have hroots := pZ_rootSet_splittingField_eq n
  have hmaps :
      (algebraMap (𝓞 (splittingField n)) (splittingField n)) ''
          (pZ n).rootSet (𝓞 (splittingField n)) =
        (pQ n).rootSet (splittingField n) := himage.trans hroots
  have hirr := pQ_irreducible (n := n) (by omega)
  constructor
  intro x y
  let xL : (pQ n).rootSet (splittingField n) :=
    ⟨algebraMap (𝓞 (splittingField n)) (splittingField n) x,
      hmaps ▸ ⟨x, x.2, rfl⟩⟩
  let yL : (pQ n).rootSet (splittingField n) :=
    ⟨algebraMap (𝓞 (splittingField n)) (splittingField n) y,
      hmaps ▸ ⟨y, y.2, rfl⟩⟩
  have hx := minpoly.eq_of_irreducible hirr (mem_rootSet.mp xL.2).2
  have hy := minpoly.eq_of_irreducible hirr (mem_rootSet.mp yL.2).2
  obtain ⟨g, hg⟩ :=
    (Normal.minpoly_eq_iff_mem_orbit (splittingField n)).mp (hy.symm.trans hx)
  refine ⟨g, Subtype.ext ?_⟩
  apply (FaithfulSMul.algebraMap_injective
    (𝓞 (splittingField n)) (splittingField n))
  change g • (algebraMap (𝓞 (splittingField n)) (splittingField n) x) =
    algebraMap (𝓞 (splittingField n)) (splittingField n) y at hg
  change g • (algebraMap (𝓞 (splittingField n)) (splittingField n) x) =
    algebraMap (𝓞 (splittingField n)) (splittingField n) y
  exact hg

set_option backward.isDefEq.respectTransparency false in
theorem pQ_gal_not_solvable (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsSolvable (pQ n).Gal := by
  classical
  have hn2 : 2 ≤ n := by omega
  letI : IsGalois ℚ (splittingField n) := splittingField_isGalois hn2
  letI : MulAction.IsPretransitive (pQ n).Gal
      ((pZ n).rootSet (𝓞 (splittingField n))) :=
    pZ_rootSet_isPretransitive hn2
  have hmorse : ∀ m : MaximalSpectrum (𝓞 (splittingField n)),
      ((pZ n).rootSet (𝓞 (splittingField n))).ncard ≤
        ((pZ n).rootSet ((𝓞 (splittingField n)) ⧸ m.asIdeal)).ncard + 1 := by
    intro m
    let k := (𝓞 (splittingField n)) ⧸ m.asIdeal
    letI : Field k := Ideal.Quotient.field m.asIdeal
    let π : (𝓞 (splittingField n)) →ₐ[ℤ] k :=
      Ideal.Quotient.mkₐ ℤ m.asIdeal
    have hsplits : ((selmer ℤ n).map (algebraMap ℤ k)).Splits := by
      change ((pZ n).map (algebraMap ℤ k)).Splits
      exact (pZ_splits_ringOfIntegers hn2).of_algHom π
    have hbound := selmer_natDegree_le_ncard_rootSet_add_one_of_splits_map
      (R := ℤ) (K := k) (n := n) hn2 hsplits
    rw [pZ_rootSet_ringOfIntegers_ncard hn2]
    simpa only [pZ, selmer_natDegree (R := ℤ) hn2] using hbound
  have hsurj : Function.Surjective
      (MulAction.toPermHom (pQ n).Gal
        ((pZ n).rootSet (𝓞 (splittingField n)))) :=
    (pZ_splits_ringOfIntegers hn2).surjective_toPermHom_of_iSup_inertia_eq_top
      hmorse (iSup_inertia_eq_top (splittingField n))
  intro hsolv
  letI : IsSolvable (pQ n).Gal := hsolv
  have hperm : IsSolvable
      (Equiv.Perm ((pZ n).rootSet (𝓞 (splittingField n)))) :=
    solvable_of_surjective hsurj
  have hcard : Fintype.card
      ((pZ n).rootSet (𝓞 (splittingField n))) = n := by
    rw [Set.fintypeCard_eq_ncard, pZ_rootSet_ringOfIntegers_ncard hn2]
  have hfive : 5 ≤ Cardinal.mk
      ((pZ n).rootSet (𝓞 (splittingField n))) := by
    rw [Cardinal.mk_fintype, hcard]
    exact_mod_cast hn
  exact (Equiv.Perm.not_solvable
    ((pZ n).rootSet (𝓞 (splittingField n))) hfive) hperm

theorem every_complex_root_not_solvableByRad (n : ℕ) (hn : 5 ≤ n)
    {x : ℂ} (hx : x ∈ (pQ n).rootSet ℂ) :
    x ∉ solvableByRad ℚ ℂ := by
  intro hxrad
  apply pQ_gal_not_solvable n hn
  have hirr := pQ_irreducible (n := n) (by omega)
  exact isSolvable_gal_of_irreducible hxrad hirr
    (Polynomial.aeval_eq_zero_of_mem_rootSet hx)

/-- The rational Selmer polynomial has exactly its degree many complex roots. -/
theorem pQ_rootSet_complex_card {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card ((pQ n).rootSet ℂ) = n := by
  classical
  have hirr := pQ_irreducible (n := n) (by omega)
  exact (card_rootSet_eq_natDegree hirr.separable
    (IsAlgClosed.splits ((pQ n).map (algebraMap ℚ ℂ)))).trans
      (selmer_natDegree (R := ℚ) hn)

theorem selmer_all_complex_roots (n : ℕ) (hn : 5 ≤ n) :
    (pQ n).Monic ∧
      (pQ n).natDegree = n ∧
      Fintype.card ((pQ n).rootSet ℂ) = n ∧
      ¬ IsSolvable (pQ n).Gal ∧
      ∀ x : ℂ, x ∈ (pQ n).rootSet ℂ → x ∉ solvableByRad ℚ ℂ := by
  have hn2 : 2 ≤ n := by omega
  exact ⟨selmer_monic (R := ℚ) hn2, selmer_natDegree (R := ℚ) hn2,
    pQ_rootSet_complex_card hn2, pQ_gal_not_solvable n hn,
    fun _ hx => every_complex_root_not_solvableByRad n hn hx⟩

/-- Every root of the Selmer polynomial also lacks a term in the repository's
explicit radical-expression syntax. -/
theorem every_complex_root_has_no_radical_expression (n : ℕ) (hn : 5 ≤ n)
    {x : ℂ} (hx : x ∈ (pQ n).rootSet ℂ) :
    ¬ Nonempty (RadicalExpression x) := by
  rw [RadicalExpression.nonempty_iff_mem_solvableByRad]
  exact every_complex_root_not_solvableByRad n hn hx

/-- A rational, degree-exact, nonvacuous witness in every degree above four. -/
theorem every_degree_gt_four_has_rational_polynomial_with_no_radical_root
    (n : ℕ) (hn : 4 < n) :
    ∃ p : ℚ[X], p.Monic ∧ p.natDegree = n ∧
      Fintype.card (p.rootSet ℂ) = n ∧
      ∀ x : ℂ, x ∈ p.rootSet ℂ → x ∉ solvableByRad ℚ ℂ := by
  have hn5 : 5 ≤ n := by omega
  obtain ⟨hmonic, hdegree, hcard, _, hroots⟩ :=
    selmer_all_complex_roots n hn5
  exact ⟨pQ n, hmonic, hdegree, hcard, hroots⟩

end LeanProofs.PolynomialFormulas.SelmerAbelRuffini
