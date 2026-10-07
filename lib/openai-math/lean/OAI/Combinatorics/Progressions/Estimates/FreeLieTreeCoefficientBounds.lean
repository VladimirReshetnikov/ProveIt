/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RationalHeight
import OAI.Combinatorics.Progressions.Estimates.TruncatedSeries
import OAI.Combinatorics.Progressions.Linear.LieWordProjection

namespace OAI

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem wordPolynomialEmbedding_single (w : FreeSemigroup X) (r : ℚ) :
    wordPolynomialEmbedding (MonoidAlgebra.single w r) = r • freeWord w.toFreeMonoid := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
    (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid (MonoidAlgebra.single w r)) = _
  rw [MonoidAlgebra.mapDomain_single, freeWord_single_symm]

theorem freeSemigroup_toFreeMonoid_length (w : FreeSemigroup X) :
    w.toFreeMonoid.length = w.length := by
  cases w
  rw [FreeSemigroup.toFreeMonoid_mk_eq_cons]
  rfl

theorem wordPolynomialEmbedding_truncation (s : ℕ) (p : WordPolynomial X) :
    wordPolynomialEmbedding (wordTruncation s p) = freeTruncation s (wordPolynomialEmbedding p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w r =>
    rw [wordTruncation_single, wordPolynomialEmbedding_single, map_smul, freeTruncation_word,
      freeSemigroup_toFreeMonoid_length]
    split_ifs <;> simp [wordPolynomialEmbedding_single]

theorem wordPolynomialEmbedding_freeLieExpansion (p : FreeLieAlgebra ℚ X) :
    wordPolynomialEmbedding (freeLieWordExpansion p) = freeLieAssociativeExpansion p :=
  DFunLike.congr_fun wordPolynomialEmbedding_comp_freeLie p

theorem lie_lift_eq_of_freeTruncation_eq {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    {p q : FreeLieAlgebra ℚ X}
    (h : freeTruncation s (freeLieAssociativeExpansion p) =
      freeTruncation s (freeLieAssociativeExpansion q)) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  apply lie_lift_eq_of_wordTruncation_eq f hnil
  apply wordPolynomialEmbedding_injective
  rw [wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_truncation,
    wordPolynomialEmbedding_freeLieExpansion, wordPolynomialEmbedding_freeLieExpansion]
  exact h

theorem freeTruncation_eq_of_scaled_series_eq {s : ℕ} {p q : FreeAlgebra ℚ X}
    (h : truncatedSeriesMk s (freeScaleSeries p) = truncatedSeriesMk s (freeScaleSeries q)) :
    freeTruncation s p = freeTruncation s q := by
  rw [freeTruncation_apply, freeTruncation_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact (truncatedSeriesMk_eq_iff s _ _).mp h n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

theorem lie_lift_eq_of_scaled_series_eq {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    {p q : FreeLieAlgebra ℚ X}
    (h : truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion p)) =
      truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion q))) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q :=
  lie_lift_eq_of_freeTruncation_eq f hnil (freeTruncation_eq_of_scaled_series_eq h)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def freeWordCoefficients : FreeAlgebra ℚ X →ₗ[ℚ] (FreeMonoid X →₀ ℚ) :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap

theorem freeWordCoefficients_word (w : FreeMonoid X) :
    freeWordCoefficients (freeWord w) = Finsupp.single w 1 := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (freeWord w)).coeff = _
  rw [freeWord_coeff]
  rfl

theorem freeWordCoefficients_truncation (s : ℕ) (p : FreeAlgebra ℚ X) (w : FreeMonoid X) :
    freeWordCoefficients (freeTruncation s p) w =
      if w.length ≤ s then freeWordCoefficients p w else 0 := by
  classical
  apply freeAlgebra_linear_induction (fun p =>
    freeWordCoefficients (freeTruncation s p) w =
      if w.length ≤ s then freeWordCoefficients p w else 0)
  · simp
  · intro p q hp hq
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split_ifs <;> simp
  · intro r p hp
    simp only [map_smul, Finsupp.smul_apply, hp]
    split_ifs <;> simp
  · intro v
    rw [freeTruncation_word]
    by_cases hv : v = w
    · subst v
      split_ifs <;> simp
    · split_ifs <;> simp [freeWordCoefficients_word, hv]

theorem freeWordCoefficients_embedding (p : WordPolynomial X) (w : FreeSemigroup X) :
    freeWordCoefficients (wordPolynomialEmbedding p) w.toFreeMonoid = p.coeff w := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
      (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid p))).coeff w.toFreeMonoid = _
  rw [AlgEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply_of_injective FreeSemigroup.toFreeMonoid_injective p.coeff w

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem wordTruncation_homogeneous (s : ℕ) {n : ℕ} {p : WordPolynomial X}
    (hp : WordHomogeneous n p) :
    wordTruncation s p = if n ≤ s then p else 0 := by
  classical
  ext w
  rw [wordTruncation_coeff]
  by_cases hw : p.coeff w = 0
  · simp only [hw]
    split_ifs <;> simp [hw]
  · rw [hp w hw]
    split_ifs <;> rfl

theorem wordTruncation_freeLie_mem (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    wordTruncation s (freeLieWordExpansion p) ∈ lieWordSubalgebra := by
  apply freeLie_linear_induction (fun p =>
    wordTruncation s (freeLieWordExpansion p) ∈ lieWordSubalgebra)
  · simpa only [map_zero] using lieWordSubalgebra.zero_mem
  · intro p q hp hq
    rw [map_add, map_add]
    exact lieWordSubalgebra.add_mem hp hq
  · intro r p hp
    rw [map_smul, map_smul]
    exact lieWordSubalgebra.smul_mem r hp
  · intro t
    rw [freeLieWordExpansion_tree, wordTruncation_homogeneous s (commutatorTree_homogeneous t)]
    split_ifs
    · exact commutatorTree_mem_lieWordSubalgebra t
    · exact lieWordSubalgebra.zero_mem

noncomputable def freeLieTruncation (s : ℕ) : FreeLieAlgebra ℚ X →ₗ[ℚ] FreeLieAlgebra ℚ X :=
  (dynkinProjection (FreeLieAlgebra.of ℚ)).comp
    ((wordTruncation s).comp freeLieWordExpansion.toLinearMap)

theorem freeLieTruncation_expansion (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieWordExpansion (freeLieTruncation s p) = wordTruncation s (freeLieWordExpansion p) :=
  (lieWordProjection_eq_self_iff _).mpr (wordTruncation_freeLie_mem s p)

theorem freeLieTruncation_associativeExpansion (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieAssociativeExpansion (freeLieTruncation s p) =
      freeTruncation s (freeLieAssociativeExpansion p) := by
  rw [← wordPolynomialEmbedding_freeLieExpansion, freeLieTruncation_expansion,
    wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_freeLieExpansion]

theorem freeLieTruncation_idempotent (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    freeLieTruncation s (freeLieTruncation s p) = freeLieTruncation s p := by
  apply freeLieWordExpansion_injective
  rw [freeLieTruncation_expansion, freeLieTruncation_expansion, wordTruncation_idempotent]

theorem freeLieTruncation_support_length (s : ℕ) (p : FreeLieAlgebra ℚ X)
    {w : FreeSemigroup X} (hw : w ∈ (freeLieWordExpansion (freeLieTruncation s p)).coeff.support) :
    w.length ≤ s := by
  have h := Finsupp.mem_support_iff.mp hw
  rw [freeLieTruncation_expansion, wordTruncation_coeff] at h
  by_contra hlen
  exact h (ite_eq_right hlen)

theorem lift_freeLieTruncation {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (p : FreeLieAlgebra ℚ X) :
    FreeLieAlgebra.lift ℚ f (freeLieTruncation s p) = FreeLieAlgebra.lift ℚ f p := by
  rw [← dynkinProjection_lift, freeLieTruncation_expansion,
    dynkinProjection_wordTruncation f hnil, dynkinProjection_lift]

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def freeWordSplits (w : FreeMonoid X) : Finset (FreeMonoid X × FreeMonoid X) := by
  classical
  exact (Finset.range (w.length + 1)).image (fun n =>
    (FreeMonoid.ofList (w.toList.take n), FreeMonoid.ofList (w.toList.drop n)))

theorem mem_freeWordSplits (w u v : FreeMonoid X) :
    (u, v) ∈ freeWordSplits w ↔ u * v = w := by
  classical
  unfold freeWordSplits
  constructor
  · intro h
    obtain ⟨n, _, hnv⟩ := Finset.mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnv
    change FreeMonoid.ofList (w.toList.take n ++ w.toList.drop n) = w
    rw [List.take_append_drop]
    rfl
  · intro h
    subst w
    apply Finset.mem_image.mpr
    refine ⟨u.length, Finset.mem_range.mpr ?_, ?_⟩
    · rw [FreeMonoid.length_mul]
      omega
    · change (FreeMonoid.ofList ((u.toList ++ v.toList).take u.toList.length),
        FreeMonoid.ofList ((u.toList ++ v.toList).drop u.toList.length)) = (u, v)
      simp only [List.take_left, List.drop_left]
      rfl

theorem freeWordSplits_card_le (w : FreeMonoid X) : (freeWordSplits w).card ≤ w.length + 1 := by
  classical
  unfold freeWordSplits
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

theorem freeWordCoefficients_mul (p q : FreeAlgebra ℚ X) (w : FreeMonoid X) :
    freeWordCoefficients (p * q) w =
      ∑ uv ∈ freeWordSplits w, freeWordCoefficients p uv.1 * freeWordCoefficients q uv.2 := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (p * q)).coeff w = _
  rw [map_mul]
  exact MonoidAlgebra.coeff_mul_antidiag _ _ _ _ (fun {uv} => mem_freeWordSplits w uv.1 uv.2)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

def FreeCoefficientBound (s D M : ℕ) (p : FreeAlgebra ℚ X) : Prop :=
  ∀ w, w.length ≤ s → ∃ a : ℤ,
    (a : ℚ) = (D : ℚ) * freeWordCoefficients p w ∧ a.natAbs ≤ M

namespace FreeCoefficientBound

variable {s D E M N : ℕ} {p q : FreeAlgebra ℚ X}

theorem mono (hp : FreeCoefficientBound s D M p) (hMN : M ≤ N) :
    FreeCoefficientBound s D N p := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  exact ⟨a, ha, hb.trans hMN⟩

theorem zero (s D M : ℕ) : FreeCoefficientBound (X := X) s D M 0 := by
  intro w _
  refine ⟨0, ?_, Nat.zero_le _⟩
  simp

theorem word (s : ℕ) (w : FreeMonoid X) : FreeCoefficientBound s 1 1 (freeWord w) := by
  classical
  intro v _
  by_cases hv : w = v
  · refine ⟨1, ?_, by simp⟩
    simp [freeWordCoefficients_word, hv]
  · refine ⟨0, ?_, by simp⟩
    simp [freeWordCoefficients_word, hv]

theorem one (s : ℕ) : FreeCoefficientBound (X := X) s 1 1 1 := by
  simpa only [map_one] using word s (1 : FreeMonoid X)

theorem neg (hp : FreeCoefficientBound s D M p) : FreeCoefficientBound s D M (-p) := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  refine ⟨-a, ?_, by simpa using hb⟩
  simp only [Int.cast_neg, map_neg, Finsupp.neg_apply, mul_neg, ha]

theorem add_same (hp : FreeCoefficientBound s D M p) (hq : FreeCoefficientBound s D N q) :
    FreeCoefficientBound s D (M + N) (p + q) := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  obtain ⟨b, he, hf⟩ := hq w hw
  refine ⟨a + b, ?_, (Int.natAbs_add_le _ _).trans (Nat.add_le_add hb hf)⟩
  simp only [Int.cast_add, map_add, Finsupp.add_apply, mul_add, ha, he]

theorem enlarge_denominator (hp : FreeCoefficientBound s D M p) (E : ℕ) :
    FreeCoefficientBound s (E * D) (E * M) p := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  refine ⟨(E : ℤ) * a, ?_, ?_⟩
  · push_cast
    rw [ha, mul_assoc]
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul_left E hb

theorem smul {r : ℚ} {a : ℤ} (hp : FreeCoefficientBound s D M p)
    (ha : (a : ℚ) = (E : ℚ) * r) (hbound : a.natAbs ≤ N) :
    FreeCoefficientBound s (E * D) (N * M) (r • p) := by
  intro w hw
  obtain ⟨b, hb, hbM⟩ := hp w hw
  refine ⟨a * b, ?_, ?_⟩
  · simp only [Int.cast_mul, Nat.cast_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, ha, hb]
    ring
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hbound hbM

theorem mul (hp : FreeCoefficientBound s D M p) (hq : FreeCoefficientBound s E N q) :
    FreeCoefficientBound s (D * E) ((s + 1) * M * N) (p * q) := by
  classical
  intro w hw
  have hlen : ∀ uv ∈ freeWordSplits w, uv.1.length ≤ s ∧ uv.2.length ≤ s := by
    intro uv huv
    have hmul := (mem_freeWordSplits w uv.1 uv.2).mp huv
    have h := congrArg FreeMonoid.length hmul
    rw [FreeMonoid.length_mul] at h
    omega
  choose a ha haM using fun uv : freeWordSplits w => hp uv.val.1 (hlen uv uv.property).1
  choose b hb hbN using fun uv : freeWordSplits w => hq uv.val.2 (hlen uv uv.property).2
  refine ⟨∑ uv, a uv * b uv, ?_, ?_⟩
  · push_cast
    simp_rw [ha, hb]
    rw [freeWordCoefficients_mul, Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro uv _
    ring
  · calc
      _ ≤ ∑ uv, (a uv * b uv).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _uv : freeWordSplits w, M * N := by
        apply Finset.sum_le_sum
        intro uv _
        simpa only [Int.natAbs_mul] using Nat.mul_le_mul (haM uv) (hbN uv)
      _ = (freeWordSplits w).card * (M * N) := by simp
      _ ≤ (s + 1) * (M * N) := Nat.mul_le_mul_right _
        ((freeWordSplits_card_le w).trans (Nat.add_le_add_right hw 1))
      _ = _ := by ring

theorem pow (hp : FreeCoefficientBound s D M p) (n : ℕ) :
    FreeCoefficientBound s (D ^ n) (((s + 1) * M) ^ n) (p ^ n) := by
  induction n with
  | zero => simpa using one s
  | succ n ih =>
    simpa only [pow_succ, mul_assoc, Nat.mul_left_comm] using ih.mul hp

theorem sum_finset {ι : Type*} (t : Finset ι) (f : ι → FreeAlgebra ℚ X)
    (hf : ∀ i ∈ t, FreeCoefficientBound s D M (f i)) :
    FreeCoefficientBound s D (t.card * M) (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using zero s D 0
  | @insert i t hi ih =>
    have h := (hf i (Finset.mem_insert_self _ _)).add_same
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
      Nat.add_mul, one_mul, Nat.add_comm] using h

theorem list_prod (f : List (FreeAlgebra ℚ X)) (hf : ∀ p ∈ f, FreeCoefficientBound s D M p) :
    FreeCoefficientBound s (D ^ f.length) (((s + 1) * M) ^ f.length) f.prod := by
  induction f with
  | nil => simpa using one s
  | cons p ps ih =>
    have h := (hf p List.mem_cons_self).mul (ih (fun q hq => hf q (List.mem_cons_of_mem p hq)))
    simpa only [List.prod_cons, List.length_cons, pow_succ', mul_assoc] using h

theorem rationalHeight (hp : FreeCoefficientBound s D M p) (hD : 0 < D)
    (w : FreeMonoid X) (hw : w.length ≤ s) :
    RationalHeightLE (freeWordCoefficients p w) (max D M) := by
  obtain ⟨a, ha, hb⟩ := hp w hw
  have heq : freeWordCoefficients p w = (a : ℚ) / (D : ℤ) := by
    apply (eq_div_iff (by exact_mod_cast hD.ne')).mpr
    simpa only [Int.cast_natCast, mul_comm] using ha.symm
  rw [heq]
  apply rationalHeightLE_fraction a (D : ℤ) (by exact_mod_cast hD.ne')
  · exact hb.trans (le_max_right _ _)
  · simpa only [Int.natAbs_natCast] using le_max_left D M

end FreeCoefficientBound

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

theorem commutatorTree_coefficient_bound (s : ℕ) (a : FreeMagma X) :
    FreeCoefficientBound s 1 ((2 * (s + 1)) ^ (a.length - 1))
      (wordPolynomialEmbedding (commutatorTree a)) := by
  induction a using FreeMagma.rec with
  | of x =>
    simpa only [commutatorTree, wordPolynomialEmbedding_generator, freeWord_of,
      FreeMagma.length, Nat.sub_self, pow_zero] using
      FreeCoefficientBound.word s (FreeMonoid.of x)
  | mul a b ha hb =>
    have h := (ha.mul hb).add_same (hb.mul ha).neg
    have he : (s + 1) * (2 * (s + 1)) ^ (a.length - 1) * (2 * (s + 1)) ^ (b.length - 1) +
        (s + 1) * (2 * (s + 1)) ^ (b.length - 1) * (2 * (s + 1)) ^ (a.length - 1) =
        (2 * (s + 1)) ^ ((a * b).length - 1) := by
      have ha0 := a.length_pos
      have hb0 := b.length_pos
      rw [show (a * b).length - 1 = (a.length - 1) + (b.length - 1) + 1 by
        change a.length + b.length - 1 = _; omega, pow_succ, pow_add]
      ring
    simpa only [commutatorTree, FreeMagma.length, map_sub, map_add, map_neg, map_mul,
      one_mul, sub_eq_add_neg, he] using h

theorem commutatorTree_coefficient_height (s : ℕ) (a : FreeMagma X)
    (w : FreeSemigroup X) (hw : w.length ≤ s) :
    RationalHeightLE ((commutatorTree a).coeff w) ((2 * (s + 1)) ^ (a.length - 1)) := by
  have h := (commutatorTree_coefficient_bound s a).rationalHeight (by omega)
    w.toFreeMonoid (by simpa only [freeSemigroup_toFreeMonoid_length] using hw)
  have hpow : 1 ≤ (2 * (s + 1)) ^ (a.length - 1) := one_le_pow₀ (by omega)
  simpa only [freeWordCoefficients_embedding, max_eq_right hpow] using h

theorem commutatorTree_coefficient_integral (s : ℕ) (a : FreeMagma X)
    (w : FreeSemigroup X) (hw : w.length ≤ s) :
    ∃ z : ℤ, (z : ℚ) = (commutatorTree a).coeff w ∧ z.natAbs ≤ (2 * (s + 1)) ^ (a.length - 1) := by
  obtain ⟨z, hz, hbound⟩ := commutatorTree_coefficient_bound s a w.toFreeMonoid
    (by simpa only [freeSemigroup_toFreeMonoid_length] using hw)
  exact ⟨z, by simpa only [Nat.cast_one, one_mul, freeWordCoefficients_embedding] using hz, hbound⟩

end Erdos3

end

end OAI
