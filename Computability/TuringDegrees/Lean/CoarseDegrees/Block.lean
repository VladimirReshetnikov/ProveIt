import CoarseDegrees.Spectrum

/-!
# The block code and its decoding

The block code `I(A) = {k : 2ⁿ ≤ k < 2ⁿ⁺¹ for some n ∈ A}` of
Hirschfeldt--Jockusch--Kuyper--Schupp (2016, Section 2), and the theorem that every coarse
description of it computes `A` (synthesis, Lemma 3.4).  This is the nonuniform embedding of the
Turing degrees into the coarse degrees, and it is what `CoarseDegrees.Cone` uses to transfer
cones.

The proof is block-majority decoding, the same argument as the column-majority decoding of
`CoarseDegrees.Majority`, with the block `[2ⁿ, 2ⁿ⁺¹)` in place of the dyadic column: the block
occupies half of the initial segment `[0, 2ⁿ⁺¹)`, so the errors in it are eventually a minority
and the majority vote is eventually right.  What is different, and what makes the reduction
*nonuniform*, is that the vote is only eventually right: the finitely many blocks on which it
may fail are corrected from a finite table, which the reduction is given but does not compute.
That table is `CoarseDegrees.finSet (bitsOf A n₀)`, spliced in along the computable set
`[0, n₀)`.

Everything in this file is proved; it replaces an `admit` that `CoarseDegrees.Cone` previously
carried.
-/

noncomputable section

open Filter Topology
open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-! ## The block code -/

/-- The block code `I(A) = {k : 2ⁿ ≤ k < 2ⁿ⁺¹ for some n ∈ A}`
(Hirschfeldt--Jockusch--Kuyper--Schupp 2016, Definition 2.1). -/
def blockCode (A : Set ℕ) : Set ℕ := {k | 0 < k ∧ Nat.log 2 k ∈ A}

theorem computable_log2 : Computable (fun k : ℕ => Nat.log 2 k) := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have hP : ComputablePred (fun p : ℕ × ℕ => p.1 < 2 ^ (p.2 + 1)) :=
    PrimrecPred.computablePred
      (Primrec.nat_lt.comp Primrec.fst
        (hpow.comp (Primrec.const 2) (Primrec.succ.comp Primrec.snd)))
  have hex : ∀ k : ℕ, ∃ n, k < 2 ^ (n + 1) := fun k => ⟨Nat.log 2 k, Nat.lt_pow_succ_log_self one_lt_two k⟩
  refine (Computable.find (P := fun k n => k < 2 ^ (n + 1)) hP hex).of_eq fun k => ?_
  rw [Nat.find_eq_iff]
  refine ⟨Nat.lt_pow_succ_log_self one_lt_two k, fun n hn hlt => ?_⟩
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hn
  have h1 : 2 ^ (n + 1) ≤ 2 ^ Nat.log 2 k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hk
  omega

/-- The block code of `A` is computable from `A`. -/
theorem blockCode_reducible (A : Set ℕ) : blockCode A ≤ᵀₛ A := by
  have h1 : RecursiveIn {characteristic A} (fun k : ℕ => characteristic A (Nat.log 2 k)) :=
    recursiveIn_precomp (RecursiveIn.oracle _ (Set.mem_singleton _)) computable_log2
  have h0 : RecursiveIn {characteristic A} (fun k : ℕ => (Part.some k : Part ℕ)) :=
    Partrec.recursiveIn (f := fun k : ℕ => (Part.some k : Part ℕ)) Computable.id
  have hc : Computable (fun p : ℕ => if 0 < p.unpair.1 then p.unpair.2 else 0) :=
    (Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)).to_comp
  have h4 := recursiveIn_map (recursiveIn_pair h0 h1) hc
  refine h4.of_eq fun k => ?_
  by_cases hk : 0 < k <;> by_cases hA : Nat.log 2 k ∈ A <;>
    simp [characteristic, blockCode, Seq.seq, hk, hA]

/-! ## Blocks -/

/-- The `t`-th element of the `n`-th block `[2ⁿ, 2ⁿ⁺¹)`. -/
def blk (n t : ℕ) : ℕ := 2 ^ n + t

theorem blk_pos (n t : ℕ) : 0 < blk n t :=
  lt_of_lt_of_le (Nat.two_pow_pos n) (Nat.le_add_right _ _)

theorem blk_lt {n t : ℕ} (ht : t < 2 ^ n) : blk n t < 2 ^ (n + 1) := by
  unfold blk; rw [pow_succ]; omega

theorem log_blk {n t : ℕ} (ht : t < 2 ^ n) : Nat.log 2 (blk n t) = n := by
  refine Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _) (blk_lt ht)

theorem blk_injective (n : ℕ) : Function.Injective (blk n) := fun _ _ h => by
  unfold blk at h; omega

theorem primrec_blk : Primrec₂ blk :=
  Primrec.nat_add.comp
    ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.fst) Primrec.snd

/-! ## Counting inside a block -/

/-- The number of the first `s` elements of the `n`-th block that lie in `D`. -/
def bcnt (D : Set ℕ) (n s : ℕ) : ℕ :=
  ((Finset.range s).filter (fun t => blk n t ∈ D)).card

theorem bcnt_zero (D : Set ℕ) (n : ℕ) : bcnt D n 0 = 0 := by simp [bcnt]

theorem bcnt_succ (D : Set ℕ) (n s : ℕ) :
    bcnt D n (s + 1) = bcnt D n s + characteristicValue D (blk n s) := by
  unfold bcnt characteristicValue
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : blk n s ∈ D
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

theorem bcnt_recursiveIn (D : Set ℕ) :
    RecursiveIn {characteristic D}
      (fun p : ℕ => (Part.some (bcnt D p.unpair.1 p.unpair.2) : Part ℕ)) := by
  refine recursiveIn_prec_total (base := fun _ => 0)
    (step := fun a n i => i + characteristicValue D (blk a n)) ?_ ?_
    (fun a => bcnt_zero D a) (fun a n => bcnt_succ D a n)
  · exact Partrec.recursiveIn (f := fun _ : ℕ => (Part.some 0 : Part ℕ)) (Computable.const 0)
  · have hq : Computable (fun p : ℕ => blk p.unpair.1 p.unpair.2.unpair.1) :=
      (primrec_blk.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
    have h1 : RecursiveIn {characteristic D}
        (fun p : ℕ => characteristic D (blk p.unpair.1 p.unpair.2.unpair.1)) :=
      recursiveIn_precomp (RecursiveIn.oracle _ (Set.mem_singleton _)) hq
    have h0 : RecursiveIn {characteristic D} (fun p : ℕ => (Part.some p : Part ℕ)) :=
      Partrec.recursiveIn (f := fun p : ℕ => (Part.some p : Part ℕ)) Computable.id
    have hc : Computable (fun q : ℕ => q.unpair.1.unpair.2.unpair.2 + q.unpair.2) :=
      (Primrec.nat_add.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
          (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
        (Primrec.snd.comp Primrec.unpair)).to_comp
    have h4 := recursiveIn_map (recursiveIn_pair h0 h1) hc
    refine h4.of_eq fun p => ?_
    simp [characteristic, Seq.seq, characteristicValue]

/-! ## The errors in a block are eventually a minority -/

theorem bcnt_le_count (E : Set ℕ) (n : ℕ) : bcnt E n (2 ^ n) ≤ count E (2 ^ (n + 1)) := by
  apply Finset.card_le_card_of_injOn (blk n)
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht ⊢
    exact ⟨blk_lt ht.1, ht.2⟩
  · exact (blk_injective n).injOn

/-- **The relative density of the errors in a block tends to zero.**  A block occupies half of
the initial segment ending at its right endpoint, so the loss is only a factor of two. -/
theorem bcnt_div_tendsto {E : Set ℕ} (hE : DensityZero E) :
    Tendsto (fun n => (bcnt E n (2 ^ n) : ℝ) / 2 ^ n) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => 2 ^ (n + 1)) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards with n
    show id n ≤ 2 ^ (n + 1)
    calc n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcomp : Tendsto (fun n : ℕ => (count E (2 ^ (n + 1)) : ℝ) / ((2 ^ (n + 1) : ℕ) : ℝ))
      atTop (𝓝 0) := hE.comp hN
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) *
      ((count E (2 ^ (n + 1)) : ℝ) / ((2 ^ (n + 1) : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (2 : ℝ)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((2 ^ (n + 1) : ℕ) : ℝ) = 2 * 2 ^ n := by push_cast; ring
  have h1 : (bcnt E n (2 ^ n) : ℝ) ≤ (count E (2 ^ (n + 1)) : ℝ) := by
    exact_mod_cast bcnt_le_count E n
  rw [hcast, ← mul_div_assoc, div_le_div_iff₀ hp (by positivity)]
  nlinarith [h1, (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)]

theorem eventually_two_bcnt_lt {E : Set ℕ} (hE : DensityZero E) :
    ∃ n₀, ∀ n, n₀ ≤ n → 2 * bcnt E n (2 ^ n) < 2 ^ n := by
  have h := bcnt_div_tendsto hE
  rw [Metric.tendsto_atTop] at h
  obtain ⟨n₀, hn₀⟩ := h (1 / 2) (by norm_num)
  refine ⟨n₀, fun n hn => ?_⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hlt := hn₀ n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hp] at hlt
  have : (2 : ℝ) * (bcnt E n (2 ^ n) : ℝ) < 2 ^ n := by linarith
  exact_mod_cast this

/-! ## The two counting inequalities -/

theorem le_bcnt_add {D A : Set ℕ} {n : ℕ} (hn : n ∈ A) :
    2 ^ n ≤ bcnt D n (2 ^ n) + bcnt (symmDiff D (blockCode A)) n (2 ^ n) := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range (2 ^ n)) (p := fun t => blk n t ∈ D)
  have hsub : ((Finset.range (2 ^ n)).filter (fun t => ¬ (blk n t ∈ D))) ⊆
      ((Finset.range (2 ^ n)).filter (fun t => blk n t ∈ symmDiff D (blockCode A))) := by
    intro t htm
    simp only [Finset.mem_filter, Finset.mem_range] at htm ⊢
    refine ⟨htm.1, ?_⟩
    have hB : blk n t ∈ blockCode A := ⟨blk_pos n t, by rw [log_blk htm.1]; exact hn⟩
    rw [Set.mem_symmDiff]
    exact Or.inr ⟨hB, htm.2⟩
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_range] at hsplit
  unfold bcnt
  omega

theorem bcnt_le_err {D A : Set ℕ} {n : ℕ} (hn : n ∉ A) :
    bcnt D n (2 ^ n) ≤ bcnt (symmDiff D (blockCode A)) n (2 ^ n) := by
  apply Finset.card_le_card
  intro t htm
  simp only [Finset.mem_filter, Finset.mem_range] at htm ⊢
  refine ⟨htm.1, ?_⟩
  have hB : blk n t ∉ blockCode A := by
    rintro ⟨-, h⟩
    rw [log_blk htm.1] at h
    exact hn h
  rw [Set.mem_symmDiff]
  exact Or.inl ⟨htm.2, hB⟩

/-! ## Decoding -/

/-- The block majority: `n` is taken in when more than half of the `n`-th block lies in `D`. -/
def bmaj (D : Set ℕ) : Set ℕ := {n | 2 ^ n < 2 * bcnt D n (2 ^ n)}

theorem bmaj_reducible (D : Set ℕ) : bmaj D ≤ᵀₛ D := by
  have hpair : Computable (fun n : ℕ => Nat.pair n (2 ^ n)) :=
    (Primrec₂.natPair.comp Primrec.id
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id)).to_comp
  have h1 : RecursiveIn {characteristic D}
      (fun n : ℕ => (Part.some (bcnt D n (2 ^ n)) : Part ℕ)) := by
    refine (recursiveIn_precomp (bcnt_recursiveIn D) hpair).of_eq fun n => ?_
    simp only [Nat.unpair_pair]
  have h0 : RecursiveIn {characteristic D} (fun n : ℕ => (Part.some n : Part ℕ)) :=
    Partrec.recursiveIn (f := fun n : ℕ => (Part.some n : Part ℕ)) Computable.id
  have hlt : PrimrecPred (fun q : ℕ => 2 ^ q.unpair.1 < 2 * q.unpair.2) :=
    Primrec.nat_lt.comp
      ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
        (Primrec.fst.comp Primrec.unpair))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair))
  have hc : Computable (fun q : ℕ => if 2 ^ q.unpair.1 < 2 * q.unpair.2 then 1 else 0) :=
    (Primrec.ite hlt (Primrec.const 1) (Primrec.const 0)).to_comp
  have h4 := recursiveIn_map (recursiveIn_pair h0 h1) hc
  refine h4.of_eq fun n => ?_
  simp [characteristic, Seq.seq, characteristicValue, bmaj]

/-- The majority vote is eventually right. -/
theorem bmaj_eventually {A D : Set ℕ} (hD : SetCoarseEq D (blockCode A)) :
    ∃ n₀, ∀ n, n₀ ≤ n → (n ∈ bmaj D ↔ n ∈ A) := by
  obtain ⟨n₀, hn₀⟩ := eventually_two_bcnt_lt hD
  refine ⟨n₀, fun n hn => ?_⟩
  have herr := hn₀ n hn
  simp only [bmaj, Set.mem_setOf_eq]
  constructor
  · intro hlt
    by_contra hA
    have := bcnt_le_err (D := D) (A := A) hA
    omega
  · intro hA
    have := le_bcnt_add (D := D) (A := A) hA
    omega

/-- **Every coarse description of the block code computes the coded set**
(Hirschfeldt--Jockusch--Kuyper--Schupp 2016, Section 2; synthesis, Lemma 3.4).  The reduction is
the block majority above a threshold `n₀`, and a finite table below it.  It is nonuniform: `n₀`
and the table depend on the description and are not computed from it. -/
theorem blockCode_decode {A D : Set ℕ} (hD : SetCoarseEq D (blockCode A)) : A ≤ᵀₛ D := by
  obtain ⟨n₀, hn₀⟩ := bmaj_eventually hD
  have hS : ComputablePred (fun n => n ∈ {n : ℕ | n < n₀}) :=
    PrimrecPred.computablePred (Primrec.nat_lt.comp Primrec.id (Primrec.const n₀))
  have hsplice := setTuringReducible_splice (O := D) (S := {n : ℕ | n < n₀}) hS
    (bmaj_reducible D)
    (setTuringReducible_of_computablePred (computable_finSet (bitsOf A n₀)))
  have hEq : (bmaj D \ {n : ℕ | n < n₀}) ∪ (finSet (bitsOf A n₀) ∩ {n : ℕ | n < n₀}) = A := by
    ext n
    by_cases hn : n < n₀
    · simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact absurd hn h
        · exact (mem_finSet_bitsOf hn).mp h
      · intro hA
        exact Or.inr ⟨(mem_finSet_bitsOf hn).mpr hA, hn⟩
    · simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact (hn₀ n (by omega)).mp h
        · exact absurd h hn
      · intro hA
        exact Or.inl ⟨(hn₀ n (by omega)).mpr hA, hn⟩
  rwa [hEq] at hsplice

end CoarseDegrees
