import CoarseDegrees.Dyadic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Majority decoding

The converse direction of the dyadic criterion (synthesis, Theorem 6.3; report 10,
Theorem 1.4(a)): a coarse description `D` of `Rc A` recovers `A` in the limit, by taking the
majority of `D` over the first `s` elements of a column.

Majority *decoding* is needed rather than simple reading: a coarse description may be wrong at
infinitely many points of a single column, since a density-zero set can meet a column in an
infinite set.  What is true is that it is wrong on a set of *relative* density zero in each
column, which is what makes the majority eventually correct.

This file supplies the enumeration `colElem` of a column, a primitive-recursion lemma for
oracle computation, and the counting function.  Everything here is proved.
-/

noncomputable section

open Filter Topology
open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-! ## Enumerating a column -/

/-- The `t`-th element of the `k`-th column. -/
def colElem (k t : ℕ) : ℕ := 2 ^ k * (2 * t + 1) - 1

theorem colElem_succ (k t : ℕ) : colElem k t + 1 = 2 ^ k * (2 * t + 1) := by
  have h : 0 < 2 ^ k * (2 * t + 1) := by positivity
  unfold colElem
  omega

/-- `colElem k t` does lie in the `k`-th column. -/
theorem col_colElem (k t : ℕ) : col (colElem k t) = k := by
  have hle : k ≤ col (colElem k t) := by
    rw [← pow_dvd_iff_le_col, colElem_succ]
    exact Dvd.intro _ rfl
  have hlt : col (colElem k t) < k + 1 := by
    by_contra hcon
    have hdvd : 2 ^ (k + 1) ∣ (colElem k t + 1) := pow_dvd_iff_le_col.mpr (by omega)
    rw [colElem_succ] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hpos : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
    have h2 : 2 * t + 1 = 2 * c := by
      have : 2 ^ k * (2 * t + 1) = 2 ^ k * (2 * c) := by rw [hc]; ring
      exact Nat.eq_of_mul_eq_mul_left hpos this
    omega
  omega

theorem colElem_injective (k : ℕ) : Function.Injective (colElem k) := by
  intro a b hab
  have h1 := colElem_succ k a
  have h2 := colElem_succ k b
  rw [hab] at h1
  have hpos : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
  have : 2 * a + 1 = 2 * b + 1 := Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)
  omega

/-- The first `s` elements of the `k`-th column lie below `2^k (2s - 1)`. -/
theorem colElem_lt {k t s : ℕ} (hts : t < s) : colElem k t < 2 ^ k * (2 * s - 1) := by
  have h := colElem_succ k t
  have hpos : (0 : ℕ) < 2 ^ k := Nat.two_pow_pos k
  have hmul : 2 ^ k * (2 * t + 1) ≤ 2 ^ k * (2 * s - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem primrec_colElem : Primrec₂ colElem :=
  Primrec.nat_sub.comp
    (Primrec.nat_mul.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
        (Primrec.const 2) Primrec.fst)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
        (Primrec.const 1)))
    (Primrec.const 1)

/-! ## Primitive recursion relative to an oracle -/

/-- A total function defined by primitive recursion from oracle-recursive data is itself
oracle-recursive. -/
theorem recursiveIn_prec_total {O : Set (ℕ →. ℕ)} {base : ℕ → ℕ} {step : ℕ → ℕ → ℕ → ℕ}
    (hb : RecursiveIn O (fun a : ℕ => (Part.some (base a) : Part ℕ)))
    (hs : RecursiveIn O (fun p : ℕ =>
      (Part.some (step p.unpair.1 p.unpair.2.unpair.1 p.unpair.2.unpair.2) : Part ℕ)))
    {F : ℕ → ℕ → ℕ} (hF0 : ∀ a, F a 0 = base a)
    (hFs : ∀ a n, F a (n + 1) = step a n (F a n)) :
    RecursiveIn O (fun p : ℕ => (Part.some (F p.unpair.1 p.unpair.2) : Part ℕ)) := by
  have hprec := Nat.RecursiveIn.prec (RecursiveIn.iff_nat.mp hb) (RecursiveIn.iff_nat.mp hs)
  have key : ∀ a n : ℕ,
      (Nat.rec (motive := fun _ => Part ℕ) (Part.some (base a))
        (fun y IH => IH.bind fun i => Part.some (step a y i)) n) = Part.some (F a n) := by
    intro a n
    induction n with
    | zero => simp [hF0]
    | succ n ih =>
      show (Nat.rec (motive := fun _ => Part ℕ) (Part.some (base a))
        (fun y IH => IH.bind fun i => Part.some (step a y i)) n).bind
          (fun i => Part.some (step a n i)) = _
      rw [ih, Part.bind_some, hFs]
  refine RecursiveIn.iff_nat.mpr (hprec.of_eq fun p => ?_)
  simp only [Nat.unpair_pair]
  exact key p.unpair.1 p.unpair.2

/-! ## The counting function -/

/-- The number of the first `s` elements of the `k`-th column that lie in `D`. -/
def cnt (D : Set ℕ) (k s : ℕ) : ℕ :=
  ((Finset.range s).filter (fun t => colElem k t ∈ D)).card

theorem cnt_zero (D : Set ℕ) (k : ℕ) : cnt D k 0 = 0 := by simp [cnt]

theorem cnt_succ (D : Set ℕ) (k s : ℕ) :
    cnt D k (s + 1) = cnt D k s + characteristicValue D (colElem k s) := by
  classical
  unfold cnt characteristicValue
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : colElem k s ∈ D
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

/-- The counting function is computable from `D`. -/
theorem cnt_recursiveIn (D : Set ℕ) :
    RecursiveIn {characteristic D} (fun p : ℕ => (Part.some (cnt D p.unpair.1 p.unpair.2) : Part ℕ)) := by
  refine recursiveIn_prec_total (base := fun _ => 0)
    (step := fun a n i => i + characteristicValue D (colElem a n)) ?_ ?_
    (fun a => cnt_zero D a) (fun a n => cnt_succ D a n)
  · exact Partrec.recursiveIn (f := fun _ : ℕ => (Part.some 0 : Part ℕ)) (Computable.const 0)
  · have hq : Computable (fun p : ℕ => colElem p.unpair.1 p.unpair.2.unpair.1) :=
      (primrec_colElem.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
    have h1 : RecursiveIn {characteristic D}
        (fun p : ℕ => characteristic D (colElem p.unpair.1 p.unpair.2.unpair.1)) :=
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


/-! ## Errors have relative density zero in each column -/

/-- The number of the first `s` elements of the `k`-th column that lie in `E`. -/
def errCnt (E : Set ℕ) (k s : ℕ) : ℕ :=
  ((Finset.range s).filter (fun t => colElem k t ∈ E)).card

theorem errCnt_le_count (E : Set ℕ) (k s : ℕ) :
    errCnt E k s ≤ count E (2 ^ k * (2 * s - 1)) := by
  apply Finset.card_le_card_of_injOn (colElem k)
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ht ⊢
    exact ⟨colElem_lt ht.1, ht.2⟩
  · exact (colElem_injective k).injOn

/-- **The relative density of the errors in a column tends to zero.**  This is what makes the
majority eventually correct, and it is where the positive density of a column is used. -/
theorem errCnt_div_tendsto {E : Set ℕ} (hE : DensityZero E) (k : ℕ) :
    Tendsto (fun s => (errCnt E k s : ℝ) / s) atTop (𝓝 0) := by
  have hN : Tendsto (fun s : ℕ => 2 ^ k * (2 * s - 1)) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop 1] with s hs
    calc s ≤ 2 * s - 1 := by omega
      _ ≤ 2 ^ k * (2 * s - 1) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
  have hcomp : Tendsto (fun s : ℕ => (count E (2 ^ k * (2 * s - 1)) : ℝ) /
      ((2 ^ k * (2 * s - 1) : ℕ) : ℝ)) atTop (𝓝 0) := hE.comp hN
  have hlim : Tendsto (fun s : ℕ => (2 : ℝ) ^ (k + 1) *
      ((count E (2 ^ k * (2 * s - 1)) : ℝ) / ((2 ^ k * (2 * s - 1) : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul ((2 : ℝ) ^ (k + 1))
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 1] with s _
    positivity
  · filter_upwards [eventually_ge_atTop 1] with s hs
    have hsp : (0 : ℝ) < s := by exact_mod_cast hs
    have hNnat : 0 < 2 ^ k * (2 * s - 1) := by
      have h1 : 0 < 2 * s - 1 := by omega
      exact Nat.mul_pos (Nat.two_pow_pos k) h1
    have hNp : (0 : ℝ) < ((2 ^ k * (2 * s - 1) : ℕ) : ℝ) := by exact_mod_cast hNnat
    have h1 : (errCnt E k s : ℝ) ≤ (count E (2 ^ k * (2 * s - 1)) : ℝ) := by
      exact_mod_cast errCnt_le_count E k s
    have h2 : ((2 ^ k * (2 * s - 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) * s := by
      have hnat : 2 ^ k * (2 * s - 1) ≤ 2 ^ (k + 1) * s := by
        calc 2 ^ k * (2 * s - 1) ≤ 2 ^ k * (2 * s) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ (k + 1) * s := by ring
      exact_mod_cast hnat
    have hc0 : (0 : ℝ) ≤ (count E (2 ^ k * (2 * s - 1)) : ℝ) := by positivity
    rw [← mul_div_assoc, div_le_div_iff₀ hsp hNp]
    nlinarith [h1, h2, hc0]

/-- Eventually, fewer than half of the first `s` elements of a column are errors. -/
theorem eventually_two_errCnt_lt {E : Set ℕ} (hE : DensityZero E) (k : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → 2 * errCnt E k s < s := by
  have h := errCnt_div_tendsto hE k
  rw [Metric.tendsto_atTop] at h
  obtain ⟨s₁, hs₁⟩ := h (1 / 2) (by norm_num)
  refine ⟨max s₁ 1, fun s hs => ?_⟩
  have hs1 : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hspos : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hsp : (0 : ℝ) < s := by exact_mod_cast hspos
  have hlt := hs₁ s hs1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
  rw [div_lt_iff₀ hsp] at hlt
  have : (2 : ℝ) * (errCnt E k s : ℝ) < s := by linarith
  exact_mod_cast this


/-! ## Majority decoding -/

/-- The majority set: `⟨k,s⟩` belongs to it when more than half of the first `s` elements of
column `k` lie in `D`.  This is the `B`-computable approximation extracted from a coarse
description `D` of the dyadic code. -/
def majSet (D : Set ℕ) : Set ℕ := {m | m.unpair.2 < 2 * cnt D m.unpair.1 m.unpair.2}

theorem majSet_reducible (D : Set ℕ) : majSet D ≤ᵀₛ D := by
  have h0 : RecursiveIn {characteristic D} (fun m : ℕ => (Part.some m : Part ℕ)) :=
    Partrec.recursiveIn (f := fun m : ℕ => (Part.some m : Part ℕ)) Computable.id
  have h1 := cnt_recursiveIn D
  have hlt : PrimrecPred (fun q : ℕ => q.unpair.1.unpair.2 < 2 * q.unpair.2) :=
    Primrec.nat_lt.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair))
  have hc : Computable (fun q : ℕ => if q.unpair.1.unpair.2 < 2 * q.unpair.2 then 1 else 0) :=
    (Primrec.ite hlt (Primrec.const 1) (Primrec.const 0)).to_comp
  have h4 := recursiveIn_map (recursiveIn_pair h0 h1) hc
  refine h4.of_eq fun m => ?_
  simp [characteristic, Seq.seq, characteristicValue, majSet]

/-! ## The two counting inequalities -/

/-- If `k ∈ A`, every non-error in column `k` is counted. -/
theorem le_cnt_add_errCnt {D A : Set ℕ} {k : ℕ} (hk : k ∈ A) (s : ℕ) :
    s ≤ cnt D k s + errCnt (symmDiff D (Rc A)) k s := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range s) (p := fun t => colElem k t ∈ D)
  have hsub : ((Finset.range s).filter (fun t => ¬ (colElem k t ∈ D))) ⊆
      ((Finset.range s).filter (fun t => colElem k t ∈ symmDiff D (Rc A))) := by
    intro t htm
    simp only [Finset.mem_filter, Finset.mem_range] at htm ⊢
    refine ⟨htm.1, ?_⟩
    have hR : colElem k t ∈ Rc A := by rw [mem_Rc, col_colElem]; exact hk
    rw [Set.mem_symmDiff]
    exact Or.inr ⟨hR, htm.2⟩
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_range] at hsplit
  unfold cnt errCnt
  omega

/-- If `k ∉ A`, everything counted in column `k` is an error. -/
theorem cnt_le_errCnt {D A : Set ℕ} {k : ℕ} (hk : k ∉ A) (s : ℕ) :
    cnt D k s ≤ errCnt (symmDiff D (Rc A)) k s := by
  apply Finset.card_le_card
  intro t htm
  simp only [Finset.mem_filter, Finset.mem_range] at htm ⊢
  refine ⟨htm.1, ?_⟩
  have hR : colElem k t ∉ Rc A := by rw [mem_Rc, col_colElem]; exact hk
  rw [Set.mem_symmDiff]
  exact Or.inl ⟨htm.2, hR⟩

/-! ## The hard direction of the criterion -/

/-- **From a coarse description to a limit approximation** (report 10, Theorem 1.4).  If `B`
computes a coarse description `D` of the dyadic code `R(A)`, then `A` is the limit of a
`B`-computable approximation: take the majority vote over the first `s` elements of column `k`.
Because a column has positive density, the errors in it are eventually a minority, so the vote
is eventually correct. -/
theorem limit_of_description {B D A : Set ℕ} (hD : D ≤ᵀₛ B) (hcoarse : SetCoarseEq D (Rc A)) :
    LimitComputableIn B A := by
  refine ⟨majSet D, (majSet_reducible D).trans hD, fun k => ?_⟩
  obtain ⟨s₀, hs₀⟩ := eventually_two_errCnt_lt hcoarse k
  refine ⟨s₀, fun t ht => ?_⟩
  have hmem : Nat.pair k t ∈ majSet D ↔ t < 2 * cnt D k t := by
    simp [majSet]
  rw [hmem]
  have herr := hs₀ t ht
  constructor
  · intro hlt
    by_contra hk
    have := cnt_le_errCnt (D := D) (A := A) hk t
    omega
  · intro hk
    have := le_cnt_add_errCnt (D := D) (A := A) hk t
    omega

/-- **The criterion for the dyadic code** (report 10, Theorem 1.4).  `B` computes a coarse
description of `R(A)` exactly when `A` is the limit of a `B`-computable approximation — which,
by Shoenfield's limit lemma, is `A ≤ᵀ B′`.  So passing to the dyadic code replaces `A` by a set
whose coarse descriptions see only `A` relative to a jump. -/
theorem description_iff_limit {B A : Set ℕ} :
    (∃ D : Set ℕ, D ≤ᵀₛ B ∧ SetCoarseEq D (Rc A)) ↔ LimitComputableIn B A :=
  ⟨fun ⟨_, hD, hc⟩ => limit_of_description hD hc, exists_description_of_limit⟩

/-- Everything in the core of a dyadic code is hyperarithmetic in the coded set's parameter:
if `B` computes a coarse description of `R(A)` then `A` is hyperarithmetic in `B`.  This is the
half of report 10, Theorem 1.4 that the hyperdegree statements use. -/
theorem hypIn_of_description {B D A : Set ℕ} (hD : D ≤ᵀₛ B) (hcoarse : SetCoarseEq D (Rc A)) :
    HypIn B A :=
  (limit_of_description hD hcoarse).hypIn

end CoarseDegrees
