import OAI.Combinatorics.Progressions.Estimates.FiniteTripleAssembly
import OAI.Combinatorics.Progressions.Estimates.NativeIntervalWeightPairs
import OAI.Combinatorics.Progressions.Linear.RankRelationBudget

namespace OAI

section

namespace Erdos3

theorem rank_pair_density_loss (p : ℝ) :
    Real.exp (-(11 * p + 7)) ≤ Real.exp (-p) / 4 *
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) := by
  have he : Real.exp (-(8 * p + 1)) * Real.exp (-p) ^ 3 = Real.exp (-(11 * p + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hright : Real.exp (-p) / 4 *
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) = Real.exp (-(11 * p + 1)) / 64 := by
    calc
      _ = (Real.exp (-(8 * p + 1)) * Real.exp (-p) ^ 3) / 64 := by ring
      _ = _ := by rw [he]
  rw [hright]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
  have h64 := two_pow_le_exp_of_le 6 le_rfl
  norm_num at h64
  calc
    _ ≤ Real.exp (-(11 * p + 7)) * Real.exp 6 :=
      mul_le_mul_of_nonneg_left h64 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure NativeWeightedRankIntervals {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (p : ℝ) where
  budget_two : 2 ≤ p
  count : ℕ
  count_pos : 0 < count
  index : Fin count → ZMod N × ZMod N × ZMod N
  index_injective : Function.Injective index
  density : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ count
  first_mem : ∀ i, (index i).2.1 ∈ H
  second_mem : ∀ i, (index i).2.1 - (index i).1 ∈ H
  third_mem : ∀ i, (index i).2.2 ∈ H
  fourth_mem : ∀ i, (index i).2.2 - (index i).1 ∈ H
  integer_relation : ∀ i,
    -((index i).2.1.val : ℤ) + ((index i).2.1 - (index i).1).val +
      (index i).2.2.val - ((index i).2.2 - (index i).1).val = 0
  branch : Fin count → Bool
  start : Fin count → ℕ
  length : Fin count → ℕ
  length_pos : ∀ i, 0 < length i
  endpoint_le : ∀ i, start i + length i ≤ N
  length_short : ∀ i, 2 * ((length i : ℤ) - 1) < N
  length_ratio : ∀ i, Real.exp (-p) ≤ (length i : ℝ) / N
  weight : ℤ → ℂ
  weight_norm : ∀ n, ‖weight n‖ ≤ 1
  lower : Fin count → ℤ → ℂ
  expansion : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (fun x => lower i (x ()))
  correlation : ∀ i, Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (start i : ℤ) (start i + length i),
    fourPointProduct (W.eval out (index i).2.1) (W.eval out ((index i).2.1 - (index i).1))
      (W.eval out (index i).2.2) (W.eval out ((index i).2.2 - (index i).1))
      (cyclicBranchOffset (index i).1 (branch i)) n * weight n * lower i n‖

end Erdos3

end

section

namespace Erdos3

structure NativeAnchoredRankFibers {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) where
  anchor : ZMod N
  branch : Bool
  selected : Finset (Fin F.count)
  parameters : Finset (ZMod N)
  parameters_nonempty : parameters.Nonempty
  parameters_density : Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ) ≤ parameters.card
  anchor_eq : ∀ i ∈ selected, (F.index i).2.2 = anchor
  branch_eq : ∀ i ∈ selected, F.branch i = branch
  pair_injective : Set.InjOn (fun i => ((F.index i).1, (F.index i).2.1)) (selected : Set (Fin F.count))
  fiber_density : ∀ a ∈ parameters, Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ) ≤
    ((selected.filter (fun i => (F.index i).1 = a)).card : ℝ)

namespace NativeWeightedRankIntervals

theorem exists_anchored_fibers {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) :
    Nonempty (NativeAnchoredRankFibers F) := by
  have hindex : Function.Injective (fun i => ((F.index i).1, (F.index i).2.1, (F.index i).2.2)) :=
    F.index_injective
  have hsize : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ Fintype.card (Fin F.count) := by
    simpa only [Fintype.card_fin] using F.density
  obtain ⟨anchor, branch, T, A, hA, hAsize, hT, hinj, hfiber⟩ := exists_dense_anchored_fibers
    (fun i => (F.index i).1) (fun i => (F.index i).2.1) (fun i => (F.index i).2.2)
    F.branch hindex (Real.exp_pos (-p)) hsize
  exact ⟨{
    anchor := anchor
    branch := branch
    selected := T
    parameters := A
    parameters_nonempty := hA
    parameters_density := hAsize
    anchor_eq := fun i hi => (hT i hi).1
    branch_eq := fun i hi => (hT i hi).2
    pair_injective := hinj
    fiber_density := hfiber }⟩

end NativeWeightedRankIntervals

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

noncomputable def fiber (a : ZMod N) : Finset (Fin F.count) :=
  A.selected.filter (fun i => (F.index i).1 = a)

theorem fiber_nonempty (a : ZMod N) (ha : a ∈ A.parameters) : (A.fiber a).Nonempty := by
  have hN : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < (A.fiber a).card :=
    lt_of_lt_of_le (by positivity) (A.fiber_density a ha)
  exact Finset.card_pos.mp (by exact_mod_cast hpos)

theorem fiber_parameter (a : ZMod N) (i : A.fiber a) : (F.index i.val).1 = a :=
  (Finset.mem_filter.mp i.property).2

theorem fiber_anchor (a : ZMod N) (i : A.fiber a) : (F.index i.val).2.2 = A.anchor :=
  A.anchor_eq i.val (Finset.mem_filter.mp i.property).1

theorem fiber_branch (a : ZMod N) (i : A.fiber a) : F.branch i.val = A.branch :=
  A.branch_eq i.val (Finset.mem_filter.mp i.property).1

theorem fiber_shift_injective (a : ZMod N) :
    Function.Injective (fun i : A.fiber a => (F.index i.val).2.1) := by
  intro i j hij
  apply Subtype.ext
  apply A.pair_injective (Finset.mem_filter.mp i.property).1 (Finset.mem_filter.mp j.property).1
  exact Prod.ext ((A.fiber_parameter a i).trans (A.fiber_parameter a j).symm) hij

end NativeAnchoredRankFibers

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

structure NativeRankInterval {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (t : ZMod N × ZMod N × ZMod N)
    (branch : Bool) (p q : ℝ) where
  first_mem : t.2.1 ∈ H
  second_mem : t.2.1 - t.1 ∈ H
  third_mem : t.2.2 ∈ H
  fourth_mem : t.2.2 - t.1 ∈ H
  integer_relation :
    -(t.2.1.val : ℤ) + (t.2.1 - t.1).val + t.2.2.val - (t.2.2 - t.1).val = 0
  start : ℕ
  length : ℕ
  length_pos : 0 < length
  endpoint_le : start + length ≤ N
  length_short : 2 * ((length : ℤ) - 1) < N
  length_ratio : Real.exp (-p) ≤ (length : ℝ) / N
  lower : ℤ → ℂ
  expansion : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) q (fun x => lower (x ()))
  correlation : Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (start : ℤ) (start + length),
    fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
      (W.eval out t.2.2) (W.eval out (t.2.2 - t.1))
      (cyclicBranchOffset t.1 branch) n * lower n‖

namespace NativeRankInterval

noncomputable def mono {s r N : ℕ} [NeZero N] {b p q p' q' : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
    (I : NativeRankInterval W out H t branch p q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeRankInterval W out H t branch p' q' :=
  { I with
    length_ratio := (Real.exp_le_exp.mpr (neg_le_neg hp)).trans I.length_ratio
    expansion := I.expansion.mono hq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hp)).trans I.correlation }

end NativeRankInterval

end Erdos3

end

section

namespace Erdos3

theorem exists_native_weighted_rank_intervals (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
      {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
      {D : NativeMixedReductionData B.mixed P} (_R : NativeReducedIntervalFamily B D K),
      Nonempty (NativeWeightedRankIntervals W.family B.rankCoordinate B.shifts
        (K + (K + C) ^ C + 2)) := by
  obtain ⟨C, hC, hexists⟩ := exists_absorbed_interval_family s
  refine ⟨C, hC, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hpow : 0 ≤ (K + C) ^ C := by positivity
  have hKP : K ≤ K + (K + C) ^ C + 2 := by linarith only [hpow]
  have hPP : (K + C) ^ C ≤ K + (K + C) ^ C + 2 := by linarith only [hK]
  obtain ⟨weight, Q, hw, hQ, hsize, hcor⟩ := hexists R
  classical
  obtain ⟨t₀, ht₀⟩ := hQ
  let : Nonempty Q := ⟨⟨t₀, ht₀⟩⟩
  have hdata (t : Q) := hcor t.val t.property
  choose v hE hv using hdata
  let e := (Fintype.equivFin Q).symm
  let old (i : Fin (Fintype.card Q)) : B.quadruples := (e i).val.val
  refine ⟨{
    budget_two := by linarith only [hK, hpow]
    count := Fintype.card Q
    count_pos := Fintype.card_pos
    index := fun i => (old i).val
    index_injective := ?_
    density := ?_
    first_mem := fun i => (B.interval (old i)).first_mem
    second_mem := fun i => (B.interval (old i)).second_mem
    third_mem := fun i => (B.interval (old i)).third_mem
    fourth_mem := fun i => (B.interval (old i)).fourth_mem
    integer_relation := fun i => (B.interval (old i)).integer_relation
    branch := fun i => (B.interval (old i)).branch
    start := fun i => (B.interval (old i)).start
    length := fun i => (B.interval (old i)).length
    length_pos := fun i => (B.interval (old i)).length_pos
    endpoint_le := fun i => (B.interval (old i)).endpoint_le
    length_short := fun i => (B.interval (old i)).length_short
    length_ratio := fun i => (Real.exp_le_exp.mpr (neg_le_neg hKP)).trans
      (R.interval_length_ratio (e i).val)
    weight := weight
    weight_norm := hw
    lower := fun i => v (e i)
    expansion := fun i => (Classical.choice (hE (e i))).mono hPP
    correlation := fun i => (Real.exp_le_exp.mpr (neg_le_neg hPP)).trans (hv (e i)) }⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hij
  · simpa only [Fintype.card_coe] using
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPP)) (by positivity)).trans hsize

end Erdos3

end

section

namespace Erdos3

namespace NativeAnchoredRankFibers

variable {s r N : ℕ} [NeZero N] {b p : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim} {H : Finset (ZMod N)}
  {F : NativeWeightedRankIntervals W out H p} (A : NativeAnchoredRankFibers F)

theorem exists_interval_pairs (a : ZMod N) (ha : a ∈ A.parameters) :
    ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(8 * p + 1)) * ((A.fiber a).card : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, Nonempty (NativeRankInterval W out H (a, t) A.branch
        (8 * p + 1) (mixedErrorPairBudget p)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := A.fiber_nonempty a ha
  let : Nonempty (A.fiber a) := ⟨⟨i₀, hi₀⟩⟩
  obtain ⟨Q, hQ, hQsize, hpair⟩ := native_interval_weight_pairs W out a A.anchor
    (cyclicBranchOffset a A.branch) (fun i : A.fiber a => (F.index i.val).2.1)
    (fun i => F.start i.val) (fun i => F.length i.val) F.weight
    (fun i => F.lower i.val) (fun i => F.expansion i.val) F.budget_two F.weight_norm
    (fun i => F.endpoint_le i.val) (fun i => F.length_short i.val)
    (fun i => F.length_ratio i.val) (fun i => by
      simpa only [A.fiber_parameter a i, A.fiber_anchor a i, A.fiber_branch a i]
        using F.correlation i.val)
  let e : (A.fiber a × A.fiber a) ↪ ZMod N × ZMod N := {
    toFun := fun t => ((F.index t.1.val).2.1, (F.index t.2.val).2.1)
    inj' := by
      intro t u htu
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj htu
      exact Prod.ext (A.fiber_shift_injective a h₁) (A.fiber_shift_injective a h₂) }
  refine ⟨Q.map e, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := hQ
    exact ⟨e t, Finset.mem_map.mpr ⟨t, ht, rfl⟩⟩
  · simpa only [Finset.card_map, Fintype.card_coe] using hQsize
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨c, len, hlen, hN, hshort, hsize, ⟨E⟩, hc⟩ := hpair u hu
    refine ⟨{
      first_mem := F.first_mem u.1.val
      second_mem := ?_
      third_mem := F.first_mem u.2.val
      fourth_mem := ?_
      integer_relation := ?_
      start := c
      length := len
      length_pos := hlen
      endpoint_le := hN
      length_short := hshort
      length_ratio := hsize
      lower := fun n => F.lower u.1.val n * star (F.lower u.2.val n)
      expansion := E
      correlation := hc }⟩
    · change (F.index u.1.val).2.1 - a ∈ H
      simpa only [A.fiber_parameter a u.1] using F.second_mem u.1.val
    · change (F.index u.2.val).2.1 - a ∈ H
      simpa only [A.fiber_parameter a u.2] using F.second_mem u.2.val
    · have h₁ := F.integer_relation u.1.val
      have h₂ := F.integer_relation u.2.val
      rw [A.fiber_parameter a u.1, A.fiber_anchor a u.1] at h₁
      rw [A.fiber_parameter a u.2, A.fiber_anchor a u.2] at h₂
      change -((F.index u.1.val).2.1.val : ℤ) + ((F.index u.1.val).2.1 - a).val +
        (F.index u.2.val).2.1.val - ((F.index u.2.val).2.1 - a).val = 0
      omega

end NativeAnchoredRankFibers

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}

theorem select_lower_term (I : NativeRankInterval W out H t branch p q) :
    ∃ i : Fin I.expansion.count, Real.exp (-(p + q)) ≤
      ‖𝔼 n ∈ Finset.Ico (I.start : ℤ) (I.start + I.length),
        fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
          (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
            (I.expansion.test i).eval (fun _ => n)‖ :=
  I.expansion.select_sample_product_correlation
    (Finset.Ico (I.start : ℤ) (I.start + I.length)) (fun n _ => n)
    (fun n => fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
      (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n)
    I.correlation

end NativeRankInterval

theorem exists_rank_interval_raised_lower_term (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
      (I : NativeRankInterval W out H t branch p q),
      ∃ i : Fin I.expansion.count,
        ∃ R : ((I.expansion.model i).raiseStep (Nat.sub_le s 1)).DegreeRankStructure r,
          R.ComplexityLE ((q + C) ^ C) ∧ R.realSubgroup s r = ⊥ ∧
          ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).ComplexityLE (raisedNiltestBudget q) ∧
          Real.exp (-(p + q)) ≤
            ‖𝔼 n ∈ Finset.Ico (I.start : ℤ) (I.start + I.length),
              fourPointProduct (W.eval out t.2.1) (W.eval out (t.2.1 - t.1))
                (W.eval out t.2.2) (W.eval out (t.2.2 - t.1)) (cyclicBranchOffset t.1 branch) n *
                  ((I.expansion.test i).raiseStep (Nat.sub_le s 1)).eval (fun _ => n)‖ := by
  obtain ⟨C, hC, hraise⟩ := RationalFilteredNilmanifold.exists_raised_degree_rank_structure s
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q W out H t branch I
  obtain ⟨i, hi⟩ := I.select_lower_term
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans (I.expansion.complexity i).1.1
  have hsmall : s - 1 < s := by omega
  obtain ⟨R, hR, hzero⟩ := hraise (I.expansion.model i) hsmall
    W.rank.filtration.rank_le_degree hq (I.expansion.complexity i).1
  refine ⟨i, R, hR, hzero,
    (I.expansion.test i).raiseStep_complexity (Nat.sub_le s 1) hq (I.expansion.complexity i), ?_⟩
  simpa only [RationalFilteredNilmanifold.Niltest.raiseStep_eval] using hi

end Erdos3

end

section

namespace Erdos3

structure NativeRankRelation {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (H : Finset (ZMod N)) (p q : ℝ) where
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  quadruples_nonempty : quadruples.Nonempty
  density : Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ quadruples.card
  branch : Bool
  interval : ∀ t : quadruples, NativeRankInterval W out H t.val branch p q

namespace NativeRankRelation

noncomputable def mono {s r N : ℕ} [NeZero N] {b p q p' q' : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (R : NativeRankRelation W out H p q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeRankRelation W out H p' q' :=
  { R with
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hp))
      (by positivity)).trans R.density
    interval := fun t => (R.interval t).mono hp hq }

end NativeRankRelation

end Erdos3

end

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

theorem monomialScale_modulus_bound (hp : 0 ≤ p) (α : Unit →₀ ℕ)
    (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s) :
    monomialScale (fun _ : Unit => (N : ℝ)) α ≤
      Real.exp ((s : ℝ) * p) * monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hlower : Real.exp (-p) * (N : ℝ) ≤ I.length :=
    (le_div_iff₀ hN).mp I.length_ratio
  have hratio : (N : ℝ) ≤ Real.exp p * I.length := by
    calc
      (N : ℝ) = Real.exp p * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp p * I.length := mul_le_mul_of_nonneg_left hlower (Real.exp_pos _).le
  exact monomialScale_le_exp_mul _ _ (fun _ => hlength) (fun _ => hN) hp
    (fun _ => hratio) α hα

theorem norm_bound_on_modulus {ι : Type*} [Fintype ι]
    (hp : 0 ≤ p) (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    {M : ℝ} (hM : 0 ≤ M) (x : ι → ℝ)
    (hx : ‖x‖ ≤ M / monomialScale (fun _ : Unit => (I.length : ℝ)) α) :
    ‖x‖ ≤ (M * Real.exp ((s : ℝ) * p)) / monomialScale (fun _ : Unit => (N : ℝ)) α := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  apply hx.trans
  apply (div_le_div_iff₀ (monomialScale_pos _ (fun _ => hlength) α)
    (monomialScale_pos _ (fun _ => hN) α)).mpr
  exact (mul_le_mul_of_nonneg_left (I.monomialScale_modulus_bound hp α hα) hM).trans_eq
    (mul_assoc _ _ _).symm

end Erdos3.NativeRankInterval

end

section

namespace Erdos3.NativeRankInterval

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q)

theorem length_lower_bound : Real.exp (-p) * N ≤ (I.length : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  exact (le_div_iff₀ hN).mp I.length_ratio

theorem length_exp_lower_bound {A : ℝ} (hN : Real.exp (p + A) ≤ N) :
    Real.exp A ≤ (I.length : ℝ) := by
  calc
    Real.exp A = Real.exp (-p) * Real.exp (p + A) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-p) * N := mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
    _ ≤ I.length := I.length_lower_bound

end Erdos3.NativeRankInterval

end

section

namespace Erdos3

namespace NativeWeightedRankIntervals

theorem remove_weight {s r N : ℕ} [NeZero N] {b p : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} (F : NativeWeightedRankIntervals W out H p) :
    Nonempty (NativeRankRelation W out H (11 * p + 7) (mixedErrorPairBudget p)) := by
  classical
  obtain ⟨A⟩ := F.exists_anchored_fibers
  have hdata (a : A.parameters) := A.exists_interval_pairs a.val a.property
  choose P _ hPsize hP using hdata
  have hpair (a : A.parameters) :
      (Real.exp (-(8 * p + 1)) * (Real.exp (-p) / 4) ^ 2) *
        (Fintype.card (ZMod N) : ℝ) ^ 2 ≤ ((P a).card : ℝ) := by
    have hf := A.fiber_density a.val a.property
    calc
      _ = Real.exp (-(8 * p + 1)) *
          (Real.exp (-p) / 4 * (Fintype.card (ZMod N) : ℝ)) ^ 2 := by ring
      _ ≤ Real.exp (-(8 * p + 1)) * ((A.fiber a.val).card : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        exact pow_le_pow_left₀ (by positivity) hf 2
      _ ≤ _ := hPsize a
  obtain ⟨Q, hQsize, hQmem⟩ := dense_triple_fibers A.parameters P
    (by positivity) A.parameters_density hpair
  have hdense : Real.exp (-(11 * p + 7)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (rank_pair_density_loss p) (by positivity)).trans hQsize
  have hN : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
  have hQpos : (0 : ℝ) < Q.card := lt_of_lt_of_le (by positivity) hdense
  have hbudget : 8 * p + 1 ≤ 11 * p + 7 := by linarith only [F.budget_two]
  have hinterval (t : Q) : Nonempty
      (NativeRankInterval W out H t.val A.branch (11 * p + 7) (mixedErrorPairBudget p)) := by
    obtain ⟨a, ha, ht⟩ := (hQmem t.val).mp t.property
    obtain ⟨I⟩ := hP a t.val.2 ht
    have heq : (a.val, t.val.2) = t.val := Prod.ext ha rfl
    rw [heq] at I
    exact ⟨I.mono hbudget le_rfl⟩
  exact ⟨{
    quadruples := Q
    quadruples_nonempty := Finset.card_pos.mp (by exact_mod_cast hQpos)
    density := hdense
    branch := A.branch
    interval := fun t => Classical.choice (hinterval t) }⟩

end NativeWeightedRankIntervals

end Erdos3

end

section

namespace Erdos3

theorem exists_native_rank_relation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
        Nonempty (NativeRankRelation W.family out H ((p + C) ^ C) ((p + C) ^ C)) := by
  obtain ⟨a, _, hreduce⟩ := exists_native_reduced_interval_family s
  obtain ⟨c, _, habsorb⟩ := exists_native_weighted_rank_intervals s
  obtain ⟨C, hC, hbudget⟩ := exists_rank_relation_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  obtain ⟨q, B, P, D, ⟨R⟩⟩ := hreduce W hf
  obtain ⟨F⟩ := habsorb R
  obtain ⟨T⟩ := F.remove_weight
  have hK : 0 ≤ (p + a) ^ a := by positivity
  have hq : q ≤ (p + C) ^ C := by
    have hpow : 0 ≤ ((p + a) ^ a + c) ^ c := by positivity
    linarith only [R.base_budget, (hbudget p hp).1, hK, hpow]
  refine ⟨B.rankCoordinate, B.shifts, B.shifts_subset, B.shifts_nonempty,
    B.shifts_short, ?_, ⟨T.mono (hbudget p hp).1 (hbudget p hp).2⟩⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hq))
    (Nat.cast_nonneg _)).trans B.shifts_density

end Erdos3

end

end OAI
