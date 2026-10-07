/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.RankOrbitCoefficientCorrections

namespace OAI

section

namespace Erdos3

theorem exists_common_rank_relation_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → p + (p + c) ^ c ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c)
  exact ⟨C, hC, fun p hp => by simpa [Polynomial.eval₂_pow] using hbudget p hp⟩

theorem exists_native_common_rank_budget (a c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let q := p + (p + a) ^ a + 2
      q ≤ (p + C) ^ C ∧ (q + c) ^ c ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpow : 0 ≤ (q + c) ^ c := by positivity
  have hsum : q + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Y, q, Polynomial.eval₂_pow] using hbudget p hp
  constructor <;> linarith only [hq, hpow, hsum]

end Erdos3

end

section

namespace Erdos3

theorem exists_rank_common_data_budget (s c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + c) ^ c ≤ (p + C) ^ C ∧
      3 * (4 * p) * (4 * p) * (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) ≤
        (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C c) ^ c
  let A := ((Y + 1 + (Y + 3) ^ 7 + 2) ^ 9 + Y + 4) ^ 4
  let P := Y + 3 * (4 * X) * (4 * X) * (A + 2) * Polynomial.C (s + 1)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hY : 0 ≤ (p + c) ^ c := by positivity
  have hA := refiltrationCoordinateBudget_nonneg hY
  have hcost : 0 ≤ 3 * (4 * p) * (4 * p) *
      (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) := by positivity
  have hsum : (p + c) ^ c + 3 * (4 * p) * (4 * p) *
      (refiltrationCoordinateBudget ((p + c) ^ c) + 2) * (s + 1) ≤ (p + C) ^ C := by
    simpa [P, A, Y, X, refiltrationCoordinateBudget, Polynomial.eval₂_pow] using hbound p hp
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_interval_data (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {α : Type*} {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {t : α → ZMod N × ZMod N × ZMod N} {branch : Bool},
      0 ≤ p → b ≤ p → (I : ∀ a, NativeRankInterval W out H (t a) branch p p) →
      (S : Finset α) → S.Nonempty →
      (∀ a ∈ S, Real.exp ((p + C) ^ C) ≤ ((I a).length : ℝ)) →
      ∃ (K : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)) (T : Finset α),
        T ⊆ S ∧ T.Nonempty ∧ Real.exp (-((p + C) ^ C)) * S.card ≤ (T.card : ℝ) ∧
        (∀ d, K d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
          ⌈Real.exp (refiltrationCoordinateBudget ((p + C) ^ C))⌉₊) ∧
        ∀ a ∈ T, ∃ E : (I a).SunflowerWitness ((p + C) ^ C),
          (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
          ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
            W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
  obtain ⟨c, _, hwitness⟩ := exists_rank_sunflower_witness s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_common_data_budget s c
  refine ⟨C, hC, ?_⟩
  intro α r N _ b p W out H t branch hp hbp I S hS hlarge
  let P := (p + c) ^ c
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨hPC, hcostC⟩ := hbudget p hp
  have hQ : 0 ≤ (p + C) ^ C := hP.trans hPC
  have hex (a : α) (ha : a ∈ S) : Nonempty ((I a).SunflowerWitness P) :=
    hwitness hp hbp (I a) ((Real.exp_le_exp.mpr hPC).trans (hlarge a ha))
  let D (a : α) (ha : a ∈ S) := Classical.choice (hex a ha)
  obtain ⟨K, T, hTS, hT, hsize, _, hdata⟩ := exists_common_rank_projection_family I S hS hP D
  have hdim : (W.dim : ℝ) ≤ p := W.complexity.1.1.trans hbp
  have hcard : Fintype.card (Σ _ : Fin 4, Fin W.dim) = 4 * W.dim := by simp
  have hn : (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) ≤ 4 * p := by
    rw [hcard, Nat.cast_mul]
    norm_num
    linarith
  have hA := refiltrationCoordinateBudget_nonneg hP
  have hcost : 3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
      Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2) * (s + 1) ≤
      (p + C) ^ C := by
    apply le_trans _ hcostC
    change 3 * (Fintype.card (Σ _ : Fin 4, Fin W.dim) : ℝ) *
      Fintype.card (Σ _ : Fin 4, Fin W.dim) * (refiltrationCoordinateBudget P + 2) * (s + 1) ≤
      3 * (4 * p) * (4 * p) * (refiltrationCoordinateBudget P + 2) * (s + 1)
    gcongr
  have hnew (a : α) (ha : a ∈ T) : ∃ E : (I a).SunflowerWitness ((p + C) ^ C),
      (∀ d : Fin (s + 1), E.projection d.val = K d) ∧
      ∀ d : Fin (s + 1), (I a).refilteredHorizontalImage E.index E.subalgebra d.val =
        W.rank.filtration.horizontalImageOfSubmodule (K d) d.val := by
    obtain ⟨E, hproj, hhor⟩ := hdata a ha
    exact ⟨E.mono hPC, hproj, hhor⟩
  refine ⟨K, T, hTS, hT, ?_, ?_, hnew⟩
  · apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith
  · obtain ⟨a, ha⟩ := hT
    obtain ⟨E, hproj, _⟩ := hnew a ha
    intro d
    rw [← hproj d]
    exact E.projection_mem_candidates hQ d.val

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankRelation

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)}

structure CommonData (R : NativeRankRelation W out H p q) (P : ℝ) where
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  subset : quadruples ⊆ R.quadruples
  nonempty : quadruples.Nonempty
  density : Real.exp (-P) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ quadruples.card
  spaces : Fin (s + 1) → Submodule ℚ (Fin 4 → W.L)
  witness : ∀ t, (ht : t ∈ quadruples) → (R.interval ⟨t, subset ht⟩).SunflowerWitness P
  projection : ∀ t (ht : t ∈ quadruples) (d : Fin (s + 1)),
    (witness t ht).projection d.val = spaces d

namespace CommonData

variable {R : NativeRankRelation W out H p q} {P Q : ℝ} (D : R.CommonData P)

theorem spaces_mem_candidates (hP : 0 ≤ P) (d : Fin (s + 1)) :
    D.spaces d ∈ heightBoundedSubspaces W.fourRankBasis (Fintype.card (Σ _ : Fin 4, Fin W.dim))
      ⌈Real.exp (refiltrationCoordinateBudget P)⌉₊ := by
  obtain ⟨t, ht⟩ := D.nonempty
  rw [← D.projection t ht d]
  exact (D.witness t ht).projection_mem_candidates hP d.val

theorem horizontalImage_eq (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples)
    (d : Fin (s + 1)) :
    (R.interval ⟨t, D.subset ht⟩).refilteredHorizontalImage
      (D.witness t ht).index (D.witness t ht).subalgebra d.val =
        W.rank.filtration.horizontalImageOfSubmodule (D.spaces d) d.val := by
  rw [(D.witness t ht).horizontalImage_eq, D.projection t ht d]

noncomputable def mono (hPQ : P ≤ Q) : R.CommonData Q :=
  { D with
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hPQ))
      (by positivity)).trans D.density
    witness := fun t ht => (D.witness t ht).mono hPQ
    projection := fun t ht d => D.projection t ht d }

theorem mono_quadruples (hPQ : P ≤ Q) : (D.mono hPQ).quadruples = D.quadruples := rfl

theorem mono_spaces (hPQ : P ≤ Q) : (D.mono hPQ).spaces = D.spaces := rfl

end CommonData

end NativeRankRelation

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_common_denominator (D : R.CommonData P) (hP : 0 ≤ P) :
    ∃ (E : R.CommonData (2 * P)) (l : ℕ),
      E.quadruples ⊆ D.quadruples ∧ E.spaces = D.spaces ∧ 0 < l ∧ (l : ℝ) ≤ Real.exp P ∧
      ∀ t (ht : t ∈ E.quadruples), (E.witness t ht).denominator = l := by
  classical
  let code (t : ZMod N × ZMod N × ZMod N) :=
    if ht : t ∈ D.quadruples then (D.witness t ht).denominator else 1
  let A := (Finset.Icc 1 ⌊Real.exp P⌋₊ : Finset ℕ)
  have hcode (t) (ht : t ∈ D.quadruples) : code t ∈ (A : Set ℕ) := by
    simp only [code, dite_eq_left ht, Finset.mem_coe, A, Finset.mem_Icc]
    exact ⟨(D.witness t ht).denominator_pos, Nat.le_floor (D.witness t ht).denominator_bound⟩
  have hcount : ((A : Set ℕ).ncard : ℝ) ≤ Real.exp P := by
    simpa only [Set.ncard_coe_finset, A, Nat.card_Icc, Nat.add_sub_cancel] using
      Nat.floor_le (Real.exp_pos P).le
  obtain ⟨l, hl, T, hTD, hT, hconst, hsize⟩ := exists_exponential_constant_fiber
    D.quadruples D.nonempty code A A.finite_toSet hcode hcount
  have hPP : P ≤ 2 * P := by linarith
  let E : R.CommonData (2 * P) := {
    quadruples := T
    subset := hTD.trans D.subset
    nonempty := hT
    density := by
      calc
        Real.exp (-(2 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
            Real.exp (-P) * (Real.exp (-P) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring
        _ ≤ Real.exp (-P) * D.quadruples.card :=
          mul_le_mul_of_nonneg_left D.density (Real.exp_pos _).le
        _ ≤ T.card := hsize
    spaces := D.spaces
    witness := fun t ht => (D.witness t (hTD ht)).mono hPP
    projection := fun t ht d => D.projection t (hTD ht) d }
  have hl' : 1 ≤ l ∧ l ≤ ⌊Real.exp P⌋₊ := Finset.mem_Icc.mp hl
  refine ⟨E, l, hTD, rfl, hl'.1,
    (Nat.cast_le.mpr hl'.2).trans (Nat.floor_le (Real.exp_pos P).le), ?_⟩
  intro t ht
  change (D.witness t (hTD ht)).denominator = l
  simpa only [code, dite_eq_left (hTD ht)] using hconst t ht

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

noncomputable def horizontal (d : Fin (s + 1)) :
    Submodule ℚ (Fin 4 → W.rank.filtration.HigherHorizontal d.val) :=
  W.rank.filtration.horizontalImageOfSubmodule (D.spaces d) d.val

theorem horizontal_frequency (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, Fin 4 → W.rank.filtration.HigherHorizontal (d j).val)
    (hv : ∀ j, v j ∈ D.horizontal (d j)) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 0)) +
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 1)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 2)) -
      W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a
        (fun j => v j 3)) = 0 := by
  obtain ⟨t, ht⟩ := D.nonempty
  apply (R.interval ⟨t, D.subset ht⟩).refilteredHorizontalImage_frequency
    (D.witness t ht).index (D.witness t ht).subalgebra (fun j => (d j).val) a hd hr
    ((D.witness t ht).bracket n (fun j => (d j).val) a hd hr) v
  intro j
  rw [D.horizontalImage_eq t ht (d j)]
  exact hv j

theorem sunflower_bracket (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, W.rank.filtration.HigherHorizontal (d j).val)
    (hv : ∀ j, v j ∈ fourFirstProjection (D.horizontal (d j)))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : v j ∈ fourDependentProjection (D.horizontal (d j)))
    (hvk : v k ∈ fourDependentProjection (D.horizontal (d k))) :
    W.vertical.frequency (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a)
    (W.rank.filtration.horizontalTreeValue (fun j => (d j).val) a)
    (fun u j hj hu => W.rank.filtration.horizontalTreeValue_zero_of_leaf
      (fun j => (d j).val) a u (i := j) hj hu)
    W.vertical.frequency (map_zero _) (fun j => D.horizontal (d j))
    (D.horizontal_frequency n d a hd hr) v hv j k hjk hj hk hvj hvk

theorem sunflower_representatives (n : ℕ) (d : Fin n → Fin (s + 1)) (a : FreeMagma (Fin n))
    (hd : lieTreeWeight (fun j => (d j).val) a = s) (hr : a.length = r)
    (v : ∀ j, W.rank.filtration.layer (d j).val 1)
    (hv : ∀ j, W.rank.filtration.higherHorizontalMk (d j).val (v j) ∈
      fourFirstProjection (D.horizontal (d j)))
    (j k : Fin n) (hjk : j ≠ k) (hj : j ∈ lieTreeSupport a) (hk : k ∈ lieTreeSupport a)
    (hvj : W.rank.filtration.higherHorizontalMk (d j).val (v j) ∈
      fourDependentProjection (D.horizontal (d j)))
    (hvk : W.rank.filtration.higherHorizontalMk (d k).val (v k) ∈
      fourDependentProjection (D.horizontal (d k))) :
    W.vertical.frequency (lieTreeEval (fun j => (v j).val) a) = 0 := by
  have h := D.sunflower_bracket n d a hd hr
    (fun j => W.rank.filtration.higherHorizontalMk (d j).val (v j)) hv j k hjk hj hk hvj hvk
  rwa [W.rank.filtration.horizontalTreeValue_mk (fun j => (d j).val) a hd hr v] at h

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_common_rank_relation (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)}, 0 ≤ p → b ≤ p →
      (R : NativeRankRelation W out H p p) →
      Real.exp ((p + C) ^ C) ≤ N → Nonempty (R.CommonData ((p + C) ^ C)) := by
  classical
  obtain ⟨c, _, hcommon⟩ := exists_common_rank_interval_data s hs
  obtain ⟨C, hC, hbudget⟩ := exists_common_rank_relation_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ b p W out H hp hbp R hN
  let A := (p + c) ^ c
  have hsum : p + A ≤ (p + C) ^ C := hbudget p hp
  have hAQ : A ≤ (p + C) ^ C := by linarith
  obtain ⟨t₀, ht₀⟩ := R.quadruples_nonempty
  let : Nonempty R.quadruples := ⟨⟨t₀, ht₀⟩⟩
  have hlong (t : R.quadruples) (_ht : t ∈ (Finset.univ : Finset R.quadruples)) :
      Real.exp ((p + c) ^ c) ≤ ((R.interval t).length : ℝ) :=
    (R.interval t).length_exp_lower_bound ((Real.exp_le_exp.mpr hsum).trans hN)
  obtain ⟨K, T, _, hT, hsize, _, hdata⟩ :=
    hcommon hp hbp R.interval Finset.univ Finset.univ_nonempty hlong
  let e : R.quadruples ↪ (ZMod N × ZMod N × ZMod N) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Q := T.map e
  have hQR : Q ⊆ R.quadruples := by
    intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
    exact u.property
  have hQ : Q.Nonempty := by
    obtain ⟨u, hu⟩ := hT
    exact ⟨e u, Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩
  have hsize' : Real.exp (-A) * (R.quadruples.card : ℝ) ≤ (T.card : ℝ) := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hsize
  have hdensity : Real.exp (-(p + A)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ Q.card := by
    calc
      _ = Real.exp (-A) * (Real.exp (-p) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
        rw [show -(p + A) = -A + -p by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-A) * R.quadruples.card :=
        mul_le_mul_of_nonneg_left R.density (Real.exp_pos _).le
      _ ≤ T.card := hsize'
      _ = Q.card := by simp only [Q, Finset.card_map]
  have hwitness (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ Q) :
      ∃ E : (R.interval ⟨t, hQR ht⟩).SunflowerWitness ((p + C) ^ C),
        ∀ d : Fin (s + 1), E.projection d.val = K d := by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ht
    obtain ⟨E, hproj, _⟩ := hdata u hu
    exact ⟨E.mono hAQ, hproj⟩
  refine ⟨{
    quadruples := Q
    subset := hQR
    nonempty := hQ
    density := ?_
    spaces := K
    witness := fun t ht => Classical.choose (hwitness t ht)
    projection := fun t ht => Classical.choose_spec (hwitness t ht) }⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hsum))
    (by positivity)).trans hdensity

end Erdos3

end

section

namespace Erdos3

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_rank_relation (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q : ℝ),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
        p ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ R : NativeRankRelation W.family out H q q,
          Nonempty (R.CommonData ((p + C) ^ C)) := by
  obtain ⟨a, _, hrelation⟩ := exists_native_rank_relation s
  obtain ⟨c, _, hcommon⟩ := exists_common_rank_relation s hs
  obtain ⟨C, hC, hbudget⟩ := exists_native_common_rank_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hbase : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  obtain ⟨hqC, hcommonC⟩ := hbudget p hp
  obtain ⟨out, H, hHW, hH, hshort, hHsize, ⟨R⟩⟩ := hrelation W hf
  let R' : NativeRankRelation W.family out H q q := R.mono hbase hbase
  obtain ⟨D⟩ := hcommon hq hpq R' ((Real.exp_le_exp.mpr hcommonC).trans hN)
  refine ⟨out, H, q, hHW, hH, hshort, ?_, hpq, hqC, R', ⟨D.mono hcommonC⟩⟩
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg (hbase.trans hqC))) (Nat.cast_nonneg _)).trans hHsize

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem exists_bounded_coefficient_corrections (D : R.CommonData P) (hs : 1 ≤ s) (hP : 0 ≤ P)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (fun j => (W.fourRankBasis.baseChange ℝ).repr (Q α).val j) ∈
        realDenominatorGrid V.projectedDenominator) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        W.rank.filtration.realFourHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α)
            (V.projectedOrbitCoefficient α - E α - Q α) ∈
          (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩).baseChange ℝ := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := V.exists_bounded_coefficient_corrections hs hP
  refine ⟨E, Q, hE, hQ, ?_⟩
  intro α hα
  exact (congrArg (fun U => _ ∈ U.baseChange ℝ)
    (D.horizontalImage_eq t ht ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).mp
    (hres α)

end Erdos3.NativeRankRelation.CommonData

end

end OAI
