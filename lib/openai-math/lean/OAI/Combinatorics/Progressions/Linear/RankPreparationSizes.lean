/-
Modified for ProveIt: explicitly simplify the singleton coordinate sum in
RankPreparationLayer.initial_value on Lean 4.32. Upstream statements are unchanged.
-/
import OAI.Combinatorics.Progressions.Estimates.IntegralSlowSlice
import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification
import OAI.Combinatorics.Progressions.Geometry.CoordinateCopySum
import OAI.Combinatorics.Progressions.Linear.RankPreparationPotential

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

def rankCutDirectionHeight (ambient columns rows H R : ℕ) : ℕ :=
  (columns + 1) *
    (H * rationalKernelHeight (rows + 1) ((ambient + 1) * (R * H) ^ ambient)) ^ columns

theorem integerPolynomialQuotient_eval {I : Type*} (D : ℕ) (Q : MvPolynomial I ℤ)
    (x : I → ℤ) :
    MvPolynomial.eval (fun i => (x i : ℝ))
      (MvPolynomial.C (1 / (D : ℝ)) * MvPolynomial.map (Int.castRingHom ℝ) Q) =
      (MvPolynomial.eval x Q : ℝ) / D := by
  have he : (MvPolynomial.eval x Q : ℝ) =
      MvPolynomial.eval (fun i => (x i : ℝ)) (MvPolynomial.map (Int.castRingHom ℝ) Q) :=
    MvPolynomial.map_eval (Int.castRingHom ℝ) x Q
  rw [map_mul, MvPolynomial.eval_C, ← he]
  simp only [div_eq_mul_inv]
  ring

theorem exists_rankPreparationStep {I J C V : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype C] [Fintype V]
    (B : Matrix J C ℚ) (A : Matrix V J ℚ) (p : VectorPolynomial I ℝ (J → ℝ))
    (N : I → ℕ) {H R h : ℕ} {δ : ℝ}
    (hH : 1 ≤ H) (hR : 1 ≤ R) (hδ : 0 < δ) (hN : ∀ i, 0 < N i)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    (hA : ∀ i j, RationalHeightLE (A i j) R)
    (hp : DegreeLE (fun _ => 1) (h + 1) p)
    (hmem : ∀ α, coefficients p α ∈ jointRationalSpace B A)
    (hfail : ¬ HasLayerSamplingRank (h + 1) (fun i => (N i : ℝ)) R (jointRationalSpace B A) p)
    (f : (∀ i, Fin (N i)) → ℝ) :
    let W := jointRationalSpace B A
    let He := rankCutDirectionHeight (Fintype.card J) (Fintype.card C) (Fintype.card V) H R
    let K := (((h + 1 : ℕ) : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ (h + 1) *
      R * Fintype.card I * ((h + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((R * He ^ Fintype.card J : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (a : J → ℤ) (e : J → ℚ) (q : ℕ) (S : ResidueBoxSlice N q)
      (cut : VectorPolynomial I ℝ (J → ℝ)) (l E : MvPolynomial I ℝ)
      (integerPart : J → MvPolynomial I ℤ) (c : J → ℝ),
      cut = map (samplingRankProjection a (fun i => (e i : ℝ))) p ∧
      (∀ i, |(a i : ℝ)| ≤ R) ∧ (∀ i, RationalHeightLE (e i) He) ∧
      (fun i => (e i : ℝ)) ∈ W ∧ integerRowLinear a (fun i => (e i : ℝ)) = 1 ∧
      (∀ α, coefficients cut α ∈ W ⊓ LinearMap.ker (integerRowLinear a)) ∧
      DegreeLE (fun _ => 1) (h + 1) cut ∧ l.totalDegree ≤ h ∧ E.totalDegree ≤ h + 1 ∧
      Module.finrank ℝ ↥(W ⊓ LinearMap.ker (integerRowLinear a)) < Module.finrank ℝ W ∧
      0 < q ∧ q ≤ R * He ^ Fintype.card J ∧
      (∀ i, 0 < S.length i ∧ ρ * N i ≤ 4 * q * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (S.length i)), f (S.point j)) ∧
      (∀ i, (integerPart i).totalDegree ≤ h + 1) ∧
      ∀ (j : ∀ i, Fin (S.length i)) (i : J),
        |(MvPolynomial.eval (fun v => ((S.point j v).val : ℝ)) E -
            MvPolynomial.eval (fun v => (S.start v : ℝ)) E) * (e i : ℝ)| ≤ δ ∧
        eval (fun v => ((S.point j v).val : ℝ)) p i =
          eval (fun v => ((S.point j v).val : ℝ)) cut i +
            MvPolynomial.eval (fun v => ((S.point j v).val : ℝ)) l * (e i : ℝ) +
            (MvPolynomial.eval (fun v => ((j v).val : ℤ)) (integerPart i) : ℝ) + c i +
            (MvPolynomial.eval (fun v => ((S.point j v).val : ℝ)) E -
              MvPolynomial.eval (fun v => (S.start v : ℝ)) E) * (e i : ℝ) := by
  classical
  intro W He K ρ hlarge
  simp only [HasLayerSamplingRank, not_forall, not_not] at hfail
  obtain ⟨a, ha, hrow, happrox⟩ := hfail
  obtain ⟨e, heW, hae, heH⟩ := exists_bounded_joint_rational_direction B A a hH hR hB hA ha
    (by simpa only [integerRowLinear_apply] using hrow)
  obtain ⟨D, hD, hDR, Q, E, l, hQ, hE, hl, hcoeff, hsplit⟩ :=
    samplingRankCut_homogeneous_split a (fun i => (e i : ℝ)) p hp
      (fun i => by exact_mod_cast hN i) (Nat.cast_nonneg R) happrox
  have hDRnat : D ≤ R := by exact_mod_cast hDR
  have hlargeD (i : I) : 4 * ((D * He ^ Fintype.card J : ℕ) : ℝ) ≤ ρ * N i :=
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.mul_le_mul_right _ hDRnat))
      (by norm_num)).trans (hlarge i)
  obtain ⟨q, S, integerPart, c, hq, hqbound, hlength, hscore, hdegree, hparts⟩ :=
    exists_integral_slow_slice N Q E e hD (Nat.cast_nonneg R) hδ hQ.totalDegree_le
      hE.totalDegree_le heH hcoeff f hlargeD
  let cut := map (samplingRankProjection a (fun i => (e i : ℝ))) p
  refine ⟨a, e, q, S, cut, l, E, integerPart, c, rfl, ha, heH, heW, hae, ?_, hp.map _, hl,
    hE.totalDegree_le, samplingRankCut_finrank_lt a _ W heW hae, hq,
    hqbound.trans (Nat.mul_le_mul_right _ hDRnat), hlength, hscore, hdegree, ?_⟩
  · intro α
    rw [coefficients_map]
    exact samplingRankProjection_mem a _ W heW hae (hmem α)
  · intro j i
    obtain ⟨herror, hparts⟩ := hparts j i
    refine ⟨herror, ?_⟩
    have hv := congrArg (fun t : VectorPolynomial I ℝ (J → ℝ) =>
      eval (fun v => ((S.point j v).val : ℝ)) t i) hsplit
    simp only [map_add, eval_tmul, MvPolynomial.aeval_eq_eval, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hv
    have hr := integerPolynomialQuotient_eval D Q (fun v => ((S.point j v).val : ℤ))
    simp only [Int.cast_natCast] at hr
    rw [hr] at hv
    change eval (fun v => ((S.point j v).val : ℝ)) p i = _ at hv
    dsimp only [cut]
    linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators TensorProduct Matrix
open VectorPolynomial

structure RankPreparationLayer (I J : Type) where
  Coord : Type
  Column : Type
  Row : Type
  coordFinite : Fintype Coord
  columnFinite : Fintype Column
  rowFinite : Fintype Row
  label : Coord → J
  basis : Matrix Coord Column ℚ
  rows : Matrix Row Coord ℚ
  poly : VectorPolynomial I ℝ (Coord → ℝ)

attribute [instance] RankPreparationLayer.coordFinite RankPreparationLayer.columnFinite
  RankPreparationLayer.rowFinite

namespace RankPreparationLayer

variable {I J : Type}

noncomputable def space (L : RankPreparationLayer I J) : Submodule ℝ (L.Coord → ℝ) :=
  jointRationalSpace L.basis L.rows

noncomputable def rank (L : RankPreparationLayer I J) : ℕ := Module.finrank ℝ L.space

def Valid (L : RankPreparationLayer I J) (degree H R : ℕ) : Prop :=
  DegreeLE (fun _ => 1) degree L.poly ∧
  (∀ α, coefficients L.poly α ∈ L.space) ∧
  (∀ i j, RationalHeightLE (L.basis i j) H) ∧
  (∀ i j, RationalHeightLE (L.rows i j) R)

theorem Valid.mono_height {L : RankPreparationLayer I J} {d H H' R : ℕ}
    (h : L.Valid d H R) (hHH' : H ≤ H') : L.Valid d H' R :=
  ⟨h.1, h.2.1, fun i j => (h.2.2.1 i j).mono hHH', h.2.2.2⟩

noncomputable def value [DecidableEq J] (L : RankPreparationLayer I J) (x : I → ℝ) : J → ℝ :=
  coordinateCopySum L.label (eval x L.poly)

noncomputable def reindex (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    RankPreparationLayer I J := { L with poly := substitute f L.poly }

@[simp] theorem reindex_space (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).space = L.space := rfl

@[simp] theorem reindex_rank (L : RankPreparationLayer I J) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).rank = L.rank := rfl

theorem Valid.reindex {L : RankPreparationLayer I J} {d H R : ℕ}
    (hL : L.Valid d H R) (f : I → MvPolynomial I ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (L.reindex f).Valid d H R :=
  ⟨degreeLE_substitute_affine f hf L.poly hL.1,
    coefficients_substitute_mem L.space f L.poly hL.2.1, hL.2.2⟩

theorem reindex_value [DecidableEq J] (L : RankPreparationLayer I J)
    (f : I → MvPolynomial I ℝ) (x : I → ℝ) :
    (L.reindex f).value x = L.value (fun i => MvPolynomial.aeval (R := ℝ) x (f i)) := by
  exact congrArg (coordinateCopySum L.label) (eval_substitute f x L.poly)

noncomputable def cut (L : RankPreparationLayer I J) (a : L.Coord → ℤ) (e : L.Coord → ℝ) :
    RankPreparationLayer I J where
  Coord := L.Coord
  Column := L.Column
  Row := Option L.Row
  coordFinite := L.coordFinite
  columnFinite := L.columnFinite
  rowFinite := inferInstance
  label := L.label
  basis := L.basis
  rows := appendRankCutRow L.rows a
  poly := map (samplingRankProjection a e) L.poly

theorem cut_space (L : RankPreparationLayer I J) (a : L.Coord → ℤ) (e : L.Coord → ℝ) :
    (L.cut a e).space = L.space ⊓ LinearMap.ker (integerRowLinear a) :=
  jointRationalSpace_appendRankCutRow L.basis L.rows a

theorem Valid.cut {L : RankPreparationLayer I J} {d H R : ℕ}
    (hL : L.Valid d H R) (hR : 1 ≤ R) (a : L.Coord → ℤ) (e : L.Coord → ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ R) (he : e ∈ L.space) (hae : integerRowLinear a e = 1) :
    (L.cut a e).Valid d H R := by
  refine ⟨hL.1.map _, ?_, hL.2.2.1, ?_⟩
  · intro α
    rw [cut_space]
    change coefficients (map (samplingRankProjection a e) L.poly) α ∈ _
    rw [coefficients_map]
    exact samplingRankProjection_mem a e L.space he hae (hL.2.1 α)
  · exact appendRankCutRow_height L.rows a hR hL.2.2.2 ha

theorem cut_rank_lt (L : RankPreparationLayer I J) (a : L.Coord → ℤ) (e : L.Coord → ℝ)
    (he : e ∈ L.space) (hae : integerRowLinear a e = 1) :
    (L.cut a e).rank < L.rank := by
  unfold rank
  rw [cut_space]
  exact samplingRankCut_finrank_lt a e L.space he hae

noncomputable def appendLine (L : RankPreparationLayer I J) {C : Type} [Fintype C]
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) : RankPreparationLayer I J where
  Coord := L.Coord ⊕ C
  Column := Option L.Column
  Row := L.Row
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := L.rowFinite
  label := Sum.elim L.label label
  basis := copiedLayerMatrix L.basis e
  rows := copiedLayerRows L.rows
  poly := copiedLayerPolynomial L.poly (l ⊗ₜ[ℝ] (fun i => (e i : ℝ)))

theorem appendLine_space (L : RankPreparationLayer I J) {C : Type} [Fintype C]
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) :
    (L.appendLine label e l).space =
      copiedLayerSpace L.space (Submodule.span ℝ {fun i => (e i : ℝ)}) :=
  jointRationalSpace_copiedLayer L.basis L.rows e

theorem appendLine_rank (L : RankPreparationLayer I J) {C : Type} [Fintype C]
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) (he : (fun i => (e i : ℝ)) ≠ 0) :
    (L.appendLine label e l).rank = L.rank + 1 := by
  unfold rank
  rw [appendLine_space]
  exact copiedLayerSpace_line_finrank L.space _ he

theorem Valid.appendLine {L : RankPreparationLayer I J} {C : Type} [Fintype C]
    {d H R He : ℕ} (hL : L.Valid d H R) (hH : 1 ≤ H) (hR : 1 ≤ R)
    (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ)
    (he : ∀ i, RationalHeightLE (e i) He) (hl : l.totalDegree ≤ d) :
    (L.appendLine label e l).Valid d (max H He) R := by
  refine ⟨copiedLayerPolynomial_degree hL.1 (degreeLE_tmul_totalDegree l _ hl), ?_,
    copiedLayerMatrix_height L.basis e hH hL.2.2.1 he,
    copiedLayerRows_height L.rows hR hL.2.2.2⟩
  intro α
  rw [appendLine_space]
  apply copiedLayerPolynomial_mem L.space _ L.poly _ hL.2.1
  intro β
  rw [coefficients_tmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

theorem appendLine_value [DecidableEq J] (L : RankPreparationLayer I J)
    {C : Type} [Fintype C] (label : C → J) (e : C → ℚ) (l : MvPolynomial I ℝ) (x : I → ℝ) :
    (L.appendLine label e l).value x =
      L.value x + coordinateCopySum label (MvPolynomial.aeval (R := ℝ) x l • fun i => (e i : ℝ)) := by
  unfold value
  change coordinateCopySum (Sum.elim L.label label)
    (eval x (copiedLayerPolynomial L.poly (l ⊗ₜ[ℝ] (fun i => (e i : ℝ))))) = _
  rw [eval_copiedLayerPolynomial, eval_tmul, coordinateCopySum_sum]

noncomputable def empty : RankPreparationLayer I J where
  Coord := PEmpty
  Column := PEmpty
  Row := PEmpty
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := inferInstance
  label := PEmpty.elim
  basis := 0
  rows := 0
  poly := 0

theorem empty_valid (d H R : ℕ) : (empty : RankPreparationLayer I J).Valid d H R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _
    change coefficients (0 : VectorPolynomial I ℝ (PEmpty → ℝ)) α = 0
    simp only [map_zero, Finsupp.zero_apply]
  · intro α
    change coefficients (0 : VectorPolynomial I ℝ (PEmpty → ℝ)) α ∈ _
    simp only [map_zero, Finsupp.zero_apply]
    exact Submodule.zero_mem _
  · intro i
    exact i.elim
  · intro i
    exact i.elim

@[simp] theorem empty_rank : (empty : RankPreparationLayer I J).rank = 0 := by
  apply Module.finrank_zero_iff.mpr
  change Subsingleton (jointRationalSpace (0 : Matrix PEmpty PEmpty ℚ) 0)
  infer_instance

@[simp] theorem empty_value [DecidableEq J] (x : I → ℝ) :
    (empty : RankPreparationLayer I J).value x = 0 := by
  have hzero (y : PEmpty → ℝ) : coordinateCopySum (PEmpty.elim : PEmpty → J) y = 0 := by
    ext j
    simp only [coordinateCopySum_apply, Fintype.sum_empty, Pi.zero_apply]
  exact hzero _

noncomputable def initial [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : RankPreparationLayer I J where
  Coord := J
  Column := J
  Row := PEmpty
  coordFinite := inferInstance
  columnFinite := inferInstance
  rowFinite := inferInstance
  label := id
  basis := 1
  rows := 0
  poly := p

theorem initial_space [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : (initial p).space = ⊤ := by
  change jointRationalSpace (1 : Matrix J J ℚ) (0 : Matrix PEmpty J ℚ) = ⊤
  ext x
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change Matrix.of (fun i j => ((1 : Matrix J J ℚ) i j : ℝ)) *ᵥ x = x
      have hcast : Matrix.of (fun i j => ((1 : Matrix J J ℚ) i j : ℝ)) = 1 := by
        ext i j
        simp only [Matrix.of_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [hcast, Matrix.one_mulVec]
    · ext i
      exact i.elim

theorem initial_valid [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) {d H R : ℕ} (hH : 1 ≤ H)
    (hp : DegreeLE (fun _ => 1) d p) : (initial p).Valid d H R := by
  refine ⟨hp, ?_, ?_, ?_⟩
  · intro α
    rw [initial_space]
    trivial
  · change ∀ i j : J, RationalHeightLE ((1 : Matrix J J ℚ) i j) H
    intro i j
    change RationalHeightLE (if i = j then (1 : ℚ) else 0) H
    split_ifs
    · exact rationalHeightLE_one hH
    · exact rationalHeightLE_zero hH
  · intro i
    exact i.elim

@[simp] theorem initial_rank [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) : (initial p).rank = Fintype.card J := by
  unfold rank
  rw [initial_space]
  change Module.finrank ℝ (⊤ : Submodule ℝ (J → ℝ)) = Fintype.card J
  simp

@[simp] theorem initial_value [Fintype J] [DecidableEq J]
    (p : VectorPolynomial I ℝ (J → ℝ)) (x : I → ℝ) : (initial p).value x = eval x p := by
  ext j
  change (coordinateCopySum (R := ℝ) (id : J → J) (eval x p)) j = _
  simp only [coordinateCopySum_apply, id_eq]
  exact Finset.sum_ite_eq_of_mem' Finset.univ j (eval x p) (Finset.mem_univ j)

end RankPreparationLayer
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem rankCutDirectionHeight_le_exp (ambient columns rows H R : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (ha : (ambient : ℝ) ≤ p) (hc : (columns : ℝ) ≤ p)
    (hr : (rows : ℝ) + 1 ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (hR : (R : ℝ) ≤ Real.exp p) :
    (rankCutDirectionHeight ambient columns rows H R : ℝ) ≤ Real.exp ((p + 2) ^ 38) := by
  let Hsys := (ambient + 1) * (R * H) ^ ambient
  have hfront : (ambient : ℝ) + 1 ≤ Real.exp p :=
    (by linarith : (ambient : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hprod : (R : ℝ) * H ≤ Real.exp (2 * p) := by
    simpa only [two_mul, Real.exp_add] using mul_le_mul hR hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hsys : (Hsys : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
    have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg R) (Nat.cast_nonneg H)) hprod ambient
    rw [← Real.exp_nat_mul] at hpow
    have htotal : (Hsys : ℝ) ≤ Real.exp (p + ambient * (2 * p)) := by
      dsimp only [Hsys]
      push_cast
      rw [Real.exp_add]
      exact mul_le_mul hfront hpow (by positivity) (Real.exp_nonneg _)
    apply htotal.trans (Real.exp_le_exp.mpr ?_)
    have hm := mul_le_mul_of_nonneg_right ha (show 0 ≤ 2 * p by positivity)
    nlinarith [show 0 ≤ p ^ 3 by positivity]
  have hp3 : p ≤ (p + 2) ^ 3 := le_power_budget hp (by decide)
  have hker : (rationalKernelHeight (rows + 1) Hsys : ℝ) ≤ Real.exp ((p + 2) ^ 35) := by
    have h := rationalKernelHeight_le_budget (rows + 1) Hsys (by positivity : 0 ≤ (p + 2) ^ 3)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hr.trans hp3) hsys
    exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 3 7))
  have hp35 : p ≤ (p + 2) ^ 35 := le_power_budget hp (by decide)
  have hbase : (H : ℝ) * rationalKernelHeight (rows + 1) Hsys ≤ Real.exp ((p + 2) ^ 36) := by
    calc
      _ ≤ Real.exp p * Real.exp ((p + 2) ^ 35) :=
        mul_le_mul hH hker (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (p + (p + 2) ^ 35) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        calc
          p + (p + 2) ^ 35 ≤ 2 * (p + 2) ^ 35 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 35 := by gcongr; linarith
          _ = _ := by ring)
  have hpow : (((H * rationalKernelHeight (rows + 1) Hsys) ^ columns : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 37) := by
    push_cast
    apply (pow_le_pow_left₀ (by positivity) hbase columns).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (columns : ℝ) * (p + 2) ^ 36 ≤ (p + 2) * (p + 2) ^ 36 := by gcongr; linarith
      _ = _ := by ring
  have hcol : (columns : ℝ) + 1 ≤ Real.exp p :=
    (by linarith : (columns : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hp37 : p ≤ (p + 2) ^ 37 := le_power_budget hp (by decide)
  unfold rankCutDirectionHeight
  change (((columns + 1) * (H * rationalKernelHeight (rows + 1) Hsys) ^ columns : ℕ) : ℝ) ≤ _
  push_cast
  simp only [Nat.cast_pow, Nat.cast_mul] at hpow
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 37) := mul_le_mul hcol hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (p + 2) ^ 37) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      calc
        p + (p + 2) ^ 37 ≤ 2 * (p + 2) ^ 37 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 37 := by gcongr; linarith
        _ = _ := by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators
open VectorPolynomial

abbrev RankPreparationFamily (I J : Type) (s : ℕ) := Fin s → RankPreparationLayer I J

namespace RankPreparationFamily

variable {I J : Type} {s : ℕ}

noncomputable def value [DecidableEq J] (L : RankPreparationFamily I J s) (x : I → ℝ) : J → ℝ :=
  ∑ i, (L i).value x

noncomputable def potential (L : RankPreparationFamily I J s) : ℕ :=
  layerRankPotential (fun i => (L i).rank)

noncomputable def reindex (L : RankPreparationFamily I J s) (f : I → MvPolynomial I ℝ) :
    RankPreparationFamily I J s := fun i => (L i).reindex f

@[simp] theorem reindex_potential (L : RankPreparationFamily I J s) (f : I → MvPolynomial I ℝ) :
    (L.reindex f).potential = L.potential := rfl

theorem reindex_value [DecidableEq J] (L : RankPreparationFamily I J s)
    (f : I → MvPolynomial I ℝ) (x : I → ℝ) :
    (L.reindex f).value x = L.value (fun i => MvPolynomial.aeval (R := ℝ) x (f i)) := by
  apply Finset.sum_congr rfl
  intro i _
  exact (L i).reindex_value f x

noncomputable def descend (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ) :
    RankPreparationFamily I J s := fun i =>
  if i = upper then (L upper).cut a (fun i => (e i : ℝ))
  else if i = lower then (L lower).appendLine (L upper).label e l
  else L i

theorem descend_potential (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hlevel : upper.val = lower.val + 1)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ)
    (he : (fun i => (e i : ℝ)) ∈ (L upper).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1) :
    (L.descend upper lower a e l).potential + 1 ≤ L.potential := by
  have hne : upper ≠ lower := by intro h; rw [h] at hlevel; omega
  have he0 : (fun i => (e i : ℝ)) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hae
    norm_num at hae
  apply layerRankPotential_transfer upper lower hlevel
  intro i
  by_cases hiu : i = upper
  · subst i
    have hd := (L upper).cut_rank_lt a (fun i => (e i : ℝ)) he hae
    simpa [descend, Pi.single_apply, hne] using hd
  · by_cases hil : i = lower
    · subst i
      simp [descend, Ne.symm hne,
        RankPreparationLayer.appendLine_rank _ _ _ _ he0]
    · simp [descend, hiu, hil]

theorem descend_valid (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hne : upper ≠ lower) (H : Fin s → ℕ) {R He : ℕ}
    (hH : ∀ i, 1 ≤ H i) (hR : 1 ≤ R)
    (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ)
    (ha : ∀ i, |(a i : ℝ)| ≤ R) (heH : ∀ i, RationalHeightLE (e i) He)
    (he : (fun i => (e i : ℝ)) ∈ (L upper).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1)
    (hl : l.totalDegree ≤ lower.val + 1) :
    ∀ i, (L.descend upper lower a e l i).Valid (i.val + 1)
      (if i = lower then max (H i) He else H i) R := by
  intro i
  by_cases hiu : i = upper
  · subst i
    simpa [descend, hne] using
      (hL upper).cut hR a (fun i => (e i : ℝ)) ha he hae
  · by_cases hil : i = lower
    · subst i
      simpa [descend, Ne.symm hne] using
        (hL lower).appendLine (hH lower) hR (L upper).label e l heH hl
    · simpa [descend, hiu, hil] using hL i

theorem sum_replace_two {A V : Type*} [Fintype A] [DecidableEq A] [AddCommGroup V]
    (f : A → V) (u v : A) (hne : u ≠ v) (a b : V) :
    (∑ i, if i = u then a else if i = v then b else f i) =
      (∑ i, f i) + (a - f u) + (b - f v) := by
  calc
    _ = ∑ i, (f i + (if i = u then a - f u else 0) + (if i = v then b - f v else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hiu : i = u
      · subst i
        simp [hne]
      · by_cases hiv : i = v
        · subst i
          simp [Ne.symm hne]
        · simp [hiu, hiv]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem descend_value [DecidableEq J] (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hne : upper ≠ lower) (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ)
    (l : MvPolynomial I ℝ) (x : I → ℝ) :
    (L.descend upper lower a e l).value x = L.value x +
      ((L upper).cut a (fun i => (e i : ℝ))).value x - (L upper).value x +
      coordinateCopySum (L upper).label
        (MvPolynomial.aeval (R := ℝ) x l • fun i => (e i : ℝ)) := by
  have ht := sum_replace_two (fun i => (L i).value x) upper lower hne
    (((L upper).cut a (fun i => (e i : ℝ))).value x)
    (((L lower).appendLine (L upper).label e l).value x)
  have hsum : (L.descend upper lower a e l).value x =
      ∑ i, if i = upper then ((L upper).cut a (fun i => (e i : ℝ))).value x
        else if i = lower then ((L lower).appendLine (L upper).label e l).value x
        else (L i).value x := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [descend]
    split_ifs <;> rfl
  rw [hsum, ht, RankPreparationLayer.appendLine_value]
  unfold value
  abel

noncomputable def absorb (L : RankPreparationFamily I J s) (lowest : Fin s)
    (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ) : RankPreparationFamily I J s :=
  fun i => if i = lowest then (L lowest).cut a (fun i => (e i : ℝ)) else L i

theorem absorb_potential (L : RankPreparationFamily I J s) (lowest : Fin s)
    (hlowest : lowest.val = 0) (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ)
    (he : (fun i => (e i : ℝ)) ∈ (L lowest).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1) :
    (L.absorb lowest a e).potential + 1 ≤ L.potential := by
  apply layerRankPotential_absorb_constant lowest hlowest
  intro i
  by_cases hi : i = lowest
  · subst i
    have hd := (L lowest).cut_rank_lt a (fun i => (e i : ℝ)) he hae
    simpa [absorb, Pi.single_apply] using hd
  · simp [absorb, hi]

theorem absorb_valid (L : RankPreparationFamily I J s) (lowest : Fin s)
    (H : Fin s → ℕ) {R : ℕ} (hR : 1 ≤ R)
    (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ)
    (ha : ∀ i, |(a i : ℝ)| ≤ R)
    (he : (fun i => (e i : ℝ)) ∈ (L lowest).space)
    (hae : integerRowLinear a (fun i => (e i : ℝ)) = 1) :
    ∀ i, (L.absorb lowest a e i).Valid (i.val + 1) (H i) R := by
  intro i
  by_cases hi : i = lowest
  · subst i
    simpa [absorb] using (hL lowest).cut hR a (fun i => (e i : ℝ)) ha he hae
  · simpa [absorb, hi] using hL i

theorem sum_replace_one {A V : Type*} [Fintype A] [DecidableEq A] [AddCommGroup V]
    (f : A → V) (u : A) (a : V) :
    (∑ i, if i = u then a else f i) = (∑ i, f i) + (a - f u) := by
  calc
    _ = ∑ i, (f i + if i = u then a - f u else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = u
      · subst i; simp
      · simp [hi]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem absorb_value [DecidableEq J] (L : RankPreparationFamily I J s) (lowest : Fin s)
    (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ) (x : I → ℝ) :
    (L.absorb lowest a e).value x = L.value x +
      ((L lowest).cut a (fun i => (e i : ℝ))).value x - (L lowest).value x := by
  have ht := sum_replace_one (fun i => (L i).value x) lowest
    (((L lowest).cut a (fun i => (e i : ℝ))).value x)
  have hsum : (L.absorb lowest a e).value x =
      ∑ i, if i = lowest then ((L lowest).cut a (fun i => (e i : ℝ))).value x else (L i).value x := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [absorb]
    split_ifs <;> rfl
  rw [hsum, ht]
  unfold value
  abel

end RankPreparationFamily
end Erdos3

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

theorem exists_descend_slice_step {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s : ℕ} (L : RankPreparationFamily I J s) (upper lower : Fin s)
    (hlevel : upper.val = lower.val + 1) (N : I → ℕ) (H : Fin s → ℕ)
    {R : ℕ} {δ : ℝ} (hH : ∀ i, 1 ≤ H i) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (hfail : ¬ HasLayerSamplingRank (upper.val + 1) (fun i => (N i : ℝ)) R
      (L upper).space (L upper).poly) (f : (∀ i, Fin (N i)) → ℝ) :
    let He := rankCutDirectionHeight (Fintype.card (L upper).Coord)
      (Fintype.card (L upper).Column) (Fintype.card (L upper).Row) (H upper) R
    let K := (((upper.val + 1 : ℕ) : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ (upper.val + 1) *
      R * Fintype.card I * ((upper.val + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((R * He ^ Fintype.card (L upper).Coord : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ)
      (q : ℕ) (S : ResidueBoxSlice N q) (l : MvPolynomial I ℝ)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      let L' := (L.descend upper lower a e l).reindex S.polynomial
      (∀ i, |(a i : ℝ)| ≤ R) ∧ (∀ i, RationalHeightLE (e i) He) ∧
      L'.potential + 1 ≤ L.potential ∧
      (∀ i, (L' i).Valid (i.val + 1) (if i = lower then max (H i) He else H i) R) ∧
      0 < q ∧ q ≤ R * He ^ Fintype.card (L upper).Coord ∧
      (∀ i, 0 < S.length i ∧ ρ * N i ≤ 4 * q * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ upper.val + 1) ∧
      (∀ x j, |err x j| ≤ Fintype.card (L upper).Coord * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro He K ρ hlarge
  have hne : upper ≠ lower := by intro h; rw [h] at hlevel; omega
  obtain ⟨a, e, q, S, cut, l, E, ip, c, hcut, ha, heH, heW, hae, hmem, hdeg, hl, hE,
    hrank, hq, hqbound, hlength, hscore, hip, hparts⟩ :=
    exists_rankPreparationStep (L upper).basis (L upper).rows (L upper).poly N
      (hH upper) hR hδ hN (hL upper).2.2.1 (hL upper).2.2.2
      (hL upper).1 (hL upper).2.1 hfail f hlarge
  let V := L.descend upper lower a e l
  let L' := V.reindex S.polynomial
  let ip' : J → MvPolynomial I ℤ := coordinateCopySum (L upper).label ip
  let c' : J → ℝ := coordinateCopySum (L upper).label c
  let er (x : ∀ i, Fin (S.length i)) (j : (L upper).Coord) : ℝ :=
    (MvPolynomial.eval (fun i => ((S.point x i).val : ℝ)) E -
      MvPolynomial.eval (fun i => (S.start i : ℝ)) E) * (e j : ℝ)
  let er' (x : ∀ i, Fin (S.length i)) : J → ℝ := coordinateCopySum (L upper).label (er x)
  refine ⟨a, e, q, S, l, ip', c', er', ha, heH, ?_, ?_, hq, hqbound, hlength, hscore, ?_, ?_, ?_⟩
  · exact L.descend_potential upper lower hlevel a e l heW hae
  · intro i
    exact (L.descend_valid upper lower hne H hH hR hL a e l ha heH heW hae
      (by omega) i).reindex S.polynomial S.polynomial_degree
  · exact coordinateCopySum_polynomial_degree (L upper).label ip hip
  · intro x j
    exact coordinateCopySum_abs_le (L upper).label hδ.le (fun i => (hparts x i).1) j
  · intro x j
    let y : I → ℝ := fun i => ((S.point x i).val : ℝ)
    have hv : eval y (L upper).poly = eval y cut +
        MvPolynomial.eval y l • (fun i => (e i : ℝ)) +
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) + c + er x := by
      ext i
      exact (hparts x i).2
    have hcopy := congrArg (coordinateCopySum (L upper).label) hv
    simp only [map_add] at hcopy
    have hint : (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip' j) : ℝ) =
        coordinateCopySum (L upper).label
          (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j :=
      coordinateCopySum_map (L upper).label
        ((Int.castRingHom ℝ).comp (MvPolynomial.eval (fun v => ((x v).val : ℤ)))) ip j
    have hnew : L'.value (fun i => ((x i).val : ℝ)) = V.value y := by
      exact (reindex_value V S.polynomial _).trans (by simp only [ResidueBoxSlice.polynomial_eval]; rfl)
    have hdesc := L.descend_value upper lower hne a e l y
    rw [hcut] at hcopy
    have hcopyj := congrFun hcopy j
    have hdescj := congrFun hdesc j
    change L.value y j = L'.value (fun i => ((x i).val : ℝ)) j + _ + _ + _
    rw [hnew, hint]
    change (L upper).value y j =
      ((L upper).cut a (fun i => (e i : ℝ))).value y j +
      coordinateCopySum (L upper).label (MvPolynomial.eval y l • fun i => (e i : ℝ)) j +
      coordinateCopySum (L upper).label
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j + c' j + er' x j at hcopyj
    simp only [Pi.add_apply, Pi.sub_apply, MvPolynomial.aeval_eq_eval] at hdescj
    dsimp only [V] at *
    linarith

theorem exists_absorb_slice_step {I J : Type} [Fintype I] [DecidableEq I] [DecidableEq J]
    {s : ℕ} (L : RankPreparationFamily I J s) (lowest : Fin s)
    (hlowest : lowest.val = 0) (N : I → ℕ) (H : Fin s → ℕ)
    {R : ℕ} {δ : ℝ} (hH : ∀ i, 1 ≤ H i) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hN : ∀ i, 0 < N i) (hL : ∀ i, (L i).Valid (i.val + 1) (H i) R)
    (hfail : ¬ HasLayerSamplingRank (lowest.val + 1) (fun i => (N i : ℝ)) R
      (L lowest).space (L lowest).poly) (f : (∀ i, Fin (N i)) → ℝ) :
    let He := rankCutDirectionHeight (Fintype.card (L lowest).Coord)
      (Fintype.card (L lowest).Column) (Fintype.card (L lowest).Row) (H lowest) R
    let K := (((lowest.val + 1 : ℕ) : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ (lowest.val + 1) *
      R * Fintype.card I * ((lowest.val + 1 : ℕ) : ℝ) * He
    let ρ := min 1 (δ / (K + 1))
    (∀ i, 4 * ((R * He ^ Fintype.card (L lowest).Coord : ℕ) : ℝ) ≤ ρ * N i) →
    ∃ (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ)
      (q : ℕ) (S : ResidueBoxSlice N q)
      (ip : J → MvPolynomial I ℤ) (c : J → ℝ) (err : (∀ i, Fin (S.length i)) → J → ℝ),
      let L' := (L.absorb lowest a e).reindex S.polynomial
      (∀ i, |(a i : ℝ)| ≤ R) ∧ (∀ i, RationalHeightLE (e i) He) ∧
      L'.potential + 1 ≤ L.potential ∧
      (∀ i, (L' i).Valid (i.val + 1) (H i) R) ∧
      0 < q ∧ q ≤ R * He ^ Fintype.card (L lowest).Coord ∧
      (∀ i, 0 < S.length i ∧ ρ * N i ≤ 4 * q * S.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 x : (∀ i, Fin (S.length i)), f (S.point x)) ∧
      (∀ j, (ip j).totalDegree ≤ lowest.val + 1) ∧
      (∀ x j, |err x j| ≤ Fintype.card (L lowest).Coord * δ) ∧
      ∀ x j, L.value (fun i => ((S.point x i).val : ℝ)) j =
        L'.value (fun i => ((x i).val : ℝ)) j +
        (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip j) : ℝ) + c j + err x j := by
  classical
  intro He K ρ hlarge
  obtain ⟨a, e, q, S, cut, l, E, ip, c, hcut, ha, heH, heW, hae, hmem, hdeg, hl, hE,
    hrank, hq, hqbound, hlength, hscore, hip, hparts⟩ :=
    exists_rankPreparationStep (L lowest).basis (L lowest).rows (L lowest).poly N
      (hH lowest) hR hδ hN (hL lowest).2.2.1 (hL lowest).2.2.2
      (hL lowest).1 (hL lowest).2.1 hfail f hlarge
  have hconst : l = MvPolynomial.C (l.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega)
  let V := L.absorb lowest a e
  let L' := V.reindex S.polynomial
  let ip' : J → MvPolynomial I ℤ := coordinateCopySum (L lowest).label ip
  let c' : J → ℝ := coordinateCopySum (L lowest).label ((l.coeff 0) • (fun i => (e i : ℝ)) + c)
  let er (x : ∀ i, Fin (S.length i)) (j : (L lowest).Coord) : ℝ :=
    (MvPolynomial.eval (fun i => ((S.point x i).val : ℝ)) E -
      MvPolynomial.eval (fun i => (S.start i : ℝ)) E) * (e j : ℝ)
  let er' (x : ∀ i, Fin (S.length i)) : J → ℝ := coordinateCopySum (L lowest).label (er x)
  refine ⟨a, e, q, S, ip', c', er', ha, heH, ?_, ?_, hq, hqbound, hlength, hscore, ?_, ?_, ?_⟩
  · exact L.absorb_potential lowest hlowest a e heW hae
  · intro i
    exact (L.absorb_valid lowest H hR hL a e ha heW hae i).reindex S.polynomial S.polynomial_degree
  · exact coordinateCopySum_polynomial_degree (L lowest).label ip hip
  · intro x j
    exact coordinateCopySum_abs_le (L lowest).label hδ.le (fun i => (hparts x i).1) j
  · intro x j
    let y : I → ℝ := fun i => ((S.point x i).val : ℝ)
    have hv : eval y (L lowest).poly = eval y cut +
        MvPolynomial.eval y l • (fun i => (e i : ℝ)) +
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) + c + er x := by
      ext i
      exact (hparts x i).2
    have hel : MvPolynomial.eval y l = l.coeff 0 := by
      conv_lhs => rw [hconst]
      rw [MvPolynomial.eval_C]
    rw [hel] at hv
    have hcopy := congrArg (coordinateCopySum (L lowest).label) hv
    simp only [map_add] at hcopy
    have hint : (MvPolynomial.eval (fun i => ((x i).val : ℤ)) (ip' j) : ℝ) =
        coordinateCopySum (L lowest).label
          (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j :=
      coordinateCopySum_map (L lowest).label
        ((Int.castRingHom ℝ).comp (MvPolynomial.eval (fun v => ((x v).val : ℤ)))) ip j
    have hnew : L'.value (fun i => ((x i).val : ℝ)) = V.value y := by
      exact (reindex_value V S.polynomial _).trans (by simp only [ResidueBoxSlice.polynomial_eval]; rfl)
    have habs := L.absorb_value lowest a e y
    rw [hcut] at hcopy
    have hcopyj := congrFun hcopy j
    have habsj := congrFun habs j
    change L.value y j = L'.value (fun i => ((x i).val : ℝ)) j + _ + _ + _
    rw [hnew, hint]
    change (L lowest).value y j =
      ((L lowest).cut a (fun i => (e i : ℝ))).value y j +
      coordinateCopySum (L lowest).label ((l.coeff 0) • fun i => (e i : ℝ)) j +
      coordinateCopySum (L lowest).label
        (fun i => (MvPolynomial.eval (fun v => ((x v).val : ℤ)) (ip i) : ℝ)) j +
      coordinateCopySum (L lowest).label c j + er' x j at hcopyj
    simp only [Pi.add_apply, Pi.sub_apply] at habsj
    dsimp only [V, c'] at *
    simp only [map_add, Pi.add_apply]
    linarith

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

variable {I J : Type} {s : ℕ}

def Sized (L : RankPreparationFamily I J s) (D t : ℕ) : Prop :=
  ∀ i, Fintype.card (L i).Coord ≤ D * (t + 1) ^ (s - 1 - i.val) ∧
    Fintype.card (L i).Column ≤ D + t ∧ Fintype.card (L i).Row ≤ t

theorem Sized.mono {L : RankPreparationFamily I J s} {D t u : ℕ}
    (h : L.Sized D t) (htu : t ≤ u) : L.Sized D u := by
  intro i
  obtain ⟨hc, hb, hr⟩ := h i
  refine ⟨hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)), by omega, by omega⟩

theorem Sized.reindex {L : RankPreparationFamily I J s} {D t : ℕ}
    (h : L.Sized D t) (f : I → MvPolynomial I ℝ) : (L.reindex f).Sized D t := h

theorem copy_power_step (a d : ℕ) : a ^ (d + 1) + a ^ d ≤ (a + 1) ^ (d + 1) := by
  calc
    a ^ (d + 1) + a ^ d = a ^ d * (a + 1) := by rw [pow_succ]; ring
    _ ≤ (a + 1) ^ d * (a + 1) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
    _ = _ := (pow_succ _ _).symm

theorem Sized.descend {L : RankPreparationFamily I J s} {D t : ℕ} (h : L.Sized D t)
    (upper lower : Fin s) (hlevel : upper.val = lower.val + 1)
    (a : (L upper).Coord → ℤ) (e : (L upper).Coord → ℚ) (l : MvPolynomial I ℝ) :
    (L.descend upper lower a e l).Sized D (t + 1) := by
  have hne : upper ≠ lower := by intro heq; rw [heq] at hlevel; omega
  have hmono := h.mono (Nat.le_succ t)
  intro i
  by_cases hiu : i = upper
  · subst i
    simp only [RankPreparationFamily.descend, ↓reduceIte]
    change Fintype.card (L upper).Coord ≤ _ ∧ Fintype.card (L upper).Column ≤ _ ∧
      Fintype.card (Option (L upper).Row) ≤ _
    exact ⟨(hmono upper).1, (hmono upper).2.1, by simpa using Nat.add_le_add_right (h upper).2.2 1⟩
  · by_cases hil : i = lower
    · subst i
      simp only [RankPreparationFamily.descend, hiu, ↓reduceIte]
      change Fintype.card ((L lower).Coord ⊕ (L upper).Coord) ≤ _ ∧
        Fintype.card (Option (L lower).Column) ≤ _ ∧ Fintype.card (L lower).Row ≤ _
      have hd : s - 1 - lower.val = (s - 1 - upper.val) + 1 := by omega
      refine ⟨?_, ?_, (hmono lower).2.2⟩
      · rw [Fintype.card_sum]
        calc
          _ ≤ D * (t + 1) ^ (s - 1 - lower.val) + D * (t + 1) ^ (s - 1 - upper.val) :=
            Nat.add_le_add (h lower).1 (h upper).1
          _ = D * ((t + 1) ^ ((s - 1 - upper.val) + 1) + (t + 1) ^ (s - 1 - upper.val)) := by
            rw [hd, Nat.mul_add]
          _ ≤ D * (t + 1 + 1) ^ ((s - 1 - upper.val) + 1) :=
            Nat.mul_le_mul_left D (copy_power_step _ _)
          _ = _ := by rw [hd]
      · rw [Fintype.card_option]
        have hb := (h lower).2.1
        omega
    · simpa only [RankPreparationFamily.descend, hiu, hil, ↓reduceIte] using hmono i

theorem Sized.absorb {L : RankPreparationFamily I J s} {D t : ℕ} (h : L.Sized D t)
    (lowest : Fin s) (a : (L lowest).Coord → ℤ) (e : (L lowest).Coord → ℚ) :
    (L.absorb lowest a e).Sized D (t + 1) := by
  have hmono := h.mono (Nat.le_succ t)
  intro i
  by_cases hi : i = lowest
  · subst i
    simp only [RankPreparationFamily.absorb, ↓reduceIte]
    change Fintype.card (L lowest).Coord ≤ _ ∧ Fintype.card (L lowest).Column ≤ _ ∧
      Fintype.card (Option (L lowest).Row) ≤ _
    exact ⟨(hmono lowest).1, (hmono lowest).2.1, by simpa using Nat.add_le_add_right (h lowest).2.2 1⟩
  · simpa only [RankPreparationFamily.absorb, hi, ↓reduceIte] using hmono i

theorem Sized.uniform {L : RankPreparationFamily I J s} {D t T : ℕ}
    (h : L.Sized D t) (ht : t ≤ T) (i : Fin s) :
    Fintype.card (L i).Coord ≤ D * (T + 1) ^ s ∧
      Fintype.card (L i).Column ≤ D + T ∧ Fintype.card (L i).Row ≤ T := by
  have hm := h.mono ht
  refine ⟨(hm i).1.trans (Nat.mul_le_mul_left D ?_), (hm i).2⟩
  exact Nat.pow_le_pow_right (by omega) (by omega)

end Erdos3.RankPreparationFamily

end

end OAI
