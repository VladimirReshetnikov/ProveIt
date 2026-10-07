import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Combinatorics.Progressions.Linear.DualIdealSteps
import OAI.Combinatorics.Progressions.Nilpotent.RationalBCHProducts

namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

noncomputable def realDualBasis (b : Basis ι ℝ L) : Basis (ι ⊕ ι) ℝ (DualLieAlgebra L) :=
  (b.prod b).map dualRealCoordinates.symm

@[simp] theorem realDualBasis_inl (b : Basis ι ℝ L) (i : ι) :
    realDualBasis b (Sum.inl i) = dualConstantLie (b i) := by
  simp [realDualBasis, Basis.map_apply]

@[simp] theorem realDualBasis_inr (b : Basis ι ℝ L) (i : ι) :
    realDualBasis b (Sum.inr i) = dualInfinitesimal (b i) := by
  simp [realDualBasis, Basis.map_apply]

@[simp] theorem realDualBasis_repr_inl (b : Basis ι ℝ L) (x : DualLieAlgebra L) (i : ι) :
    (realDualBasis b).repr x (Sum.inl i) = b.repr (dualBaseLinear x) i := by
  simp [realDualBasis, Basis.map_repr]

@[simp] theorem realDualBasis_repr_inr (b : Basis ι ℝ L) (x : DualLieAlgebra L) (i : ι) :
    (realDualBasis b).repr x (Sum.inr i) = b.repr (dualTangentLinear x) i := by
  simp [realDualBasis, Basis.map_repr]

def dualStructureConstants (c : ι → ι → ι → ℚ) : (ι ⊕ ι) → (ι ⊕ ι) → (ι ⊕ ι) → ℚ
  | Sum.inl i, Sum.inl j, Sum.inl k => c i j k
  | Sum.inl i, Sum.inr j, Sum.inr k => c i j k
  | Sum.inr i, Sum.inl j, Sum.inr k => c i j k
  | _, _, _ => 0

theorem realDualBasis_structure (b : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ ℝ (c i j k) = b.repr ⁅b i, b j⁆ k)
    (i j k : ι ⊕ ι) :
    algebraMap ℚ ℝ (dualStructureConstants c i j k) =
      (realDualBasis b).repr ⁅realDualBasis b i, realDualBasis b j⁆ k := by
  cases i <;> cases j <;> cases k <;>
    simp [dualStructureConstants, dualBaseLinear_lie, dualTangentLinear_lie, ← hc]

theorem dualStructureConstants_height (c : ι → ι → ι → ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (i j k : ι ⊕ ι) :
    RationalHeightLE (dualStructureConstants c i j k) H := by
  cases i <;> cases j <;> cases k <;>
    first | exact hc _ _ _ | exact rationalHeightLE_zero hH

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

private theorem dual_basis_bound {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] (e : Basis ι ℝ L)
    (z : DualLieAlgebra L) (M : ℝ)
    (hb : ∀ i, |e.repr (dualBaseLinear z) i| ≤ M)
    (ht : ∀ i, |e.repr (dualTangentLinear z) i| ≤ M) :
    ∀ i, |(realDualBasis e).repr z i| ≤ M := by
  intro i
  cases i with
  | inl i => simpa only [realDualBasis_repr_inl] using hb i
  | inr i => simpa only [realDualBasis_repr_inr] using ht i

theorem exists_dual_coordinate_operation_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L]
      [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      (∀ z : DualGroup hnil,
        (∀ i, |e.repr (dualBaseLinear z.coord) i| ≤ Real.exp ((p + 2) ^ a)) →
        (∀ i, |e.repr (dualTangentLinear z.coord) i| ≤ Real.exp ((p + 2) ^ a)) →
        ∀ i, |e.repr (dualLogDerivative z) i| ≤ Real.exp ((p + C) ^ C)) ∧
      (∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
        (∀ i, |e.repr g.coord i| ≤ Real.exp ((p + 2) ^ a)) →
        (∀ i, |e.repr x i| ≤ Real.exp ((p + 2) ^ a)) →
        ∀ i, |e.repr (dualAdjoint g x) i| ≤ Real.exp ((p + C) ^ C)) := by
  have hproductExists := exists_bch_fixed_product_exp_bound s a 3
  obtain ⟨K, _, hproduct⟩ := hproductExists
  let B : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C K) ^ K
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ _ _ e c H p hnil hstructure hH hp hd hHp hc
  have hfinal : (2 * p + K) ^ K ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((2 * p + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a)
  have hdim : (Fintype.card (ι ⊕ ι) : ℝ) ≤ 2 * p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  have hproducts (rs : List (DualGroup hnil)) (hlen : rs.length ≤ 3)
      (hrs : ∀ r ∈ rs, ∀ i,
        |(realDualBasis e).repr r.coord i| ≤ Real.exp ((p + 2) ^ a)) :
      ∀ i, |(realDualBasis e).repr rs.prod.coord i| ≤ Real.exp ((p + C) ^ C) := by
    have hb := hproduct (realDualBasis e) (dualStructureConstants c) H (2 * p)
      (dualLie_lowerCentralSeries_eq_bot hnil) rs (realDualBasis_structure e c hstructure)
      (by positivity) hdim hlen (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
      (dualStructureConstants_height c hH hc) (fun r hr i => (hrs r hr i).trans hinput)
    exact fun i => (hb i).trans (Real.exp_le_exp.mpr hfinal)
  constructor
  · intro z hbase htangent i
    have hconst : ∀ j, |(realDualBasis e).repr
        ((dualConstantHom (dualBaseHom z))⁻¹).coord j| ≤ Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (-dualConstantLie (dualBaseLinear z.coord))) j| ≤ _
        simpa only [map_neg, dualBaseLinear_constant, Finsupp.neg_apply, abs_neg] using hbase j
      · intro j
        change |e.repr (dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord))) j| ≤ _
        simp only [map_neg, dualTangentLinear_constant, neg_zero, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
    have hinputs : ∀ r ∈ [z, (dualConstantHom (dualBaseHom z))⁻¹],
        ∀ j, |(realDualBasis e).repr r.coord j| ≤ Real.exp ((p + 2) ^ a) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dual_basis_bound e _ _ hbase htangent
      · exact hconst
    have hh := hproducts [z, (dualConstantHom (dualBaseHom z))⁻¹] (by simp) hinputs (Sum.inr i)
    simpa only [List.prod_cons, List.prod_nil, mul_one, realDualBasis_repr_inr, dualLogDerivative] using hh
  · intro g x hg hx i
    have hleft : ∀ j, |(realDualBasis e).repr (dualConstantHom g).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (dualConstantLie g.coord)) j| ≤ _
        simpa only [dualBaseLinear_constant] using hg j
      · intro j
        change |e.repr (dualTangentLinear (dualConstantLie g.coord)) j| ≤ _
        simp only [dualTangentLinear_constant, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
    have hmiddle : ∀ j, |(realDualBasis e).repr (dualTangentElement (hnil := hnil) x).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      apply dual_basis_bound
      · intro j
        change |e.repr (dualBaseLinear (dualInfinitesimal x)) j| ≤ _
        simp only [dualBaseLinear_infinitesimal, map_zero, Finsupp.zero_apply, abs_zero]
        exact Real.exp_nonneg _
      · intro j
        change |e.repr (dualTangentLinear (dualInfinitesimal x)) j| ≤ _
        simpa only [dualTangentLinear_infinitesimal] using hx j
    have hright : ∀ j, |(realDualBasis e).repr ((dualConstantHom g)⁻¹).coord j| ≤
        Real.exp ((p + 2) ^ a) := by
      intro j
      simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hleft j
    have hinputs : ∀ r ∈ [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹],
        ∀ j, |(realDualBasis e).repr r.coord j| ≤ Real.exp ((p + 2) ^ a) := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hleft
      · exact hmiddle
      · exact hright
    have hh := hproducts [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹]
      (by simp) hinputs (Sum.inr i)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc, realDualBasis_repr_inr, dualAdjoint] using hh

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def rationalDualBasis (b : Basis ι ℚ L) : Basis (ι ⊕ ι) ℚ (DualLieAlgebra L) :=
  (b.prod b).map dualCoordinates.symm

@[simp] theorem rationalDualBasis_inl (b : Basis ι ℚ L) (i : ι) :
    rationalDualBasis b (Sum.inl i) = dualConstantLie (b i) := by
  simp [rationalDualBasis, Basis.map_apply]

@[simp] theorem rationalDualBasis_inr (b : Basis ι ℚ L) (i : ι) :
    rationalDualBasis b (Sum.inr i) = dualInfinitesimal (b i) := by
  simp [rationalDualBasis, Basis.map_apply]

@[simp] theorem rationalDualBasis_repr_inl (b : Basis ι ℚ L) (x : DualLieAlgebra L) (i : ι) :
    (rationalDualBasis b).repr x (Sum.inl i) = b.repr (dualBaseLinear x) i := by
  simp [rationalDualBasis, Basis.map_repr]

@[simp] theorem rationalDualBasis_repr_inr (b : Basis ι ℚ L) (x : DualLieAlgebra L) (i : ι) :
    (rationalDualBasis b).repr x (Sum.inr i) = b.repr (dualTangentLinear x) i := by
  simp [rationalDualBasis, Basis.map_repr]

theorem rationalDualBasis_structure (b : Basis ι ℚ L) (i j k : ι ⊕ ι) :
    lieStructureConstants (L := DualLieAlgebra L) (rationalDualBasis b) i j k =
      dualStructureConstants (lieStructureConstants b) i j k := by
  cases i <;> cases j <;> cases k <;>
    simp [lieStructureConstants, dualStructureConstants, dualBaseLinear_lie, dualTangentLinear_lie]

theorem rationalDualBasis_structure_height (b : Basis ι ℚ L) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H) (i j k : ι ⊕ ι) :
    RationalHeightLE (lieStructureConstants (L := DualLieAlgebra L) (rationalDualBasis b) i j k) H := by
  rw [rationalDualBasis_structure]
  exact dualStructureConstants_height _ hH hc i j k

theorem rationalDualBasis_grid_iff [Fintype ι] (b : Basis ι ℚ L) (l : ℕ) (x : DualLieAlgebra L) :
    (rationalDualBasis b).equivFun x ∈ denominatorGrid l ↔
      b.equivFun (dualBaseLinear x) ∈ denominatorGrid l ∧
      b.equivFun (dualTangentLinear x) ∈ denominatorGrid l := by
  constructor
  · rintro ⟨a, ha⟩
    constructor
    · exact ⟨fun i => a (Sum.inl i), fun i => by
        simpa only [Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inl] using ha (Sum.inl i)⟩
    · exact ⟨fun i => a (Sum.inr i), fun i => by
        simpa only [Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inr] using ha (Sum.inr i)⟩
  · rintro ⟨⟨a, ha⟩, ⟨b', hb'⟩⟩
    refine ⟨Sum.elim a b', ?_⟩
    intro i
    cases i with
    | inl i => simpa only [Sum.elim_inl, Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inl] using ha i
    | inr i => simpa only [Sum.elim_inr, Basis.equivFun_apply, Pi.smul_apply, rationalDualBasis_repr_inr] using hb' i

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

theorem exists_rational_dual_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ z : DualGroup hnil,
          e.equivFun (dualBaseLinear z.coord) ∈ denominatorGrid l →
          e.equivFun (dualTangentLinear z.coord) ∈ denominatorGrid l →
          e.equivFun (dualLogDerivative z) ∈ denominatorGrid m) ∧
        (∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
          e.equivFun g.coord ∈ denominatorGrid l → e.equivFun x ∈ denominatorGrid l →
          e.equivFun (dualAdjoint g x) ∈ denominatorGrid m) := by
  have hproductsExists := exists_bch_rational_product_bound s 3
  obtain ⟨D, _, hproducts⟩ := hproductsExists
  let B : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C D) ^ D
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hH hp hd hHp hc l hl hlp
  have hp2 : p ≤ 2 * p := by linarith
  have hdim : (Fintype.card (ι ⊕ ι) : ℝ) ≤ 2 * p := by
    rw [Fintype.card_sum, Nat.cast_add]
    linarith
  have hdata := hproducts (rationalDualBasis e) H (2 * p) (dualLie_lowerCentralSeries_eq_bot hnil)
    (by positivity) hdim (hHp.trans (Real.exp_le_exp.mpr hp2))
    (rationalDualBasis_structure_height e hH hc) l hl (hlp.trans (Real.exp_le_exp.mpr hp2))
  obtain ⟨m, hm, hmp, hlm, hprod⟩ := hdata
  have hfinal : (2 * p + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hzero : (0 : ι → ℚ) ∈ denominatorGrid l := ⟨0, by intro i; simp⟩
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_, ?_⟩
  · intro z hb ht
    have hz := (rationalDualBasis_grid_iff e l z.coord).mpr ⟨hb, ht⟩
    have hconst : (rationalDualBasis e).equivFun (dualConstantHom (dualBaseHom z)).coord ∈
        denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualConstantLie (dualBaseLinear z.coord))) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualConstantLie (dualBaseLinear z.coord))) ∈ _
      simpa only [dualBaseLinear_constant, dualTangentLinear_constant, map_zero] using And.intro hb hzero
    have hinv : (rationalDualBasis e).equivFun ((dualConstantHom (dualBaseHom z))⁻¹).coord ∈
        denominatorGrid l := by
      simpa only [coord_inv, map_neg] using denominatorGrid_neg l hconst
    have hinputs : ∀ r ∈ [z, (dualConstantHom (dualBaseHom z))⁻¹],
        (rationalDualBasis e).equivFun r.coord ∈ denominatorGrid l := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hz
      · exact hinv
    have hout := (rationalDualBasis_grid_iff e m _).mp
      (hprod [z, (dualConstantHom (dualBaseHom z))⁻¹] (by simp) hinputs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, dualLogDerivative] using hout.2
  · intro g x hg hx
    have hleft : (rationalDualBasis e).equivFun (dualConstantHom g).coord ∈ denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualConstantLie g.coord)) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualConstantLie g.coord)) ∈ _
      simpa only [dualBaseLinear_constant, dualTangentLinear_constant, map_zero] using And.intro hg hzero
    have hmiddle : (rationalDualBasis e).equivFun (dualTangentElement (hnil := hnil) x).coord ∈
        denominatorGrid l := by
      apply (rationalDualBasis_grid_iff e l _).mpr
      change e.equivFun (dualBaseLinear (dualInfinitesimal x)) ∈ _ ∧
        e.equivFun (dualTangentLinear (dualInfinitesimal x)) ∈ _
      simpa only [dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, map_zero] using And.intro hzero hx
    have hright : (rationalDualBasis e).equivFun ((dualConstantHom g)⁻¹).coord ∈ denominatorGrid l := by
      simpa only [coord_inv, map_neg] using denominatorGrid_neg l hleft
    have hinputs : ∀ r ∈ [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹],
        (rationalDualBasis e).equivFun r.coord ∈ denominatorGrid l := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hleft
      · exact hmiddle
      · exact hright
    have hout := (rationalDualBasis_grid_iff e m _).mp
      (hprod [dualConstantHom g, dualTangentElement x, (dualConstantHom g)⁻¹] (by simp) hinputs)
    simpa only [List.prod_cons, List.prod_nil, mul_one, ← mul_assoc, dualAdjoint] using hout.2

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem real_dual_log_grid_of_rational (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (hlog : ∀ z : DualGroup hnil,
      e.equivFun (dualBaseLinear z.coord) ∈ denominatorGrid l →
      e.equivFun (dualTangentLinear z.coord) ∈ denominatorGrid l →
      e.equivFun (dualLogDerivative z) ∈ denominatorGrid m)
    (z : DualGroup (realification_lowerCentralSeries_eq_bot hnil))
    (hb : (e.baseChange ℝ).equivFun (dualBaseLinear z.coord) ∈ realDenominatorGrid l)
    (ht : (e.baseChange ℝ).equivFun (dualTangentLinear z.coord) ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (dualLogDerivative z) ∈ realDenominatorGrid m := by
  obtain ⟨a, ha, hea⟩ := real_grid_exists_rationalLieInclusion e l hl _ hb
  obtain ⟨b, hb, heb⟩ := real_grid_exists_rationalLieInclusion e l hl _ ht
  let q : DualGroup hnil := ⟨dualConstantLie a + dualInfinitesimal b⟩
  have hqa : dualBaseLinear q.coord = a := by
    change dualBaseLinear (dualConstantLie a + dualInfinitesimal b) = a
    simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]
  have hqb : dualTangentLinear q.coord = b := by
    change dualTangentLinear (dualConstantLie a + dualInfinitesimal b) = b
    simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]
  have hq := hlog q (by rwa [hqa]) (by rwa [hqb])
  have he : rationalLieInclusion (dualLogDerivative q) = dualLogDerivative z := by
    apply dualLinearLift_logDerivative_eq (realification_lowerCentralSeries_eq_bot hnil)
      (⊤ : LieIdeal ℚ L) rationalLieInclusion rationalLieInclusion.toLinearMap
      (fun x y _ => rationalLieInclusion.map_lie x y) q (by trivial) z
    apply dual_ext
    · rw [dualLinearLift_base, hqa]
      exact hea
    · rw [dualLinearLift_tangent, hqb]
      exact heb
  change (fun i => (e.baseChange ℝ).repr (dualLogDerivative z) i) ∈ realDenominatorGrid m
  rw [← he]
  simp_rw [rationalLieInclusion_coordinates]
  exact (real_cast_mem_denominatorGrid_iff m _).mpr hq

theorem real_dual_adjoint_grid_of_rational (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (had : ∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
      e.equivFun g.coord ∈ denominatorGrid l → e.equivFun x ∈ denominatorGrid l →
      e.equivFun (dualAdjoint g x) ∈ denominatorGrid m)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (x : ℝ ⊗[ℚ] L)
    (hg : (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l)
    (hx : (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (dualAdjoint g x) ∈ realDenominatorGrid m := by
  obtain ⟨a, ha, hea⟩ := real_grid_exists_rationalLieInclusion e l hl _ hg
  obtain ⟨b, hb, heb⟩ := real_grid_exists_rationalLieInclusion e l hl _ hx
  let q : NilpotentLieBCHGroup L s hnil := ⟨a⟩
  have hq := had q b ha hb
  have he : rationalLieInclusion (dualAdjoint q b) = dualAdjoint g x :=
    dualLinearLift_adjoint_eq (realification_lowerCentralSeries_eq_bot hnil)
      (⊤ : LieIdeal ℚ L) rationalLieInclusion rationalLieInclusion.toLinearMap
      (fun u v _ => rationalLieInclusion.map_lie u v) q b (by trivial) g x hea heb
  change (fun i => (e.baseChange ℝ).repr (dualAdjoint g x) i) ∈ realDenominatorGrid m
  rw [← he]
  simp_rw [rationalLieInclusion_coordinates]
  exact (real_cast_mem_denominatorGrid_iff m _).mpr hq

theorem exists_real_dual_operation_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥),
      1 ≤ H → 0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        (∀ z : DualGroup (realification_lowerCentralSeries_eq_bot hnil),
          (e.baseChange ℝ).equivFun (dualBaseLinear z.coord) ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualTangentLinear z.coord) ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualLogDerivative z) ∈ realDenominatorGrid m) ∧
        (∀ (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
          (x : ℝ ⊗[ℚ] L),
          (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
          (e.baseChange ℝ).equivFun (dualAdjoint g x) ∈ realDenominatorGrid m) := by
  have hratExists := exists_rational_dual_operation_grid s
  obtain ⟨C, hC, hrat⟩ := hratExists
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hnil hH hp hd hHp hc l hl hlp
  have hdata := hrat e H p hnil hH hp hd hHp hc l hl hlp
  obtain ⟨m, hm, hmp, hlm, hlog, had⟩ := hdata
  exact ⟨m, hm, hmp, hlm, real_dual_log_grid_of_rational e l m hl hlog,
    real_dual_adjoint_grid_of_rational e l m hl had⟩

end Erdos3

end

end OAI
