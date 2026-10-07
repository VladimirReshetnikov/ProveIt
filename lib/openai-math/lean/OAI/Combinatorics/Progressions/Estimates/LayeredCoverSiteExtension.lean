import OAI.Combinatorics.Progressions.Geometry.CoefficientDeckChartRecovery
import OAI.Combinatorics.Progressions.Geometry.NormalizedCoveredChart
import OAI.Combinatorics.Progressions.Geometry.SeparatedChartExtension
import OAI.Combinatorics.Progressions.Lattices.CircleResiduePartition

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable (q : ℕ) [NeZero q]

noncomputable def circleQuarterCover (a : ZMod q) (x : ℝ) : UnitAddCircle :=
  ZMod.toAddCircle a + ((x / q : ℝ) : UnitAddCircle)

theorem circleQuarterCover_zero (a : ZMod q) :
    circleQuarterCover q a 0 = ZMod.toAddCircle a := by
  simp only [circleQuarterCover, zero_div, AddCircle.coe_zero, add_zero]

theorem circleQuarterCover_dist (a : ZMod q) {x y : ℝ}
    (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (q : ℝ) * dist (circleQuarterCover q a x) (circleQuarterCover q a y) = dist x y := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxy : |x - y| ≤ 1 / 2 := by
    have htri : |x - y| ≤ |x| + |y| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
    linarith
  have hsmall : |(x - y) / q| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hq]
    exact (div_le_iff₀ hq).mpr (hxy.trans (by linarith))
  have hn : ‖(((x - y) / q : ℝ) : UnitAddCircle)‖ = |(x - y) / q| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).mpr (by simpa using hsmall)
  unfold circleQuarterCover
  rw [dist_add_left, dist_eq_norm, ← AddCircle.coe_sub, ← sub_div, hn,
    abs_div, abs_of_pos hq, mul_div_cancel₀ _ hq.ne', Real.dist_eq]

theorem circleQuarterCover_center_dist (a : ZMod q) {x : ℝ} (hx : |x| ≤ 1 / 4) :
    (q : ℝ) * dist (circleQuarterCover q a x) (ZMod.toAddCircle a) ≤ 1 / 4 := by
  have h := circleQuarterCover_dist q a hx (by norm_num : |(0 : ℝ)| ≤ 1 / 4)
  rw [circleQuarterCover_zero, Real.dist_eq, sub_zero] at h
  exact h.le.trans hx

theorem circleQuarterCover_separated {a b : ZMod q} (hab : a ≠ b) {x y : ℝ}
    (hx : |x| ≤ 1 / 4) (hy : |y| ≤ 1 / 4) :
    (1 : ℝ) ≤ (2 * q) * dist (circleQuarterCover q a x) (circleQuarterCover q b y) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have ha := circleQuarterCover_center_dist q a hx
  have hb := circleQuarterCover_center_dist q b hy
  rw [dist_comm] at ha
  have ht : dist (ZMod.toAddCircle a) (ZMod.toAddCircle b) ≤
      dist (ZMod.toAddCircle a) (circleQuarterCover q a x) +
        dist (circleQuarterCover q a x) (circleQuarterCover q b y) +
          dist (circleQuarterCover q b y) (ZMod.toAddCircle b) := by
    linarith [dist_triangle (ZMod.toAddCircle a) (circleQuarterCover q a x) (ZMod.toAddCircle b),
      dist_triangle (circleQuarterCover q a x) (circleQuarterCover q b y) (ZMod.toAddCircle b)]
  have hs := CircleFourier.one_le_mul_dist_toAddCircle hab
  have hm := mul_le_mul_of_nonneg_left ht hq
  nlinarith

noncomputable def quarterCoverPoint {D : Type*} (a : D → ZMod q) (x : D → ℝ) :
    D → UnitAddCircle := fun i => circleQuarterCover q (a i) (x i)

theorem quarterCoverPoint_intCast {D : Type*} (a : D → ℤ) (x : D → ℝ) :
    quarterCoverPoint q (fun i => (a i : ZMod q)) x =
      fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle) := by
  funext i
  change ZMod.toAddCircle (a i : ZMod q) + ((x i / q : ℝ) : UnitAddCircle) = _
  rw [ZMod.toAddCircle_intCast, ← AddCircle.coe_add, ← add_div]

theorem quarterCoverPoint_within {D : Type*} [Fintype D] (a : D → ZMod q) {x y : D → ℝ}
    (hx : ∀ i, |x i| ≤ 1 / 4) (hy : ∀ i, |y i| ≤ 1 / 4) :
    dist x y ≤ (q : ℝ) * dist (quarterCoverPoint q a x) (quarterCoverPoint q a y) := by
  apply (dist_pi_le_iff (mul_nonneg (Nat.cast_nonneg q) dist_nonneg)).mpr
  intro i
  calc
    dist (x i) (y i) = (q : ℝ) * dist (circleQuarterCover q (a i) (x i))
        (circleQuarterCover q (a i) (y i)) := (circleQuarterCover_dist q (a i) (hx i) (hy i)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dist_le_pi_dist (quarterCoverPoint q a x) (quarterCoverPoint q a y) i) (Nat.cast_nonneg q)

theorem quarterCoverPoint_separated {D : Type*} [Fintype D] {a b : D → ZMod q} (hab : a ≠ b)
    {x y : D → ℝ} (hx : ∀ i, |x i| ≤ 1 / 4) (hy : ∀ i, |y i| ≤ 1 / 4) :
    (1 : ℝ) ≤ (2 * q) * dist (quarterCoverPoint q a x) (quarterCoverPoint q b y) := by
  obtain ⟨i, hi⟩ := not_forall.mp (fun h : ∀ i, a i = b i => hab (funext h))
  exact (circleQuarterCover_separated q hi (hx i) (hy i)).trans
    (mul_le_mul_of_nonneg_left
      (dist_le_pi_dist (quarterCoverPoint q a x) (quarterCoverPoint q b y) i) (by positivity))

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_quarter_cover_extension {D : Type*} [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧
      (∀ a x, (∀ i, |x i| ≤ 1 / 4) → g (quarterCoverPoint q a x) = f a x) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_bounded_extension_on_separated_charts
    (quarterCoverPoint (D := D) q) {x | ∀ i, |x i| ≤ 1 / 4}
    (q : ℝ≥0) (2 * q) L B
    (fun a x hx y hy => quarterCoverPoint_within q a hx hy)
    (by
      intro a b hab x hx y hy
      simpa using quarterCoverPoint_separated q hab hx hy)
    f (fun a => (hf a).lipschitzOnWith) (fun a x _ => hb a x)
  refine ⟨g, ?_, hvalue, hbound⟩
  have heq : 2 * B * (2 * (q : ℝ≥0)) = 4 * B * q := by ring
  simpa only [heq] using hg

theorem exists_integer_quarter_cover_extension {D : Type*} [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (a : D → ℤ) (x : D → ℝ), (∀ i, |x i| ≤ 1 / 4) →
        g (fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle)) = f (fun i => (a i : ZMod q)) x := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_quarter_cover_extension q f L B hf hb
  refine ⟨g, hg, hbound, ?_⟩
  intro a x hx
  rw [← quarterCoverPoint_intCast]
  exact hvalue (fun i => (a i : ZMod q)) x hx

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_parametric_quarter_cover_extension
    {Y D : Type*} [PseudoMetricSpace Y] [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → Y × (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : Y × (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧
      (∀ a y x, (∀ i, |x i| ≤ 1 / 4) → g (y, quarterCoverPoint q a x) = f a (y, x)) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  let chart : (D → ZMod q) → Y × (D → ℝ) → Y × (D → UnitAddCircle) :=
    fun a p => (p.1, quarterCoverPoint q a p.2)
  let Q : Set (Y × (D → ℝ)) := {p | ∀ i, |p.2 i| ≤ 1 / 4}
  have hwithin (a : D → ZMod q) (x : Y × (D → ℝ)) (hx : x ∈ Q)
      (y : Y × (D → ℝ)) (hy : y ∈ Q) :
      dist x y ≤ (max 1 (q : ℝ≥0) : ℝ) * dist (chart a x) (chart a y) := by
    have hK1 : (1 : ℝ) ≤ (max 1 (q : ℝ≥0) : ℝ) := by
      exact_mod_cast le_max_left (1 : ℝ≥0) (q : ℝ≥0)
    have hKq : (q : ℝ) ≤ (max 1 (q : ℝ≥0) : ℝ) := by
      exact_mod_cast le_max_right (1 : ℝ≥0) (q : ℝ≥0)
    change max (dist x.1 y.1) (dist x.2 y.2) ≤
      (max 1 (q : ℝ≥0) : ℝ) * max (dist x.1 y.1)
        (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q a y.2))
    apply max_le
    · calc
        dist x.1 y.1 ≤ max (dist x.1 y.1)
            (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q a y.2)) := le_max_left _ _
        _ = 1 * max (dist x.1 y.1)
            (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q a y.2)) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hK1 (le_trans dist_nonneg (le_max_left _ _))
    · exact (quarterCoverPoint_within q a hx hy).trans
        (mul_le_mul hKq (le_max_right _ _) dist_nonneg (by positivity))
  have hsep (a b : D → ZMod q) (hab : a ≠ b)
      (x : Y × (D → ℝ)) (hx : x ∈ Q) (y : Y × (D → ℝ)) (hy : y ∈ Q) :
      (1 : ℝ) ≤ (2 * (q : ℝ≥0) : ℝ≥0) * dist (chart a x) (chart b y) := by
    have h := quarterCoverPoint_separated q hab hx hy
    change (1 : ℝ) ≤ (2 * (q : ℝ)) * max (dist x.1 y.1)
      (dist (quarterCoverPoint q a x.2) (quarterCoverPoint q b y.2))
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_bounded_extension_on_separated_charts
    chart Q (max 1 q) (2 * q) L B hwithin hsep f
    (fun a => (hf a).lipschitzOnWith) (fun a x _ => hb a x)
  refine ⟨g, ?_, fun a y x hx => hvalue a (y, x) hx, hbound⟩
  have heq : 2 * B * (2 * (q : ℝ≥0)) = 4 * B * q := by ring
  simpa only [heq] using hg

theorem exists_parametric_integer_quarter_cover_extension
    {Y D : Type*} [PseudoMetricSpace Y] [Fintype D] (q : ℕ) [NeZero q]
    (f : (D → ZMod q) → Y × (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hb : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : Y × (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧
      (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (a : D → ℤ) (y : Y) (x : D → ℝ), (∀ i, |x i| ≤ 1 / 4) →
        g (y, fun i => ((((a i : ℝ) + x i) / q : ℝ) : UnitAddCircle)) =
          f (fun i => (a i : ZMod q)) (y, x) := by
  obtain ⟨g, hg, hvalue, hbound⟩ := exists_parametric_quarter_cover_extension q f L B hf hb
  refine ⟨g, hg, hbound, ?_⟩
  intro a y x hx
  rw [← quarterCoverPoint_intCast]
  exact hvalue (fun i => (a i : ZMod q)) y x hx

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix NNReal Classical

variable {D I : Type*} [Fintype D] [DecidableEq D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D))
variable (bW : Basis I ℤ (latticeSection (standardEuclideanLattice D) W))
variable (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (q : ℕ) [NeZero q]

theorem exists_normalized_sheet_residue_map :
    ∃ r : (D → ZMod q) → (Fin n → ZMod q), ∀ (z : Fin n → ℤ) (w : I → ℤ),
      r (fun i => (latticeDeckInteger W bW b hb z w i : ZMod q)) = fun i => (z i : ZMod q) := by
  obtain ⟨A, _hA, hres⟩ := standardLatticeCoordinates_residue W bW b hb q
  refine ⟨fun a i => (integerResidueMatrix A q *ᵥ a) (Sum.inl i), ?_⟩
  intro z w
  funext i
  change (integerResidueMatrix A q *ᵥ
    integerResidueMap D q (latticeDeckInteger W bW b hb z w)) (Sum.inl i) = _
  rw [← hres, latticeDeckInteger_coordinates]
  rfl

omit [DecidableEq D] in
theorem exists_normalized_representative_offset (u : W) (x : W × (Fin n → ℤ))
    (hu : (QuotientAddGroup.mk u : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
      normalizedLatticeQuotient W b hb x) :
    ∃ w : I → ℤ, normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val = u := by
  have hmem : u - normalizedLatticeRepresentative W b hb x ∈
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup :=
    QuotientAddGroup.eq_iff_sub_mem.mp (hu.trans (normalizedLatticeRepresentative_mk W b hb x).symm)
  let c : latticeSection (standardEuclideanLattice D) W := ⟨u - normalizedLatticeRepresentative W b hb x, hmem⟩
  refine ⟨bW.equivFun c, ?_⟩
  rw [LinearEquiv.symm_apply_apply]
  change _ + (u - _) = u
  abel

theorem exists_normalized_cover_site_extension
    (f : (Fin n → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (x : W × (Fin n → ℤ)) (w : I → ℤ),
        (∀ i, |normalizedLatticePoint W b x i| ≤ 1 / 4) →
        g (fun i => (((normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val).val i /
          q : ℝ) : UnitAddCircle)) =
          f (fun i => (x.2 i : ZMod q)) (fun i => normalizedLatticePoint W b x i) := by
  obtain ⟨r, hr⟩ := exists_normalized_sheet_residue_map W bW b hb q
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_integer_quarter_cover_extension q
    (fun a x => f (r a) x) L B (fun a => hf (r a)) (fun a x => hbound (r a) x)
  refine ⟨g, hg, hgb, ?_⟩
  intro x w hx
  have heq := hvalue (latticeDeckInteger W bW b hb x.2 w)
    (fun i => normalizedLatticePoint W b x i) hx
  rw [hr] at heq
  have hpoint : (fun i =>
      ((((latticeDeckInteger W bW b hb x.2 w i : ℝ) + normalizedLatticePoint W b x i) / q : ℝ) : UnitAddCircle)) =
      fun i => (((normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val).val i / q : ℝ) : UnitAddCircle) := by
    funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ D => v i) (normalizedDeckPoint_identity W bW b hb x w)
    change (normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val).val i =
      normalizedLatticePoint W b x i + (latticeDeckInteger W bW b hb x.2 w i : ℝ) at hi
    rw [hi, add_comm (latticeDeckInteger W bW b hb x.2 w i : ℝ)]
  simpa only [hpoint] using heq

include bW in
theorem exists_normalized_quotient_cover_site_extension
    (f : (Fin n → ZMod q) → (D → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (D → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (u : W) (x : W × (Fin n → ℤ)),
        (QuotientAddGroup.mk u : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
          normalizedLatticeQuotient W b hb x →
        (∀ i, |normalizedLatticePoint W b x i| ≤ 1 / 4) →
        g (fun i => ((u.val i / q : ℝ) : UnitAddCircle)) =
          f (fun i => (x.2 i : ZMod q)) (fun i => normalizedLatticePoint W b x i) := by
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_normalized_cover_site_extension W bW b hb q f L B hf hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro u x hu hx
  obtain ⟨w, hw⟩ := exists_normalized_representative_offset W bW b hb u x hu
  simpa only [hw] using hvalue x w hx

end Erdos3

end

section

namespace Erdos3

open Module Submodule

theorem exists_covered_representative_offset
    {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (d : ℕ) [NeZero d] (u : W) (x : W × (Fin n → ℤ)) (r : E → ZMod d)
    (hu : (QuotientAddGroup.mk u : W ⧸
      (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) =
        normalizedCoveredChart W b hb bW d (x, r)) :
    ∃ w : E → ℤ, normalizedLatticeRepresentative W b hb x + (bW.equivFun.symm w).val =
        (d : ℝ) • u ∧ integerResidueMap E d w = r := by
  let Γ := (latticeSection (standardEuclideanLattice D) W).toAddSubgroup
  let e := coverKernelBasisEquiv Γ bW d (NeZero.pos d)
  have hp := congrArg (quotientIntegerCover Γ d) hu
  change quotientIntegerCover Γ d (QuotientAddGroup.mk' Γ u) =
    quotientIntegerCover Γ d (normalizedCoverLift W b hb d x + (e r).val) at hp
  rw [quotientIntegerCover_mk, map_add, (e r).property, add_zero,
    normalizedCoverLift_projection W b hb d (NeZero.pos d)] at hp
  obtain ⟨w, hw⟩ := exists_normalized_representative_offset W bW b hb ((d : ℝ) • u) x hp
  refine ⟨w, hw, ?_⟩
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have he := normalizedCoverLift_add_deck W bW b hb d (NeZero.pos d) x w
  rw [hw, smul_smul, inv_mul_cancel₀ hd0, one_smul] at he
  have hsum : normalizedCoverLift W b hb d x + (e (integerResidueMap E d w)).val =
      normalizedCoverLift W b hb d x + (e r).val := he.trans hu
  apply e.injective
  exact Subtype.ext (add_left_cancel hsum)

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped NNReal Classical

variable {M : Type*} [Fintype M] {D E : M → Type*}
variable [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)]
variable {n : M → ℕ}
variable (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
variable (q : ℕ) [NeZero q]

local notation "ambient" => (Σ j : M, D j)

include bW in
theorem exists_layered_cover_site_extension
    (f : (∀ j, Fin (n j) → ZMod q) → (ambient → ℝ) → ℂ) (L B : ℝ≥0)
    (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a x, ‖f a x‖ ≤ B) :
    ∃ g : (ambient → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (u : ∀ j, W j) (x : ∀ j, W j × (Fin (n j) → ℤ)),
        (∀ j, (QuotientAddGroup.mk (u j) : W j ⧸
          (latticeSection (standardEuclideanLattice (D j)) (W j)).toAddSubgroup) =
            normalizedLatticeQuotient (W j) (b j) (hb j) (x j)) →
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (fun a => ((((u a.1).val a.2) / q : ℝ) : UnitAddCircle)) =
          f (fun j i => ((x j).2 i : ZMod q))
            (fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  choose r hr using (fun j => exists_normalized_sheet_residue_map (W j) (bW j) (b j) (hb j) q)
  let R : (ambient → ZMod q) → (∀ j, Fin (n j) → ZMod q) :=
    fun a j => r j (fun i => a ⟨j, i⟩)
  let F := fun a v => f (R a) v
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_integer_quarter_cover_extension q F L B
    (fun a => hf (R a)) (fun a v => hbound (R a) v)
  refine ⟨g, hg, hgb, ?_⟩
  intro u x hu hx
  choose w hw using (fun j => exists_normalized_representative_offset
    (W j) (bW j) (b j) (hb j) (u j) (x j) (hu j))
  let β : ambient → ℤ := fun a => latticeDeckInteger (W a.1) (bW a.1) (b a.1) (hb a.1)
    (x a.1).2 (w a.1) a.2
  let v : ambient → ℝ := fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2
  have hrβ : R (fun a => (β a : ZMod q)) = fun j i => ((x j).2 i : ZMod q) := by
    funext j
    exact hr j (x j).2 (w j)
  have heq := hvalue β v (fun a => hx a.1 a.2)
  change g (fun a => ((((β a : ℝ) + v a) / q : ℝ) : UnitAddCircle)) =
    f (R (fun a => (β a : ZMod q))) v at heq
  rw [hrβ] at heq
  have hpoint : (fun a => ((((β a : ℝ) + v a) / q : ℝ) : UnitAddCircle)) =
      fun a => ((((u a.1).val a.2) / q : ℝ) : UnitAddCircle) := by
    funext a
    rcases a with ⟨j, i⟩
    have h := normalizedDeckPoint_identity (W j) (bW j) (b j) (hb j) (x j) (w j)
    rw [hw j] at h
    have hi := congrArg (fun z : EuclideanSpace ℝ (D j) => z i) h
    change (u j).val i = v ⟨j, i⟩ + (β ⟨j, i⟩ : ℝ) at hi
    rw [hi, add_comm (β ⟨j, i⟩ : ℝ)]
  simpa only [hpoint] using heq

end Erdos3

end

end OAI
