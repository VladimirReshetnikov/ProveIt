import Mathlib.Tactic.Group
import OAI.Combinatorics.Progressions.Geometry.QuotientSubgroupCoordinates
import OAI.Combinatorics.Progressions.Linear.GradeProjectionRemainder
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDerivativeInvariant

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem lie_mem_invariant_sup_layer_of_degree
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {i j : ℕ}
    {u v : L} (hu : u ∈ U) (hui : u ∈ F.layer i) (hv : v ∈ V ⊔ F.layer j) :
    ⁅u, v⁆ ∈ V ⊔ F.layer (i + j) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  rw [lie_add]
  exact (V ⊔ F.layer (i + j)).add_mem
    (Submodule.mem_sup_left (hUV _ hu _ hx))
    (Submodule.mem_sup_right (F.lie_mem hui hy))

theorem correction_adjoint_sub_current_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (a : F.Group) (haU : a.coord ∈ U) (ha : a.coord ∈ F.layer (j - 1))
    (x k : L) (hx : x - k ∈ V ⊔ F.layer 2) :
    dualAdjoint a x - (x + ⁅a.coord, k⁆) ∈ V ⊔ F.layer (j + 1) := by
  have hx1 : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hrem := F.dualAdjoint_sub_first_bracket_mem_layer hs a ha x hx1
  have hrem' : dualAdjoint a x - (x + ⁅a.coord, x⁆) ∈ F.layer (j + 1) :=
    F.antitone (by omega) hrem
  have hbr : ⁅a.coord, x - k⁆ ∈ V ⊔ F.layer (j + 1) := by
    have h := F.lie_mem_invariant_sup_layer_of_degree U V hUV haU ha hx
    have he : j - 1 + 2 = j + 1 := by omega
    simpa only [he] using h
  have h := (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right hrem') hbr
  rw [lie_sub] at h
  convert h using 1; abel

theorem correction_inverse_adjoint_sub_current_bracket_mem (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (a : F.Group) (haU : a.coord ∈ U) (ha : a.coord ∈ F.layer (j - 1))
    (x k : L) (hx : x - k ∈ V ⊔ F.layer 2) :
    dualAdjoint a⁻¹ x - (x - ⁅a.coord, k⁆) ∈ V ⊔ F.layer (j + 1) := by
  have h := F.correction_adjoint_sub_current_bracket_mem hs U V hUV hj a⁻¹
    (U.neg_mem haU) ((F.layer (j - 1)).neg_mem ha) x k hx
  simpa only [coord_inv, neg_lie, ← sub_eq_add_neg] using h

theorem correction_removal_coord_sub_mem_layer {j : ℕ}
    (a g c : F.Group) (ha : a.coord ∈ F.layer (j - 1))
    (hc : c.coord ∈ F.layer (j - 1)) (hj : 1 ≤ j) :
    (a⁻¹ * g * c⁻¹).coord - (g.coord - a.coord - c.coord) ∈ F.layer j := by
  have hg1 : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hag1 : (a⁻¹ * g).coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have ha' : -a.coord ∈ F.layer (j - 1) := (F.layer (j - 1)).neg_mem ha
  have hc' : -c.coord ∈ F.layer (j - 1) := (F.layer (j - 1)).neg_mem hc
  have hleft : ⁅-a.coord, g.coord⁆ ∈ F.layer j := by
    simpa only [Nat.sub_add_cancel hj] using F.lie_mem ha' hg1
  have hright : ⁅(a⁻¹ * g).coord, -c.coord⁆ ∈ F.layer j := by
    have he : 1 + (j - 1) = j := by omega
    simpa only [he] using F.lie_mem hag1 hc'
  have h1 := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot (F.layerIdeal j)
    (-a.coord) g.coord hleft
  have h2 := lieBCH_sub_add_mem F.lowerCentralSeries_eq_bot (F.layerIdeal j)
    (a⁻¹ * g).coord (-c.coord) hright
  change (a⁻¹ * g).coord - (-a.coord + g.coord) ∈ F.layer j at h1
  change (a⁻¹ * g * c⁻¹).coord - ((a⁻¹ * g).coord + -c.coord) ∈ F.layer j at h2
  convert (F.layer j).add_mem h2 h1 using 1; abel

theorem correction_removal_preserves_lower_layers {j : ℕ}
    (a g c : F.Group) (ha : a.coord ∈ F.layer (j - 1))
    (hc : c.coord ∈ F.layer (j - 1)) (hj : 1 ≤ j) :
    (a⁻¹ * g * c⁻¹).coord - g.coord ∈ F.layer (j - 1) := by
  have h := F.antitone (by omega : j - 1 ≤ j)
    (F.correction_removal_coord_sub_mem_layer a g c ha hc hj)
  have hneg := (F.layer (j - 1)).neg_mem ((F.layer (j - 1)).add_mem ha hc)
  convert (F.layer (j - 1)).add_mem h hneg using 1; abel

theorem correction_removal_preserves_mod_invariant {j : ℕ}
    (V : Submodule ℚ L) (a g c : F.Group) (ha : a.coord ∈ F.layer (j - 1))
    (hc : c.coord ∈ F.layer (j - 1)) (hj : 1 ≤ j)
    (haV : a.coord ∈ V) (hcV : c.coord ∈ V) :
    (a⁻¹ * g * c⁻¹).coord - g.coord ∈ V ⊔ F.layer j := by
  have h := F.correction_removal_coord_sub_mem_layer a g c ha hc hj
  have hneg := V.neg_mem (V.add_mem haV hcV)
  have he := (V ⊔ F.layer j).add_mem (Submodule.mem_sup_right h) (Submodule.mem_sup_left hneg)
  convert he using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem removal_adjoint_relation (a g c : F.Group) (x y : L)
    (hxy : x = dualAdjoint g y) :
    dualAdjoint a⁻¹ x = dualAdjoint (a⁻¹ * g * c⁻¹) (dualAdjoint c y) := by
  rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, hxy]

theorem current_layer_normalization {κ : Type*} (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) {j : ℕ} (hj : 2 ≤ j)
    (g a c : F.Group) (hg : g.coord ∈ U) (haU : a.coord ∈ U) (hcU : c.coord ∈ U)
    (ha : a.coord ∈ F.layer (j - 1)) (hc : c.coord ∈ F.layer (j - 1))
    (S R k : κ → L) (p : L) (hp : p ∈ F.layer (j - 1))
    (hSR : ∀ b, S b = dualAdjoint g (R b))
    (hR : ∀ b, R b - k b ∈ V ⊔ F.layer j)
    (hlower : ∀ b, ⁅g.coord - p, k b⁆ ∈ V ⊔ F.layer (j + 1))
    (hleft : ∀ b, S b - k b - ⁅a.coord, k b⁆ ∈ V ⊔ F.layer (j + 1))
    (hright : ∀ b, R b - k b + ⁅c.coord, k b⁆ ∈ V ⊔ F.layer (j + 1)) :
    let g' := a⁻¹ * g * c⁻¹
    let S' := fun b => dualAdjoint a⁻¹ (S b)
    let R' := fun b => dualAdjoint c (R b)
    let p' := p - a.coord - c.coord
    a * g' * c = g ∧ g'.coord ∈ U ∧ p' ∈ F.layer (j - 1) ∧
      g'.coord - (g.coord - a.coord - c.coord) ∈ F.layer j ∧
      (∀ b, S' b = dualAdjoint g' (R' b)) ∧
      ∀ b, S' b - k b ∈ V ⊔ F.layer (j + 1) ∧
        R' b - k b ∈ V ⊔ F.layer (j + 1) ∧
        ⁅p', k b⁆ ∈ V ⊔ F.layer (j + 1) := by
  intro g' S' R' p'
  have hj1 : 1 ≤ j := by omega
  have hdown : V ⊔ F.layer j ≤ V ⊔ F.layer 2 :=
    sup_le le_sup_left ((F.antitone hj).trans le_sup_right)
  have hR2 (b : κ) : R b - k b ∈ V ⊔ F.layer 2 := hdown (hR b)
  have hS2 (b : κ) : S b - k b ∈ V ⊔ F.layer 2 := by
    have hx : R b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    have h := F.dualAdjoint_sub_mem_next_layer 1 g (R b) hx
    rw [hSR b]
    convert (V ⊔ F.layer 2).add_mem (Submodule.mem_sup_right h) (hR2 b) using 1
    abel
  refine ⟨?_, ?_, (F.layer (j - 1)).sub_mem ((F.layer (j - 1)).sub_mem hp ha) hc,
    F.correction_removal_coord_sub_mem_layer a g c ha hc hj1,
    fun b => F.removal_adjoint_relation a g c (S b) (R b) (hSR b), ?_⟩
  · dsimp [g']
    group
  · exact lieBCH_mem U s (lieBCH_mem U s (U.neg_mem haU) hg) (U.neg_mem hcU)
  · intro b
    have hSa := F.correction_inverse_adjoint_sub_current_bracket_mem hs U V hUV hj
      a haU ha (S b) (k b) (hS2 b)
    have hRc := F.correction_adjoint_sub_current_bracket_mem hs U V hUV hj
      c hcU hc (R b) (k b) (hR2 b)
    have hk1 : k b ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
    have hbr := F.adjoint_current_layer_relation U V hUV hs hj1 g hg (R b) (k b)
      p hp hk1 (hR b) (hlower b)
    rw [← hSR b] at hbr
    refine ⟨?_, ?_, ?_⟩
    · convert (V ⊔ F.layer (j + 1)).add_mem hSa (hleft b) using 1; dsimp [S']; abel
    · convert (V ⊔ F.layer (j + 1)).add_mem hRc (hright b) using 1; dsimp [R']; abel
    · have h := (V ⊔ F.layer (j + 1)).sub_mem
        ((V ⊔ F.layer (j + 1)).add_mem hbr (hleft b)) (hright b)
      dsimp [p']
      rw [sub_lie, sub_lie]
      convert h using 1; abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem logDerivative_current_layer_of_lower_brackets (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hz : dualBaseLinear z.coord ∈ U)
    (k : L) (ht : dualTangentLinear z.coord - k ∈ V ⊔ F.layer j)
    (hk : ⁅dualBaseLinear z.coord, k⁆ ∈ V ⊔ F.layer (j + 1)) :
    dualLogDerivative z - dualTangentLinear z.coord ∈ V ⊔ F.layer (j + 1) := by
  apply F.logDerivative_current_layer_relation hs U V hUV j z hz
  have h := (V ⊔ F.layer (j + 1)).add_mem
    (F.lie_mem_invariant_sup_next_layer U V hUV j hz ht) hk
  simpa only [lie_sub, sub_add_cancel] using h

theorem adjoint_sub_mem_invariant_next_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (g : F.Group) (hg : g.coord ∈ U) (r : L) (hr : r ∈ V ⊔ F.layer j) :
    dualAdjoint g r - r ∈ V ⊔ F.layer (j + 1) := by
  have hbr := F.lie_mem_invariant_sup_next_layer U V hUV j hg hr
  have hW := F.invariant_sup_layer U V hUV (j + 1)
  have hrem := dualAdjoint_sub_first_bracket_mem hs U (V ⊔ F.layer (j + 1))
    hW g hg r (hW _ hg _ hbr)
  convert (V ⊔ F.layer (j + 1)).add_mem hrem hbr using 1; abel

theorem current_layer_derivative_system (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (z : DualGroup F.lowerCentralSeries_eq_bot) (hz : dualBaseLinear z.coord ∈ U)
    (k small rational extra : L)
    (ht : dualTangentLinear z.coord - k ∈ V ⊔ F.layer j)
    (hk : ⁅dualBaseLinear z.coord, k⁆ ∈ V ⊔ F.layer (j + 1))
    (hr : rational ∈ V ⊔ F.layer j) (he : extra - k ∈ V ⊔ F.layer (j + 1))
    (hsystem : dualLogDerivative z = small + dualAdjoint (dualBaseHom z) rational + extra) :
    dualTangentLinear z.coord - k - (small + rational) ∈ V ⊔ F.layer (j + 1) := by
  have hY := F.logDerivative_current_layer_of_lower_brackets (by omega) U V hUV j z hz k ht hk
  have hA := F.adjoint_sub_mem_invariant_next_layer hs U V hUV j (dualBaseHom z) hz rational hr
  rw [hsystem] at hY
  convert (V ⊔ F.layer (j + 1)).add_mem
    ((V ⊔ F.layer (j + 1)).neg_mem hY) ((V ⊔ F.layer (j + 1)).add_mem hA he) using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_mem_layer (k : ℕ) (x : ℝ ⊗[ℚ] L) :
    basisGradeProjection (b.baseChange ℝ) w k x ∈ F.realification.layer k := by
  change basisGradeProjection (b.baseChange ℝ) w k x ∈ (F.realLayer k).toSubmodule
  rw [F.realLayer_eq_span_basis b k _ (hlayers k)]
  apply Submodule.span_mono (Set.image_mono ?_)
    (basisCoordinateProjection_mem_span (b.baseChange ℝ) {i | w i = k} x)
  intro i hi
  exact (show w i = k from hi).ge

include hlayers in

theorem real_corrected_middle_mem_next_layer
    (U : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U) (k : ℕ)
    (Y A D : F.realification.Group)
    (hY : Y.coord ∈ U ⊔ (F.realLayer k).toSubmodule)
    (hA : A.coord ∈ F.realification.layer k)
    (hD : D.coord ∈ F.realification.layer k)
    (hgrade : basisGradeProjection (b.baseChange ℝ) w k Y.coord -
      basisGradeProjection (b.baseChange ℝ) w k A.coord -
      basisGradeProjection (b.baseChange ℝ) w k D.coord ∈ U) :
    (A⁻¹ * Y * D⁻¹).coord ∈ U ⊔ (F.realLayer (k + 1)).toSubmodule := by
  let P := A⁻¹ * Y * D⁻¹
  have hAn : -A.coord ∈ F.realification.layer k := (F.realification.layer k).neg_mem hA
  have hDn : -D.coord ∈ F.realification.layer k := (F.realification.layer k).neg_mem hD
  have hrem : P.coord - (-A.coord + Y.coord + -D.coord) ∈
      F.realification.layer (k + 1) :=
    F.realification.bch_triple_sub_sum_mem_next_layer k _ _ _ hAn hDn
  have hsum : -A.coord + Y.coord + -D.coord ∈ U ⊔ (F.realLayer k).toSubmodule :=
    (U ⊔ (F.realLayer k).toSubmodule).add_mem
      ((U ⊔ (F.realLayer k).toSubmodule).add_mem (Submodule.mem_sup_right hAn) hY)
      (Submodule.mem_sup_right hDn)
  have hP : P.coord ∈ U ⊔ (F.realLayer k).toSubmodule := by
    have hsmall : P.coord - (-A.coord + Y.coord + -D.coord) ∈ (F.realLayer k).toSubmodule :=
      F.realification.antitone (Nat.le_succ k) hrem
    have h := (U ⊔ (F.realLayer k).toSubmodule).add_mem (Submodule.mem_sup_right hsmall) hsum
    simpa only [sub_add_cancel] using h
  have hPg : basisGradeProjection (b.baseChange ℝ) w k P.coord ∈ U := by
    have h := F.realGradeProjection_bch_triple b w hlayers k (-A.coord) Y.coord (-D.coord) hAn hDn
    change basisGradeProjection (b.baseChange ℝ) w k P.coord = _ at h
    rw [h, map_neg, map_neg]
    convert hgrade using 1
    abel
  rw [F.realLayer_eq_span_basis b k _ (hlayers k)] at hP
  change P.coord ∈ U ⊔ (F.realLayer (k + 1)).toSubmodule
  rw [F.realLayer_eq_span_basis b (k + 1) _ (hlayers (k + 1))]
  exact hU.mem_sup_higher_of_grade (b.baseChange ℝ) w U k P.coord hP hPg

theorem real_quotient_mem_subgroup_iff (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (k : ℕ) (g : F.realification.Group) :
    NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) g ∈
      (NilpotentLieBCHGroup.realLieSubgroup
        (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot)
          (F.realification.layerIdeal k)) ↔
      g.coord ∈ U.toSubmodule ⊔ (F.realLayer k).toSubmodule := by
  rw [NilpotentLieBCHGroup.realLieSubgroup,
    NilpotentLieBCHGroup.quotient_mem_map_subgroup_iff]
  change g.coord ∈ U.toSubmodule.restrictScalars ℚ ⊔
    (F.realLayer k).toSubmodule.restrictScalars ℚ ↔ _
  rw [← Submodule.restrictScalars_sup]
  rfl

include hlayers in
theorem real_corrected_middle_quotient_mem_next_layer
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule) (k : ℕ)
    (Y A D : F.realification.Group)
    (hY : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) Y ∈
      (NilpotentLieBCHGroup.realLieSubgroup
        (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot)
          (F.realification.layerIdeal k)))
    (hA : A.coord ∈ F.realification.layer k)
    (hD : D.coord ∈ F.realification.layer k)
    (hgrade : basisGradeProjection (b.baseChange ℝ) w k Y.coord -
      basisGradeProjection (b.baseChange ℝ) w k A.coord -
      basisGradeProjection (b.baseChange ℝ) w k D.coord ∈ U) :
    NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal (k + 1)) (A⁻¹ * Y * D⁻¹) ∈
      (NilpotentLieBCHGroup.realLieSubgroup
        (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot)
          (F.realification.layerIdeal (k + 1))) := by
  apply (F.real_quotient_mem_subgroup_iff U (k + 1) _).mpr
  exact F.real_corrected_middle_mem_next_layer b w hlayers U.toSubmodule hU k Y A D
    ((F.real_quotient_mem_subgroup_iff U k Y).mp hY) hA hD hgrade

include hlayers in

theorem simultaneous_real_grade_correction {η : Type*}
    (U : η → LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : ∀ i, BasisGradedSubmodule (b.baseChange ℝ) w (U i).toSubmodule)
    (k : ℕ) (X E₀ R₀ A D : F.realification.Group)
    (hY : ∀ i, (E₀⁻¹ * X * R₀⁻¹).coord ∈ (U i).toSubmodule ⊔ (F.realLayer k).toSubmodule)
    (hA : A.coord ∈ F.realification.layer k)
    (hD : D.coord ∈ F.realification.layer k)
    (hgrade : ∀ i, basisGradeProjection (b.baseChange ℝ) w k (E₀⁻¹ * X * R₀⁻¹).coord -
      basisGradeProjection (b.baseChange ℝ) w k A.coord -
      basisGradeProjection (b.baseChange ℝ) w k D.coord ∈ U i) :
    (E₀ * A) * (A⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * D⁻¹) * (D * R₀) = X ∧
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E₀ * A) =
        NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) E₀ ∧
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (D * R₀) =
        NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) R₀ ∧
      ∀ i, (A⁻¹ * (E₀⁻¹ * X * R₀⁻¹) * D⁻¹).coord ∈
        (U i).toSubmodule ⊔ (F.realLayer (k + 1)).toSubmodule := by
  have hqA : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) A = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact (lieQuotientMap_eq_zero (F.realification.layerIdeal k) _).mpr hA
  have hqD : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) D = 1 := by
    apply NilpotentLieBCHGroup.ext
    exact (lieQuotientMap_eq_zero (F.realification.layerIdeal k) _).mpr hD
  refine ⟨by group, ?_, ?_, ?_⟩
  · rw [map_mul, hqA, mul_one]
  · rw [map_mul, hqD, one_mul]
  · intro i
    exact F.real_corrected_middle_mem_next_layer b w hlayers (U i).toSubmodule (hU i) k
      (E₀⁻¹ * X * R₀⁻¹) A D (hY i) hA hD (hgrade i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_correction_removal_current_grade
    (E V : Submodule ℝ (ℝ ⊗[ℚ] L)) (j : ℕ)
    (hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (a g c : F.realification.Group) (ha : a.coord ∈ E) (hc : c.coord ∈ E)
    (hres : basisGradeProjection (b.baseChange ℝ) w j g.coord - a.coord - c.coord ∈ E ⊓ V) :
    a * (a⁻¹ * g * c⁻¹) * c = g ∧
      basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord ∈ E ⊓ V ∧
      ∀ k < j, basisGradeProjection (b.baseChange ℝ) w k (a⁻¹ * g * c⁻¹).coord =
        basisGradeProjection (b.baseChange ℝ) w k g.coord := by
  have hga := hE a.coord ha
  have hgc := hE c.coord hc
  have hal : a.coord ∈ F.realification.layer j := by
    simpa only [hga] using F.realGradeProjection_mem_layer b w hlayers j a.coord
  have hcl : c.coord ∈ F.realification.layer j := by
    simpa only [hgc] using F.realGradeProjection_mem_layer b w hlayers j c.coord
  refine ⟨by group, ?_, ?_⟩
  · have hg := F.realGradeProjection_bch_triple b w hlayers j (-a.coord) g.coord (-c.coord)
      ((F.realification.layer j).neg_mem hal) ((F.realification.layer j).neg_mem hcl)
    change basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord = _ at hg
    rw [hg, map_neg, map_neg, hga, hgc]
    convert hres using 1
    abel
  · intro k hk
    have hdiff : (a⁻¹ * g * c⁻¹).coord - g.coord ∈ F.realification.layer j := by
      have h := F.realification.correction_removal_preserves_lower_layers (j := j + 1)
        a g c (by simpa using hal) (by simpa using hcl) (by omega)
      simpa only [Nat.add_sub_cancel] using h
    have hzero := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers k _
      (F.realification.antitone (Nat.succ_le_of_lt hk) hdiff)
    exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

include hlayers in

theorem real_polynomial_correction_removal
    (E V : Submodule ℚ L) (j : ℕ)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (P A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hA : ∀ α, coefficients A α ∈ E.baseChange ℝ)
    (hB : ∀ α, coefficients B α ∈ E.baseChange ℝ)
    (hres : ∀ α, coefficients (P - A - B) α ∈ (E ⊓ V).baseChange ℝ)
    (t : σ → ℝ) (g : F.realification.Group)
    (hg : basisGradeProjection (b.baseChange ℝ) w j g.coord = eval₂ t P) :
    let a : F.realification.Group := ⟨eval₂ t A⟩
    let c : F.realification.Group := ⟨eval₂ t B⟩
    a * (a⁻¹ * g * c⁻¹) * c = g ∧
      basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord ∈ (E ⊓ V).baseChange ℝ ∧
      ∀ k < j, basisGradeProjection (b.baseChange ℝ) w k (a⁻¹ * g * c⁻¹).coord =
        basisGradeProjection (b.baseChange ℝ) w k g.coord := by
  dsimp only
  have ha := eval₂_mem_of_coefficients (E.baseChange ℝ) A hA t
  have hb := eval₂_mem_of_coefficients (E.baseChange ℝ) B hB t
  have hr := eval₂_mem_of_coefficients ((E ⊓ V).baseChange ℝ) (P - A - B) hres t
  rw [realification_inf] at hr ⊢
  simp only [map_sub] at hr
  exact F.real_correction_removal_current_grade b w hlayers (E.baseChange ℝ)
    (V.baseChange ℝ) j hE ⟨eval₂ t A⟩ g ⟨eval₂ t B⟩ ha hb (by simpa only [hg] using hr)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem basisBelowProjection_succ {K L ι : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Basis ι K L) (w : ι → ℕ) (j : ℕ) (x : L) :
    basisBelowProjection b w (j + 1) x =
      basisBelowProjection b w j x + basisGradeProjection b w j x := by
  rw [basisBelowProjection_eq_sum_grades, Finset.sum_range_succ,
    ← basisBelowProjection_eq_sum_grades]

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem real_current_bracket_remainder (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (j : ℕ)
    (x k : ℝ ⊗[ℚ] L) (hk : k ∈ F.realification.layer 1)
    (hlower : ∀ d < j, ⁅basisGradeProjection (b.baseChange ℝ) w d x, k⁆ ∈ V) :
    ⁅x - basisGradeProjection (b.baseChange ℝ) w j x, k⁆ ∈
      V ⊔ (F.realLayer (j + 2)).toSubmodule := by
  have hlow : ⁅basisBelowProjection (b.baseChange ℝ) w j x, k⁆ ∈ V := by
    rw [basisBelowProjection_eq_sum_grades, sum_lie]
    exact V.sum_mem (fun d hd => hlower d (Finset.mem_range.mp hd))
  have hhigh : ⁅x - basisBelowProjection (b.baseChange ℝ) w (j + 1) x, k⁆ ∈
      F.realification.layer (j + 2) := by
    have h := F.realification.lie_mem (i := j + 1) (j := 1)
      (F.sub_realGradeTruncation_mem b w hlayers (j + 1) x) hk
    simpa only [Nat.add_assoc] using h
  have h := (V ⊔ (F.realLayer (j + 2)).toSubmodule).add_mem
    (Submodule.mem_sup_right hhigh) (Submodule.mem_sup_left hlow)
  rw [basisBelowProjection_succ, sub_lie, add_lie] at h
  convert h using 1
  rw [sub_lie]
  abel

include hlayers in
theorem realGradeProjection_mem_of_mem_sup_next
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (j : ℕ) (x : ℝ ⊗[ℚ] L) (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    basisGradeProjection (b.baseChange ℝ) w j x ∈ V := by
  obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers j z hz, add_zero]
  exact hV j v hv

include hlayers in
theorem real_mem_of_homogeneous_mem_sup_next
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (j : ℕ) (x : ℝ ⊗[ℚ] L) (hgrade : basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hx : x ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule) : x ∈ V := by
  have h := F.realGradeProjection_mem_of_mem_sup_next b w hlayers V hV j x hx
  rwa [hgrade] at h

include hlayers in
theorem real_correction_preserves_grades_below (j : ℕ) (a g c : F.realification.Group)
    (ha : a.coord ∈ F.realification.layer j) (hc : c.coord ∈ F.realification.layer j) :
    ∀ d < j, basisGradeProjection (b.baseChange ℝ) w d (a⁻¹ * g * c⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w d g.coord := by
  have hdiff : (a⁻¹ * g * c⁻¹).coord - g.coord ∈ F.realification.layer j := by
    have h := F.realification.correction_removal_preserves_lower_layers (j := j + 1)
      a g c (by simpa using ha) (by simpa using hc) (by omega)
    simpa only [Nat.add_sub_cancel] using h
  intro d hd
  have hz := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers d _
    (F.realification.antitone (Nat.succ_le_of_lt hd) hdiff)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

include hlayers in
theorem real_correction_current_grade (j : ℕ) (a g c : F.realification.Group)
    (ha : a.coord ∈ F.realification.layer j) (hc : c.coord ∈ F.realification.layer j) :
    basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord =
      basisGradeProjection (b.baseChange ℝ) w j g.coord -
        basisGradeProjection (b.baseChange ℝ) w j a.coord -
        basisGradeProjection (b.baseChange ℝ) w j c.coord := by
  have h := F.realGradeProjection_bch_triple b w hlayers j (-a.coord) g.coord (-c.coord)
    ((F.realification.layer j).neg_mem ha) ((F.realification.layer j).neg_mem hc)
  change basisGradeProjection (b.baseChange ℝ) w j (a⁻¹ * g * c⁻¹).coord = _ at h
  rw [h, map_neg, map_neg]
  abel

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

section Rational

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adjoint_correction_sub_mem_layer (hs : 2 ≤ s) (j : ℕ)
    (a : F.Group) (ha : a.coord ∈ F.layer j) (x : L) :
    dualAdjoint a x - x ∈ F.layer (j + 1) := by
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hrem := F.dualAdjoint_sub_first_bracket_mem_layer hs a ha x hx
  have hsmall : dualAdjoint a x - (x + ⁅a.coord, x⁆) ∈ F.layer (j + 1) :=
    F.antitone (by omega) hrem
  have hbr : ⁅a.coord, x⁆ ∈ F.layer (j + 1) := F.lie_mem ha hx
  convert (F.layer (j + 1)).add_mem hsmall hbr using 1
  abel

theorem current_layer_correction_preserves_lifts {κ : Type*} (hs : 2 ≤ s)
    (V : Submodule ℚ L) (j : ℕ) (a g c : F.Group)
    (ha : a.coord ∈ F.layer j) (hc : c.coord ∈ F.layer j)
    (S R k : κ → L) (hSR : ∀ t, S t = dualAdjoint g (R t))
    (hS : ∀ t, S t - k t ∈ V ⊔ F.layer (j + 1))
    (hR : ∀ t, R t - k t ∈ V ⊔ F.layer (j + 1)) :
    ∀ t, dualAdjoint a⁻¹ (S t) = dualAdjoint (a⁻¹ * g * c⁻¹) (dualAdjoint c (R t)) ∧
      dualAdjoint a⁻¹ (S t) - k t ∈ V ⊔ F.layer (j + 1) ∧
      dualAdjoint c (R t) - k t ∈ V ⊔ F.layer (j + 1) := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, hSR t]
  · have h := F.adjoint_correction_sub_mem_layer hs j a⁻¹ ((F.layer j).neg_mem ha) (S t)
    convert (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right h) (hS t) using 1
    abel
  · have h := F.adjoint_correction_sub_mem_layer hs j c hc (R t)
    convert (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right h) (hR t) using 1
    abel

theorem derivative_removal_preserves_layer_mod_invariant
    (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (a c : DualGroup F.lowerCentralSeries_eq_bot)
    (haU : dualBaseLinear a.coord ∈ U) (hcU : dualBaseLinear c.coord ∈ U)
    (haT : dualTangentLinear a.coord ∈ V ⊔ F.layer j)
    (hcT : dualTangentLinear c.coord ∈ V ⊔ F.layer j)
    (small rational : L) (hsmall : small ∈ V ⊔ F.layer j) (hrational : rational ∈ V ⊔ F.layer j) :
    dualAdjoint (dualBaseHom a)⁻¹ (small - dualLogDerivative a) ∈ V ⊔ F.layer j ∧
      dualAdjoint (dualBaseHom c) rational - dualLogDerivative c ∈ V ⊔ F.layer j := by
  have hW := F.invariant_sup_layer U V hUV j
  have hYa := dualLogDerivative_mem_of_invariant U (V ⊔ F.layer j) hW a haU haT
  have hYc := dualLogDerivative_mem_of_invariant U (V ⊔ F.layer j) hW c hcU hcT
  constructor
  · exact dualAdjoint_mem_of_invariant U (V ⊔ F.layer j) hW _ (U.neg_mem haU) _
      ((V ⊔ F.layer j).sub_mem hsmall hYa)
  · exact (V ⊔ F.layer j).sub_mem
      (dualAdjoint_mem_of_invariant U (V ⊔ F.layer j) hW _ hcU rational hrational) hYc

end Rational

section Real

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem real_pure_correction_preserves_log_conditions
    (V K : Submodule ℝ (ℝ ⊗[ℚ] L)) {j : ℕ} (hj : 2 ≤ j)
    (a g c : F.realification.Group)
    (ha : basisGradeProjection (b.baseChange ℝ) w (j - 1) a.coord = a.coord)
    (hc : basisGradeProjection (b.baseChange ℝ) w (j - 1) c.coord = c.coord)
    (haK : j = 2 → a.coord ∈ K) (hcK : j = 2 → c.coord ∈ K)
    (haV : 2 < j → a.coord ∈ V) (hcV : 2 < j → c.coord ∈ V)
    (hK : basisGradeProjection (b.baseChange ℝ) w 1 g.coord ∈ K)
    (hV : ∀ d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d g.coord ∈ V) :
    basisGradeProjection (b.baseChange ℝ) w 1 (a⁻¹ * g * c⁻¹).coord ∈ K ∧
      ∀ d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (a⁻¹ * g * c⁻¹).coord ∈ V := by
  have hal : a.coord ∈ F.realification.layer (j - 1) := by
    simpa only [ha] using F.realGradeProjection_mem_layer b w hlayers (j - 1) a.coord
  have hcl : c.coord ∈ F.realification.layer (j - 1) := by
    simpa only [hc] using F.realGradeProjection_mem_layer b w hlayers (j - 1) c.coord
  have hbelow := F.real_correction_preserves_grades_below b w hlayers (j - 1) a g c hal hcl
  have hcurrent := F.real_correction_current_grade b w hlayers (j - 1) a g c hal hcl
  rw [ha, hc] at hcurrent
  constructor
  · by_cases hj2 : j = 2
    · have h := K.sub_mem (K.sub_mem hK (haK hj2)) (hcK hj2)
      rw [hj2] at hcurrent
      change basisGradeProjection (b.baseChange ℝ) w 1 (a⁻¹ * g * c⁻¹).coord = _ at hcurrent
      rwa [hcurrent]
    · rw [hbelow 1 (by omega)]
      exact hK
  · intro d hd hdj
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · rw [hbelow d hlt]
      exact hV d hd hdj
    · rw [hcurrent]
      exact V.sub_mem (V.sub_mem (hV (j - 1) hd hdj) (haV (by omega))) (hcV (by omega))

end Real
end Erdos3.NilpotentLieFiltration

end

end OAI
