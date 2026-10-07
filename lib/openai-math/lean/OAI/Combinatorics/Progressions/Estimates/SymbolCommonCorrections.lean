import OAI.Combinatorics.Progressions.Dynamics.CommonCorrectionBudget
import OAI.Combinatorics.Progressions.Dynamics.RestrictedGradePathMembership
import OAI.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
import OAI.Combinatorics.Progressions.Estimates.FastCoefficientBlocks
import OAI.Combinatorics.Progressions.Geometry.FilteredSubalgebraCoordinates
import OAI.Combinatorics.Progressions.Nilpotent.BCHSubmoduleRemainder

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem bracket_mem_subalgebra_sup_layer_succ (U : LieSubalgebra ℚ L)
    {j : ℕ} (hj : 1 ≤ j) {a b : L}
    (ha : a ∈ U.toSubmodule ⊔ F.layer j) (hb : b ∈ U.toSubmodule ⊔ F.layer j) :
    ⁅a, b⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  obtain ⟨u, hu, x, hx, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨v, hv, y, hy, rfl⟩ := Submodule.mem_sup.mp hb
  have hu1 : u ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hv1 : v ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have huv : ⁅u, v⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) (U.lie_mem hu hv)
  have huy : ⁅u, y⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
    apply (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1))
    simpa only [Nat.add_comm 1 j] using F.lie_mem hu1 hy
  have hxv : ⁅x, v⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1)) (F.lie_mem hx hv1)
  have hxy : ⁅x, y⁆ ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_right : F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer (j + 1))
      (F.antitone (by omega : j + 1 ≤ j + j) (F.lie_mem hx hy))
  rw [add_lie, lie_add, lie_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ huv huy) (Submodule.add_mem _ hxv hxy)

theorem bch_triple_remainder_mem_subalgebra_sup_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j : ℕ} (hj : 1 ≤ j) (a b c : L)
    (ha : a ∈ U.toSubmodule ⊔ F.layer j)
    (hb : b ∈ U.toSubmodule ⊔ F.layer j)
    (hc : c ∈ U.toSubmodule ⊔ F.layer j) :
    lieBCH s (lieBCH s a b) c - (a + b + c) ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
  lieBCH_triple_sub_sum_mem_submodule hs _ _
    (sup_le_sup_left (F.antitone (Nat.le_succ j)) _)
    (fun _ hx _ hy => F.bracket_mem_subalgebra_sup_layer_succ U hj hx hy) a b c ha hb hc

theorem outer_sum_mem_subalgebra_sup_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j : ℕ} (hj : 1 ≤ j) (a d p p' : L)
    (ha : a ∈ U.toSubmodule ⊔ F.layer j)
    (hd : d ∈ U.toSubmodule ⊔ F.layer j)
    (hp : p ∈ U) (hp' : p' ∈ U)
    (heq : p = lieBCH s (lieBCH s a p') d) :
    a + d ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  have hrem := F.bch_triple_remainder_mem_subalgebra_sup_layer hs U hj a p' d ha
    ((le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer j) hp') hd
  rw [← heq] at hrem
  have hpW : p ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) hp
  have hp'W : p' ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    (le_sup_left : U.toSubmodule ≤ U.toSubmodule ⊔ F.layer (j + 1)) hp'
  convert Submodule.sub_mem _ (Submodule.sub_mem _ hpW hp'W) hrem using 1
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem outer_factors_mem_of_separation (U : LieSubalgebra ℚ L)
    (A D P P' : F.Group) (hP : P.coord ∈ U) (hP' : P'.coord ∈ U)
    (hidentity : P = A * P' * D)
    (hseparate : ∀ j : ℕ, 1 ≤ j → j ≤ s →
      A.coord + D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      A.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧
        D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    A.coord ∈ U ∧ D.coord ∈ U := by
  have hind : ∀ n : ℕ, n ≤ s →
      A.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) ∧
        D.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.zero_add, F.one_eq_top, sup_top_eq]
      exact ⟨Submodule.mem_top, Submodule.mem_top⟩
    | succ n ih =>
      intro hn
      obtain ⟨ha, hd⟩ := ih (by omega)
      apply hseparate (n + 1) (by omega) hn
      apply F.outer_sum_mem_subalgebra_sup_layer (by omega) U (by omega)
        A.coord D.coord P.coord P'.coord ha hd hP hP'
      exact congrArg NilpotentLieBCHGroup.coord hidentity
  change A.coord ∈ U.toSubmodule ∧ D.coord ∈ U.toSubmodule
  simpa only [F.terminal, sup_bot_eq] using hind s le_rfl

theorem comparison_middle_identity (E P R E' P' R' : F.Group)
    (h : E * P * R = E' * P' * R') :
    P = (E⁻¹ * E') * P' * (R' * R⁻¹) := by
  have heq := congrArg (fun x : F.Group => E⁻¹ * x * R⁻¹) h
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using heq

theorem compatible_factors_mem_of_separation (U : LieSubalgebra ℚ L)
    (E P R E' P' R' : F.Group) (hP : P.coord ∈ U) (hP' : P'.coord ∈ U)
    (h : E * P * R = E' * P' * R')
    (hseparate : ∀ j : ℕ, 1 ≤ j → j ≤ s →
      (E⁻¹ * E').coord + (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      (E⁻¹ * E').coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧
        (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    (E⁻¹ * E').coord ∈ U ∧ (R' * R⁻¹).coord ∈ U :=
  F.outer_factors_mem_of_separation U (E⁻¹ * E') (R' * R⁻¹) P P' hP hP'
    (F.comparison_middle_identity E P R E' P' R' h) hseparate

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem outer_sum_mem_of_identity_mod_layer (hs : 1 ≤ s)
    (U : LieSubalgebra ℚ L) {j k : ℕ} (hj : 1 ≤ j) (hjk : j + 1 ≤ k)
    (a d p p' : L) (ha : a ∈ U.toSubmodule ⊔ F.layer j) (hd : d ∈ U.toSubmodule ⊔ F.layer j)
    (hp : p ∈ U.toSubmodule ⊔ F.layer k) (hp' : p' ∈ U.toSubmodule ⊔ F.layer k)
    (heq : p - lieBCH s (lieBCH s a p') d ∈ F.layer k) :
    a + d ∈ U.toSubmodule ⊔ F.layer (j + 1) := by
  have hkw : U.toSubmodule ⊔ F.layer k ≤ U.toSubmodule ⊔ F.layer (j + 1) :=
    sup_le_sup_left (F.antitone hjk) _
  have hwj : U.toSubmodule ⊔ F.layer (j + 1) ≤ U.toSubmodule ⊔ F.layer j :=
    sup_le_sup_left (F.antitone (Nat.le_succ j)) _
  have hrem := F.bch_triple_remainder_mem_subalgebra_sup_layer hs U hj a p' d ha (hwj (hkw hp')) hd
  have herr : p - lieBCH s (lieBCH s a p') d ∈ U.toSubmodule ⊔ F.layer (j + 1) :=
    Submodule.mem_sup_right (F.antitone hjk heq)
  convert Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (hkw hp) (hkw hp')) herr) hrem using 1
  abel

theorem outer_factors_mem_mod_layer_of_separation (U : LieSubalgebra ℚ L)
    (k : ℕ) (hk : k ≤ s + 1) (A D P P' : F.Group)
    (hP : P.coord ∈ U.toSubmodule ⊔ F.layer k) (hP' : P'.coord ∈ U.toSubmodule ⊔ F.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) P =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (A * P' * D))
    (hseparate : ∀ j : ℕ, 1 ≤ j → j < k →
      A.coord + D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      A.coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧ D.coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    A.coord ∈ U.toSubmodule ⊔ F.layer k ∧ D.coord ∈ U.toSubmodule ⊔ F.layer k := by
  cases k with
  | zero =>
    have hall (x : L) : x ∈ F.layer 0 := F.antitone (Nat.zero_le 1) (by rw [F.one_eq_top]; trivial)
    exact ⟨Submodule.mem_sup_right (hall _), Submodule.mem_sup_right (hall _)⟩
  | succ k =>
    have herr : P.coord - lieBCH s (lieBCH s A.coord P'.coord) D.coord ∈ F.layer (k + 1) := by
      apply (lieQuotientMap_eq_zero (F.layerIdeal (k + 1)) _).mp
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg NilpotentLieBCHGroup.coord hidentity)
    have hind : ∀ n : ℕ, n ≤ k →
        A.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) ∧ D.coord ∈ U.toSubmodule ⊔ F.layer (n + 1) := by
      intro n
      induction n with
      | zero =>
        intro _
        rw [Nat.zero_add, F.one_eq_top, sup_top_eq]
        exact ⟨Submodule.mem_top, Submodule.mem_top⟩
      | succ n ih =>
        intro hn
        obtain ⟨ha, hd⟩ := ih (by omega)
        apply hseparate (n + 1) (by omega) (by omega)
        exact F.outer_sum_mem_of_identity_mod_layer (by omega) U (by omega) (by omega)
          A.coord D.coord P.coord P'.coord ha hd hP hP' herr
    exact hind k le_rfl

theorem compatible_factors_mem_mod_layer_of_separation (U : LieSubalgebra ℚ L)
    (k : ℕ) (hk : k ≤ s + 1) (E P R E' P' R' : F.Group)
    (hP : P.coord ∈ U.toSubmodule ⊔ F.layer k) (hP' : P'.coord ∈ U.toSubmodule ⊔ F.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (E * P * R) =
      NilpotentLieBCHGroup.quotientHom (F.layerIdeal k) (E' * P' * R'))
    (hseparate : ∀ j : ℕ, 1 ≤ j → j < k →
      (E⁻¹ * E').coord + (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1) →
      (E⁻¹ * E').coord ∈ U.toSubmodule ⊔ F.layer (j + 1) ∧
        (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer (j + 1)) :
    (E⁻¹ * E').coord ∈ U.toSubmodule ⊔ F.layer k ∧ (R' * R⁻¹).coord ∈ U.toSubmodule ⊔ F.layer k := by
  let q := NilpotentLieBCHGroup.quotientHom (hnil := F.lowerCentralSeries_eq_bot) (F.layerIdeal k)
  change q (E * P * R) = q (E' * P' * R') at hidentity
  have hmiddle : q P = q ((E⁻¹ * E') * P' * (R' * R⁻¹)) := by
    have h := congrArg (fun x => (q E)⁻¹ * x * (q R)⁻¹) hidentity
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  exact F.outer_factors_mem_mod_layer_of_separation U k hk (E⁻¹ * E') (R' * R⁻¹) P P' hP hP' hmiddle hseparate

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem controlled_outer_factors_mem (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (A D P P' : F.realification.Group)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP' : P'.coord ∈ realificationLieSubalgebra U)
    (hidentity : P = A * P' * D)
    (ha : ‖(e.baseChange ℝ).equivFun A.coord‖ ≤ Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun D.coord ∈ realDenominatorGrid l) :
    A.coord ∈ realificationLieSubalgebra U ∧ D.coord ∈ realificationLieSubalgebra U := by
  let W := realLieSubalgebraOverRat (realificationLieSubalgebra U)
  change A.coord ∈ W ∧ D.coord ∈ W
  apply F.realification.outer_factors_mem_of_separation W A D P P' hP hP' hidentity
  intro j _ _ hsum
  let M : Matrix ι (κ ⊕ ι) ℚ := fun i z => e.repr (subalgebraLayerFamily e v ω (j + 1) z) i
  have hM : ∀ i z, RationalHeightLE (M i z) H :=
    fun i z => subalgebraLayerFamily_height e v ω (j + 1) hH hv z i
  have hcols : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hsum' : (e.baseChange ℝ).equivFun A.coord + (e.baseChange ℝ).equivFun D.coord ∈
      Submodule.span ℝ (Set.range (fun z i => (M i z : ℝ))) := by
    rw [← map_add]
    exact (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mp hsum
  obtain ⟨ha', hd'⟩ := controlled_small_vector_separation M hH hl hM (by linarith)
    (hι.trans (by linarith)) hcols
    (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
    (hlp.trans (Real.exp_le_exp.mpr (by linarith))) _ _ ha hd hsum'
  exact ⟨(F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mpr ha',
    (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan (j + 1) _).mpr hd'⟩

theorem controlled_compatible_factors_mem (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (E P R E' P' R' : F.realification.Group)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hP' : P'.coord ∈ realificationLieSubalgebra U)
    (hidentity : E * P * R = E' * P' * R')
    (ha : ‖(e.baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun (R' * R⁻¹).coord ∈ realDenominatorGrid l) :
    (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
      (R' * R⁻¹).coord ∈ realificationLieSubalgebra U :=
  F.controlled_outer_factors_mem e ω hlayers U v hspan hH hl hv hp hι hκ hHp hlp
    (E⁻¹ * E') (R' * R⁻¹) P P' hP hP'
    (F.realification.comparison_middle_identity E P R E' P' R' hidentity) ha hd

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem controlled_separation_at_layer (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (j : ℕ) (x y : ℝ ⊗[ℚ] L)
    (hx : ‖(e.baseChange ℝ).equivFun x‖ ≤ Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hy : (e.baseChange ℝ).equivFun y ∈ realDenominatorGrid l)
    (hsum : x + y ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j) :
    x ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j ∧
      y ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j := by
  let M : Matrix ι (κ ⊕ ι) ℚ := fun i z => e.repr (subalgebraLayerFamily e v ω j z) i
  have hM : ∀ i z, RationalHeightLE (M i z) H :=
    fun i z => subalgebraLayerFamily_height e v ω j hH hv z i
  have hcols : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hsum' : (e.baseChange ℝ).equivFun x + (e.baseChange ℝ).equivFun y ∈
      Submodule.span ℝ (Set.range (fun z i => (M i z : ℝ))) := by
    rw [← map_add]
    exact (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mp hsum
  obtain ⟨hx', hy'⟩ := controlled_small_vector_separation M hH hl hM (by linarith)
    (hι.trans (by linarith)) hcols (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
    (hlp.trans (Real.exp_le_exp.mpr (by linarith))) _ _ hx hy hsum'
  exact ⟨(F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mpr hx',
    (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mpr hy'⟩

theorem controlled_compatible_factors_mod_layer (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (k : ℕ) (hk : k ≤ s + 1)
    (E P R E' P' R' : F.realification.Group)
    (hP : P.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k)
    (hP' : P'.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k)
    (hidentity : NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E * P * R) =
      NilpotentLieBCHGroup.quotientHom (F.realification.layerIdeal k) (E' * P' * R'))
    (ha : ‖(e.baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hd : (e.baseChange ℝ).equivFun (R' * R⁻¹).coord ∈ realDenominatorGrid l) :
    (E⁻¹ * E').coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k ∧
      (R' * R⁻¹).coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer k := by
  apply F.realification.compatible_factors_mem_mod_layer_of_separation
    (realLieSubalgebraOverRat (realificationLieSubalgebra U)) k hk E P R E' P' R' hP hP' hidentity
  intro j _ _ hsum
  exact F.controlled_separation_at_layer e ω hlayers U v hspan hH hl hv hp hι hκ hHp hlp (j + 1)
    (E⁻¹ * E').coord (R' * R⁻¹).coord ha hd hsum

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      P.coord ∈ realificationLieSubalgebra U → P'.coord ∈ realificationLieSubalgebra U →
      E * P * R = E' * P' * R' →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R' →
      (E⁻¹ * E').coord ∈ realificationLieSubalgebra U ∧
        (R' * R⁻¹).coord ∈ realificationLieSubalgebra U := by
  obtain ⟨cs, _, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (2 * Q + 2) ^ 48 + (2 * Q + 2) ^ 24 + 2 * Q + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T hT E P R E' P' R' hP hP' heq hE hE' hR hR'
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let q : ℝ := (p + (s + 2)) ^ (s + 2) + (p + cs) ^ cs + (p + cr) ^ cr + p + 2
  have hd0 : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsq : (p + cs) ^ cs ≤ q := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    ((Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)).trans
          (by dsimp [q]; linarith)
  have hcutoff : separationBudget (2 * q) ≤ (p + C) ^ C := by
    simpa [B, Q, q, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hAslow : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + cs) ^ cs)) (E⁻¹ * E') := by
    have hinputs : ∀ g ∈ [E⁻¹, E'], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E).mpr hE
      · exact hE'
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hTpos [E⁻¹, E'] (by simp) hinputs
  obtain ⟨m, hm, hmp, _, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  have hDgrid : F.SymbolRationalGrid b ω hlayers w m (R' * R⁻¹) := by
    have hinputs : ∀ g ∈ [R', R⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR'
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [R', R⁻¹] (by simp) hinputs
  have hAnorm : ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * q) / Real.exp (separationBudget (2 * q)) := by
    have hnorm := F.symbolSlowBound_log_norm b ω hlayers w T
      (Real.one_le_exp (separationBudget_nonneg (by positivity : 0 ≤ 2 * q)))
      (fun i => (Real.exp_le_exp.mpr hcutoff).trans (hT i)) (Real.exp_nonneg _) (E⁻¹ * E') hAslow
    exact hnorm.trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (hsq.trans (by linarith))) (Real.exp_nonneg _))
  exact (F.polynomialSymbolFiltration w).controlled_compatible_factors_mem
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) U v hspan hH hm hv hq hdim (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hmp.trans (Real.exp_le_exp.mpr hrq))
    E P R E' P' R' hP hP' heq hAnorm hDgrid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem realSymbolGradeQuotient_mem_iff {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (k : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w k g ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w k) ↔
      g.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔
        (F.polynomialSymbolFiltration w).realification.layer k :=
  NilpotentLieBCHGroup.quotient_mem_map_subgroup_iff
    ((F.polynomialSymbolFiltration w).realification.layerIdeal k)
    (realLieSubalgebraOverRat (realificationLieSubalgebra U)) g

theorem exists_controlled_symbol_comparison_mod_layer (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∀ k : ℕ, k ≤ s + 1 → ∀ E P R E' P' R' : F.RealPolynomialSymbolGroup w,
      F.realSymbolGradeQuotientHom w k P ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) →
      F.realSymbolGradeQuotientHom w k P' ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) →
      F.realSymbolGradeQuotientHom w k (E * P * R) = F.realSymbolGradeQuotientHom w k (E' * P' * R') →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
      F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E' →
      F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R' →
      F.realSymbolGradeQuotientHom w k (E⁻¹ * E') ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) ∧
      F.realSymbolGradeQuotientHom w k (R' * R⁻¹) ∈
        (NilpotentLieBCHGroup.realificationSubgroup (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
          (F.realSymbolGradeQuotientHom w k) := by
  obtain ⟨cs, _, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (2 * Q + 2) ^ 48 + (2 * Q + 2) ^ 24 + 2 * Q + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hlayers w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T hT k hk E P R E' P' R' hP hP' heq hE hE' hR hR'
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let q : ℝ := (p + (s + 2)) ^ (s + 2) + (p + cs) ^ cs + (p + cr) ^ cr + p + 2
  have hd0 : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsq : (p + cs) ^ cs ≤ q := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ q :=
    ((Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
        (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)).trans
          (by dsimp [q]; linarith)
  have hcutoff : separationBudget (2 * q) ≤ (p + C) ^ C := by
    simpa [B, Q, q, separationBudget, Polynomial.eval₂_pow] using hbound p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hAslow : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + cs) ^ cs)) (E⁻¹ * E') := by
    have hinputs : ∀ g ∈ [E⁻¹, E'], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E).mpr hE
      · exact hE'
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hTpos [E⁻¹, E'] (by simp) hinputs
  obtain ⟨m, hm, hmp, _, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  have hDgrid : F.SymbolRationalGrid b ω hlayers w m (R' * R⁻¹) := by
    have hinputs : ∀ g ∈ [R', R⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR'
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [R', R⁻¹] (by simp) hinputs
  have hAnorm : ‖((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).equivFun (E⁻¹ * E').coord‖ ≤
      Real.exp (2 * q) / Real.exp (separationBudget (2 * q)) := by
    have hnorm := F.symbolSlowBound_log_norm b ω hlayers w T
      (Real.one_le_exp (separationBudget_nonneg (by positivity : 0 ≤ 2 * q)))
      (fun i => (Real.exp_le_exp.mpr hcutoff).trans (hT i)) (Real.exp_nonneg _) (E⁻¹ * E') hAslow
    exact hnorm.trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (hsq.trans (by linarith))) (Real.exp_nonneg _))
  have hresult := (F.polynomialSymbolFiltration w).controlled_compatible_factors_mod_layer
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) U v hspan hH hm hv hq hdim (hκ.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hmp.trans (Real.exp_le_exp.mpr hrq)) k hk
    E P R E' P' R' ((F.realSymbolGradeQuotient_mem_iff w U k P).mp hP)
      ((F.realSymbolGradeQuotient_mem_iff w U k P').mp hP') heq hAnorm hDgrid
  exact ⟨(F.realSymbolGradeQuotient_mem_iff w U k _).mpr hresult.1,
    (F.realSymbolGradeQuotient_mem_iff w U k _).mpr hresult.2⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_bounded_symbol_comparison (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : κ → F.PolynomialSymbol w),
      Submodule.span ℚ (Set.range v) = U.toSubmodule →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF w).repr (v i) z) H) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
        ∀ E₀ P₀ R₀ E P R : F.RealPolynomialSymbolGroup w,
          P₀.coord ∈ realificationLieSubalgebra U → P.coord ∈ realificationLieSubalgebra U →
          E₀ * P₀ * R₀ = E * P * R →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E₀ →
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) E →
          F.SymbolRationalGrid b ω hF w l R₀ → F.SymbolRationalGrid b ω hF w l R →
          (E₀⁻¹ * E).coord ∈ realificationLieSubalgebra U ∧
          (R * R₀⁻¹).coord ∈ realificationLieSubalgebra U ∧
          F.SymbolSlowBound b ω hF w T (Real.exp ((p + C) ^ C)) (E₀⁻¹ * E) ∧
          F.SymbolRationalGrid b ω hF w m (R * R₀⁻¹) := by
  have hcompExists := exists_controlled_symbol_comparison s a
  obtain ⟨cc, _, hcomp⟩ := hcompExists
  have hslowExists := exists_symbol_slow_product_bound s a 2
  obtain ⟨cs, _, hslow⟩ := hslowExists
  have hratExists := exists_symbol_rational_product_bound s 2
  obtain ⟨cr, _, hrat⟩ := hratExists
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Polynomial.X + Polynomial.C cs) ^ cs + (Polynomial.X + Polynomial.C cr) ^ cr
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
  have hsum : (p + cc) ^ cc + (p + cs) ^ cs + (p + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbound p hp
  have hc0 : 0 ≤ (p + cc) ^ cc := by positivity
  have hs0 : 0 ≤ (p + cs) ^ cs := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hcb : (p + cc) ^ cc ≤ (p + C) ^ C := by linarith
  have hsb : (p + cs) ^ cs ≤ (p + C) ^ C := by linarith
  have hrb : (p + cr) ^ cr ≤ (p + C) ^ C := by linarith
  have hproductsExists := hrat F b ω hF w hw H p hH hp hι hσ hHp hb l hl hlp
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hproductsExists
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrb), hlm, ?_⟩
  intro T hT E₀ P₀ R₀ E P R hP₀ hP heq hE₀ hE hR₀ hR
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hmem := hcomp F b ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hb hv
    T (fun i => (Real.exp_le_exp.mpr hcb).trans (hT i)) E₀ P₀ R₀ E P R
    hP₀ hP heq hE₀ hE hR₀ hR
  refine ⟨hmem.1, hmem.2, ?_, ?_⟩
  · have hinputs : ∀ x ∈ [E₀⁻¹, E], F.SymbolSlowBound b ω hF w T (Real.exp ((p + 2) ^ a)) x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hF w T _ E₀).mpr hE₀
      · exact hE
    have hpair : F.SymbolSlowBound b ω hF w T (Real.exp ((p + cs) ^ cs)) (E₀⁻¹ * E) := by
      simpa only [List.prod_cons, List.prod_nil, mul_one] using
        hslow F b ω hF w hw H p hH hp hι hσ hHp hb T hTpos [E₀⁻¹, E] (by simp) hinputs
    exact F.symbolSlowBound_mono b ω hF w T hTpos (Real.exp_le_exp.mpr hsb) _ hpair
  · have hinputs : ∀ x ∈ [R, R₀⁻¹], F.SymbolRationalGrid b ω hF w l x := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hR
      · exact F.symbolRationalGrid_inv b ω hF w l hR₀
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts [R, R₀⁻¹] (by simp) hinputs

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem symbol_current_grade_residual_mem
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ (F.PolynomialSymbol w))
    (hU : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) U.toSubmodule)
    (k : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) k
    π (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord - π (E₀⁻¹ * E).coord - π (R * R₀⁻¹).coord ∈
      realificationLieSubalgebra U := by
  exact (F.polynomialSymbolFiltration w).realGradeProjection_normalized_residual_mem
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w)
    (realificationLieSubalgebra U).toSubmodule
    (hU.baseChange (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule)
    k E P R E₀ R₀ hP hE hR

theorem exists_controlled_symbol_grade_step (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ {η : Type*} (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)),
        (∀ i, BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
          (fun z => ω z.val.2) (U i).toSubmodule) →
        ∀ (k : ℕ) (X E R A D : F.RealPolynomialSymbolGroup w),
        (∀ i, F.realSymbolGradeQuotientHom w k (E⁻¹ * X * R⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U i)).map
            (F.realSymbolGradeQuotientHom w k)) →
        A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k →
        D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k →
        (let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) k
         ∀ i, π (E⁻¹ * X * R⁻¹).coord - π A.coord - π D.coord ∈ realificationLieSubalgebra (U i)) →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) A →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l D →
        (E * A) * (A⁻¹ * (E⁻¹ * X * R⁻¹) * D⁻¹) * (D * R) = X ∧
          F.realSymbolGradeQuotientHom w k (E * A) = F.realSymbolGradeQuotientHom w k E ∧
          F.realSymbolGradeQuotientHom w k (D * R) = F.realSymbolGradeQuotientHom w k R ∧
          (∀ i, F.realSymbolGradeQuotientHom w (k + 1) (A⁻¹ * (E⁻¹ * X * R⁻¹) * D⁻¹) ∈
            (NilpotentLieBCHGroup.realificationSubgroup
              (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U i)).map
              (F.realSymbolGradeQuotientHom w (k + 1))) ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A) ∧
          F.SymbolRationalGrid b ω hlayers w m (D * R) := by
  obtain ⟨cs, hcs, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, hcr, hrat⟩ := exists_symbol_rational_product_bound s 2
  refine ⟨max cs cr, hcs.trans (le_max_left _ _), ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  have hs : (p + cs) ^ cs ≤ (p + (max cs cr : ℕ)) ^ max cs cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hr : (p + cr) ^ cr ≤ (p + (max cs cr : ℕ)) ^ max cs cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hr), hlm, ?_⟩
  intro η U hU k X E R A D hY hA hD hgrade hEslow hAslow hRgrid hDgrid
  let G := F.polynomialSymbolFiltration w
  let B := F.polynomialSymbolBasis b ω hlayers w
  have hUr : ∀ i, BasisGradedSubmodule (B.baseChange ℝ) (fun z => ω z.val.2)
      (realificationLieSubalgebra (U i)).toSubmodule :=
    fun i => (hU i).baseChange B (fun z => ω z.val.2) (U i).toSubmodule
  have hYr : ∀ i, (E⁻¹ * X * R⁻¹).coord ∈
      (realificationLieSubalgebra (U i)).toSubmodule ⊔ (G.realLayer k).toSubmodule :=
    fun i => (G.real_quotient_mem_subgroup_iff (realificationLieSubalgebra (U i)) k _).mp (hY i)
  obtain ⟨hprod, hEq, hRq, hnext⟩ := G.simultaneous_real_grade_correction B (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) (fun i => realificationLieSubalgebra (U i))
    hUr k X E R A D hYr hA hD hgrade
  refine ⟨hprod, hEq, hRq, ?_, ?_, ?_⟩
  · intro i
    exact (G.real_quotient_mem_subgroup_iff (realificationLieSubalgebra (U i)) (k + 1) _).mpr (hnext i)
  · have hi : ∀ g ∈ [E, A], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hEslow
      · exact hAslow
    have h := hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT [E, A] (by simp) hi
    simp only [List.prod_cons, List.prod_nil, mul_one] at h
    exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr hs) _ h
  · have hi : ∀ g ∈ [D, R], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hDgrid
      · exact hRgrid
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [D, R] (by simp) hi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_common_symbol_grade_corrections (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (k : ℕ) (x : F.RealPolynomialSymbol w) (E R : η → F.RealPolynomialSymbolGroup w),
        let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) k
        (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
        (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
        (∀ j, π x - π (E j).coord - π (R j).coord ∈ realificationLieSubalgebra (U j)) →
        ∃ A D : F.RealPolynomialSymbolGroup w,
          A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
          D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) A ∧
          F.SymbolRationalGrid b ω hlayers w m D ∧
          ∀ j, π x - π A.coord - π D.coord ∈ realificationLieSubalgebra (U j) := by
  obtain ⟨C, hC, hbound⟩ := exists_common_correction_budget s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hv T hT
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let N : ℝ := (p + (s + 2)) ^ (s + 2)
  let q : ℝ := N * (p + 1) + (p + 2) ^ a + p + 2
  let t : ℝ := ((q + 2) ^ 10 + 2) ^ 4
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hNp : 0 ≤ N * (p + 1) := mul_nonneg hN (by positivity)
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hNterm : N ≤ N * (p + 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ p + 1 by linarith) hN
  have hNq : N ≤ q := hNterm.trans (by dsimp [q]; linarith)
  have hNpq : N * p ≤ q :=
    (mul_le_mul_of_nonneg_left (show p ≤ p + 1 by linarith) hN).trans (by dsimp [q]; linarith)
  have haq : (p + 2) ^ a ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ N :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hcols : ((Fintype.card (SymbolBasisIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hdim hκ (Nat.cast_nonneg _) hN).trans hNpq
  have hrows : (Fintype.card (Σ _ : η, SymbolBasisIndex w ω) : ℝ) ≤ q := by
    simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    exact (mul_le_mul hη hdim (Nat.cast_nonneg _) hp).trans (by simpa only [mul_comm] using hNpq)
  have hall : separationBudget t + (t + 2) ^ 36 + ((t + 2) ^ 18 + t) ≤ (p + C) ^ C := by
    exact hbound p hp
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ separationBudget t := separationBudget_nonneg ht
  have hden0 : 0 ≤ (t + 2) ^ 36 := by positivity
  have hslow0 : 0 ≤ (t + 2) ^ 18 + t := by positivity
  have hcut : separationBudget t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right hden0).trans ((le_add_of_nonneg_right hslow0).trans hall)
  have hden : (t + 2) ^ 36 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hs).trans ((le_add_of_nonneg_right hslow0).trans hall)
  have hslow : (t + 2) ^ 18 + t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (add_nonneg hs hden0)).trans hall
  let e := F.polynomialSymbolBasis b ω hlayers w
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_block_subspace_corrections e (fun z => z.val.1)
    (fun j => (U j).toSubmodule) v hspan hblock hH hl hv hq (hdim.trans hNq) hcols hrows
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hden), hlm, ?_⟩
  intro k x E R
  dsimp only
  intro hE hR hres
  let π := basisGradeProjection (e.baseChange ℝ) (fun z => ω z.val.2) k
  have hπ (z : F.RealPolynomialSymbol w) : π (π z) = π z :=
    basisCoordinateProjection_idempotent (e.baseChange ℝ) {z | ω z.val.2 = k} z
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hW : ∀ α, 0 < monomialScale T α := monomialScale_pos T hTpos
  have hWmin : ∀ z : SymbolBasisIndex w ω, Real.exp (separationBudget t) ≤ monomialScale T z.val.1 :=
    fun z => le_monomialScale_of_ne_zero T (Real.one_le_exp hs)
      (fun i => (Real.exp_le_exp.mpr hcut).trans (hT i))
      (F.symbolBasisIndex_monomial_ne_zero b ω hlayers w z)
  have he : ∀ j z, |(e.baseChange ℝ).equivFun (π (E j).coord) z| ≤ Real.exp q / monomialScale T z.val.1 := by
    intro j z
    exact ((basisCoordinateProjection_abs_repr_le (e.baseChange ℝ) {z | ω z.val.2 = k} (E j).coord z).trans
      (hE j z)).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr haq) (hW _).le)
  have hr : ∀ j, (e.baseChange ℝ).equivFun (π (R j).coord) ∈ realDenominatorGrid l :=
    fun j => basisCoordinateProjection_real_grid (e.baseChange ℝ) {z | ω z.val.2 = k} l (R j).coord (hR j)
  obtain ⟨u, d, hu, hd, hcommon⟩ := hsolve (monomialScale T) hW hWmin
    (fun j => π (E j).coord) (fun j => π (R j).coord) (π x) he hr hres
  refine ⟨⟨π u⟩, ⟨π d⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer e (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hlayers w) k u
  · exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer e (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hlayers w) k d
  · intro z
    exact ((basisCoordinateProjection_abs_repr_le (e.baseChange ℝ) {z | ω z.val.2 = k} u z).trans
      (hu z)).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) (hW _).le)
  · exact basisCoordinateProjection_real_grid (e.baseChange ℝ) {z | ω z.val.2 = k} m d hd
  · intro j
    have hgraded : BasisGradedSubmodule e (fun z => ω z.val.2) (U j).toSubmodule := by
      have heq : (fun z : SymbolBasisIndex w ω => ω z.val.2) = (fun z => Finsupp.weight w z.val.1) :=
        funext (fun z => z.property.symm)
      rw [heq]
      exact (hblock j).graded e (fun z => z.val.1) (U j).toSubmodule (Finsupp.weight w)
    have h := hgraded.baseChange e (fun z => ω z.val.2) (U j).toSubmodule k
      (π x - u - d) (hcommon j)
    change π (π x - u - d) ∈ (U j).toSubmodule.baseChange ℝ at h
    change π x - π (π u) - π (π d) ∈ (U j).toSubmodule.baseChange ℝ
    simpa only [map_sub, hπ] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
