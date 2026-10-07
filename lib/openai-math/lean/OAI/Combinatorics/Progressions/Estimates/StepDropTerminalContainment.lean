/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.FormalInductionTerminal
import OAI.Combinatorics.Progressions.Linear.BasisProjectionRealification

namespace OAI

section

namespace Erdos3

open Module

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

def stepDropBracketKernel (K V : Submodule R L) : Submodule R L where
  carrier := {x | ∀ k ∈ K, ⁅x, k⁆ ∈ V}
  zero_mem' := by intro k _; rw [zero_lie]; exact V.zero_mem
  add_mem' := by
    intro x y hx hy k hk
    rw [add_lie]
    exact V.add_mem (hx k hk) (hy k hk)
  smul_mem' := by
    intro a x hx k hk
    rw [smul_lie]
    exact V.smul_mem a (hx k hk)

noncomputable def stepDropSubmodule (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) : Submodule R L :=
  U.toSubmodule ⊓ (K.comap (basisGradeProjection b w 1) ⊓
    ((stepDropBracketKernel K V).comap (basisGradeProjection b w 1) ⊓
      V.comap (LinearMap.id - basisGradeProjection b w 1)))

theorem mem_stepDropSubmodule (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) (x : L) :
    x ∈ stepDropSubmodule b w U V K ↔
      x ∈ U ∧ basisGradeProjection b w 1 x ∈ K ∧
      (∀ k ∈ K, ⁅basisGradeProjection b w 1 x, k⁆ ∈ V) ∧
      x - basisGradeProjection b w 1 x ∈ V := Iff.rfl

theorem basisGradeProjection_one_lie_eq_zero [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (x y : L) :
    basisGradeProjection b w 1 ⁅x, y⁆ = 0 := by
  classical
  have hb (i j : ι) : basisGradeProjection b w 1 ⁅b i, b j⁆ = 0 := by
    apply b.repr.injective
    ext k
    simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
    split_ifs with hk
    · exact hgraded i j k (by have := hw i; have := hw j; omega)
    · rfl
  rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [sum_lie_sum, smul_lie, lie_smul, map_sum, map_smul, hb, smul_zero,
    Finset.sum_const_zero]

theorem stepDropSubmodule_lie_mem [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    {x y : L} (hx : x ∈ stepDropSubmodule b w U V K) (hy : y ∈ stepDropSubmodule b w U V K) :
    ⁅x, y⁆ ∈ stepDropSubmodule b w U V K := by
  obtain ⟨hxU, _, hxbr, hxV⟩ := (mem_stepDropSubmodule b w U V K x).mp hx
  obtain ⟨hyU, hyK, _, hyV⟩ := (mem_stepDropSubmodule b w U V K y).mp hy
  have hbr : ⁅x, y⁆ ∈ V := by
    have h₁ := hxbr (basisGradeProjection b w 1 y) hyK
    have h₂ := hUV _ (hU 1 x hxU) _ hyV
    have h₃ : ⁅x - basisGradeProjection b w 1 x, y⁆ ∈ V := by
      rw [← lie_skew]
      exact V.neg_mem (hUV y hyU _ hxV)
    have he : ⁅x, y⁆ =
        ⁅basisGradeProjection b w 1 x, basisGradeProjection b w 1 y⁆ +
        ⁅basisGradeProjection b w 1 x, y - basisGradeProjection b w 1 y⁆ +
        ⁅x - basisGradeProjection b w 1 x, y⁆ := by
      rw [lie_sub, sub_lie]
      abel
    rw [he]
    exact V.add_mem (V.add_mem h₁ h₂) h₃
  have hz := basisGradeProjection_one_lie_eq_zero b w hw hgraded x y
  apply (mem_stepDropSubmodule b w U V K _).mpr
  refine ⟨U.lie_mem hxU hyU, ?_, ?_, ?_⟩
  · rw [hz]
    exact K.zero_mem
  · intro k _
    rw [hz, zero_lie]
    exact V.zero_mem
  · rwa [hz, sub_zero]

noncomputable def stepDropSubalgebra [Fintype ι]
    (b : Basis ι R L) (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    (hgraded : BasisHomogeneousBrackets b w) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieSubalgebra R L :=
  { stepDropSubmodule b w U V K with
    lie_mem' := stepDropSubmodule_lie_mem b w hw hgraded U V K hU hUV }

theorem stepDropSubmodule_graded (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule) (hV : BasisGradedSubmodule b w V) :
    BasisGradedSubmodule b w (stepDropSubmodule b w U V K) := by
  intro j x hx
  obtain ⟨hxU, hxK, hxbr, hxV⟩ := (mem_stepDropSubmodule b w U V K x).mp hx
  apply (mem_stepDropSubmodule b w U V K _).mpr
  by_cases hj : j = 1
  · subst j
    have hi := basisCoordinateProjection_idempotent b {i | w i = 1} x
    refine ⟨hU 1 x hxU, ?_, ?_, ?_⟩
    · simpa only [basisGradeProjection, hi] using hxK
    · intro k hk
      simpa only [basisGradeProjection, hi] using hxbr k hk
    · rw [show basisGradeProjection b w 1 (basisGradeProjection b w 1 x) =
        basisGradeProjection b w 1 x from hi, sub_self]
      exact V.zero_mem
  · have hz := basisGradeProjection_other b w (Ne.symm hj) x
    have hback := basisGradeProjection_other b w hj x
    have hv := hV j _ hxV
    rw [map_sub, hback, sub_zero] at hv
    refine ⟨hU j x hxU, ?_, ?_, ?_⟩
    · rw [hz]
      exact K.zero_mem
    · intro k _
      rw [hz, zero_lie]
      exact V.zero_mem
    · rwa [hz, sub_zero]

theorem stepDropSubmodule_mem_higher_grade (b : Basis ι R L) (w : ι → ℕ)
    (U : LieSubalgebra R L) (V K : Submodule R L) {j : ℕ} (hj : j ≠ 1)
    {x : L} (hx : basisGradeProjection b w j x = x) :
    x ∈ stepDropSubmodule b w U V K ↔ x ∈ U ∧ x ∈ V := by
  have hz : basisGradeProjection b w 1 x = 0 := by
    rw [← hx]
    exact basisGradeProjection_other b w (Ne.symm hj) x
  rw [mem_stepDropSubmodule]
  constructor
  · rintro ⟨hU, _, _, hV⟩
    exact ⟨hU, by simpa only [hz, sub_zero] using hV⟩
  · rintro ⟨hU, hV⟩
    refine ⟨hU, ?_, ?_, ?_⟩
    · rw [hz]
      exact K.zero_mem
    · intro k _
      rw [hz, zero_lie]
      exact V.zero_mem
    · rwa [hz, sub_zero]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

def rightLieLinear {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L] (k : L) : L →ₗ[R] L where
  toFun x := ⁅x, k⁆
  map_add' x y := add_lie x y k
  map_smul' a x := smul_lie a x k

@[simp] theorem rightLieLinear_apply {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (k x : L) : rightLieLinear (R := R) k x = ⁅x, k⁆ := rfl

theorem stepDropBracketKernel_eq_iInf {R L κ : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    [Fintype κ] (K V : Submodule R L) (e : Basis κ R K) :
    stepDropBracketKernel K V = ⨅ z, V.comap (rightLieLinear (e z : L)) := by
  classical
  ext x
  change (∀ k ∈ K, ⁅x, k⁆ ∈ V) ↔ _
  simp only [Submodule.mem_iInf, Submodule.mem_comap, rightLieLinear_apply]
  constructor
  · intro h z
    exact h (e z) (e z).property
  · intro h k hk
    have he : (∑ z, e.repr ⟨k, hk⟩ z • (e z : L)) = k := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg K.subtype (e.sum_repr ⟨k, hk⟩)
    rw [← he, lie_sum]
    apply V.sum_mem
    intro z _
    rw [lie_smul]
    exact V.smul_mem _ (h z)

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightLieLinear_baseChange (k : L) :
    (rightLieLinear (R := ℚ) k).baseChange ℝ = rightLieLinear (R := ℝ) ((1 : ℝ) ⊗ₜ[ℚ] k) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul, rightLieLinear_apply,
      LieAlgebra.ExtendScalars.bracket_tmul, mul_one]

theorem stepDropBracketKernel_baseChange [Fintype κ]
    (K V : Submodule ℚ L) (e : Basis κ ℚ K) :
    (stepDropBracketKernel K V).baseChange ℝ = stepDropBracketKernel (K.baseChange ℝ) (V.baseChange ℝ) := by
  apply le_antisymm
  · intro x hx k hk
    exact lie_mem_real_baseChange (stepDropBracketKernel K V) K V
      (fun _ ha _ hb => ha _ hb) hx hk
  · intro x hx
    rw [stepDropBracketKernel_eq_iInf K V e, real_baseChange_iInf]
    rw [Submodule.mem_iInf]
    intro z
    rw [realification_comap]
    change (rightLieLinear (R := ℚ) (e z : L)).baseChange ℝ x ∈ V.baseChange ℝ
    rw [rightLieLinear_baseChange, rightLieLinear_apply]
    exact hx _ (Submodule.tmul_mem_baseChange_of_mem 1 (e z).property)

theorem stepDropSubmodule_baseChange [Fintype κ]
    (b : Basis ι ℚ L) (w : ι → ℕ) (U : LieSubalgebra ℚ L)
    (V K : Submodule ℚ L) (e : Basis κ ℚ K) :
    (stepDropSubmodule b w U V K).baseChange ℝ =
      stepDropSubmodule (b.baseChange ℝ) w (realificationLieSubalgebra U) (V.baseChange ℝ) (K.baseChange ℝ) := by
  simp only [stepDropSubmodule, realification_inf, realification_comap,
    stepDropBracketKernel_baseChange K V e, basisGradeProjection,
    basisCoordinateProjection_baseChange, LinearMap.baseChange_sub, LinearMap.baseChange_id,
    realificationLieSubalgebra_toSubmodule]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {R L μ : Type*} [Field R] [AddCommGroup L] [Module R L]

noncomputable def homogeneousIntersection (b : Basis μ R L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule R L) : Submodule R L :=
  U ⊓ (V ⊓ LinearMap.ker (basisGradeProjection b w j - LinearMap.id))

theorem mem_homogeneousIntersection (b : Basis μ R L) (w : μ → ℕ) (j : ℕ)
    (U V : Submodule R L) (x : L) :
    x ∈ homogeneousIntersection b w j U V ↔
      x ∈ U ∧ x ∈ V ∧ basisGradeProjection b w j x = x := by
  simp only [homogeneousIntersection, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem homogeneousIntersection_finrank_le [Fintype μ]
    (b : Basis μ R L) (w : μ → ℕ) (j : ℕ) (U V : Submodule R L) :
    Module.finrank R (homogeneousIntersection b w j U V) ≤ Fintype.card μ := by
  let : FiniteDimensional R L := b.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (homogeneousIntersection b w j U V).subtype) (fun _ _ h => Subtype.ext h)
  simpa only [Module.finrank_eq_card_basis b] using h

theorem homogeneousIntersection_baseChange {L μ : Type*} [AddCommGroup L] [Module ℚ L]
    (b : Basis μ ℚ L) (w : μ → ℕ) (j : ℕ) (U V : Submodule ℚ L) :
    (homogeneousIntersection b w j U V).baseChange ℝ =
      homogeneousIntersection (b.baseChange ℝ) w j (U.baseChange ℝ) (V.baseChange ℝ) := by
  simp only [homogeneousIntersection, realification_inf, realification_ker,
    LinearMap.baseChange_sub, LinearMap.baseChange_id, basisGradeProjection,
    basisCoordinateProjection_baseChange]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

abbrev StepDropRow (υ χ κ ν : Type*) := υ ⊕ χ ⊕ (κ × ν) ⊕ ν

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def stepDropSystem (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) :
    L →ₗ[ℚ] (StepDropRow υ χ κ ν → ℚ) :=
  LinearMap.pi fun
    | .inl i => (fU.coord i).comp U.toSubmodule.mkQ
    | .inr (.inl i) => (fK.coord i).comp (K.mkQ.comp (basisGradeProjection b w 1))
    | .inr (.inr (.inl z)) => (fV.coord z.2).comp
        (V.mkQ.comp ((rightLieLinear (eK z.1 : L)).comp (basisGradeProjection b w 1)))
    | .inr (.inr (.inr i)) => (fV.coord i).comp
        (V.mkQ.comp (LinearMap.id - basisGradeProjection b w 1))

theorem stepDrop_quotient_mem_iff {ρ : Type*} (V : Submodule ℚ L)
    (f : Basis ρ ℚ (L ⧸ V)) (x : L) :
    x ∈ V ↔ ∀ i, f.repr (V.mkQ x) i = 0 := by
  simp only [Submodule.mkQ_apply]
  constructor
  · intro hx i
    rw [(Submodule.Quotient.mk_eq_zero V).mpr hx, map_zero]
    rfl
  · intro h
    apply (Submodule.Quotient.mk_eq_zero V).mp
    apply f.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h i

theorem stepDropSystem_ker [Fintype κ] (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) :
    LinearMap.ker (stepDropSystem b w U V K fU fK fV eK) = stepDropSubmodule b w U V K := by
  ext x
  rw [LinearMap.mem_ker, mem_stepDropSubmodule]
  constructor
  · intro hx
    have hU := (stepDrop_quotient_mem_iff U.toSubmodule fU x).mpr
      (fun i => congrFun hx (.inl i))
    have hK := (stepDrop_quotient_mem_iff K fK (basisGradeProjection b w 1 x)).mpr
      (fun i => congrFun hx (.inr (.inl i)))
    have hbr : basisGradeProjection b w 1 x ∈ stepDropBracketKernel K V := by
      rw [stepDropBracketKernel_eq_iInf K V eK, Submodule.mem_iInf]
      intro z
      exact (stepDrop_quotient_mem_iff V fV _).mpr
        (fun i => congrFun hx (.inr (.inr (.inl (z, i)))))
    have hV := (stepDrop_quotient_mem_iff V fV (x - basisGradeProjection b w 1 x)).mpr
      (fun i => congrFun hx (.inr (.inr (.inr i))))
    exact ⟨hU, hK, hbr, hV⟩
  · rintro ⟨hU, hK, hbr, hV⟩
    funext i
    rcases i with i | i | ⟨z, i⟩ | i
    · exact (stepDrop_quotient_mem_iff U.toSubmodule fU x).mp hU i
    · exact (stepDrop_quotient_mem_iff K fK _).mp hK i
    · exact (stepDrop_quotient_mem_iff V fV _).mp (hbr (eK z) (eK z).property) i
    · exact (stepDrop_quotient_mem_iff V fV _).mp hV i

theorem stepDropSystem_basis_height (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H B : ℕ} (hH : 1 ≤ H)
    (hU : ∀ i j, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b j)) i) H)
    (hK : ∀ i j, RationalHeightLE (fK.repr (K.mkQ (b j)) i) H)
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (hbr : ∀ i j z, RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) B)
    (i : StepDropRow υ χ κ ν) (j : μ) :
    RationalHeightLE (stepDropSystem b w U V K fU fK fV eK (b j) i) (max H B) := by
  classical
  have hp : basisGradeProjection b w 1 (b j) = if w j = 1 then b j else 0 :=
    basisCoordinateProjection_basis b {i | w i = 1} j
  have hzero := rationalHeightLE_zero (hH.trans (Nat.le_max_left H B))
  rcases i with i | i | ⟨z, i⟩ | i
  · exact (hU i j).mono (Nat.le_max_left H B)
  · change RationalHeightLE (fK.repr (K.mkQ (basisGradeProjection b w 1 (b j))) i) _
    rw [hp]
    split_ifs
    · exact (hK i j).mono (Nat.le_max_left H B)
    · simpa only [map_zero, Finsupp.zero_apply] using hzero
  · change RationalHeightLE (fV.repr (V.mkQ ⁅basisGradeProjection b w 1 (b j), (eK z : L)⁆) i) _
    rw [hp]
    split_ifs
    · exact (hbr i j z).mono (Nat.le_max_right H B)
    · simpa only [zero_lie, map_zero, Finsupp.zero_apply] using hzero
  · change RationalHeightLE (fV.repr (V.mkQ (b j - basisGradeProjection b w 1 (b j))) i) _
    rw [hp]
    split_ifs
    · simpa only [sub_self, map_zero, Finsupp.zero_apply] using hzero
    · simpa only [sub_zero] using (hV i j).mono (Nat.le_max_left H B)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem stepDropSubmodule_top_frequency
    {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (b : Basis ι R L) (w : ι → ℕ) (U : LieSubalgebra R L) (V K : Submodule R L)
    (hU : BasisGradedSubmodule b w U.toSubmodule) (hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[R] R) {s : ℕ} (hs : 2 ≤ s)
    (hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    {x : L} (hx : x ∈ stepDropSubmodule b w U V K) :
    η (basisGradeProjection b w s x) = 0 := by
  have hmem := stepDropSubmodule_graded b w U V K hU hV s x hx
  have hpure : basisGradeProjection b w s (basisGradeProjection b w s x) =
      basisGradeProjection b w s x := basisCoordinateProjection_idempotent b {i | w i = s} x
  exact hη _ ((stepDropSubmodule_mem_higher_grade b w U V K (by omega) hpure).mp hmem).2 hpure

namespace NilpotentLieFiltration

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {q : ℝ}
  {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}

theorem FormalInductionRun.terminal_coefficients_mem_stepDropSubmodule
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (α : σ →₀ ℕ) :
    coefficients W.state.P.coord α ∈
      stepDropSubmodule (b.baseChange ℝ) w U (V.baseChange ℝ) (K.baseChange ℝ) := by
  apply (mem_stepDropSubmodule _ _ _ _ _ _).mpr
  refine ⟨W.state.mem_U α, W.state.horizontal α, ?_, ?_⟩
  · rintro k ⟨x, rfl⟩
    apply real_bracket_mem_of_basis (eK.baseChange ℝ) (K.subtype.baseChange ℝ) (V.baseChange ℝ)
      (basisGradeProjection (b.baseChange ℝ) w 1 (coefficients W.state.P.coord α)) _ x
    intro z
    simpa only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Submodule.subtype_apply] using
      W.terminal_lower_bracket hs 1 (by omega) z α
  · have h := F.real_sub_horizontal_mem_of_lower_grades b w hF (V.baseChange ℝ)
      (j := s + 1) (by omega) (coefficients W.state.P.coord α)
      (fun d hd hds => W.terminal_lower_log hs α d hd (by omega))
    rw [F.realLayer_terminal] at h
    simpa only [LieSubmodule.bot_toSubmodule, sup_bot_eq] using h

theorem FormalInductionRun.terminal_coefficients_mem_rational_stepDrop
    {U₀ : LieSubalgebra ℚ L}
    (W : F.FormalInductionRun b w (realificationLieSubalgebra U₀) V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (α : σ →₀ ℕ) :
    coefficients W.state.P.coord α ∈ (stepDropSubmodule b w U₀ V K).baseChange ℝ := by
  rw [stepDropSubmodule_baseChange b w U₀ V K eK]
  exact W.terminal_coefficients_mem_stepDropSubmodule hs hF α

theorem FormalInductionRun.terminal_log_mem_stepDropSubalgebra [Fintype μ]
    {U₀ : LieSubalgebra ℚ L}
    (W : F.FormalInductionRun b w (realificationLieSubalgebra U₀) V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (hgraded : BasisHomogeneousBrackets b w)
    (hU : BasisGradedSubmodule b w U₀.toSubmodule)
    (hUV : ∀ u ∈ U₀, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (t : σ → ℝ) :
    eval₂ t W.state.P.coord ∈ realificationLieSubalgebra
      (stepDropSubalgebra b w (F.adaptedBasis_weight_pos b w hF) hgraded U₀ V K hU hUV) := by
  apply (eval₂_mem_iff_coefficients _ W.state.P.coord).mpr _ t
  intro α
  exact W.terminal_coefficients_mem_rational_stepDrop hs hF α

end NilpotentLieFiltration
end Erdos3

end

end OAI
