import Mathlib.Algebra.Module.TransferInstance
import OAI.Combinatorics.Progressions.Linear.DualAdjointAction
import OAI.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear

namespace OAI


namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dualConstant_infinitesimal_lie (x y : L) :
    ⁅dualConstantLie x, dualInfinitesimal y⁆ = dualInfinitesimal ⁅x, y⁆ := by
  change ⁅(1 : DualNumber ℚ) ⊗ₜ[ℚ] x, DualNumber.eps ⊗ₜ[ℚ] y⁆ = _
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  rfl

theorem dualInfinitesimal_constant_lie (x y : L) :
    ⁅dualInfinitesimal x, dualConstantLie y⁆ = dualInfinitesimal ⁅x, y⁆ := by
  change ⁅DualNumber.eps ⊗ₜ[ℚ] x, (1 : DualNumber ℚ) ⊗ₜ[ℚ] y⁆ = _
  rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one]
  rfl

theorem dualTangentLinear_lie (x y : DualLieAlgebra L) :
    dualTangentLinear ⁅x, y⁆ =
      ⁅dualBaseLinear x, dualTangentLinear y⁆ + ⁅dualTangentLinear x, dualBaseLinear y⁆ := by
  have he := congrArg₂ (fun a b : DualLieAlgebra L => ⁅a, b⁆)
    (dualLie_decomposition x) (dualLie_decomposition y)
  calc
    _ = dualTangentLinear ⁅dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x),
      dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y)⁆ :=
      congrArg dualTangentLinear he
    _ = _ := by
      rw [LieRing.add_lie (dualConstantLie (dualBaseLinear x)) (dualInfinitesimal (dualTangentLinear x))
        (dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y))]
      rw [LieRing.lie_add (dualConstantLie (dualBaseLinear x)) (dualConstantLie (dualBaseLinear y))
        (dualInfinitesimal (dualTangentLinear y))]
      rw [LieRing.lie_add (dualInfinitesimal (dualTangentLinear x)) (dualConstantLie (dualBaseLinear y))
        (dualInfinitesimal (dualTangentLinear y))]
      rw [dualConstant_infinitesimal_lie, dualInfinitesimal_constant_lie, dualInfinitesimal_lie,
        ← dualConstantLie.map_lie]
      simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal,
        zero_add, add_zero]

noncomputable def dualIdealSubalgebra (I : LieIdeal ℚ L) : LieSubalgebra ℚ (DualLieAlgebra L) :=
  { I.toSubmodule.comap dualTangentLinear with
    lie_mem' := by
      intro x y hx hy
      change dualTangentLinear ⁅x, y⁆ ∈ I
      rw [dualTangentLinear_lie]
      exact I.add_mem (I.lie_mem hy) (lie_mem_left ℚ L I _ _ hx) }

@[simp] theorem mem_dualIdealSubalgebra (I : LieIdeal ℚ L) (x : DualLieAlgebra L) :
    x ∈ dualIdealSubalgebra I ↔ dualTangentLinear x ∈ I := Iff.rfl

noncomputable def dualIdealRealization (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) : dualIdealSubalgebra I →ₗ⁅ℚ⁆ L ⧸ J :=
  { toLinearMap := (lieQuotientMap J).toLinearMap.comp
      ((dualBaseLinear + dualTangentLinear).comp (dualIdealSubalgebra I).incl.toLinearMap)
    map_lie' := by
      intro x y
      change lieQuotientMap J (dualBaseLinear ⁅x.val, y.val⁆ + dualTangentLinear ⁅x.val, y.val⁆) =
        ⁅lieQuotientMap J (dualBaseLinear x.val + dualTangentLinear x.val),
          lieQuotientMap J (dualBaseLinear y.val + dualTangentLinear y.val)⁆
      rw [← (lieQuotientMap J).map_lie]
      rw [← sub_eq_zero, ← map_sub]
      apply (lieQuotientMap_eq_zero J _).mpr
      rw [dualBaseLinear_lie, dualTangentLinear_lie, LieRing.add_lie, LieRing.lie_add,
        LieRing.lie_add]
      have he : ⁅dualBaseLinear x.val, dualBaseLinear y.val⁆ +
          (⁅dualBaseLinear x.val, dualTangentLinear y.val⁆ +
            ⁅dualTangentLinear x.val, dualBaseLinear y.val⁆) -
          (⁅dualBaseLinear x.val, dualBaseLinear y.val⁆ +
            ⁅dualBaseLinear x.val, dualTangentLinear y.val⁆ +
              (⁅dualTangentLinear x.val, dualBaseLinear y.val⁆ +
                ⁅dualTangentLinear x.val, dualTangentLinear y.val⁆)) =
          -⁅dualTangentLinear x.val, dualTangentLinear y.val⁆ := by abel
      rw [he]
      exact J.neg_mem (hIJ _ x.property _ y.property) }

@[simp] theorem dualIdealRealization_apply (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (x : dualIdealSubalgebra I) :
    dualIdealRealization I J hIJ x =
      lieQuotientMap J (dualBaseLinear x.val + dualTangentLinear x.val) := rfl

noncomputable def dualQuotientEvaluate (J : LieIdeal ℚ L) : DualLieAlgebra L →ₗ[ℚ] L ⧸ J :=
  (lieQuotientMap J).toLinearMap.comp (dualBaseLinear + dualTangentLinear)

@[simp] theorem dualQuotientEvaluate_apply (J : LieIdeal ℚ L) (x : DualLieAlgebra L) :
    dualQuotientEvaluate J x = lieQuotientMap J (dualBaseLinear x + dualTangentLinear x) := rfl

@[simp] theorem dualQuotientEvaluate_constant (J : LieIdeal ℚ L) (x : L) :
    dualQuotientEvaluate J (dualConstantLie x) = lieQuotientMap J x := by
  rw [dualQuotientEvaluate_apply, dualBaseLinear_constant, dualTangentLinear_constant, add_zero]

@[simp] theorem dualQuotientEvaluate_infinitesimal (J : LieIdeal ℚ L) (x : L) :
    dualQuotientEvaluate J (dualInfinitesimal x) = lieQuotientMap J x := by
  rw [dualQuotientEvaluate_apply, dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, zero_add]

theorem dualQuotientEvaluate_lieBCH (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (s : ℕ) {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualQuotientEvaluate J (lieBCH s x y) =
      lieBCH s (dualQuotientEvaluate J x) (dualQuotientEvaluate J y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualQuotientEvaluate J ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualQuotientEvaluate J) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH (dualIdealRealization I J hIJ) s a b

end Erdos3


namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_conjugation_mod (I J : LieIdeal ℚ L)
    (hIJ : ∀ a ∈ I, ∀ b ∈ I, ⁅a, b⁆ ∈ J)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : x ∈ I) :
    lieQuotientMap J (dualAdjoint g x) =
      lieQuotientMap J (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  calc
    _ = dualQuotientEvaluate J
        (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹).coord := by
      rw [dualAdjoint_spec]
      exact (dualQuotientEvaluate_infinitesimal J _).symm
    _ = _ := by
      change dualQuotientEvaluate J
        (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
          (-dualConstantLie g.coord)) =
        lieQuotientMap J (lieBCH s (lieBCH s g.coord x) (-g.coord))
      rw [dualQuotientEvaluate_lieBCH I J hIJ s
        (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc),
        dualQuotientEvaluate_lieBCH I J hIJ s hc ht,
        map_neg, dualQuotientEvaluate_constant, dualQuotientEvaluate_infinitesimal,
        map_lieBCH, map_lieBCH, map_neg]

theorem dualAdjoint_eq_conjugation_of_abelian_ideal (I : LieIdeal ℚ L)
    (hI : ∀ a ∈ I, ∀ b ∈ I, ⁅a, b⁆ = 0)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : x ∈ I) :
    dualAdjoint g x = (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord := by
  have he := dualAdjoint_conjugation_mod I ⊥
    (fun a ha b hb => (Submodule.mem_bot ℚ).mpr (hI a ha b hb)) g x hx
  have hz : lieQuotientMap (⊥ : LieIdeal ℚ L)
      (dualAdjoint g x - (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord) = 0 := by
    rw [map_sub, he, sub_self]
  exact sub_eq_zero.mp ((Submodule.mem_bot ℚ).mp ((lieQuotientMap_eq_zero _ _).mp hz))

end Erdos3.NilpotentLieBCHGroup


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualCoordinates : DualLieAlgebra L ≃ₗ[ℚ] L × L where
  toLinearMap := dualBaseLinear.prod dualTangentLinear
  invFun x := dualConstantLie x.1 + dualInfinitesimal x.2
  left_inv x := (dualLie_decomposition x).symm
  right_inv x := by ext <;> simp

@[simp] theorem dualCoordinates_apply (x : DualLieAlgebra L) :
    dualCoordinates x = (dualBaseLinear x, dualTangentLinear x) := rfl

@[simp] theorem dualCoordinates_symm_apply (x : L × L) :
    dualCoordinates.symm x = dualConstantLie x.1 + dualInfinitesimal x.2 := rfl

end Erdos3


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualFirstOrderIdeal (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) : LieIdeal ℚ (dualIdealSubalgebra I) :=
  { (I.toSubmodule.comap (dualBaseLinear.comp (dualIdealSubalgebra I).incl.toLinearMap)) ⊓
      (J.toSubmodule.comap (dualTangentLinear.comp (dualIdealSubalgebra I).incl.toLinearMap)) with
    lie_mem := by
      intro x y hy
      change dualBaseLinear ⁅x.val, y.val⁆ ∈ I ∧ dualTangentLinear ⁅x.val, y.val⁆ ∈ J
      rw [dualBaseLinear_lie, dualTangentLinear_lie]
      exact ⟨I.lie_mem hy.1, J.add_mem (J.lie_mem hy.2) (hIJ _ x.property _ hy.1)⟩ }

def DualFirstOrderCongruent (I J : LieIdeal ℚ L) (x y : DualLieAlgebra L) : Prop :=
  dualBaseLinear (x - y) ∈ I ∧ dualTangentLinear (x - y) ∈ J

theorem dualFirstOrderCongruent_lieBCH (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (s : ℕ)
    {a b c d : DualLieAlgebra L}
    (ha : a ∈ dualIdealSubalgebra I) (hb : b ∈ dualIdealSubalgebra I)
    (hc : c ∈ dualIdealSubalgebra I) (hd : d ∈ dualIdealSubalgebra I)
    (hac : DualFirstOrderCongruent I J a c) (hbd : DualFirstOrderCongruent I J b d) :
    DualFirstOrderCongruent I J (lieBCH s a b) (lieBCH s c d) := by
  let K := dualFirstOrderIdeal I J hIJ
  let a' : dualIdealSubalgebra I := ⟨a, ha⟩
  let b' : dualIdealSubalgebra I := ⟨b, hb⟩
  let c' : dualIdealSubalgebra I := ⟨c, hc⟩
  let d' : dualIdealSubalgebra I := ⟨d, hd⟩
  have heac : lieQuotientMap K a' = lieQuotientMap K c' := by
    rw [← sub_eq_zero, ← map_sub]
    exact (lieQuotientMap_eq_zero K _).mpr hac
  have hebd : lieQuotientMap K b' = lieQuotientMap K d' := by
    rw [← sub_eq_zero, ← map_sub]
    exact (lieQuotientMap_eq_zero K _).mpr hbd
  have he : lieBCH s a' b' - lieBCH s c' d' ∈ K := by
    apply (lieQuotientMap_eq_zero K _).mp
    rw [map_sub, map_lieBCH, map_lieBCH, heac, hebd, sub_self]
  have hv : (lieBCH s a' b' - lieBCH s c' d').val = lieBCH s a b - lieBCH s c d := by
    change (dualIdealSubalgebra I).incl (lieBCH s a' b' - lieBCH s c' d') = _
    rw [map_sub, map_lieBCH, map_lieBCH]
    rfl
  change dualBaseLinear (lieBCH s a' b' - lieBCH s c' d').val ∈ I ∧
    dualTangentLinear (lieBCH s a' b' - lieBCH s c' d').val ∈ J at he
  rw [hv] at he
  exact he

theorem dualFirstOrderCongruent_constant (I J : LieIdeal ℚ L) {x y : L}
    (hxy : x - y ∈ I) : DualFirstOrderCongruent I J (dualConstantLie x) (dualConstantLie y) := by
  constructor
  · simpa only [map_sub, dualBaseLinear_constant] using hxy
  · simp only [map_sub, dualTangentLinear_constant, sub_self]
    exact J.zero_mem

theorem dualFirstOrderCongruent_infinitesimal (I J : LieIdeal ℚ L) {x y : L}
    (hxy : x - y ∈ J) : DualFirstOrderCongruent I J (dualInfinitesimal x) (dualInfinitesimal y) := by
  constructor
  · simp only [map_sub, dualBaseLinear_infinitesimal, sub_self]
    exact I.zero_mem
  · simpa only [map_sub, dualTangentLinear_infinitesimal] using hxy

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_sub_mem (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (z z' : DualGroup hnil)
    (hz : dualTangentLinear z.coord ∈ I) (hz' : dualTangentLinear z'.coord ∈ I)
    (he : DualFirstOrderCongruent I J z.coord z'.coord) :
    dualLogDerivative z - dualLogDerivative z' ∈ J := by
  have hbase : -dualBaseLinear z.coord - -dualBaseLinear z'.coord ∈ I := by
    have hh := I.neg_mem he.1
    rw [map_sub, neg_sub] at hh
    rw [neg_sub_neg]
    exact hh
  have hconst := dualFirstOrderCongruent_constant I J hbase
  rw [map_neg, map_neg] at hconst
  have hc (x : L) : -dualConstantLie x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (-dualConstantLie x) ∈ I
    rw [map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hh := dualFirstOrderCongruent_lieBCH I J hIJ s hz (hc _) hz' (hc _) he hconst
  have ht := hh.2
  rw [map_sub] at ht
  exact ht

theorem dualAdjoint_sub_mem (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J)
    (g g' : NilpotentLieBCHGroup L s hnil) (x x' : L)
    (hx : x ∈ I) (hx' : x' ∈ I) (hg : g.coord - g'.coord ∈ I) (hxx' : x - x' ∈ J) :
    dualAdjoint g x - dualAdjoint g' x' ∈ J := by
  have hc (a : L) : dualConstantLie a ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie a) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have ht' : dualInfinitesimal x' ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x') ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hcc := dualFirstOrderCongruent_constant I J hg
  have htt := dualFirstOrderCongruent_infinitesimal I J hxx'
  have hp := dualFirstOrderCongruent_lieBCH I J hIJ s (hc _) ht (hc _) ht' hcc htt
  have hneg : -g.coord - -g'.coord ∈ I := by
    rw [neg_sub_neg]
    have hh := I.neg_mem hg
    rwa [neg_sub] at hh
  have hcc' := dualFirstOrderCongruent_constant I J hneg
  rw [map_neg, map_neg] at hcc'
  have hh := dualFirstOrderCongruent_lieBCH I J hIJ s
    (lieBCH_mem (dualIdealSubalgebra I) s (hc _) ht) ((dualIdealSubalgebra I).neg_mem (hc _))
    (lieBCH_mem (dualIdealSubalgebra I) s (hc _) ht') ((dualIdealSubalgebra I).neg_mem (hc _)) hp hcc'
  have he := hh.2
  rw [map_sub] at he
  exact he

end NilpotentLieBCHGroup
end Erdos3


namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem dual_ext {x y : DualLieAlgebra M}
    (hb : dualBaseLinear x = dualBaseLinear y) (ht : dualTangentLinear x = dualTangentLinear y) : x = y := by
  calc
    x = dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x) := dualLie_decomposition x
    _ = dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y) := by rw [hb, ht]
    _ = y := (dualLie_decomposition y).symm

noncomputable def dualLinearLift (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) :
    DualLieAlgebra L →ₗ[ℚ] DualLieAlgebra M :=
  dualConstantLie.toLinearMap.comp (B.toLinearMap.comp dualBaseLinear) +
    dualInfinitesimal.comp (T.comp dualTangentLinear)

@[simp] theorem dualLinearLift_apply (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualLinearLift B T x = dualConstantLie (B (dualBaseLinear x)) +
      dualInfinitesimal (T (dualTangentLinear x)) := rfl

@[simp] theorem dualLinearLift_base (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualBaseLinear (dualLinearLift B T x) = B (dualBaseLinear x) := by
  rw [dualLinearLift_apply, map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem dualLinearLift_tangent (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualTangentLinear (dualLinearLift B T x) = T (dualTangentLinear x) := by
  rw [dualLinearLift_apply, map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem dualLinearLift_constant (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : L) :
    dualLinearLift B T (dualConstantLie x) = dualConstantLie (B x) := by
  rw [dualLinearLift_apply, dualBaseLinear_constant, dualTangentLinear_constant, map_zero,
    map_zero, add_zero]

@[simp] theorem dualLinearLift_infinitesimal (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : L) :
    dualLinearLift B T (dualInfinitesimal x) = dualInfinitesimal (T x) := by
  rw [dualLinearLift_apply, dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, map_zero,
    map_zero, zero_add]

variable (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hT in
theorem dualIdealMorphism_left {x y : L} (hx : x ∈ I) : T ⁅x, y⁆ = ⁅T x, B y⁆ := by
  calc
    T ⁅x, y⁆ = T (-⁅y, x⁆) := congrArg T (lie_skew x y).symm
    _ = -⁅B y, T x⁆ := by rw [map_neg, hT y x hx]
    _ = ⁅T x, B y⁆ := lie_skew _ _

noncomputable def dualIdealMorphism : dualIdealSubalgebra I →ₗ⁅ℚ⁆ DualLieAlgebra M :=
  { toLinearMap := (dualLinearLift B T).comp (dualIdealSubalgebra I).incl.toLinearMap
    map_lie' := by
      intro x y
      apply dual_ext
      · change dualBaseLinear (dualLinearLift B T ⁅x.val, y.val⁆) =
          dualBaseLinear ⁅dualLinearLift B T x.val, dualLinearLift B T y.val⁆
        rw [dualLinearLift_base, dualBaseLinear_lie, dualBaseLinear_lie,
          dualLinearLift_base, dualLinearLift_base, B.map_lie]
      · change dualTangentLinear (dualLinearLift B T ⁅x.val, y.val⁆) =
          dualTangentLinear ⁅dualLinearLift B T x.val, dualLinearLift B T y.val⁆
        rw [dualLinearLift_tangent, dualTangentLinear_lie, dualTangentLinear_lie,
          dualLinearLift_base, dualLinearLift_base, dualLinearLift_tangent, dualLinearLift_tangent,
          map_add, hT _ _ y.property, dualIdealMorphism_left I B T hT x.property] }

include hT in
theorem dualLinearLift_lieBCH (s : ℕ) {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualLinearLift B T (lieBCH s x y) = lieBCH s (dualLinearLift B T x) (dualLinearLift B T y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualLinearLift B T ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualLinearLift B T) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH (dualIdealMorphism I B T hT) s a b

end Erdos3


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

noncomputable instance dualRealModule : Module ℝ (DualLieAlgebra L) :=
  (dualCoordinates (L := L)).toAddEquiv.module ℝ

noncomputable def dualRealCoordinates : DualLieAlgebra L ≃ₗ[ℝ] L × L :=
  (dualCoordinates (L := L)).toAddEquiv.linearEquiv ℝ

@[simp] theorem dualRealCoordinates_apply (x : DualLieAlgebra L) :
    dualRealCoordinates x = (dualBaseLinear x, dualTangentLinear x) := rfl

@[simp] theorem dualRealCoordinates_symm_apply (x : L × L) :
    dualRealCoordinates.symm x = dualConstantLie x.1 + dualInfinitesimal x.2 := rfl

@[simp] theorem dualBaseLinear_smul_real (r : ℝ) (x : DualLieAlgebra L) :
    dualBaseLinear (r • x) = r • dualBaseLinear x :=
  congrArg Prod.fst (dualRealCoordinates.map_smul r x)

@[simp] theorem dualTangentLinear_smul_real (r : ℝ) (x : DualLieAlgebra L) :
    dualTangentLinear (r • x) = r • dualTangentLinear x :=
  congrArg Prod.snd (dualRealCoordinates.map_smul r x)

instance dualRealScalarTower [IsScalarTower ℚ ℝ L] : IsScalarTower ℚ ℝ (DualLieAlgebra L) where
  smul_assoc q r x := by
    apply dualCoordinates.injective
    ext <;> simp [smul_assoc]

noncomputable instance dualRealLieAlgebra : LieAlgebra ℝ (DualLieAlgebra L) where
  lie_smul r x y := by
    apply dualCoordinates.injective
    ext
    · simp only [dualCoordinates_apply, dualBaseLinear_lie, dualBaseLinear_smul_real, lie_smul]
    · simp only [dualCoordinates_apply, dualTangentLinear_lie, dualTangentLinear_smul_real,
        dualBaseLinear_smul_real, lie_smul, smul_add]

end Erdos3


namespace Erdos3.NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
  (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

theorem map_coord (f : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hL) :
    (map (hM := hM) f g).coord = f g.coord := rfl

include hT in
theorem dualLinearLift_logDerivative (z : DualGroup hL)
    (hz : dualTangentLinear z.coord ∈ I) :
    T (dualLogDerivative z) =
      dualLogDerivative (hnil := hM) (⟨dualLinearLift B T z.coord⟩ : DualGroup hM) := by
  have hc : -dualConstantLie (dualBaseLinear z.coord) ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (-dualConstantLie (dualBaseLinear z.coord)) ∈ I
    rw [map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hh := dualLinearLift_lieBCH I B T hT s hz hc
  have ht := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent, map_neg, dualLinearLift_constant] at ht
  change T (dualLogDerivative z) =
    dualTangentLinear (lieBCH s (dualLinearLift B T z.coord)
      (-dualConstantLie (dualBaseLinear (dualLinearLift B T z.coord))))
  rw [dualLinearLift_base]
  exact ht

include hT in
theorem dualLinearLift_adjoint (g : NilpotentLieBCHGroup L s hL) (x : L) (hx : x ∈ I) :
    T (dualAdjoint g x) = dualAdjoint (map (hM := hM) B g) (T x) := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hh := dualLinearLift_lieBCH I B T hT s
    (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc)
  rw [dualLinearLift_lieBCH I B T hT s hc ht, dualLinearLift_constant,
    dualLinearLift_infinitesimal, map_neg, dualLinearLift_constant] at hh
  have he := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent] at he
  exact he

include hT in
theorem dualLinearLift_logDerivative_eq (z : DualGroup hL)
    (hz : dualTangentLinear z.coord ∈ I) (z' : DualGroup hM)
    (he : dualLinearLift B T z.coord = z'.coord) :
    T (dualLogDerivative z) = dualLogDerivative (hnil := hM) z' := by
  have hg : (⟨dualLinearLift B T z.coord⟩ : DualGroup hM) = z' := NilpotentLieBCHGroup.ext he
  exact (dualLinearLift_logDerivative hM I B T hT z hz).trans
    (congrArg (dualLogDerivative (hnil := hM)) hg)

include hT in
theorem dualLinearLift_adjoint_eq (g : NilpotentLieBCHGroup L s hL) (x : L) (hx : x ∈ I)
    (g' : NilpotentLieBCHGroup M s hM) (x' : M)
    (hg : B g.coord = g'.coord) (hxx' : T x = x') :
    T (dualAdjoint g x) = dualAdjoint g' x' := by
  have hmap : map (hM := hM) B g = g' := NilpotentLieBCHGroup.ext hg
  have he := dualLinearLift_adjoint hM I B T hT g x hx
  rw [hmap, hxx'] at he
  exact he

end Erdos3.NilpotentLieBCHGroup


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualInvariantSubalgebra (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieSubalgebra ℚ (DualLieAlgebra L) :=
  { U.toSubmodule.comap dualBaseLinear ⊓ V.comap dualTangentLinear with
    lie_mem' := by
      intro x y hx hy
      constructor
      · change dualBaseLinear ⁅x, y⁆ ∈ U
        rw [dualBaseLinear_lie]
        exact U.lie_mem hx.1 hy.1
      · change dualTangentLinear ⁅x, y⁆ ∈ V
        rw [dualTangentLinear_lie]
        apply V.add_mem (hUV _ hx.1 _ hy.2)
        rw [← lie_skew]
        exact V.neg_mem (hUV _ hy.1 _ hx.2) }

@[simp] theorem mem_dualInvariantSubalgebra (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (x : DualLieAlgebra L) :
    x ∈ dualInvariantSubalgebra U V hUV ↔ dualBaseLinear x ∈ U ∧ dualTangentLinear x ∈ V :=
  Iff.rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L) (hx : x ∈ V) :
    dualAdjoint g x ∈ V := by
  let S := dualInvariantSubalgebra U V hUV
  have hc : dualConstantLie g.coord ∈ S := by
    change dualBaseLinear (dualConstantLie g.coord) ∈ U ∧
      dualTangentLinear (dualConstantLie g.coord) ∈ V
    simpa only [dualBaseLinear_constant, dualTangentLinear_constant] using And.intro hg V.zero_mem
  have ht : dualInfinitesimal x ∈ S := by
    change dualBaseLinear (dualInfinitesimal x) ∈ U ∧ dualTangentLinear (dualInfinitesimal x) ∈ V
    simpa only [dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal] using And.intro U.zero_mem hx
  exact (lieBCH_mem S s (lieBCH_mem S s hc ht) (S.neg_mem hc)).2

theorem dualLogDerivative_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (z : DualGroup hnil)
    (hb : dualBaseLinear z.coord ∈ U) (ht : dualTangentLinear z.coord ∈ V) :
    dualLogDerivative z ∈ V := by
  let S := dualInvariantSubalgebra U V hUV
  have hz : z.coord ∈ S := ⟨hb, ht⟩
  have hc : dualConstantLie (dualBaseLinear z.coord) ∈ S := by
    change dualBaseLinear (dualConstantLie (dualBaseLinear z.coord)) ∈ U ∧
      dualTangentLinear (dualConstantLie (dualBaseLinear z.coord)) ∈ V
    simpa only [dualBaseLinear_constant, dualTangentLinear_constant] using And.intro hb V.zero_mem
  exact (lieBCH_mem S s hz (S.neg_mem hc)).2

theorem dualAdjoint_mem_ideal (I : LieIdeal ℚ L) (g : NilpotentLieBCHGroup L s hnil)
    (x : L) (hx : x ∈ I) : dualAdjoint g x ∈ I :=
  dualAdjoint_mem_of_invariant ⊤ I.toSubmodule (fun _ _ _ hv => I.lie_mem hv) g (by trivial) x hx

theorem dualLogDerivative_mem_ideal (I : LieIdeal ℚ L) (z : DualGroup hnil)
    (ht : dualTangentLinear z.coord ∈ I) : dualLogDerivative z ∈ I :=
  dualLogDerivative_mem_of_invariant ⊤ I.toSubmodule (fun _ _ _ hv => I.lie_mem hv) z (by trivial) ht

end NilpotentLieBCHGroup
end Erdos3


namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)
  (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hL hM hT in
theorem dualLinearLift_lieBCH_of_steps {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualLinearLift B T (lieBCH s x y) =
      lieBCH t (dualLinearLift B T x) (dualLinearLift B T y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualLinearLift B T ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualLinearLift B T) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH_of_nilpotent_steps (dualIdealMorphism I B T hT)
      (lie_subalgebra_lowerCentralSeries_eq_bot (dualLie_lowerCentralSeries_eq_bot hL)
        (dualIdealSubalgebra I))
      (dualLie_lowerCentralSeries_eq_bot hM) a b

namespace NilpotentLieBCHGroup

include hT in
theorem dualLinearLift_adjoint_of_steps (g : NilpotentLieBCHGroup L s hL)
    (x : L) (hx : x ∈ I) :
    T (dualAdjoint g x) = dualAdjoint (mapOfSteps (hM := hM) B g) (T x) := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hh := dualLinearLift_lieBCH_of_steps hL hM I B T hT
    (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc)
  rw [dualLinearLift_lieBCH_of_steps hL hM I B T hT hc ht, dualLinearLift_constant,
    dualLinearLift_infinitesimal, map_neg, dualLinearLift_constant] at hh
  have he := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent] at he
  exact he

theorem mapOfSteps_dualAdjoint (g : NilpotentLieBCHGroup L s hL) (x : L) :
    B (dualAdjoint g x) = dualAdjoint (mapOfSteps (hM := hM) B g) (B x) :=
  dualLinearLift_adjoint_of_steps hL hM ⊤ B B.toLinearMap
    (fun a b _ => B.map_lie a b) g x (by trivial)

end NilpotentLieBCHGroup
end Erdos3

end OAI
