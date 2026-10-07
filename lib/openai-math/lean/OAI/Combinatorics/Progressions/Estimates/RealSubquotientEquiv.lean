/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. Import paths are adapted to Mathlib v4.32.0. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem one_tmul_mem_real_baseChange_iff {V : Type*} [AddCommGroup V] [Module ℚ V]
    (S : Submodule ℚ V) (v : V) : (1 : ℝ) ⊗ₜ[ℚ] v ∈ S.baseChange ℝ ↔ v ∈ S := by
  constructor
  · intro hv
    let : Module.Free ℚ (V ⧸ S) := Module.Free.of_divisionRing ℚ (V ⧸ S)
    have hker : S.baseChange ℝ ≤ LinearMap.ker (S.mkQ.baseChange ℝ) := by
      rw [Submodule.baseChange_eq_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      change S.mkQ.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) = 0
      rw [LinearMap.baseChange_tmul]
      have hxq : S.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hx
      rw [hxq, TensorProduct.tmul_zero]
    have hz : (1 : ℝ) ⊗ₜ[ℚ] S.mkQ v = 0 := hker hv
    have hinj := Module.Flat.tensorProduct_mk_injective (R := ℚ) (S := ℝ) (M := V ⧸ S)
    have hvq : S.mkQ v = 0 := hinj (by simpa only [TensorProduct.mk_apply, map_zero] using hz)
    exact (Submodule.Quotient.mk_eq_zero S).mp hvq
  · exact Submodule.tmul_mem_baseChange_of_mem 1

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem real_baseChange_iSup {I : Sort*} {L : Type*} [AddCommGroup L] [Module ℚ L]
    (P : I → Submodule ℚ L) :
    (⨆ i, P i).baseChange ℝ = ⨆ i, (P i).baseChange ℝ := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.iSup_induction P hy
      (motive := fun y => (1 : ℝ) ⊗ₜ[ℚ] y ∈ ⨆ i, (P i).baseChange ℝ)
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i (Submodule.tmul_mem_baseChange_of_mem 1 hy)
    · simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
    · intro y z hy hz
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
  · apply iSup_le
    intro i
    exact Submodule.baseChange_mono ℝ (le_iSup P i)

theorem real_restrictScalars_iSup {I : Sort*} {L : Type*} [AddCommGroup L]
    [Module ℚ L] [Module ℝ L] [IsScalarTower ℚ ℝ L] (P : I → Submodule ℝ L) :
    (⨆ i, P i).restrictScalars ℚ = ⨆ i, (P i).restrictScalars ℚ := by
  apply le_antisymm
  · intro x hx
    change x ∈ ⨆ i, P i at hx
    apply Submodule.iSup_induction P hx
      (motive := fun y => y ∈ ⨆ i, (P i).restrictScalars ℚ)
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i hy
    · exact Submodule.zero_mem _
    · intro y z hy hz
      exact Submodule.add_mem _ hy hz
  · apply iSup_le
    intro i x hx
    exact Submodule.mem_iSup_of_mem i hx

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_subtype_injective (P : Submodule ℚ V) :
    Function.Injective (P.subtype.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) P.subtype
    (fun _ _ h => Subtype.ext h)

noncomputable def realificationSubmoduleEquiv (P : Submodule ℚ V) :
    (ℝ ⊗[ℚ] P) ≃ₗ[ℝ] P.baseChange ℝ :=
  LinearEquiv.ofInjective (P.subtype.baseChange ℝ) (realification_subtype_injective P)

@[simp] theorem realificationSubmoduleEquiv_coe (P : Submodule ℚ V) (x : ℝ ⊗[ℚ] P) :
    (realificationSubmoduleEquiv P x : ℝ ⊗[ℚ] V) = P.subtype.baseChange ℝ x := rfl

@[simp] theorem realificationSubmoduleEquiv_tmul (P : Submodule ℚ V) (r : ℝ) (x : P) :
    (realificationSubmoduleEquiv P (r ⊗ₜ[ℚ] x) : ℝ ⊗[ℚ] V) = r ⊗ₜ[ℚ] (x : V) := rfl

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

theorem realification_ker (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have h : Function.Exact ((LinearMap.ker f).subtype.baseChange ℝ) (f.baseChange ℝ) :=
    Module.Flat.lTensor_exact ℝ f.exact_subtype_ker_map
  exact (LinearMap.exact_iff.mp h).symm

theorem realification_comap (P : Submodule ℚ W) (f : V →ₗ[ℚ] W) :
    (P.comap f).baseChange ℝ = (P.baseChange ℝ).comap (f.baseChange ℝ) := by
  have he : P.comap f = LinearMap.ker (P.mkQ.comp f) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [he, realification_ker, LinearMap.baseChange_comp, LinearMap.ker_comp,
    ← realification_ker, Submodule.ker_mkQ]

theorem realification_mkQ_eq_zero_iff (P : Submodule ℚ V) (x : ℝ ⊗[ℚ] V) :
    P.mkQ.baseChange ℝ x = 0 ↔ x ∈ P.baseChange ℝ := by
  change x ∈ LinearMap.ker (P.mkQ.baseChange ℝ) ↔ _
  rw [← realification_ker, Submodule.ker_mkQ]

theorem realification_prod (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z) (x : ℝ ⊗[ℚ] V) :
    TensorProduct.prodRight ℚ ℝ ℝ W Z ((f.prod g).baseChange ℝ x) =
      (f.baseChange ℝ x, g.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

theorem realification_prod_eq_zero_iff (f : V →ₗ[ℚ] W) (g : V →ₗ[ℚ] Z)
    (x : ℝ ⊗[ℚ] V) :
    (f.prod g).baseChange ℝ x = 0 ↔ f.baseChange ℝ x = 0 ∧ g.baseChange ℝ x = 0 := by
  constructor
  · intro h
    have he := congrArg (TensorProduct.prodRight ℚ ℝ ℝ W Z) h
    rw [realification_prod, map_zero] at he
    exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
  · intro h
    apply (TensorProduct.prodRight ℚ ℝ ℝ W Z).injective
    rw [realification_prod, map_zero, h.1, h.2]
    rfl

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (P Q : Submodule ℚ E)

abbrev RealSubquotient :=
  @HasQuotient.Quotient (P.baseChange ℝ) (Submodule ℝ (P.baseChange ℝ))
    (@Submodule.hasQuotient ℝ (P.baseChange ℝ) _ _ _)
    ((Q.baseChange ℝ).comap (P.baseChange ℝ).subtype)

noncomputable def realSubquotientProjection : P.baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] (P ⧸ Q.comap P.subtype)) :=
  ((Q.comap P.subtype).mkQ.baseChange ℝ).comp (realificationSubmoduleEquiv P).symm.toLinearMap

theorem realSubquotientProjection_surjective : Function.Surjective (realSubquotientProjection P Q) := by
  have hq : Function.Surjective ((Q.comap P.subtype).mkQ.baseChange ℝ) :=
    LinearMap.lTensor_surjective ℝ (Q.comap P.subtype).mkQ_surjective
  exact hq.comp (realificationSubmoduleEquiv P).symm.surjective

theorem realSubquotientProjection_ker :
    LinearMap.ker (realSubquotientProjection P Q) =
      (Q.baseChange ℝ).comap (P.baseChange ℝ).subtype := by
  ext x
  change (Q.comap P.subtype).mkQ.baseChange ℝ ((realificationSubmoduleEquiv P).symm x) = 0 ↔
    x.val ∈ Q.baseChange ℝ
  rw [realification_mkQ_eq_zero_iff, realification_comap]
  change P.subtype.baseChange ℝ ((realificationSubmoduleEquiv P).symm x) ∈ Q.baseChange ℝ ↔ _
  have he := congrArg Subtype.val ((realificationSubmoduleEquiv P).apply_symm_apply x)
  rw [← realificationSubmoduleEquiv_coe, he]

noncomputable def realSubquotientEquiv :
    (ℝ ⊗[ℚ] (P ⧸ Q.comap P.subtype)) ≃ₗ[ℝ]
      RealSubquotient P Q :=
  (realSubquotientProjection P Q).quotKerEquivOfSurjective (realSubquotientProjection_surjective P Q) |>.symm |>.trans
    (Submodule.quotEquivOfEq _ _ (realSubquotientProjection_ker P Q))

theorem realSubquotientEquiv_project (x : ℝ ⊗[ℚ] P) :
    realSubquotientEquiv P Q ((Q.comap P.subtype).mkQ.baseChange ℝ x) =
      ((Q.baseChange ℝ).comap (P.baseChange ℝ).subtype).mkQ (realificationSubmoduleEquiv P x) := by
  have hx : (Q.comap P.subtype).mkQ.baseChange ℝ x =
      realSubquotientProjection P Q (realificationSubmoduleEquiv P x) := by
    simp only [realSubquotientProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  rw [hx]
  dsimp only [realSubquotientEquiv, LinearEquiv.trans_apply]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end Erdos3

end

end OAI
