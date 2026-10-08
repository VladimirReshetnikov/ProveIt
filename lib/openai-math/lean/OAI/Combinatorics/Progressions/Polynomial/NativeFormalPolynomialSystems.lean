/-
Modified for ProveIt: give nativeFast_derivativeSystem_to_formal a local
400000-heartbeat budget for Lean 4.32 reduction of dependent quotient types.
The upstream theorem statements and proof text are otherwise unchanged.
-/
import OAI.Combinatorics.Progressions.Linear.FastCoefficientRelativeKernel
import OAI.Combinatorics.Progressions.Linear.RealGradedFastCoefficientKernel

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Kf" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
local notation "φ" => F.realFirstCoefficientGradedPolynomial e ω hF (fun _ : σ => 1)
local notation "Vg" => Submodule.restrictScalars ℚ (Submodule.baseChange ℝ (F.fullFastGradedRelative e ω hF W))

theorem realFastCoefficient_relative_iff_polynomial
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (x : F.RealFirstCoefficientModule (fun _ : σ => 1)) :
    x ∈ Kf ↔ φ x ∈ coefficientSubmodule Vg := by
  rw [F.realFirstCoefficientFastSubmodule_relative]
  exact F.realFirstCoefficientFastSubmodule_iff_graded e ω hF (fun _ : σ => 1) W
    (fun _ => Nat.zero_lt_one) hW x

theorem nativeFast_liftSystem_to_formal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (S R : κ → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (h : ∀ z, (Kf).mkQ (S z) =
      F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf g ((Kf).mkQ (R z))) :
    PolynomialLiftSystemMod Vg (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val)
      (fun z => φ (S z)) (fun z => φ (R z)) := by
  intro z
  have hz := h z
  rw [F.realFastCoefficientAction_mk] at hz
  have hq : (Kf).mkQ (S z - F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (R z)) = 0 := by
    rw [map_sub, hz, sub_self]
  have hm : S z - F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (R z) ∈ Kf :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  have hp := (F.realFastCoefficient_relative_iff_polynomial e ω hF W hW _).mp hm
  simpa only [map_sub, F.realFirstCoefficientGradedPolynomial_adjoint] using hp

theorem realFirstCoefficientGradedPolynomial_basisLift {K : Type*}
    [AddCommGroup K] [Module ℝ K] (b : Basis κ ℝ K)
    (S : K →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1)) (x : K) :
    φ (S x) = basisPolynomialLift b (fun z => φ (S (b z))) x := by
  have he : (φ).comp S = basisPolynomialLift b (fun z => φ (S (b z))) := by
    apply b.ext
    intro z
    simp only [LinearMap.comp_apply, basisPolynomialLift_basis]
  exact LinearMap.congr_fun he x

variable [Fintype σ] [DecidableEq σ]

set_option maxHeartbeats 400000 in
theorem nativeFast_derivativeSystem_to_formal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (small rational extra : σ → F.RealFirstCoefficientModule (fun _ : σ => 1))
    (h : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      (Kf).mkQ (small i) +
        F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf g ((Kf).mkQ (rational i)) +
          (Kf).mkQ (extra i)) :
    PolynomialDerivativeSystemMod Vg (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val)
      (fun i => φ (small i)) (fun i => φ (rational i)) (fun i => φ (extra i)) := by
  intro i
  have hi := h i
  rw [F.realFastCoefficientAction_mk] at hi
  change (Kf).mkQ (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1)) = _ at hi
  have hq : (Kf).mkQ (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i)) = 0 := by
    rw [map_sub, map_add, map_add]
    exact sub_eq_zero.mpr hi
  have hm : F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i) ∈ Kf :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  have hp := (F.realFastCoefficient_relative_iff_polynomial e ω hF W hW
    (F.realFirstCoefficientDirectionMap g.val.coord (Pi.single i 1) -
      (small i + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g.val (rational i) + extra i))).mp hm
  simpa only [map_sub, map_add, F.realFirstCoefficientGradedPolynomial_direction,
    F.realFirstCoefficientGradedPolynomial_adjoint] using hp

end Erdos3.NilpotentLieFiltration

end

end OAI
