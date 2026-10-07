import OAI.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
import OAI.Combinatorics.Progressions.Polynomial.DegreeRankSunflower

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def higherHorizontalAmbient (d : ℕ) : F.HigherHorizontal d →ₗ[ℚ] L ⧸ F.layer d 2 :=
  (F.higherHorizontalKernel d).liftQ
    ((F.layer d 2).mkQ.comp (F.layer d 1).subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero (F.layer d 2)).mpr hx)

@[simp] theorem higherHorizontalAmbient_mk (d : ℕ) (x : F.layer d 1) :
    F.higherHorizontalAmbient d (F.higherHorizontalMk d x) = (F.layer d 2).mkQ x.val := rfl

theorem higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective (F.higherHorizontalAmbient d) := by
  intro x y h
  obtain ⟨x, rfl⟩ := F.higherHorizontalMk_surjective d x
  obtain ⟨y, rfl⟩ := F.higherHorizontalMk_surjective d y
  apply (F.higherHorizontalMk_eq d x y).mpr
  exact (Submodule.Quotient.eq (F.layer d 2)).mp h

theorem real_higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective ((F.higherHorizontalAmbient d).baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
    (F.higherHorizontalAmbient d) (F.higherHorizontalAmbient_injective d)

def fourHorizontalAmbient (d : ℕ) :
    (Fin 4 → F.HigherHorizontal d) →ₗ[ℚ] (Fin 4 → L ⧸ F.layer d 2) :=
  LinearMap.pi (fun k => (F.higherHorizontalAmbient d).comp (LinearMap.proj k))

@[simp] theorem fourHorizontalAmbient_apply (d : ℕ) (x : Fin 4 → F.HigherHorizontal d) (k : Fin 4) :
    F.fourHorizontalAmbient d x k = F.higherHorizontalAmbient d (x k) := rfl

theorem fourHorizontalAmbient_injective (d : ℕ) :
    Function.Injective (F.fourHorizontalAmbient d) := by
  intro x y h
  funext k
  exact F.higherHorizontalAmbient_injective d (congrFun h k)

theorem fourHorizontalAmbient_map (d : ℕ) (x : F.fourHorizontalLayer d) (k : Fin 4) :
    F.fourHorizontalAmbient d (F.fourHorizontalMap d x) k = (F.layer d 2).mkQ (x.val k) := rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
