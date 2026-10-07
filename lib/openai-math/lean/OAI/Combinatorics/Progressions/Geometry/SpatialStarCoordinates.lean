import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod

namespace OAI

section

namespace Erdos3

def spatialStar {I R : Type*} [Add R] (v : (Unit ⊕ I) → R) : (Unit ⊕ I) → R :=
  Sum.elim (fun _ => v (.inl ())) (fun i => v (.inl ()) + v (.inr i))

def spatialUnstar {I R : Type*} [Sub R] (v : (Unit ⊕ I) → R) : (Unit ⊕ I) → R :=
  Sum.elim (fun _ => v (.inl ())) (fun i => v (.inr i) - v (.inl ()))

theorem spatialUnstar_star {I R : Type*} [AddCommGroup R] (v : (Unit ⊕ I) → R) :
    spatialUnstar (spatialStar v) = v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar]

theorem spatialStar_unstar {I R : Type*} [AddCommGroup R] (v : (Unit ⊕ I) → R) :
    spatialStar (spatialUnstar v) = v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar]

theorem spatialUnstar_lipschitz (I : Type*) [Fintype I] :
    LipschitzWith 2 (spatialUnstar (I := I) (R := ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  cases i with
  | inl i =>
    have h := dist_le_pi_dist v w (.inl ())
    change dist (v (.inl ())) (w (.inl ())) ≤ _
    norm_num only [NNReal.coe_ofNat]
    linarith [dist_nonneg (x := v) (y := w)]
  | inr i =>
    have h := dist_sub_sub_le (v (.inr i)) (v (.inl ())) (w (.inr i)) (w (.inl ()))
    have h1 := dist_le_pi_dist v w (.inr i)
    have h0 := dist_le_pi_dist v w (.inl ())
    change dist (v (.inr i) - v (.inl ())) (w (.inr i) - w (.inl ())) ≤ _
    norm_num only [NNReal.coe_ofNat]
    linarith

theorem spatialUnstar_scaled_star {I : Type*} (v : (Unit ⊕ I) → ℤ) (H : ℝ) :
    spatialUnstar (fun i => ((spatialStar v i : ℤ) : ℝ) / H) = fun i => (v i : ℝ) / H := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar, Int.cast_add, add_div]

theorem spatialUnstar_residue_star {I : Type*} (v : (Unit ⊕ I) → ℤ) (m : ℕ) :
    spatialUnstar (fun i => ((spatialStar v i : ℤ) : ZMod m)) = integerResidueMap (Unit ⊕ I) m v := by
  funext i
  cases i with
  | inl i => cases i; rfl
  | inr i => simp [spatialUnstar, spatialStar, integerResidueMap]

def spatialStarVertex {I : Type*} : (Unit ⊕ I) → Finset I :=
  Sum.elim (fun _ => ∅) (fun i => {i})

theorem spatialStar_vertex {I R : Type*} [AddCommMonoid R] (v : (Unit ⊕ I) → R) (i : Unit ⊕ I) :
    spatialStar v i = v (.inl ()) + ∑ j ∈ spatialStarVertex i, v (.inr j) := by
  cases i with
  | inl i => cases i; simp [spatialStar, spatialStarVertex]
  | inr i => simp [spatialStar, spatialStarVertex]

end Erdos3

end

end OAI
