/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import OAI.Combinatorics.Progressions.Geometry.FiniteUnitCoordinate
import OAI.Combinatorics.Progressions.Polynomial.FiniteMomentPolynomial

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem continuous_momentProduct (m : ℕ) :
    Continuous (fun v : Fin m → Fin m → ℂ => momentProduct v) := by
  unfold momentProduct
  fun_prop

theorem exists_momentProduct_unit_lower (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin m → Fin m → ℂ,
      (∀ i, ‖v i‖ = 1) → c ≤ ‖momentProduct v‖ := by
  have hcompact : IsCompact {v : Fin m → Fin m → ℂ | ∀ i, ‖v i‖ = 1} := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      isCompact_pi_infinite (fun _i : Fin m => isCompact_sphere (0 : Fin m → ℂ) 1)
  apply hcompact.exists_forall_le' ((continuous_momentProduct m).norm.continuousOn)
  intro v hv
  apply norm_pos_iff.mpr
  obtain ⟨z, hz⟩ := momentProduct_ne_zero_some v (fun i hi => by
    have h := hv i
    simp only [hi, norm_zero, zero_ne_one] at h)
  intro h
  exact hz (congrFun h z)

theorem momentProduct_smul {m : ℕ} (v : Fin m → Fin m → ℂ) (c : Fin m → ℂ) :
    momentProduct (fun i => c i • v i) = (∏ i, c i) • momentProduct v := by
  funext z
  simp only [momentProduct, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum, Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_momentProduct_lower (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin m → Fin m → ℂ,
      (∀ i, v i ≠ 0) → ∃ z, c * ∏ i, ‖v i‖ ≤ ‖momentProduct v z‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_momentProduct_unit_lower m
  refine ⟨c, hc, ?_⟩
  intro v hv
  let w : Fin m → Fin m → ℂ := fun i => (‖v i‖ : ℂ)⁻¹ • v i
  have hn (i) : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (hv i)
  have hnc (i) : (‖v i‖ : ℂ) ≠ 0 := by exact_mod_cast hn i
  have hw (i) : ‖w i‖ = 1 := by
    simp only [w, norm_smul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (hn i)
  have hreconstruct : (fun i => (‖v i‖ : ℂ) • w i) = v := by
    funext i
    simp only [w, smul_smul, mul_inv_cancel₀ (hnc i), one_smul]
  have hex : ∃ z, c ≤ ‖momentProduct w z‖ := by
    by_contra h
    push Not at h
    exact not_lt_of_ge (hbound w hw) ((pi_norm_lt_iff hc).mpr h)
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ?_⟩
  have heq : ‖momentProduct v z‖ = (∏ i, ‖v i‖) * ‖momentProduct w z‖ := by
    have h := congrFun (momentProduct_smul w (fun i => (‖v i‖ : ℂ))) z
    rw [hreconstruct] at h
    rw [h, Pi.smul_apply, norm_smul, norm_prod]
    simp only [Complex.norm_real, norm_norm]
  rw [heq, mul_comm c]
  exact mul_le_mul_of_nonneg_left hz (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))

noncomputable def momentLowerConstant (m : ℕ) : ℝ :=
  Classical.choose (exists_momentProduct_lower m)

theorem momentLowerConstant_pos (m : ℕ) : 0 < momentLowerConstant m :=
  (Classical.choose_spec (exists_momentProduct_lower m)).1

theorem momentLowerConstant_bound {m : ℕ} (v : Fin m → Fin m → ℂ)
    (hv : ∀ i, v i ≠ 0) :
    ∃ z, momentLowerConstant m * ∏ i, ‖v i‖ ≤ ‖momentProduct v z‖ :=
  (Classical.choose_spec (exists_momentProduct_lower m)).2 v hv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev SymmetricEvaluationIndex (m : ℕ) (I : Type*) := (Fin m → I) × Fin (m * m + 1)

noncomputable def symmetricEvaluation {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (k : SymmetricEvaluationIndex m I) : ℂ :=
  momentProduct (fun i j => v i (k.1 j)) k.2

theorem symmetricEvaluation_permute {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (e : Equiv.Perm (Fin m)) :
    symmetricEvaluation (fun i => v (e i)) = symmetricEvaluation v := by
  funext k
  exact Equiv.prod_comp e (fun i => ∑ j, v i (k.1 j) * (k.2.val : ℂ) ^ j.val)

theorem symmetricEvaluation_smul {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (c : Fin m → ℂ) :
    symmetricEvaluation (fun i => c i • v i) = (∏ i, c i) • symmetricEvaluation v := by
  funext k
  exact congrFun (momentProduct_smul (fun i j => v i (k.1 j)) c) k.2

theorem symmetricEvaluation_const_mul {m : ℕ} {I : Type*}
    (v : Fin m → I → ℂ) (c : ℂ) (k : SymmetricEvaluationIndex m I) :
    symmetricEvaluation (fun i j => c * v i j) k = c ^ m * symmetricEvaluation v k := by
  have h := congrFun (symmetricEvaluation_smul v (fun _ => c)) k
  change symmetricEvaluation (fun i => c • v i) k = _
  simpa only [Pi.smul_apply, smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

theorem symmetricEvaluationIndex_card (m : ℕ) (I : Type*) [Fintype I] :
    Fintype.card (SymmetricEvaluationIndex m I) = Fintype.card I ^ m * (m * m + 1) := by
  simp only [SymmetricEvaluationIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem symmetricEvaluation_lower {m : ℕ} {I : Type*} [Fintype I]
    (v : Fin m → I → ℂ) (hv : ∀ i, ∑ j, ‖v i j‖ ^ 2 = 1) :
    ∃ k, momentLowerConstant m / (Fintype.card I + 1 : ℝ) ^ m ≤
      ‖symmetricEvaluation v k‖ := by
  classical
  choose a ha using fun i => exists_large_unit_coordinate (v i) (hv i)
  let w : Fin m → Fin m → ℂ := fun i j => v i (a j)
  let δ : ℝ := 1 / (Fintype.card I + 1 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hw (i) : δ ≤ ‖w i‖ := (ha i).trans (norm_le_pi_norm (w i) i)
  have hw0 (i) : w i ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hw i))
  obtain ⟨z, hz⟩ := momentLowerConstant_bound w hw0
  refine ⟨(a, z), ?_⟩
  have hprod : δ ^ m ≤ ∏ i, ‖w i‖ := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (fun _ _ => hδ.le) (fun i _ => hw i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  calc
    _ = momentLowerConstant m * δ ^ m := by simp [δ, div_eq_mul_inv, inv_pow]
    _ ≤ momentLowerConstant m * ∏ i, ‖w i‖ :=
      mul_le_mul_of_nonneg_left hprod (momentLowerConstant_pos m).le
    _ ≤ ‖symmetricEvaluation v (a, z)‖ := hz

end Erdos3

end

end OAI
