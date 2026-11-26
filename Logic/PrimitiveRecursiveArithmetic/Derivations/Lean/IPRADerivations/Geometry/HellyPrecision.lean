import IPRADerivations.Core.IntCertificates
import IPRADerivations.Topology.MetricNets

/-!
# Precision-preserving Helly: the weighted error bound

Packet: `geometry/helly-ipra`, `helly.tex`, Theorem `thm:approx` ("Precision-preserving Helly") and the remark
on closed intervals with real endpoints, as iPRA derivations (weights and coordinates as integer terms cleared
of denominators, interval endpoints as natural terms):

* `weighted_precision`: "`‖v_{i,k}(t) − y_k‖ ≤ ∑_T w_{iT} ‖u_T(t) − u_T(k)‖ ≤ 2^{-t} + 2^{-k}`": for weights
  `w_T ≥ 0` of mass `m` and coordinate errors `|x_T| ≤ E`, `|∑_T w_T x_T| ≤ m E` (the same bound gives the
  regularity of the name `v_{i,k}`, "by summing the individual bounds with nonnegative weights of mass one");
* `join_shift`: "The inequality `|max_j u_j − max_j v_j| ≤ max_j |u_j − v_j|` preserves the regularity bound":
  the maximum of two terms is nonexpansive (one side; the other by symmetry).
-/

namespace LeanProofs.IPRA.Geometry.HellyPrecision

open_ipra
open LeanProofs.IPRA.Topology.MetricNets (join le_join_left le_join_right join_le)

variable {n t : ℕ} {Γ : List (Fm PTm n)}

/-- The weighted error bound: `|∑ w_T x_T| ≤ m E` for `w_T ≥ 0`, `∑ w_T = m`, `|x_T| ≤ E`. -/
theorem weighted_precision (w x : Fin t → ZT n) (E m : ZT n)
    (hw : ∀ T, Γ ⊢[PRAAx] zle (ZT.natLit 0) (w T)) (h₁ : ∀ T, Γ ⊢[PRAAx] zle (-E) (x T))
    (h₂ : ∀ T, Γ ⊢[PRAAx] zle (x T) E) (hm : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin w) m) :
    (Γ ⊢[PRAAx] zle (-(m * E)) (ZT.sumFin fun T => w T * x T)) ∧
      (Γ ⊢[PRAAx] zle (ZT.sumFin fun T => w T * x T) (m * E)) := by
  have e := ZT.toZ_eq hm
  simp only [ZT.toZ_sumFin] at e
  have hsum : ∑ T, ZT.toZ Γ (w T) * ZT.toZ Γ E = ZT.toZ Γ m * ZT.toZ Γ E := by
    rw [← Finset.sum_mul, e]
  have key₁ : ∑ T, ZT.toZ Γ (w T) * (ZT.toZ Γ (x T) - -ZT.toZ Γ E) =
      ∑ T, ZT.toZ Γ (w T) * ZT.toZ Γ (x T) + ZT.toZ Γ m * ZT.toZ Γ E := by
    rw [← hsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun T _ => by ring
  have key₂ : ∑ T, ZT.toZ Γ (w T) * (ZT.toZ Γ E - ZT.toZ Γ (x T)) =
      ZT.toZ Γ m * ZT.toZ Γ E - ∑ T, ZT.toZ Γ (w T) * ZT.toZ Γ (x T) := by
    rw [← hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun T _ => by ring
  refine ⟨?_, ?_⟩
  · refine zle_of_comb (∑ T, ZT.toZ Γ (w T) * zsl (h₁ T)) ?_
      (nn_sum _ _ fun T _ => nn_mul (nn_zle0 (hw T)) (nn_zsl _))
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_neg]
    rw [key₁]
    ring
  · refine zle_of_comb (∑ T, ZT.toZ Γ (w T) * zsl (h₂ T)) ?_
      (nn_sum _ _ fun T _ => nn_mul (nn_zle0 (hw T)) (nn_zsl _))
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul]
    rw [key₂]

/-- The maximum is nonexpansive: `a ≤ D + a'` and `b ≤ D + b'` give `max a b ≤ D + max a' b'`. -/
theorem join_shift {a b a' b' D : PTm n} (ha : Γ ⊢[PRAAx] le a (D + a')) (hb : Γ ⊢[PRAAx] le b (D + b')) :
    Γ ⊢[PRAAx] le (join a b) (D + join a' b') := by
  have la := le_join_left (Γ := Γ) a' b'
  have lb := le_join_right (Γ := Γ) a' b'
  refine join_le ?_ ?_
  · ipra_le sl ha + sl la
  · ipra_le sl hb + sl lb

end LeanProofs.IPRA.Geometry.HellyPrecision
