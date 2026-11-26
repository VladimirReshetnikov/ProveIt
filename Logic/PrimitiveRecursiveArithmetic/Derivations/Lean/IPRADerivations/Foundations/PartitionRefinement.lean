import IPRADerivations.Foundations.ErrorBudget
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.Header

/-!
# Integration is invariant under certified partition refinement

Packet: `foundations/ipra_continuous_measure_2026-11-20`, `lean/ContinuousMeasure/Presentations.lean` (host-level
Lean there): `Refinement` ("a finite partition refinement including all mass equations, also for zero-mass
coarse cells"), `refinement_integral` ("Exact integration is unchanged by a certified finite refinement"),
`refinement_l1` and `refinement_rho`.

For `k` coarse cells with weights `C_i`, `m` fine cells with weights `W_j` and a parent map `p : Fin m → Fin k`
(fixed finite data), with the mass equations `∑_{j : p j = i} W_j = C_i` as derived hypotheses, and any
observation `f` of natural terms on the coarse cells:

* `refinement_integral`: `∑_j W_j f_{p(j)} = ∑_i C_i f_i`;
* `refinement_l1`: the same for `|f − g|`, so the `L¹` distance (and likewise every pulled-back observation)
  is unchanged.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.PartitionRefinement

open_ipra
open LeanProofs.IPRA.Foundations.ErrorBudget (nsum toG_nsum)
open LeanProofs.IPRA.Probability.Variance (ad)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The regrouping identity in any commutative ring. -/
theorem fiber_identity {R : Type*} [CommRing R] {k m : ℕ} (p : Fin m → Fin k) (W : Fin m → R)
    (C F : Fin k → R) (hm : ∀ i, ∑ j, (if p j = i then W j else 0) = C i) :
    ∑ j, W j * F (p j) = ∑ i, C i * F i := by
  have : ∑ i, C i * F i = ∑ i, ∑ j, (if p j = i then W j * F i else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hm i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [this, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (p j)]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `refinement_integral`: `∑_j W_j f_{p(j)} = ∑_i C_i f_i`. -/
theorem refinement_integral {k m : ℕ} (p : Fin m → Fin k) (W : Fin m → PTm n) (C f : Fin k → PTm n)
    (hm : ∀ i, Γ ⊢[PRAAx] (nsum fun j => if p j = i then W j else zero) ≐ C i) :
    Γ ⊢[PRAAx] (nsum fun j => W j * f (p j)) ≐ nsum fun i => C i * f i := by
  have hm' : ∀ i, ∑ j, (if p j = i then Groth.ι (Q.mk Γ (W j)) else 0) = Groth.ι (Q.mk Γ (C i)) := by
    intro i
    have h := natEq (hm i)
    rw [toG_nsum] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp [Q.mk_zero]
  apply deriveNat
  simp only [toG_nsum, Q.mk_mul, map_mul]
  exact fiber_identity p (fun j => Groth.ι (Q.mk Γ (W j))) (fun i => Groth.ι (Q.mk Γ (C i)))
    (fun i => Groth.ι (Q.mk Γ (f i))) hm'

/-- `refinement_l1`: the `L¹` distance is unchanged by refinement. -/
theorem refinement_l1 {k m : ℕ} (p : Fin m → Fin k) (W : Fin m → PTm n) (C f g : Fin k → PTm n)
    (hm : ∀ i, Γ ⊢[PRAAx] (nsum fun j => if p j = i then W j else zero) ≐ C i) :
    Γ ⊢[PRAAx] (nsum fun j => W j * ad (f (p j)) (g (p j))) ≐ nsum fun i => C i * ad (f i) (g i) :=
  refinement_integral p W C (fun i => ad (f i) (g i)) hm

end LeanProofs.IPRA.Foundations.PartitionRefinement
