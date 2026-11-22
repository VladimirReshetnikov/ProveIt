import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The cone identity of a simplex

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Theorem A20
(`thm:simplex-carrier`), its key step: "For a chosen vertex `a` of a simplex, let `c_a[w₀, …, w_k] =
[a, w₀, …, w_k]` … Deleting the first vertex gives the original tuple; every other face cancels its counterpart
in `c_a ∂`. Hence `∂ c_a + c_a ∂ = 1`, including degree zero."

Tuples `σ : Fin (n+1) → V` with faces `σ ∘ j.succAbove` (as in `Topology/BoundarySquare`), the cone
`c_a σ = Fin.cons a σ`, and any additive evaluation `φ`:

* `cone_face_zero`: deleting the first vertex of `c_a σ` gives `σ`;
* `cone_face_succ`: deleting vertex `j + 1` of `c_a σ` gives `c_a` of the `j`-th face of `σ`;
* `cone_identity`: `∑_i (−1)^i φ(face_i (c_a σ)) + ∑_j (−1)^j φ(c_a (face_j σ)) = φ(σ)`, i.e. `∂ c_a + c_a ∂ = 1`
  on every simplex, in degree zero with the empty tuple as the augmentation `∂[w] = 1` and `c_a(1) = [a]`.
-/

namespace LeanProofs.IPRA.Topology.SimplicialCone

variable {V M : Type*} [AddCommGroup M] {n : ℕ}

/-- The cone `c_a σ = [a, σ]`. -/
def cone {m : ℕ} (a : V) (σ : Fin m → V) : Fin (m + 1) → V := Fin.cons a σ

theorem cone_face_zero (a : V) (σ : Fin (n + 1) → V) : cone a σ ∘ Fin.succ = σ := by
  funext x
  simp [cone]

theorem cone_face_succ (a : V) (σ : Fin (n + 1) → V) (j : Fin (n + 1)) :
    cone a σ ∘ j.succ.succAbove = cone a (σ ∘ j.succAbove) := by
  funext x
  refine Fin.cases ?_ (fun y => ?_) x
  · simp [cone, Fin.succ_succAbove_zero]
  · simp [cone, Fin.succ_succAbove_succ]

/-- `∂ c_a + c_a ∂ = 1`. -/
theorem cone_identity (φ : (Fin (n + 1) → V) → M) (a : V) (σ : Fin (n + 1) → V) :
    (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) • φ (cone a σ ∘ i.succAbove)) +
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ j.val) • φ (cone a (σ ∘ j.succAbove)) = φ σ := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, cone_face_zero, Fin.val_succ,
    cone_face_succ, _root_.pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

end LeanProofs.IPRA.Topology.SimplicialCone
