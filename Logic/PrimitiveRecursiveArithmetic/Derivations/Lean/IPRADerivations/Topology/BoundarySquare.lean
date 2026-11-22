import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.Data.Fin.SuccPred
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

/-!
# The simplicial boundary squares to zero

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Proposition A01
(`prop:boundary-square`): for `∂[v₀, …, v_k] = ∑_i (−1)^i [v₀, …, v̂_i, …, v_k]`, "`∂² = 0`. Fix two distinct
deleted vertices with original indices `i < j`. Deleting `j` first and then `i` contributes sign `(−1)^{i+j}` …
Deleting `i` first and then the vertex now in position `j − 1` contributes `(−1)^{i+j−1}`. These contributions
cancel. … This is a finite reindexing of integer sums".

A `(k+1)`-simplex is a vertex tuple `σ : Fin (k+2) → V`; its `i`-th face is `σ ∘ i.succAbove`. For any additive
evaluation `φ` of `k`-simplices (a coefficient functional, an indicator of a target face, or a homomorphism to
the integer terms of an iPRA context):

* `swap` is the pairing of deletion orders `(i, j) ↦ (i.succAbove j, j.predAbove i)`: an involution
  (`swap_swap`) without fixed points (`swap_ne`) that preserves the double face (`swap_face`, Mathlib's
  `Fin.succAbove_succAbove_succAbove_predAbove`) and reverses the sign (`swap_sign`);
* `bd_sq`: `∑_{i, j} (−1)^{i+j} φ(σ ∘ i.succAbove ∘ j.succAbove) = 0`;
* `bd_sq_coeff`: every coefficient of `∂∂σ` vanishes, i.e. the integer boundary matrices satisfy `∂² = 0`;
* `bd_sq_chain`: the same for every finite chain `∑_s c_s σ_s`.
-/

namespace LeanProofs.IPRA.Topology.BoundarySquare

variable {V M : Type*} [AddCommGroup M] {n : ℕ}

/-- The pairing of the two deletion orders. -/
def swap (p : Fin (n + 2) × Fin (n + 1)) : Fin (n + 2) × Fin (n + 1) :=
  (p.1.succAbove p.2, p.2.predAbove p.1)

theorem swap_swap (p : Fin (n + 2) × Fin (n + 1)) : swap (swap p) = p := by
  rcases p with ⟨i, j⟩
  simp only [swap, Prod.mk.injEq]
  exact ⟨Fin.succAbove_succAbove_predAbove i j, Fin.predAbove_predAbove_succAbove i j⟩

theorem swap_ne (p : Fin (n + 2) × Fin (n + 1)) : swap p ≠ p := fun h =>
  Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst h)

theorem swap_face (σ : Fin (n + 2) → V) (p : Fin (n + 2) × Fin (n + 1)) :
    σ ∘ (swap p).1.succAbove ∘ (swap p).2.succAbove = σ ∘ p.1.succAbove ∘ p.2.succAbove := by
  funext k
  simp only [swap, Function.comp]
  rw [Fin.succAbove_succAbove_succAbove_predAbove]

theorem swap_sign (p : Fin (n + 2) × Fin (n + 1)) :
    (-1 : ℤ) ^ ((swap p).1.val + (swap p).2.val) = -(-1 : ℤ) ^ (p.1.val + p.2.val) := by
  rcases p with ⟨i, j⟩
  rcases Fin.lt_or_le j.castSucc i with h | h
  · simp only [swap, Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h,
      Fin.val_castSucc, Fin.val_pred]
    have hi : 1 ≤ i.val := by
      have := Fin.lt_def.mp h
      simp only [Fin.val_castSucc] at this
      omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hi
    rw [hm, show j.val + (1 + m - 1) = j.val + m by omega, show 1 + m + j.val = (j.val + m) + 1 by omega,
      _root_.pow_succ]
    ring
  · simp only [swap, Fin.succAbove_of_le_castSucc _ _ h, Fin.predAbove_of_le_castSucc _ _ h,
      Fin.val_succ, Fin.coe_castPred]
    rw [show j.val + 1 + i.val = (i.val + j.val) + 1 by omega, _root_.pow_succ]
    ring

/-- A01: `∑_{i, j} (−1)^{i+j} φ(σ ∘ i.succAbove ∘ j.succAbove) = 0`. -/
theorem bd_sq (φ : (Fin n → V) → M) (σ : Fin (n + 2) → V) :
    ∑ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (p.1.val + p.2.val)) • φ (σ ∘ p.1.succAbove ∘ p.2.succAbove) = 0 := by
  refine Finset.sum_involution (fun p _ => swap p) ?_ ?_ ?_ ?_
  · intro p _
    show ((-1 : ℤ) ^ (p.1.val + p.2.val)) • φ (σ ∘ p.1.succAbove ∘ p.2.succAbove) +
      ((-1 : ℤ) ^ ((swap p).1.val + (swap p).2.val)) • φ (σ ∘ (swap p).1.succAbove ∘ (swap p).2.succAbove) = 0
    rw [swap_face, swap_sign, neg_smul, add_neg_cancel]
  · intro p _ _
    exact swap_ne p
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact swap_swap p

/-- Every coefficient of `∂∂σ` vanishes. -/
theorem bd_sq_coeff [DecidableEq V] (σ : Fin (n + 2) → V) (τ : Fin n → V) :
    ∑ p : Fin (n + 2) × Fin (n + 1),
      (if σ ∘ p.1.succAbove ∘ p.2.succAbove = τ then (-1 : ℤ) ^ (p.1.val + p.2.val) else 0) = 0 := by
  have h := bd_sq (M := ℤ) (fun f => if f = τ then (1 : ℤ) else 0) σ
  simpa [smul_eq_mul, mul_ite] using h

/-- `∂∂` vanishes on every finite chain `∑_s c_s σ_s`. -/
theorem bd_sq_chain {ι : Type*} (S : Finset ι) (c : ι → ℤ) (σ : ι → Fin (n + 2) → V)
    (φ : (Fin n → V) → M) :
    ∑ s ∈ S, c s • ∑ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (p.1.val + p.2.val)) • φ (σ s ∘ p.1.succAbove ∘ p.2.succAbove) = 0 :=
  Finset.sum_eq_zero fun s _ => by rw [bd_sq, smul_zero]

end LeanProofs.IPRA.Topology.BoundarySquare
