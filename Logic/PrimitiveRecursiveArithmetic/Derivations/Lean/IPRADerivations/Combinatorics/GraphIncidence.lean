import IPRADerivations.Core.IntCertificates

/-!
# Incidence identities of a finite graph

Packet: `combinatorics/graph-ipra`, `tex/elementary.tex`, Proposition 2.1 (`prop:degree`, "Incidence identities
and parity") and Theorem 9.1 ("Laplacian energy, nullity and eigenvalue bounds"); also result 19 of
`combinatorics/Combinatorics-iPRA` ("`∑_v d(v) = 2 e(G)`"). The graph has vertex set `Fin k` and a symmetric
weight matrix `A v w` of integer terms (edge multiplicities or weights; `0/1` for a simple graph), as iPRA
derivations:

* `sum_sym`, `handshake`: for a symmetric matrix with zero diagonal, `∑_v ∑_w A_{vw} = 2 ∑_{v<w} A_{vw}`: the
  degree sum is twice the number of edges ("Each edge has two ends");
* `laplacian_identity`, `laplacian_energy`: `2 xᵀ L x = ∑_v ∑_w A_{vw} (x_v − x_w)²` for the Laplacian
  `L = D − A`;
* `laplacian_nonneg`: for nonnegative weights, `xᵀ L x ≥ 0` (doubled).
-/

namespace LeanProofs.IPRA.Combinatorics.GraphIncidence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- A symmetric matrix with zero diagonal: the full sum is twice the sum above the diagonal. -/
theorem sum_sym (a : Fin k → Fin k → R) (hs : ∀ v w, a v w = a w v) (h0 : ∀ v, a v v = 0) :
    ∑ v, ∑ w, a v w = 2 * ∑ v, ∑ w, (if v < w then a v w else 0) := by
  have hpt : ∀ v w, a v w = (if v < w then a v w else 0) + (if w < v then a v w else 0) := by
    intro v w
    rcases _root_.lt_trichotomy v w with h | h | h
    · rw [if_pos h, if_neg (_root_.not_lt.mpr (_root_.le_of_lt h)), _root_.add_zero]
    · subst h
      rw [if_neg (_root_.lt_irrefl v), h0, _root_.add_zero]
    · rw [if_neg (_root_.not_lt.mpr (_root_.le_of_lt h)), if_pos h, _root_.zero_add]
  have hswap : ∑ v, ∑ w, (if w < v then a v w else 0) = ∑ v, ∑ w, (if v < w then a v w else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by rw [hs w v]
  have hsplit : ∑ v, ∑ w, a v w =
      ∑ v, ∑ w, (if v < w then a v w else 0) + ∑ v, ∑ w, (if w < v then a v w else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => hpt v w
  rw [hsplit, hswap]
  ring

/-- `2 xᵀ (D − A) x = ∑_v ∑_w a_{vw} (x_v − x_w)²` for a symmetric matrix. -/
theorem laplacian_identity (a : Fin k → Fin k → R) (x : Fin k → R) (hs : ∀ v w, a v w = a w v) :
    2 * ∑ v, x v * ((∑ w, a v w) * x v - ∑ w, a v w * x w) = ∑ v, ∑ w, a v w * (x v - x w) ^ 2 := by
  have h1 : ∀ v, x v * ((∑ w, a v w) * x v - ∑ w, a v w * x w) =
      ∑ w, (a v w * x v ^ 2 - a v w * (x v * x w)) := by
    intro v
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  have h3 : ∑ v, ∑ w, a v w * x w ^ 2 = ∑ v, ∑ w, a v w * x v ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by rw [hs w v]
  have e1 : ∑ v, ∑ w, (a v w * x v ^ 2 - a v w * (x v * x w)) =
      ∑ v, ∑ w, a v w * x v ^ 2 - ∑ v, ∑ w, a v w * (x v * x w) := by
    simp only [Finset.sum_sub_distrib]
  have e2 : ∑ v, ∑ w, a v w * (x v - x w) ^ 2 =
      ∑ v, ∑ w, a v w * x v ^ 2 - 2 * ∑ v, ∑ w, a v w * (x v * x w) + ∑ v, ∑ w, a v w * x w ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [Finset.sum_congr rfl fun v _ => h1 v, e1, e2, h3]
  ring

end Ring

/-! ## The derivations -/

/-- The handshake identity: the degree sum is twice the sum over the pairs `v < w`. -/
theorem handshake (A : Fin k → Fin k → ZT n) (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v))
    (h0 : ∀ v, Γ ⊢[PRAAx] ZT.eq (A v v) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => ZT.sumFin fun w => A v w)
      (ZT.natLit 2 * ZT.sumFin fun v => ZT.sumFin fun w => if v < w then A v w else ZT.natLit 0) := by
  have hs' : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have h0' : ∀ v, ZT.toZ Γ (A v v) = 0 := fun v => by
    have h := ZT.toZ_eq (h0 v)
    simpa only [ZT.toZ_natLit, Nat.cast_zero] using h
  have e := sum_sym (fun v w => ZT.toZ Γ (A v w)) hs' h0'
  beta_reduce at e
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat, apply_ite (ZT.toZ Γ), Nat.cast_zero]
  exact e

/-- The Laplacian energy: `2 xᵀ L x = ∑_v ∑_w A_{vw} (x_v − x_w)²`. -/
theorem laplacian_energy (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * ZT.sumFin fun v => x v * ((ZT.sumFin fun w => A v w) * x v - ZT.sumFin fun w => A v w * x w))
      (ZT.sumFin fun v => ZT.sumFin fun w => A v w * ZT.sq (x v - x w)) := by
  have hs' : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have e := laplacian_identity (fun v w => ZT.toZ Γ (A v w)) (fun v => ZT.toZ Γ (x v)) hs'
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- For nonnegative weights the Laplacian is positive semidefinite: `0 ≤ 2 xᵀ L x`. -/
theorem laplacian_nonneg (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) (hA : ∀ v w, Γ ⊢[PRAAx] zle (ZT.natLit 0) (A v w)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 0)
      (ZT.natLit 2 * ZT.sumFin fun v => x v * ((ZT.sumFin fun w => A v w) * x v - ZT.sumFin fun w => A v w * x w)) := by
  have hs' : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have e := laplacian_identity (fun v w => ZT.toZ Γ (A v w)) (fun v => ZT.toZ Γ (x v)) hs'
  beta_reduce at e
  refine zle_of_comb (∑ v, ∑ w, ZT.toZ Γ (A v w) * ZT.toZ Γ (x v - x w) ^ 2) ?_
    (nn_sum _ _ fun v _ => nn_sum _ _ fun w _ => nn_mul (nn_zle0 (hA v w)) (nn_zsq _))
  zsimp
  rw [sub_zero]
  exact e

end LeanProofs.IPRA.Combinatorics.GraphIncidence
