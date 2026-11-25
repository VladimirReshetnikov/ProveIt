import IPRADerivations.Core.CertificateTactics

/-!
# Degree sequences: parity, regular graphs and the edge bound

Packet: `combinatorics/graph-ipra`, `tex/elementary.tex`, Proposition 2.1 (`prop:degree`, the parity and regular
parts) and Proposition 2.2 ("Simple graph degree bounds"). The degrees `d_v` of the vertices `v : Fin k` and the
number of edges `m` are integer terms with the handshake identity `∑_v d_v = 2m`
(`Combinatorics/GraphIncidence.handshake`) as a hypothesis. As iPRA derivations:

* `odd_vertices_even`: "Write `d(v) = 2 q_v + b_v` with `b_v ∈ {0, 1}`. Reducing the sum modulo two proves the
  parity assertion": `∑_v b_v = 2 (m − ∑_v q_v)`, so the number of odd-degree vertices is even;
* `regular_count`: "In an `r`-regular graph `n r = 2m`";
* `edge_bound`: "`0 ≤ d(v) ≤ n − 1` and `m ≤ C(n, 2)`", as `2m ≤ (k + 1) k` on `k + 1` vertices;
* `complement_degrees`: "Complementation replaces each degree `d` by `n − 1 − d`": the complementary degrees sum
  to `(k + 1) k − 2m`, twice the number `C(n, 2) − m` of missing edges.

Not derived: "some two vertices have the same degree" (a pigeonhole on the degree values) and the equality case
`K_n`.
-/

namespace LeanProofs.IPRA.Combinatorics.DegreeBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- `∑ (2 q_v + b_v) = 2 ∑ q_v + ∑ b_v`. -/
theorem sum_parity {R : Type*} [CommRing R] (q b : Fin k → R) :
    ∑ v, (2 * q v + b v) = 2 * ∑ v, q v + ∑ v, b v := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The number of odd-degree vertices is even: `∑ b_v = 2 (m − ∑ q_v)`. -/
theorem odd_vertices_even (d q b : Fin k → ZT n) (m : ZT n)
    (hd : ∀ v, Γ ⊢[PRAAx] ZT.eq (d v) (ZT.natLit 2 * q v + b v))
    (hs : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin b) (ZT.natLit 2 * (m - ZT.sumFin q)) := by
  have hd1 : ∀ v, ZT.toZ Γ (d v) = 2 * ZT.toZ Γ (q v) + ZT.toZ Γ (b v) := fun v => by
    have h := ZT.toZ_eq (hd v)
    simpa only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] using h
  have e := ZT.toZ_eq hs
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at e
  rw [Finset.sum_congr rfl fun v _ => hd1 v, sum_parity] at e
  ipra_lc e

/-- An `r`-regular graph on `k` vertices: `k r = 2m`. -/
theorem regular_count (d : Fin k → ZT n) (r m : ZT n) (hd : ∀ v, Γ ⊢[PRAAx] ZT.eq (d v) r)
    (hs : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit k * r) (ZT.natLit 2 * m) := by
  have hd1 : ∀ v, ZT.toZ Γ (d v) = ZT.toZ Γ r := fun v => ZT.toZ_eq (hd v)
  have e := ZT.toZ_eq hs
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at e
  rw [Finset.sum_congr rfl fun v _ => hd1 v, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at e
  apply ZT.derive
  zsimp
  exact e

/-- The edge bound on `k + 1` vertices: degrees at most `k` give `2m ≤ (k + 1) k`. -/
theorem edge_bound (d : Fin (k + 1) → ZT n) (m : ZT n) (hd : ∀ v, Γ ⊢[PRAAx] zle (d v) (ZT.natLit k))
    (hs : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m)) :
    Γ ⊢[PRAAx] zle (ZT.natLit 2 * m) (ZT.natLit (k + 1) * ZT.natLit k) := by
  have e := ZT.toZ_eq hs
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at e
  refine zle_of_comb (∑ v, zsl (hd v)) ?_ (nn_sum _ _ fun v _ => nn_zsl _)
  zsimp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination e

/-- The complementary degrees `k − d_v` on `k + 1` vertices sum to `(k + 1) k − 2m`. -/
theorem complement_degrees (d : Fin (k + 1) → ZT n) (m : ZT n)
    (hs : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => ZT.natLit k - d v)
      (ZT.natLit (k + 1) * ZT.natLit k - ZT.natLit 2 * m) := by
  ipra_lc [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] -ZT.toZ_eq hs

end LeanProofs.IPRA.Combinatorics.DegreeBounds
