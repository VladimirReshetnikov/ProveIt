import IPRADerivations.Core.CertificateTactics

/-!
# Degree sums of the four graph products

Packet: `combinatorics/graph-ipra`, `tex/operations.tex`, Proposition `prop:products` ("Products and line
graphs"): for simple graphs `G, H` of orders `n, h`, sizes `m, l` and degrees `d_u, e_x`, the Cartesian, tensor,
strong and lexicographic products have degree `d_u + e_x`, `d_u e_x`, `d_u + e_x + d_u e_x`, `h d_u + e_x` at
`(u, x)`, and `m h + l n`, `2 m l`, `m h + l n + 2 m l`, `m h² + n l` edges.

The degrees are vectors `d : Fin p → ZT n`, `e : Fin q → ZT n` of integer terms with `∑ d = 2 m` and
`∑ e = 2 l` (the handshake identity of each factor). As iPRA derivations, the sum of the degrees of each
product over the `p q` vertices is twice the stated number of edges:

* `cartesian_degree_sum`: `∑_{u,x} (d_u + e_x) = 2 (m q + l p)`;
* `tensor_degree_sum`: `∑_{u,x} d_u e_x = 2 (2 m l)`;
* `strong_degree_sum`: `∑_{u,x} (d_u + e_x + d_u e_x) = 2 (m q + l p + 2 m l)`;
* `lexicographic_degree_sum`: `∑_{u,x} (q d_u + e_x) = 2 (m q² + p l)`.

Not derived: the adjacency of the products and their degrees as counts, and the line-graph formulas.
-/

namespace LeanProofs.IPRA.Combinatorics.GraphProducts

open_ipra

variable {n p q : ℕ} {Γ : List (Fm PTm n)}

/-- `∑_{u,x} (d_u + e_x) = q ∑ d + p ∑ e`. -/
theorem sum_add_grid {R : Type*} [CommRing R] (d : Fin p → R) (e : Fin q → R) :
    ∑ u, ∑ x, (d u + e x) = (q : R) * ∑ u, d u + (p : R) * ∑ x, e x := by
  have h1 : ∀ u, ∑ x, (d u + e x) = (q : R) * d u + ∑ x, e x := fun u => by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun u _ => h1 u, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `∑_{u,x} d_u e_x = (∑ d)(∑ e)`. -/
theorem sum_mul_grid {R : Type*} [CommRing R] (d : Fin p → R) (e : Fin q → R) :
    ∑ u, ∑ x, d u * e x = (∑ u, d u) * ∑ x, e x :=
  (Finset.sum_mul_sum _ _ _ _).symm

/-- The Cartesian product: the degrees sum to `2 (m q + l p)`. -/
theorem cartesian_degree_sum (d : Fin p → ZT n) (e : Fin q → ZT n) {m l : ZT n}
    (hd : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m))
    (he : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin e) (ZT.natLit 2 * l)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun u => ZT.sumFin fun x => d u + e x)
      (ZT.natLit 2 * (m * ZT.natLit q + l * ZT.natLit p)) := by
  have ed := ZT.toZ_eq hd
  have ee := ZT.toZ_eq he
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at ed ee
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat]
  rw [sum_add_grid (fun u => ZT.toZ Γ (d u)) (fun x => ZT.toZ Γ (e x))]
  linear_combination (q : Groth (Q Γ)) * ed + (p : Groth (Q Γ)) * ee

/-- The tensor product: the degrees sum to `2 (2 m l)`. -/
theorem tensor_degree_sum (d : Fin p → ZT n) (e : Fin q → ZT n) {m l : ZT n}
    (hd : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m))
    (he : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin e) (ZT.natLit 2 * l)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun u => ZT.sumFin fun x => d u * e x)
      (ZT.natLit 2 * (ZT.natLit 2 * m * l)) := by
  have ed := ZT.toZ_eq hd
  have ee := ZT.toZ_eq he
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at ed ee
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat]
  rw [sum_mul_grid (fun u => ZT.toZ Γ (d u)) (fun x => ZT.toZ Γ (e x))]
  linear_combination (∑ x, ZT.toZ Γ (e x)) * ed + 2 * ZT.toZ Γ m * ee

/-- The strong product: the degrees sum to `2 (m q + l p + 2 m l)`. -/
theorem strong_degree_sum (d : Fin p → ZT n) (e : Fin q → ZT n) {m l : ZT n}
    (hd : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m))
    (he : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin e) (ZT.natLit 2 * l)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun u => ZT.sumFin fun x => d u + e x + d u * e x)
      (ZT.natLit 2 * (m * ZT.natLit q + l * ZT.natLit p + ZT.natLit 2 * m * l)) := by
  have ed := ZT.toZ_eq hd
  have ee := ZT.toZ_eq he
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at ed ee
  have s1 := sum_add_grid (fun u => ZT.toZ Γ (d u)) (fun x => ZT.toZ Γ (e x))
  have s2 := sum_mul_grid (fun u => ZT.toZ Γ (d u)) (fun x => ZT.toZ Γ (e x))
  beta_reduce at s1 s2
  ipra_lc [Finset.sum_add_distrib] s1 + s2 + ((q : Groth (Q Γ)) + ∑ x, ZT.toZ Γ (e x)) * ed +
    ((p : Groth (Q Γ)) + 2 * ZT.toZ Γ m) * ee

/-- The lexicographic product: the degrees sum to `2 (m q² + p l)`. -/
theorem lexicographic_degree_sum (d : Fin p → ZT n) (e : Fin q → ZT n) {m l : ZT n}
    (hd : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m))
    (he : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin e) (ZT.natLit 2 * l)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun u => ZT.sumFin fun x => ZT.natLit q * d u + e x)
      (ZT.natLit 2 * (m * (ZT.natLit q * ZT.natLit q) + ZT.natLit p * l)) := by
  have ed := ZT.toZ_eq hd
  have ee := ZT.toZ_eq he
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at ed ee
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat]
  rw [sum_add_grid (fun u => (q : Groth (Q Γ)) * ZT.toZ Γ (d u)) (fun x => ZT.toZ Γ (e x)), ← Finset.mul_sum]
  linear_combination (q : Groth (Q Γ)) * (q : Groth (Q Γ)) * ed + (p : Groth (Q Γ)) * ee

end LeanProofs.IPRA.Combinatorics.GraphProducts
