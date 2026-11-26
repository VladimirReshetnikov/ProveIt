import IPRADerivations.Core.IntCertificates

/-!
# Closed walks and cuts of a finite simple graph

Packet: `combinatorics/graph-ipra`, `tex/elementary.tex`, Proposition 2.1 (`prop:degree`, the cut identity) and
Proposition 2.4 ("Adjacency powers, triangles, and quadrangles"). The graph has vertex set `Fin k` and a symmetric
adjacency matrix `A v w` of integer terms with `A_{vw}² = A_{vw}` (bits); a vertex set `S` is a bit vector `x`.
With `d_v = ∑_w A_{vw}` and the codegrees `c_{uw} = ∑_v A_{uv} A_{vw}` (the entries of `A²`), as iPRA derivations:

* `closed_walks_two`: `tr(A²) = ∑_v d_v` ("A closed two-step walk chooses a starting end of an edge"), which is
  `2m` by `Combinatorics/GraphIncidence.handshake`;
* `cut_degree`: "For every cut `S`, `∑_{v ∈ S} d(v) = 2 |E(S)| + |δ(S)|`", in the form
  `∑_v x_v d_v = ∑_{v,w} A_{vw} x_v x_w + ∑_{v,w} A_{vw} x_v (1 − x_w)`;
* `cut_energy`: the Laplacian energy of a bit vector is twice its cut, `∑_{v,w} A_{vw} (x_v − x_w)² =
  2 ∑_{v,w} A_{vw} x_v (1 − x_w)` (with `Combinatorics/GraphIncidence.laplacian_energy`, `xᵀ L x = |δ(S)|`);
* `closed_walks_four`: `tr(A⁴) = ∑_v d_v + 2 ∑_v d_v (d_v − 1) + ∑_{u ≠ w} c_{uw} (c_{uw} − 1)`, the three
  classes of closed four-step walks: on one edge (`2m`), on a two-edge path (`4 ∑_v C(d_v, 2)`), and on a simple
  four-cycle (`8q`, since each four-cycle is counted once for each ordered pair of opposite vertices and each
  ordered pair of their two common neighbours).

Not derived: `tr(A³) = 6t` in terms of unordered triangles, and the walk-count reading of `A^k` for general `k`.
-/

namespace LeanProofs.IPRA.Combinatorics.GraphWalks

open_ipra

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- `tr(A²) = ∑ d_v` for a symmetric matrix of bits. -/
theorem trace_sq (a : Fin k → Fin k → R) (hs : ∀ v w, a v w = a w v) (hb : ∀ v w, a v w * a v w = a v w) :
    ∑ v, ∑ w, a v w * a w v = ∑ v, ∑ w, a v w :=
  Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by rw [← hs v w, hb]

/-- The degree sum over a vertex set splits into inner and boundary incidences. -/
theorem cut_identity (a : Fin k → Fin k → R) (x : Fin k → R) :
    ∑ v, x v * ∑ w, a v w =
      ∑ v, ∑ w, a v w * (x v * x w) + ∑ v, ∑ w, a v w * (x v * (1 - x w)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

/-- The Laplacian energy of a bit vector is twice its cut. -/
theorem cut_energy_identity (a : Fin k → Fin k → R) (x : Fin k → R) (hs : ∀ v w, a v w = a w v)
    (hx : ∀ v, x v * x v = x v) :
    ∑ v, ∑ w, a v w * (x v - x w) ^ 2 = 2 * ∑ v, ∑ w, a v w * (x v * (1 - x w)) := by
  have e : ∀ v w, a v w * (x v - x w) ^ 2 =
      a v w * (x v * (1 - x w)) + a v w * (x w * (1 - x v)) := fun v w => by
    linear_combination a v w * hx v + a v w * hx w
  have sw : ∑ v, ∑ w, a v w * (x w * (1 - x v)) = ∑ v, ∑ w, a v w * (x v * (1 - x w)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by rw [hs w v]
  have h : ∑ v, ∑ w, a v w * (x v - x w) ^ 2 =
      ∑ v, ∑ w, a v w * (x v * (1 - x w)) + ∑ v, ∑ w, a v w * (x w * (1 - x v)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => e v w
  rw [h, sw]
  ring

/-- `tr(A⁴)` for a symmetric matrix of bits, split by the support of the walk. -/
theorem trace_fourth (a : Fin k → Fin k → R) (hs : ∀ v w, a v w = a w v) (hb : ∀ v w, a v w * a v w = a v w) :
    ∑ u, ∑ w, (∑ v, a u v * a v w) ^ 2 =
      ∑ u, ∑ w, a u w + 2 * ∑ u, (∑ w, a u w) * ((∑ w, a u w) - 1) +
        ∑ u, ∑ w, (if u = w then 0 else (∑ v, a u v * a v w) * ((∑ v, a u v * a v w) - 1)) := by
  have hcd : ∀ u, ∑ v, a u v * a v u = ∑ w, a u w := fun u =>
    Finset.sum_congr rfl fun v _ => by rw [← hs u v, hb]
  have hcs : ∑ u, ∑ w, ∑ v, a u v * a v w = ∑ v, (∑ w, a v w) ^ 2 := by
    have e1 : ∀ u, ∑ w, ∑ v, a u v * a v w = ∑ v, a u v * ∑ w, a v w := fun u => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun v _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl fun u _ => e1 u, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun u _ => hs u v]
    ring
  have hpt : ∀ u w, (∑ v, a u v * a v w) ^ 2 =
      (if u = w then (∑ v, a u v * a v w) ^ 2 else 0) +
        (if u = w then 0 else (∑ v, a u v * a v w) * ((∑ v, a u v * a v w) - 1)) +
        (∑ v, a u v * a v w) - (if u = w then ∑ v, a u v * a v w else 0) := fun u w => by
    split_ifs <;> ring
  have hA : ∑ u, ∑ w, (if u = w then (∑ v, a u v * a v w) ^ 2 else 0) = ∑ u, (∑ w, a u w) ^ 2 := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, hcd]
  have hB : ∑ u, ∑ w, (if u = w then ∑ v, a u v * a v w else 0) = ∑ u, ∑ w, a u w := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, hcd]
  have hd : ∑ u, (∑ w, a u w) * ((∑ w, a u w) - 1) = ∑ u, (∑ w, a u w) ^ 2 - ∑ u, ∑ w, a u w := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hsum : ∑ u, ∑ w, (∑ v, a u v * a v w) ^ 2 =
      ∑ u, ∑ w, (if u = w then (∑ v, a u v * a v w) ^ 2 else 0) +
        ∑ u, ∑ w, (if u = w then 0 else (∑ v, a u v * a v w) * ((∑ v, a u v * a v w) - 1)) +
        ∑ u, ∑ w, ∑ v, a u v * a v w - ∑ u, ∑ w, (if u = w then ∑ v, a u v * a v w else 0) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => hpt u w
  rw [hsum, hA, hB, hcs, hd]
  ring

end Ring

/-! ## The derivations -/

/-- Closed two-step walks: `tr(A²) = ∑_v d_v`. -/
theorem closed_walks_two (A : Fin k → Fin k → ZT n) (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v))
    (hb : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w * A v w) (A v w)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => ZT.sumFin fun w => A v w * A w v)
      (ZT.sumFin fun v => ZT.sumFin fun w => A v w) := by
  have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have hb1 : ∀ v w, ZT.toZ Γ (A v w) * ZT.toZ Γ (A v w) = ZT.toZ Γ (A v w) := fun v w => by
    simpa only [ZT.toZ_mul] using ZT.toZ_eq (hb v w)
  have e := trace_sq (fun v w => ZT.toZ Γ (A v w)) hs1 hb1
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- The cut identity: `∑_{v ∈ S} d_v` is the inner incidences plus the boundary edges. -/
theorem cut_degree (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => x v * ZT.sumFin fun w => A v w)
      ((ZT.sumFin fun v => ZT.sumFin fun w => A v w * (x v * x w)) +
        ZT.sumFin fun v => ZT.sumFin fun w => A v w * (x v * (ZT.natLit 1 - x w))) := by
  have e := cut_identity (fun v w => ZT.toZ Γ (A v w)) (fun v => ZT.toZ Γ (x v))
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- The Laplacian energy of a bit vector is twice the size of its cut. -/
theorem cut_energy (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) (hx : ∀ v, Γ ⊢[PRAAx] ZT.eq (x v * x v) (x v)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => ZT.sumFin fun w => A v w * ZT.sq (x v - x w))
      (ZT.natLit 2 * ZT.sumFin fun v => ZT.sumFin fun w => A v w * (x v * (ZT.natLit 1 - x w))) := by
  have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have hx1 : ∀ v, ZT.toZ Γ (x v) * ZT.toZ Γ (x v) = ZT.toZ Γ (x v) := fun v => by
    simpa only [ZT.toZ_mul] using ZT.toZ_eq (hx v)
  have e := cut_energy_identity (fun v w => ZT.toZ Γ (A v w)) (fun v => ZT.toZ Γ (x v)) hs1 hx1
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- Closed four-step walks: `tr(A⁴) = ∑ d_v + 2 ∑ d_v (d_v − 1) + ∑_{u ≠ w} c_{uw} (c_{uw} − 1)`. -/
theorem closed_walks_four (A : Fin k → Fin k → ZT n) (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v))
    (hb : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w * A v w) (A v w)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun u => ZT.sumFin fun w => ZT.sq (ZT.sumFin fun v => A u v * A v w))
      ((ZT.sumFin fun u => ZT.sumFin fun w => A u w) +
        ZT.natLit 2 * (ZT.sumFin fun u =>
          (ZT.sumFin fun w => A u w) * ((ZT.sumFin fun w => A u w) - ZT.natLit 1)) +
        ZT.sumFin fun u => ZT.sumFin fun w =>
          if u = w then ZT.natLit 0
          else (ZT.sumFin fun v => A u v * A v w) * ((ZT.sumFin fun v => A u v * A v w) - ZT.natLit 1)) := by
  have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have hb1 : ∀ v w, ZT.toZ Γ (A v w) * ZT.toZ Γ (A v w) = ZT.toZ Γ (A v w) := fun v w => by
    simpa only [ZT.toZ_mul] using ZT.toZ_eq (hb v w)
  have e := trace_fourth (fun v w => ZT.toZ Γ (A v w)) hs1 hb1
  beta_reduce at e
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_natLit,
    apply_ite (ZT.toZ Γ), Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  exact e

end LeanProofs.IPRA.Combinatorics.GraphWalks
