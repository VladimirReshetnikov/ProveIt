import IPRADerivations.Combinatorics.Turan

/-!
# A lower bound for the number of triangles

Packets: `combinatorics/graph-ipra`, `tex/color.tex`, Theorem 14.1 (`co:turan`), last sentence for `r = 2`
("Strictly more than `t_r(n)` edges yields an explicit `(r + 1)`-clique"), and
`combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 20. For a symmetric matrix of bits `A` on `Fin k`, with
`E = ∑_{u,v} A_{uv}` (twice the number of edges) and `T = ∑_{u,v,w} A_{vw} A_{uv} A_{uw}` (six times the number
of triangles), as an iPRA derivation:

* `triangle_count_bound`: `E (2E − k²) ≤ k T`, that is `t ≥ e (4e − k²)/(3k)` for `e` edges and `t`
  triangles. In particular a graph with more than `k²/4` edges has `T > 0`, so it contains a triangle.

The certificate is `k` times the common-neighbour squares of `Combinatorics/Turan.common_sum` (with every vertex
in the support) plus twice the Cauchy slack `k ∑ d_u² − E²`.

Not derived: the search for the triangle, and the corresponding count for larger cliques.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.TriangleDensity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Turan (common_sum)
open Syn
open scoped Fm

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- `E (2E − k²) ≤ k T`: a lower bound for the number of triangles of a graph. -/
theorem triangle_count_bound (A : Fin k → Fin k → ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v))
    (hb : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w * A v w) (A v w)) :
    Γ ⊢[PRAAx] zle
      ((ZT.sumFin fun u => ZT.sumFin fun v => A u v) *
        (ZT.natLit 2 * (ZT.sumFin fun u => ZT.sumFin fun v => A u v) - ZT.natLit (k * k)))
      (ZT.natLit k * ZT.sumFin fun u => ZT.sumFin fun v => ZT.sumFin fun w => A v w * (A u v * A u w)) := by
  have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have hb1 : ∀ v w, ZT.toZ Γ (A v w) * ZT.toZ Γ (A v w) = ZT.toZ Γ (A v w) := fun v w => by
    have e := ZT.toZ_eq (hb v w)
    simpa only [ZT.toZ_mul] using e
  have L := common_sum (fun u v => ZT.toZ Γ (A u v)) (fun _ : Fin k => (1 : Groth (Q Γ))) hs1 hb1
    (fun _ => _root_.mul_one _) (fun _ _ => _root_.mul_one _)
  beta_reduce at L
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, _root_.mul_one] at L
  have hc := cauchy_int (Γ := Γ) (fun u => ZT.sumFin fun v => A u v)
  refine zle_of_comb ((k : Groth (Q Γ)) *
      (∑ u, ∑ v, ∑ w, ZT.toZ Γ (A u v * ((ZT.natLit 1 - A u w) * (ZT.natLit 1 - A v w))) ^ 2) +
      2 * zsl hc) ?_
    (nn_add (nn_mul (nn_natCast k)
      (nn_sum _ _ fun u _ => nn_sum _ _ fun v _ => nn_sum _ _ fun w _ => nn_zsq _))
      (nn_mul (nn_ofNat 2) (nn_zsl _)))
  zsimp
  push_cast
  linear_combination (-(k : Groth (Q Γ))) * L

end LeanProofs.IPRA.Combinatorics.TriangleDensity
