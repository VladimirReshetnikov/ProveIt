import IPRADerivations.AnalyticNumberTheory.GramBound
import IPRADerivations.Core.CertificateTactics

/-!
# Mantel's theorem: the triangle-free case of Turán's theorem

Packet: `combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 20 (`thm:graph-turan`, "Turán, including
equality"): "In particular the triangle-free maximum is `⌊n²/4⌋`". The bound is derived here by the
degree-sum argument (Cauchy–Schwarz on the degrees) instead of the packet's induction on `r`, because that
argument is one polynomial certificate.

The graph has vertex set `Fin k` and a symmetric matrix `A u v` of integer terms (`0/1` for a simple graph).
Triangle-freeness is the family of inequalities `A_{uv} (A_{uw} + A_{vw}) ≤ A_{uv}`: the two ends of an edge
have no common neighbour `w`.

* `mantel_sum`: `∑_{u,v,w} (a_{uv} − a_{uv}(a_{uw} + a_{vw})) = k ∑_{u,v} a_{uv} − 2 ∑_u d_u²` for a symmetric
  matrix with row sums `d_u`;
* `mantel`: with `D = ∑_{u,v} A_{uv}` (twice the number of edges), `2 D² ≤ k² D`. For `D > 0` this is
  `2D ≤ k²`, that is `4 e ≤ k²`: a triangle-free graph on `k` vertices has at most `k²/4` edges. The
  certificate is `2 (k ∑ d_u² − D²)` (`Core/IntCertificates.cauchy_int`) plus `k` times the triangle slacks.

Two further steps of the proof of `thm:graph-turan` (and of Theorem 14.1 `co:turan` of
`combinatorics/graph-ipra`, `tex/color.tex`):

* `turan_step`: "Summing degrees over `T` gives `e(S, T) + 2 e(T) ≤ d |T|`, `e(G) ≤ e(S) + d |T| − e(T)`": for
  a bit vector `x` (the set `S`, with `T` its complement) and a bound `d` on the degrees,
  `∑_{u,v} A_{uv} ≤ ∑_{u,v} A_{uv} x_u x_v + 2 d ∑_v (1 − x_v)`, that is `2 e(G) ≤ 2 e(S) + 2 d |T|`;
* `multipartite_bound`: "`t_r(n) ≤ (1 − 1/r) n²/2`: the identity `r ∑ a_i² − (∑ a_i)² = ∑_{i<j} (a_i − a_j)²`
  gives the bound from `2 t_r(n) = n² − ∑ a_i²`", as `r (N² − ∑ a_i²) ≤ (r − 1) N²` for part sizes `a_i` with
  sum `N` (stated for `r + 1` parts).
* `turan_induction`: the induction on the number of parts. With `S` the neighbourhood of a vertex of maximal
  degree `d`, the Turán step gives `E ≤ E_S + 2 d (N − d)` for the doubled edge counts, and the bound for `ρ + 1`
  parts on `S` is `(ρ + 1) E_S ≤ ρ d²`; then `(ρ + 2) E ≤ (ρ + 1) N²`, the bound for `ρ + 2` parts. The
  certificate is `((ρ + 1) N − (ρ + 2) d)²`, after cancelling the positive numeral `ρ + 1`.

The extremal graphs and the assembly of the recursion over the neighbourhoods are not derived.
-/

namespace LeanProofs.IPRA.Combinatorics.Mantel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.GramBound (zle_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n k : ℕ} {Γ : List (Fm PTm n)}

/-- The triangle slacks of a symmetric matrix sum to `k ∑ a − 2 ∑ d_u²`. -/
theorem mantel_sum {R : Type*} [CommRing R] (a : Fin k → Fin k → R) (hs : ∀ v w, a v w = a w v) :
    ∑ u, ∑ v, ∑ w, (a u v - a u v * (a u w + a v w)) =
      (k : R) * ∑ u, ∑ v, a u v - 2 * ∑ u, (∑ w, a u w) ^ 2 := by
  have hin : ∀ u v, ∑ w, (a u v - a u v * (a u w + a v w)) =
      (k : R) * a u v - a u v * (∑ w, a u w) - a u v * (∑ w, a v w) := by
    intro u v
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_add_distrib]
    ring
  have h1 : ∑ u, ∑ v, a u v * (∑ w, a u w) = ∑ u, (∑ w, a u w) ^ 2 := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul]
    ring
  have h2 : ∑ u, ∑ v, a u v * (∑ w, a v w) = ∑ u, (∑ w, a u w) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun u _ => hs u v]
    ring
  have hk : ∑ u, ∑ v, (k : R) * a u v = (k : R) * ∑ u, ∑ v, a u v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
  have hsplit : ∑ u, ∑ v, ((k : R) * a u v - a u v * (∑ w, a u w) - a u v * (∑ w, a v w)) =
      ∑ u, ∑ v, (k : R) * a u v - ∑ u, ∑ v, a u v * (∑ w, a u w) - ∑ u, ∑ v, a u v * (∑ w, a v w) := by
    simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hin u v, hsplit, hk, h1, h2]
  ring

/-- Mantel's theorem, cleared: `2 D² ≤ k² D` for `D = ∑_{u,v} A_{uv}` in a triangle-free graph. -/
theorem mantel (A : Fin k → Fin k → ZT n) (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v))
    (htri : ∀ u v w, Γ ⊢[PRAAx] zle (A u v * (A u w + A v w)) (A u v)) :
    Γ ⊢[PRAAx] zle
      (ZT.natLit 2 * ZT.sq (ZT.sumFin fun u => ZT.sumFin fun v => A u v))
      (ZT.natLit (k * k) * ZT.sumFin fun u => ZT.sumFin fun v => A u v) := by
  have hs' : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have hc := cauchy_int (Γ := Γ) (fun u => ZT.sumFin fun w => A u w)
  have L := mantel_sum (fun u v => ZT.toZ Γ (A u v)) hs'
  beta_reduce at L
  refine zle_of_comb (2 * zsl hc + (k : Groth (Q Γ)) * ∑ u, ∑ v, ∑ w, zsl (htri u v w)) ?_
    (nn_add (nn_mul (nn_ofNat 2) (nn_zsl _))
      (nn_mul (nn_natCast k) (nn_sum _ _ fun u _ => nn_sum _ _ fun v _ => nn_sum _ _ fun w _ => nn_zsl _)))
  zsimp
  rw [L]
  push_cast
  ring

/-- The certificate identity of the Turán step. -/
theorem turan_step_identity {R : Type*} [CommRing R] (a : Fin k → Fin k → R) (x : Fin k → R) (d : R)
    (hs : ∀ v w, a v w = a w v) :
    2 * d * ∑ v, (1 - x v) - ∑ v, ∑ w, a v w + ∑ v, ∑ w, a v w * (x v * x w) =
      2 * ∑ v, (1 - x v) * (d - ∑ w, a v w) + ∑ v, ∑ w, (1 - x w) * (a v w * (1 - x v)) := by
  have q : ∀ v, (1 - x v) * (d - ∑ w, a v w) = d * (1 - x v) - ∑ w, a v w + x v * ∑ w, a v w := by
    intro v
    ring
  have hA : ∑ v, (1 - x v) * (d - ∑ w, a v w) =
      d * ∑ v, (1 - x v) - ∑ v, ∑ w, a v w + ∑ v, x v * ∑ w, a v w := by
    rw [Finset.sum_congr rfl fun v _ => q v, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum]
  have p : ∀ v w, (1 - x w) * (a v w * (1 - x v)) =
      a v w - a v w * x v - a v w * x w + a v w * (x v * x w) := by
    intro v w
    ring
  have hB : ∑ v, ∑ w, (1 - x w) * (a v w * (1 - x v)) =
      ∑ v, ∑ w, a v w - ∑ v, ∑ w, a v w * x v - ∑ v, ∑ w, a v w * x w +
        ∑ v, ∑ w, a v w * (x v * x w) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => p v w
  have hT2 : ∑ v, ∑ w, a v w * x v = ∑ v, x v * ∑ w, a v w := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul]
    ring
  have hT3 : ∑ v, ∑ w, a v w * x w = ∑ v, x v * ∑ w, a v w := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun v _ => hs v w]
    ring
  rw [hA, hB, hT2, hT3]
  ring

/-- The Turán step: `2 e(G) ≤ 2 e(S) + 2 d |T|` for a vertex set `S` with complement `T` and degrees at most
`d`. -/
theorem turan_step (A : Fin k → Fin k → ZT n) (x : Fin k → ZT n) (d : ZT n)
    (hs : ∀ v w, Γ ⊢[PRAAx] ZT.eq (A v w) (A w v)) (hA : ∀ v w, Γ ⊢[PRAAx] zle (ZT.natLit 0) (A v w))
    (hx : ∀ v, Γ ⊢[PRAAx] zle (x v) (ZT.natLit 1))
    (hd : ∀ v, Γ ⊢[PRAAx] zle (ZT.sumFin fun w => A v w) d) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun v => ZT.sumFin fun w => A v w)
      ((ZT.sumFin fun v => ZT.sumFin fun w => A v w * (x v * x w)) +
        ZT.natLit 2 * d * ZT.sumFin fun v => ZT.natLit 1 - x v) := by
  have hs1 : ∀ v w, ZT.toZ Γ (A v w) = ZT.toZ Γ (A w v) := fun v w => ZT.toZ_eq (hs v w)
  have L := turan_step_identity (fun v w => ZT.toZ Γ (A v w)) (fun v => ZT.toZ Γ (x v)) (ZT.toZ Γ d) hs1
  beta_reduce at L
  refine zle_of_comb (2 * ∑ v, zsl (hx v) * zsl (hd v) +
      ∑ v, ∑ w, zsl (hx w) * (ZT.toZ Γ (A v w) * zsl (hx v))) ?_
    (nn_add (nn_mul (nn_ofNat 2) (nn_sum _ _ fun v _ => nn_mul (nn_zsl _) (nn_zsl _)))
      (nn_sum _ _ fun v _ => nn_sum _ _ fun w _ =>
        nn_mul (nn_zsl _) (nn_mul (nn_zle0 (hA v w)) (nn_zsl _))))
  zsimp
  linear_combination L

/-- The edge count of a complete multipartite graph with `r + 1` parts of sizes `a_i` and `N = ∑ a_i`
vertices: `(r + 1) (N² − ∑ a_i²) ≤ r N²`. -/
theorem multipartite_bound {r : ℕ} (a : Fin (r + 1) → ZT n) :
    Γ ⊢[PRAAx] zle
      (ZT.natLit (r + 1) * (ZT.sq (ZT.sumFin a) - ZT.sumFin fun i => ZT.sq (a i)))
      (ZT.natLit r * ZT.sq (ZT.sumFin a)) := by
  have hc := cauchy_int (Γ := Γ) a
  ipra_zle (zsl hc)

/-- The induction step of Turán's bound: from `E ≤ E_S + 2 d (N − d)` and the bound `(ρ + 1) E_S ≤ ρ d²` for
`ρ + 1` parts, the bound `(ρ + 2) E ≤ (ρ + 1) N²` for `ρ + 2` parts. -/
theorem turan_induction {ρ : ℕ} {E ES d N : ZT n}
    (hS : Γ ⊢[PRAAx] zle (ZT.natLit (ρ + 1) * ES) (ZT.natLit ρ * (d * d)))
    (hstep : Γ ⊢[PRAAx] zle E (ES + ZT.natLit 2 * d * (N - d))) :
    Γ ⊢[PRAAx] zle (ZT.natLit (ρ + 2) * E) (ZT.natLit (ρ + 1) * (N * N)) := by
  have hk : Γ ⊢[PRAAx] (num (ρ + 1) : PTm n) ≐ succ (pred (num (ρ + 1))) :=
    congrSucc (pred_succ (num ρ)).eqSymm
  have h2 : Γ ⊢[PRAAx] zle (ZT.natLit (ρ + 1) * (ZT.natLit (ρ + 2) * E))
      (ZT.natLit (ρ + 1) * (ZT.natLit (ρ + 1) * (N * N))) := by
    ipra_zle (((ρ + 2 : ℕ) : Groth (Q Γ)) * ((ρ + 1 : ℕ) : Groth (Q Γ)) * zsl hstep + ((ρ + 2 : ℕ) : Groth (Q Γ)) * zsl hS + ZT.toZ Γ (ZT.natLit (ρ + 1) * N - ZT.natLit (ρ + 2) * d) ^ 2)
  exact zle_cancel hk h2

end LeanProofs.IPRA.Combinatorics.Mantel
