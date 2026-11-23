import IPRADerivations.Combinatorics.DoubleCounting

/-!
# Euler bounds for spherical maps

Packet: `combinatorics/graph-ipra`, `tex/plane.tex`, Theorem 10.3 (`thm:densplane`, "Euler bounds and explicit
obstructions") and the first step of Theorem 10.4 (`thm:five`, "Constructive five-colour theorem"). The numbers of
vertices, edges and faces are integer terms `v`, `m`, `f` with Euler's relation `v + f = m + 2` ("Substitute
`f = 2 − n + m`") as a hypothesis. As iPRA derivations:

* `face_lengths`: "Each dart is on exactly one facial walk, so face lengths sum to `2m`. ... Therefore
  `2m ≥ 3f`": for the incidence table of `f` faces and `2m` darts with every face of length at least `g` and
  every dart on at most one face, `g f ≤ 2m` (`Combinatorics/DoubleCounting.count_le`);
* `planar_edges`: "`m ≤ 3n − 6`", from `3f ≤ 2m`;
* `planar_edges_triangle_free`: "If it is triangle-free, `m ≤ 2n − 4`", from `4f ≤ 2m`;
* `k5_nonplanar`: "`K₅` has ten edges against a bound of nine": the data `v = 5`, `m = 10` are contradictory;
* `k33_nonplanar`: "The bipartite `K_{3,3}` has nine against a triangle-free bound of eight": `v = 6`, `m = 9`
  with `4f ≤ 2m` are contradictory;
* `degree_five`: "Every nonempty such graph has a vertex of degree at most five. ... a contrary degree sum would
  give `2m ≥ 6n`": degrees `d_i ≥ 6` on `k` vertices with `∑ d_i = 2m` contradict `m + 6 ≤ 3k`.

Not derived: Euler's relation itself, the face-length analysis, minor closure, and the recursion of the
five-colour theorem.
-/

namespace LeanProofs.IPRA.Combinatorics.PlanarBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.DoubleCounting (count_le)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Faces of length at least `g` on `2m` darts: `g f ≤ 2m`. -/
theorem face_lengths {f m : ℕ} (M : Fin f → Fin (2 * m) → ZT n) (g : ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] zle g (ZT.sumFin fun j => M i j))
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => M i j) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] zle (g * ZT.natLit f) (ZT.natLit 2 * ZT.natLit m) := by
  have h := count_le M _ _ hr hc
  refine zle_of_comb (zsl h) ?_ (nn_zsl _)
  zsimp
  push_cast
  ring

/-- `m ≤ 3v − 6` for a simple spherical map, as `m + 6 ≤ 3v`. -/
theorem planar_edges {v m f : ZT n} (hE : Γ ⊢[PRAAx] ZT.eq (v + f) (m + ZT.natLit 2))
    (hF : Γ ⊢[PRAAx] zle (ZT.natLit 3 * f) (ZT.natLit 2 * m)) :
    Γ ⊢[PRAAx] zle (m + ZT.natLit 6) (ZT.natLit 3 * v) := by
  have e := ZT.toZ_eq hE
  simp only [ZT.toZ_add, ZT.toZ_natLit, Nat.cast_ofNat] at e
  refine zle_of_comb (zsl hF) ?_ (nn_zsl _)
  zsimp
  linear_combination (3 : Groth (Q Γ)) * e

/-- `m ≤ 2v − 4` for a triangle-free simple spherical map, as `m + 4 ≤ 2v`. -/
theorem planar_edges_triangle_free {v m f : ZT n} (hE : Γ ⊢[PRAAx] ZT.eq (v + f) (m + ZT.natLit 2))
    (hF : Γ ⊢[PRAAx] zle (ZT.natLit 4 * f) (ZT.natLit 2 * m)) :
    Γ ⊢[PRAAx] zle (m + ZT.natLit 4) (ZT.natLit 2 * v) := by
  have e := ZT.toZ_eq hE
  simp only [ZT.toZ_add, ZT.toZ_natLit, Nat.cast_ofNat] at e
  refine zle_of_comb_two (zsl hF) ?_ (nn_zsl _)
  zsimp
  linear_combination (4 : Groth (Q Γ)) * e

/-- `K₅` is not a spherical map: five vertices and ten edges contradict `m + 6 ≤ 3v`. -/
theorem k5_nonplanar {f : ZT n} (hE : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 5 + f) (ZT.natLit 10 + ZT.natLit 2))
    (hF : Γ ⊢[PRAAx] zle (ZT.natLit 3 * f) (ZT.natLit 2 * ZT.natLit 10)) (φ : Fm PTm n) :
    Γ ⊢[PRAAx] φ := by
  have h := planar_edges hE hF
  refine false_of_comb (zsl h) ?_ (nn_zsl _) φ
  zsimp
  norm_num

/-- `K_{3,3}` is not a spherical map: six vertices and nine edges contradict `m + 4 ≤ 2v`. -/
theorem k33_nonplanar {f : ZT n} (hE : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 6 + f) (ZT.natLit 9 + ZT.natLit 2))
    (hF : Γ ⊢[PRAAx] zle (ZT.natLit 4 * f) (ZT.natLit 2 * ZT.natLit 9)) (φ : Fm PTm n) :
    Γ ⊢[PRAAx] φ := by
  have h := planar_edges_triangle_free hE hF
  refine false_of_comb (zsl h) ?_ (nn_zsl _) φ
  zsimp
  norm_num

/-- Some vertex has degree at most five: degrees `≥ 6` with sum `2m` contradict `m + 6 ≤ 3k`. -/
theorem degree_five {k : ℕ} {m : ZT n} (d : Fin k → ZT n)
    (hd : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit 6) (d i))
    (hs : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin d) (ZT.natLit 2 * m))
    (hm : Γ ⊢[PRAAx] zle (m + ZT.natLit 6) (ZT.natLit 3 * ZT.natLit k)) (φ : Fm PTm n) :
    Γ ⊢[PRAAx] φ := by
  have e := ZT.toZ_eq hs
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_ofNat] at e
  refine false_of_comb (∑ i, zsl (hd i) + 2 * zsl hm + 11) ?_
    (nn_add (nn_add (nn_sum _ _ fun i _ => nn_zsl _) (nn_mul (nn_ofNat 2) (nn_zsl _))) (nn_ofNat 11)) φ
  zsimp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination e

end LeanProofs.IPRA.Combinatorics.PlanarBounds
