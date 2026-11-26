import IPRADerivations.Core.CertificateTactics

/-!
# The Petersen graph: cubic, diameter two, girth five, and its minimal polynomial

Packets: `combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 23 ("The Petersen graph is cubic ... of
diameter two and girth five"), and `combinatorics/graph-ipra`, `tex/operations.tex`, Theorem `thm:petersen`,
and `tex/spectral.tex`, Theorem `spec:petersen` ("The adjacency characteristic polynomial of the Petersen graph
is `(t − 3)(t − 1)⁵ (t + 2)⁴`").

"Use labels `O_i, I_i` for `i` modulo five. Join `O_i` to `O_{i+1}`, `I_i` to `I_{i+2}` and `O_i` to `I_i`": the
vertices `0, …, 4` are the `O_i`, the vertices `5, …, 9` the `I_i`, and `padj` is the adjacency table of
numerals. As iPRA derivations, for all vertices:

* `petersen_symm`, `petersen_loop`: the table is symmetric with zero diagonal;
* `petersen_cubic`: every vertex has degree three;
* `petersen_srg`: for `u ≠ v`, the number of common neighbours plus the adjacency bit is one: adjacent vertices
  have no common neighbour and nonadjacent vertices exactly one. Hence there are no triangles and no
  quadrilaterals (girth at least five), and any two vertices are within two steps (diameter two);
* `petersen_minimal`: `A³ + 6 I = 2 A² + 5 A`, that is `(A − 3)(A − 1)(A + 2) = 0`: the eigenvalues are among
  `3, 1, −2`.

Not derived: the multiplicities `1, 5, 4`, the tree count `2000`, biconnectedness and the absence of a
Hamiltonian cycle.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.PetersenGraph

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The adjacency of the Petersen graph on `O_0, …, O_4, I_0, …, I_4`. -/
def padj (u v : Fin 10) : ℕ :=
  if u.val < 5 ∧ v.val < 5 then
    (if v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5 then 1 else 0)
  else if 5 ≤ u.val ∧ 5 ≤ v.val then
    (if v.val - 5 = (u.val - 5 + 2) % 5 ∨ u.val - 5 = (v.val - 5 + 2) % 5 then 1 else 0)
  else (if u.val + 5 = v.val ∨ v.val + 5 = u.val then 1 else 0)

theorem padj_symm : ∀ u v : Fin 10, padj u v = padj v u := by decide

theorem padj_loop : ∀ u : Fin 10, padj u u = 0 := by decide

theorem padj_cubic : ∀ u : Fin 10, ∑ v, padj u v = 3 := by decide

theorem padj_srg : ∀ u v : Fin 10, u ≠ v → (∑ w, padj u w * padj w v) + padj u v = 1 := by decide

theorem padj_minimal : ∀ u v : Fin 10,
    (∑ w, ∑ x, padj u w * padj w x * padj x v) + 6 * (if u = v then 1 else 0) =
      2 * (∑ w, padj u w * padj w v) + 5 * padj u v := by decide

/-- The adjacency table is symmetric. -/
theorem petersen_symm (u v : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit (padj u v) : ZT n) (ZT.natLit (padj v u)) := by
  rw [padj_symm u v]
  apply ZT.derive
  rfl

/-- There are no loops. -/
theorem petersen_loop (u : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit (padj u u) : ZT n) (ZT.natLit 0) := by
  rw [padj_loop u]
  apply ZT.derive
  rfl

/-- Every vertex has degree three. -/
theorem petersen_cubic (u : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun v => (ZT.natLit (padj u v) : ZT n)) (ZT.natLit 3) := by
  ipra_cast padj_cubic u

/-- Two distinct vertices: common neighbours plus adjacency is one. -/
theorem petersen_srg (u v : Fin 10) (huv : u ≠ v) :
    Γ ⊢[PRAAx] ZT.eq
      ((ZT.sumFin fun w => (ZT.natLit (padj u w) : ZT n) * ZT.natLit (padj w v)) + ZT.natLit (padj u v))
      (ZT.natLit 1) := by
  ipra_cast padj_srg u v huv

/-- `A³ + 6 I = 2 A² + 5 A`: the adjacency matrix is annihilated by `(t − 3)(t − 1)(t + 2)`. -/
theorem petersen_minimal (u v : Fin 10) :
    Γ ⊢[PRAAx] ZT.eq
      ((ZT.sumFin fun w => ZT.sumFin fun x =>
          (ZT.natLit (padj u w) : ZT n) * ZT.natLit (padj w x) * ZT.natLit (padj x v)) +
        ZT.natLit 6 * ZT.natLit (if u = v then 1 else 0))
      (ZT.natLit 2 * (ZT.sumFin fun w => ZT.natLit (padj u w) * ZT.natLit (padj w v)) +
        ZT.natLit 5 * ZT.natLit (padj u v)) := by
  ipra_cast padj_minimal u v

end LeanProofs.IPRA.Combinatorics.PetersenGraph
