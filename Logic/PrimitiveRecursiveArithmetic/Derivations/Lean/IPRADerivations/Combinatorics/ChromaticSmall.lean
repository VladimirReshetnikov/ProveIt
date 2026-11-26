import IPRADerivations.Combinatorics.IsingChain

/-!
# Chromatic polynomials of trees, cycles and small complete graphs

Packet: `combinatorics/graph-ipra`, `tex/color.tex`, Theorems `co:poly` ("Chromatic identities":
"`P_G = P_D − P_H`" for deletion and contraction of an edge) and `co:stanley` ("The number `a(G)` of acyclic
orientations of `G` is `(−1)^n P_G(−1)`"). The number of colours is a free integer term `q`, powers are
`pwr` of `Combinatorics/IsingChain`. As iPRA derivations:

* `chromatic_tree_step`: a leaf: `q · (q (q − 1)^N) − q (q − 1)^N = q (q − 1)^{N+1}` (delete the pendant edge,
  which leaves a tree and an isolated vertex, and contract it): trees on `N + 1` vertices have
  `P = q (q − 1)^N`;
* `chromatic_triangle`, `chromatic_K4`: `P(K₃) = P(P₃) − P(K₂) = q (q − 1)(q − 2)` and
  `P(K₄) = P(K₄ − e) − P(K₃) = q (q − 1)(q − 2)(q − 3)`;
* `cyc`, `sg`, `chromatic_cycle`: the recursion `P(C_{n+1}) = P(P_{n+1}) − P(C_n)` from `P(C₃)` has the solution
  `P(C_n) = (q − 1)^n + (−1)^n (q − 1)`, for every numeral `n ≥ 3`;
* `neg_two_pow`, `stanley_tree`, `stanley_cycle`: `(−1)^{N+1} P_tree(−1) = 2^N` and
  `(−1)^n P_{C_n}(−1) = 2^n − 2`: the numbers of acyclic orientations of a tree with `N` edges and of a cycle.

Not derived: the chromatic polynomial as a count of proper colourings of a coded graph, and the general
deletion–contraction recursion.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.ChromaticSmall

open_ipra
open LeanProofs.IPRA.Combinatorics.IsingChain (pwr toZ_pwr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `P(C_{N+3})`, by `P(C₃) = q (q − 1)(q − 2)` and `P(C_{n+1}) = q (q − 1)^n − P(C_n)`. -/
def cyc (q : ZT n) : ℕ → ZT n
  | 0 => q * (q - ZT.natLit 1) * (q - ZT.natLit 2)
  | N + 1 => q * pwr (q - ZT.natLit 1) (N + 3) - cyc q N

/-- The sign `(−1)^{N+3}`. -/
def sg : ℕ → ZT n
  | 0 => -(ZT.natLit 1)
  | N + 1 => -(sg N)

local macro "csimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [toZ_pwr, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] $[$loc]?)
attribute [local ipra_defs] toZ_pwr

/-- A pendant edge: `q P_T − P_T = (q − 1) P_T` for `P_T = q (q − 1)^N`. -/
theorem chromatic_tree_step (q : ZT n) (N : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (q * (q * pwr (q - ZT.natLit 1) N) - q * pwr (q - ZT.natLit 1) N)
      (q * pwr (q - ZT.natLit 1) (N + 1)) := by
  ipra_lc

/-- `P(K₃) = P(P₃) − P(K₂)`. -/
theorem chromatic_triangle (q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (q * (q - ZT.natLit 1) * (q - ZT.natLit 1) - q * (q - ZT.natLit 1))
      (q * (q - ZT.natLit 1) * (q - ZT.natLit 2)) := by
  ipra_lc

/-- `P(K₄) = P(K₄ − e) − P(K₃)`. -/
theorem chromatic_K4 (q : ZT n) :
    Γ ⊢[PRAAx] ZT.eq
      (q * (q - ZT.natLit 1) * (q - ZT.natLit 2) * (q - ZT.natLit 2) - q * (q - ZT.natLit 1) * (q - ZT.natLit 2))
      (q * (q - ZT.natLit 1) * (q - ZT.natLit 2) * (q - ZT.natLit 3)) := by
  ipra_lc

/-- `P(C_{N+3}) = (q − 1)^{N+3} + (−1)^{N+3} (q − 1)`. -/
theorem chromatic_cycle (q : ZT n) (N : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (cyc q N) (pwr (q - ZT.natLit 1) (N + 3) + sg N * (q - ZT.natLit 1)) := by
  induction N with
  | zero =>
    apply ZT.derive
    show ZT.toZ Γ (q * (q - ZT.natLit 1) * (q - ZT.natLit 2)) =
      ZT.toZ Γ (pwr (q - ZT.natLit 1) 3 + -(ZT.natLit 1) * (q - ZT.natLit 1))
    csimp
    ring
  | succ N ih =>
    have e := ZT.toZ_eq ih
    csimp at e
    apply ZT.derive
    show ZT.toZ Γ (q * pwr (q - ZT.natLit 1) (N + 3) - cyc q N) =
      ZT.toZ Γ (pwr (q - ZT.natLit 1) (N + 1 + 3) + -(sg N) * (q - ZT.natLit 1))
    csimp
    linear_combination -e

/-- `(−1)^N (−2)^N = 2^N`. -/
theorem neg_two_pow (N : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (pwr (-(ZT.natLit 1 : ZT n)) N * pwr (-(ZT.natLit 2)) N) (pwr (ZT.natLit 2) N) := by
  induction N with
  | zero =>
    ipra_lc
  | succ N ih =>
    ipra_lc 2 * ZT.toZ_eq ih

/-- A tree with `N` edges has `2^N` acyclic orientations: `(−1)^{N+1} P(−1) = 2^N`. -/
theorem stanley_tree (N : ℕ) :
    Γ ⊢[PRAAx] ZT.eq
      (pwr (-(ZT.natLit 1 : ZT n)) (N + 1) * (-(ZT.natLit 1) * pwr (-(ZT.natLit 1) - ZT.natLit 1) N))
      (pwr (ZT.natLit 2) N) := by
  have e := ZT.toZ_eq (neg_two_pow (Γ := Γ) (n := n) N)
  csimp at e
  apply ZT.derive
  csimp
  have h : (-1 - 1 : Groth (Q Γ)) = -2 := by ring
  rw [h]
  linear_combination e

/-- A cycle `C_{N+3}` has `2^{N+3} − 2` acyclic orientations: `(−1)^n P(−1) = 2^n − 2`, with the value of
`P(C_n)` at `q = −1` written `(−2)^n + (−1)^n (−2)`. -/
theorem stanley_cycle (N : ℕ) :
    Γ ⊢[PRAAx] ZT.eq
      (pwr (-(ZT.natLit 1 : ZT n)) (N + 3) *
        (pwr (-(ZT.natLit 2)) (N + 3) + pwr (-(ZT.natLit 1)) (N + 3) * (-(ZT.natLit 2))))
      (pwr (ZT.natLit 2) (N + 3) - ZT.natLit 2) := by
  have e := ZT.toZ_eq (neg_two_pow (Γ := Γ) (n := n) (N + 3))
  csimp at e
  have sq : ((-1 : Groth (Q Γ)) ^ (N + 3)) * ((-1) ^ (N + 3)) = 1 := by
    rw [← _root_.mul_pow]
    norm_num
  ipra_lc e - 2 * sq

end LeanProofs.IPRA.Combinatorics.ChromaticSmall
