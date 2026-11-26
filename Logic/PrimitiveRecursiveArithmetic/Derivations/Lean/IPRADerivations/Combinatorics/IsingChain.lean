import IPRADerivations.Core.CertificateTactics

/-!
# The Ising chain and ring by the transfer matrix

Packet: `combinatorics/Combinatorics-iPRA`, `models.tex`, result 75 ("Open chain, ring and two-point
functions"): "For uniform weights `a, b`, put `p = a + b`, `q = a − b`. On a tree with `v ≥ 1` vertices,
`Z = 2 p^{v−1}` ... On the cycle of `n ≥ 3` vertices, `Z = p^n + q^n`,
`Z_{x,y} = q^d p^{n−d} + q^{n−d} p^d`".

The weights `a` (equal spins) and `b` (unequal spins) are integer terms. The transfer matrix
`T = [[a, b], [b, a]]` is symmetric with equal diagonal entries, and so are its powers: `T^N = [[α_N, β_N],
[β_N, α_N]]` with the pair `tp a b N = (α_N, β_N)` defined by the recursion of the matrix product. As iPRA
derivations, for all numerals:

* `tp_eigen`: `α_N + β_N = (a + b)^N` and `α_N − β_N = (a − b)^N` (the two eigenvalues);
* `chain_partition`: the sum `2 (α_N + β_N)` of the entries of `T^N`, the partition function of the open chain
  with `N + 1` sites, is `2 p^N`;
* `ring_partition`: the trace `2 α_N` of `T^N`, the partition function of the ring with `N` sites, is
  `p^N + q^N`;
* `ring_two_point`: with the spin matrix `S = diag(1, −1)`, `S T^d S = [[α_d, −β_d], [−β_d, α_d]]` and the
  trace `2 (α_d α_m − β_d β_m)` of `S T^d S T^m` is `q^d p^m + p^d q^m`: the two-point function of the ring with
  `n = d + m` sites;
* `chain_two_point`: on the chain the inserted pair multiplies the weight of the middle segment by
  `α_d − β_d = q^d` instead of `α_d + β_d = p^d`: "`Z_{x,y} / Z = (q / p)^d`".

Not derived: the identification of these matrix expressions with the sums over spin configurations, and the
high- and low-temperature expansions of result 74 for a general graph.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.IsingChain

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The power `u^k` of an integer term. -/
def pwr (u : ZT n) : ℕ → ZT n
  | 0 => ZT.natLit 1
  | k + 1 => pwr u k * u

theorem toZ_pwr (u : ZT n) (k : ℕ) : ZT.toZ Γ (pwr u k) = ZT.toZ Γ u ^ k := by
  induction k with
  | zero => simp only [pwr, ZT.toZ_natLit, Nat.cast_one, pow_zero]
  | succ k ih => simp only [pwr, ZT.toZ_mul, ih, pow_succ]

/-- The entries `(α_N, β_N)` of `T^N` for `T = [[a, b], [b, a]]`. -/
def tp (a b : ZT n) : ℕ → ZT n × ZT n
  | 0 => (ZT.natLit 1, ZT.natLit 0)
  | N + 1 => (a * (tp a b N).1 + b * (tp a b N).2, b * (tp a b N).1 + a * (tp a b N).2)

local macro "isimp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [toZ_pwr, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_natLit, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] $[$loc]?)
attribute [local ipra_defs] toZ_pwr

/-- The eigenvalues: `α_N + β_N = (a + b)^N` and `α_N − β_N = (a − b)^N`. -/
theorem tp_eigen (a b : ZT n) (N : ℕ) :
    (Γ ⊢[PRAAx] ZT.eq ((tp a b N).1 + (tp a b N).2) (pwr (a + b) N)) ∧
      (Γ ⊢[PRAAx] ZT.eq ((tp a b N).1 - (tp a b N).2) (pwr (a - b) N)) := by
  induction N with
  | zero =>
    constructor
    · apply ZT.derive
      show ZT.toZ Γ (ZT.natLit 1 + ZT.natLit 0) = ZT.toZ Γ (pwr (a + b) 0)
      isimp
      ring
    · apply ZT.derive
      show ZT.toZ Γ (ZT.natLit 1 - ZT.natLit 0) = ZT.toZ Γ (pwr (a - b) 0)
      isimp
      ring
  | succ N ih =>
    have e1 := ZT.toZ_eq ih.1
    have e2 := ZT.toZ_eq ih.2
    isimp at e1 e2
    constructor
    · apply ZT.derive
      show ZT.toZ Γ (a * (tp a b N).1 + b * (tp a b N).2 + (b * (tp a b N).1 + a * (tp a b N).2)) =
        ZT.toZ Γ (pwr (a + b) (N + 1))
      isimp
      linear_combination (ZT.toZ Γ a + ZT.toZ Γ b) * e1
    · apply ZT.derive
      show ZT.toZ Γ (a * (tp a b N).1 + b * (tp a b N).2 - (b * (tp a b N).1 + a * (tp a b N).2)) =
        ZT.toZ Γ (pwr (a - b) (N + 1))
      isimp
      linear_combination (ZT.toZ Γ a - ZT.toZ Γ b) * e2

/-- The open chain with `N + 1` sites: `Z = 2 p^N`. -/
theorem chain_partition (a b : ZT n) (N : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * ((tp a b N).1 + (tp a b N).2)) (ZT.natLit 2 * pwr (a + b) N) := by
  ipra_lc 2 * ZT.toZ_eq (tp_eigen (Γ := Γ) a b N).1

/-- The ring with `N` sites: `Z = p^N + q^N`. -/
theorem ring_partition (a b : ZT n) (N : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (tp a b N).1) (pwr (a + b) N + pwr (a - b) N) := by
  ipra_lc ZT.toZ_eq (tp_eigen (Γ := Γ) a b N).1 + ZT.toZ_eq (tp_eigen (Γ := Γ) a b N).2

/-- The two-point function of the ring: `2 (α_d α_m − β_d β_m) = q^d p^m + p^d q^m`. -/
theorem ring_two_point (a b : ZT n) (d m : ℕ) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * ((tp a b d).1 * (tp a b m).1 - (tp a b d).2 * (tp a b m).2))
      (pwr (a - b) d * pwr (a + b) m + pwr (a + b) d * pwr (a - b) m) := by
  ipra_lc (ZT.toZ Γ (tp a b m).1 - ZT.toZ Γ (tp a b m).2) * ZT.toZ_eq (tp_eigen (Γ := Γ) a b d).1 +
    (ZT.toZ Γ (tp a b m).1 + ZT.toZ Γ (tp a b m).2) * ZT.toZ_eq (tp_eigen (Γ := Γ) a b d).2 +
    (ZT.toZ Γ a - ZT.toZ Γ b) ^ d * ZT.toZ_eq (tp_eigen (Γ := Γ) a b m).1 +
    (ZT.toZ Γ a + ZT.toZ Γ b) ^ d * ZT.toZ_eq (tp_eigen (Γ := Γ) a b m).2

/-- The two-point function of the chain: the middle segment contributes `α_d − β_d = q^d`, so
`Z_{x,y} p^d = Z q^d` for `Z = 2 p^i p^d p^j`. -/
theorem chain_two_point (a b : ZT n) (i d j : ℕ) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.natLit 2 * pwr (a + b) i * ((tp a b d).1 - (tp a b d).2) * pwr (a + b) j * pwr (a + b) d)
      (ZT.natLit 2 * pwr (a + b) i * pwr (a + b) d * pwr (a + b) j * pwr (a - b) d) := by
  ipra_lc 2 * (ZT.toZ Γ a + ZT.toZ Γ b) ^ i * (ZT.toZ Γ a + ZT.toZ Γ b) ^ j * (ZT.toZ Γ a + ZT.toZ Γ b) ^ d * ZT.toZ_eq (tp_eigen (Γ := Γ) a b d).2

end LeanProofs.IPRA.Combinatorics.IsingChain
