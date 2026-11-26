import IPRADerivations.Combinatorics.CodingBounds

/-!
# The first-moment bound and the Schröder–Hipparchus recurrence

Packet: `combinatorics/Combinatorics-iPRA`, `graphs.tex`, result 33 ("A finite first-moment lower bound"), and
`enumeration.tex`, result 12 ("Schröder–Hipparchus numbers").

Result 33: "Multiplying by `C(n, k)` counts the pairs (coloring, bad set), and the hypothesis says this is less
than the number `2^M` of colorings. If all colorings had a bad set, assigning the first one to each would give
at least `2^M` pairs." With `M` colourings, `N` sets, a table `B` of integer terms (a bit when the set is bad
for the colouring) and `c` bad colourings per set, as iPRA derivations:

* `first_moment`: if every colouring has a bad set, then `M ≤ N c`;
* `first_moment_absurd`: so `N c < M` is contradictory with it: some colouring has no bad set.

Result 12: "`H_1 = 1`, `H_n = 2 ∑_{i=1}^{n−1} H_i H_{n−i} − H_{n−1}` (`n ≥ 2`) ... In particular
`H_{10} = 103049`". For the table `hip` of the values `H_0, …, H_{10}`:

* `hipparchus_recurrence`: `H_n + H_{n−1} = 2 ∑_{0<i<n} H_i H_{n−i}` for `2 ≤ n ≤ 10`, as an iPRA derivation
  about numerals (so the recurrence from `H_1 = 1` produces `H_{10} = 103049`).

Not derived: the search for the colouring, the count of bad colourings per set, and the bijections between the
families counted by `H_n`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FirstMoment

open_ipra
open LeanProofs.IPRA.Combinatorics.CodingBounds (sphere_covering)

variable {n M N : ℕ} {Γ : List (Fm PTm n)}

/-- If every colouring has a bad set and every set is bad for at most `c` colourings, then `M ≤ N c`. -/
theorem first_moment (B : Fin M → Fin N → ZT n) (c : ZT n)
    (hrow : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun j => B i j))
    (hcol : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => B i j) c) :
    Γ ⊢[PRAAx] zle (ZT.natLit M) (ZT.natLit N * c) :=
  sphere_covering (fun j i => B i j) c hcol hrow

/-- With `N c < M`, not every colouring has a bad set. -/
theorem first_moment_absurd (B : Fin M → Fin N → ZT n) (c : ZT n)
    (hrow : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin fun j => B i j))
    (hcol : ∀ j, Γ ⊢[PRAAx] zle (ZT.sumFin fun i => B i j) c)
    (hlt : Γ ⊢[PRAAx] zle (ZT.natLit N * c + ZT.natLit 1) (ZT.natLit M)) (φ : Fm PTm n) :
    Γ ⊢[PRAAx] φ := by
  have h := first_moment B c hrow hcol
  ipra_absurd (zsl h + zsl hlt)

/-- The Schröder–Hipparchus numbers `H_0, …, H_{10}`. -/
def hip (k : ℕ) : ℕ := [0, 1, 1, 3, 11, 45, 197, 903, 4279, 20793, 103049].getD k 0

theorem hip_rec : ∀ m : Fin 11, 2 ≤ m.val →
    hip m.val + hip (m.val - 1) =
      2 * ∑ i : Fin 11, (if 1 ≤ i.val ∧ i.val < m.val then hip i.val * hip (m.val - i.val) else 0) := by
  decide

/-- `H_n + H_{n−1} = 2 ∑_{0<i<n} H_i H_{n−i}` for `2 ≤ n ≤ 10`. -/
theorem hipparchus_recurrence (m : Fin 11) (hm : 2 ≤ m.val) :
    Γ ⊢[PRAAx] ZT.eq ((ZT.natLit (hip m.val) : ZT n) + ZT.natLit (hip (m.val - 1)))
      (ZT.natLit 2 * ZT.sumFin fun i : Fin 11 =>
        ZT.natLit (if 1 ≤ i.val ∧ i.val < m.val then hip i.val * hip (m.val - i.val) else 0)) := by
  ipra_cast hip_rec m hm

end LeanProofs.IPRA.Combinatorics.FirstMoment
