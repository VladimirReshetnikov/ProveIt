# ZRows: toolkit for the unrestricted-integer rows

This is the shared Lean layer for iPRA endpoints of the frontier rows whose unknowns range over ℤ
(10ℤ to 17ℤ in `con-zfc-diophantine-forms/README.md`). The modules live in
`Lean/DiophantineConsistency/ZRows/`.

**Status:** stages 1 and 2 are built. Each module re-elaborates without errors or warnings,
and every `#print axioms` reports `[propext, Classical.choice, Quot.sound]` or a subset of it. No
ℤ frontier endpoint is closed yet.

## Convention

"The equation `e` has no integer solution" is formalized as `nativeNoZero (signedSplit e)`.
`signedSplit e` replaces each integer unknown `xᵢ` by the difference `aᵢ − bᵢ` of two natural
unknowns. Inside a model of `𝗜𝚺₁`, the natural zeros of `signedSplit e` correspond exactly to the
zeros of `e` in the ring of differences `DiffRing V` (`IntegerDomain.integer_zero_iff`).

## Modules (stage 1)

| Module | Content |
|---|---|
| `IntegerDomain` | `signedSplit`; `IntegerModelBridge e`: in every model of `𝗜𝚺₁`, `e` has a zero in `DiffRing V` ↔ machine 215 halts internally (the halting predicate of `IPRAOrdinary12.PositiveModelBridge`); `bridge_of_integer`; `native_of_integer`, `standard_of_integer`, `reference_of_integer` (native, standard and equality-only iPRA equivalences with the selected Foundation ZFC consistency predicate) |
| `ModelFermat` | in every model of `𝗜𝚺₁`, for irreducible `p`: `p ∣ C(p,k)` for `0 < k < p`; Fermat's little theorem (`fermat`, `fermat_mod`, `fermat_ring`); cube roots modulo `p = 3m + 2`; `−3` is a square modulo `p = 3m + 1`, given a witness `g` with `p ∤ g^m − 1` (`neg_three_square_of_witness`) |
| `PellDirichlet` | irrationality of `√d` by descent (`no_square_ratio`); internal Dirichlet approximation using integer square roots and squared comparisons only (`dirichlet`); arbitrarily large good approximations (`large_pair`) |
| `ModelPellExistence` | general Pell existence: for `d > 0` not a square, `∃ x y, 0 < y ∧ x² = dy² + 1` (`exists_pos`), and additionally `N ∣ y` for any `N > 0` (`exists_dvd`). The proof codes `E⁴ + 1` approximations (`E = 2d + 3`), applies `ArithmeticPellPigeonhole.pigeonhole` once to their base-`E` codes, and combines with Brahmagupta's identity |

## Modules (stage 2)

| Module | Content |
|---|---|
| `CoprimeSquares` | if `a·b = c²` with `Bez a b 1`, both factors are squares (`squares_of_mul_square`); the version for three pairwise coprime factors (`squares_of_mul_mul_square`); in `DiffRing V`, the absolute values are squares; `bez_of_no_common_irred`; `b² ∣ a² ⇒ b ∣ a` |
| `ModelRootWitness` | power sums `Σ_{g<p} g^j ≡ 0 (mod p)` for `1 ≤ j ≤ p − 2` (`sumPow_dvd`, by strong induction from `Σ_{i≤j} C(j+1,i)·Σ_{g<N} g^i = N^{j+1}`); hence a non-root of `g^m ≡ 1` exists (`exists_non_root`); `neg_three_square`: `−3` is a square modulo every irreducible `p = 3m + 1`; `cube_root_or_neg_three` for irreducible `p ≠ 3` |
| `Intersective19` | `root`: for every `m > 0` there is a `t` in `DiffRing V` with `m ∣ (t² + 3)(t³ − 19)`. The proof uses a simple-root Hensel step (`lift_step`, `hensel`) at internal exponents, the 3-adic cube root of 19 (`three_adic`), the prime-power cases `p = 2`, `p = 3`, `p ∣ 19`, `p ≡ 1` and `p ≡ 2 (mod 3)`, the splitting `m = pᵏ·r` with `p ∤ r` (`valuation`), and CRT (`crt_step`) inside an order induction on `m` |
| `GcdCRT` | congruences modulo `M` and `N` have a common solution iff `gcd(M, N) ∣ a − b` (`crt_gcd`, `crt_gcd_iff`) |

## What remains (for 11ℤ, 10ℤ and 113's 12ℤ)

* Interpolation, the Pell-specific part: the period `4n₀f` modulo `f²`, the valuation fact
  `v_p(ψ(n₀)) ≥ v_p(n₀)` (in the form `gcd(λ, 4I²) ∣ 4I`), and the Chebyshev congruences.
* The per-point graph, soundness and completeness modules. The halting side at the source34
  ports, needed by 11ℤ, is done: `Source34Converse.halt_iff_facts` (see
  [`source34-calibration`](../source34-calibration/README.md)).

The 12ℤ–17ℤ rows other than 113 have a guard of the form `1 + p₁² + p₂² + p₃(p₃ + 1)`. For them,
completeness also needs Legendre's three-square theorem inside models of `𝗜𝚺₁`. It is not in
Mathlib, Foundation or this tree.
