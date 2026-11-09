# ZRows: toolkit for the unrestricted-integer rows

This is the shared Lean layer for iPRA endpoints of the frontier rows whose unknowns range over ℤ
(10ℤ to 17ℤ in `con-zfc-diophantine-forms/README.md`). The modules live in
`Lean/DiophantineConsistency/ZRows/`.

**Status:** stages 1–4 are built. Each module re-elaborates without errors or warnings,
and every `#print axioms` reports `[propext, Classical.choice, Quot.sound]` or a subset of it.
The first ℤ frontier endpoints using them are package 138's eleven-integer 924/107 and 840/108
(`P138/IPRAInteger138`, `P138/IPRAInteger138Short`; record in
[`p138-integer11`](../p138-integer11/README.md)).

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

## Modules (stage 3: supported-modulus interpolation)

The convention is Lean's `ycoord n a`, with discriminant `delta a = (a+1)(a+3)`.

| Module | Content |
|---|---|
| `PellBinomial` | the internal binomial expansion of both Pell coordinates (`coords`); Euler's form `ψ(p) = Q·p + Δ^((p−1)/2)` at an irreducible odd `p` (`ycoord_prime`); `p ∣ ψ(p) ⇒ p ∣ Δ` |
| `PellValuationIndex` | `k ∣ ψ(t) ⇒ k·ψ(t) ∣ ψ(kt)` (`lift`); Frobenius `p ∣ ψ(pm) ⇒ p ∣ ψ(m)` for `p ∤ 2Δ`; `index_valuation`: `p ∣ ψ(n)` and `pᵏ ∣ n` give `pᵏ ∣ ψ(n)`; the split `n₀ = g·w` with `g ∣ I` and `w` coprime to `I` (`coprime_split`); `strong_index` |
| `PellEvenChebyshev` | `ψ(2t) ≡ −2t` and `ψ(2t+1) ≡ 2t+1 (mod 2(b+3))`; `even_ordinate`: `ψ(2L) = 2(b+2)P` with `P ≡ ±L (mod 4(b+2)²)` |
| `LinearInterpolation` | the odd quotient modulo every `c ∣ 4I²`; the square period; `linear_interpolation` and `supported_interpolation`: stepping the auxiliary index by `4·I·f·w` moves `T` linearly by a unit modulo `I²`, so `T` reaches every class modulo any `M ∣ I²` |

This replaces the lifting-the-exponent theorem and the valuation isometry of 112 §5 by linear
stepping. Neither LTE nor a pigeonhole surjectivity argument is needed.

## Modules (stage 4: interpolation modulo `I⁴`)

The linear-cofactor completeness (packages 135, 144, 153, 165, 172) interpolates modulo
`u·s·r = A²·d·s·t³`, which divides `I⁴` but in general not `I²`.

| Module | Content |
|---|---|
| `QuarticInterpolation` | `step_law`: the linear law of the abscissa quotient from an arbitrary base point of the progression, for any half step `m = 2·I·f·w·k` with `ψ_ρ(m) = 2ρ·I·Q·P`; `first_ordinate` (`Q = 1`) and `second_ordinate` (`Q = I²`, `m = 2·I·f·w·I²`, `P` coprime to `I`), the latter by the composition `ψ_ρ(m₁·I²) = ψ_ρ(m₁)·ψ_C(I²)` at `C = χ_ρ(m₁)`, the residue law `ψ_C(N) ≡ N (mod C − 1)` and `I⁴ ∣ C − 1`; `quartic_interpolation` and `supported_interpolation4`: stepping first by `4·I·f·w` and then by `4·I³·f·w` makes `T` reach every class modulo any `M ∣ I⁴` |

The second level needs only that the cofactor `P` of `ψ_ρ(2·I·f·w·I²) = 2ρ·I³·P` is a unit
modulo `I`. The sharper congruence `P ≡ ±L (mod L·ρ²)` (`L = I³·f·w`) considered during route
planning is false in general (it fails for `a = 0`, `n0 = 6`, `I = 780`, and in every small instance
tested with `3 ∣ I`) and is not used. The bound is `M ∣ I⁴`: one more level per further
factor `I²` would need one more composition, that is, an internal induction over levels.

## What remains (for 11ℤ, 10ℤ and 113's 12ℤ)

* The per-point graph, soundness and completeness modules. The halting side at the source34
  ports, needed by 11ℤ, is done: `Source34Converse.halt_iff_facts` (see
  [`source34-calibration`](../source34-calibration/README.md)).

The 12ℤ–17ℤ rows other than 113 have a guard of the form `1 + p₁² + p₂² + p₃(p₃ + 1)`. For them,
completeness also needs Legendre's three-square theorem inside models of `𝗜𝚺₁`. It is not in
Mathlib, Foundation or this tree.
