# ZRows: toolkit for the unrestricted-integer rows

This is the shared Lean layer for iPRA endpoints of the frontier rows whose unknowns range over ℤ
(10ℤ to 17ℤ in `con-zfc-diophantine-forms/README.md`). The modules live in
`Lean/DiophantineConsistency/ZRows/`.

**Status:** stage 1 is built. Each module re-elaborates without errors or warnings, and every
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. No ℤ frontier endpoint is
closed yet.

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

## What remains (for 11ℤ, 10ℤ and 113's 12ℤ)

* The witness for `neg_three_square_of_witness`. This needs a bound on the number of roots of
  `Xᵐ − 1` modulo `p` for a nonstandard `m`, for example from the finite-difference identity
  `Σₖ (−1)^{m−k} C(m,k)(c+k)^m = m!`.
* Coprime factors of a square are squares, up to sign.
* Intersective roots: for every `m > 0` there is a `t` with `m ∣ (t² + 3)(t³ − 19)`. The proof
  uses CRT, Hensel lifting and the special primes 2, 3 and 19.
* Interpolation: `v_p(ψ(n₀)) ≥ v_p(n₀)` and CRT for moduli that need not be coprime.
* The source34 converse port (11ℤ) and the per-point graph, soundness and completeness modules.

The 12ℤ–17ℤ rows other than 113 have a guard of the form `1 + p₁² + p₂² + p₃(p₃ + 1)`. For them,
completeness also needs Legendre's three-square theorem inside models of `𝗜𝚺₁`. It is not in
Mathlib, Foundation or this tree.
