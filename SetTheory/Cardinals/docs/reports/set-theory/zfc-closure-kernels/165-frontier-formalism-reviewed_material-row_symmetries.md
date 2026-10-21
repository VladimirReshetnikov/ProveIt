# Exact schema symmetries for source search

Pinned parent: ProveIt main `2762b8a183830b1f5a30cf059ffb4d92e77cddde`, candidate-k215.

## Logical row coordinates

Let `L=(G,rho6,rho5,rho4,rho3,rho2,rho1)` be the seven unguarded logical row functions of the three independent natural parameters `(a,b,c)`. Their current half-open primitive-leaf spans are:

| Row | Span |
|---|---|
| G | [479,888) |
| rho6 | [888,1171) |
| rho5 | [1171,1467) |
| rho4 | [1467,1766) |
| rho3 | [1766,2062) |
| rho2 | [2062,2412) |
| rho1 | [2412,2643) |

The source agent independently parsed these spans symbolically. Their postfix macro words agree with expansion of the inherited Dag230 axiom emitter, with G replacing rho7:

```
G    = 168 166 182 168 121 182 166 121 181 166 121 182 180 119 119
rho6 = 166 166 168 180 183 168 119
rho5 = 168 166 182 168 121 181 166 121 181 119 119
rho4 = 166 121 168 180 180 121 166 168 180 180 119
rho3 = 166 121 182 168 166 181 168 121 181 119 119
rho2 = 166 121 168 119 180 166 121 180 166 168 180 119 119
rho1 = 166 166 121 182 183
```

Macros 166,121,168 push the old top and load a,b,c respectively; 119 is implication,181 relation,180 universal quantification,182 equality,183 existential quantification. Their inherited `ProgLib230.v` contracts require clean scratch registers 6,7, preserve all parameter registers, and implement the constructor on the current top and stack. Each listed complete row block therefore sends `(top,stack)` to `(row(a,b,c), cons(top,stack))`, with no other observable change and with scratch registers clean again. Existential construction can equivalently expand as negation, universal construction, negation.

## Independent coordinate permutations

For each row index j choose a permutation sigma_j of the three coordinates. Let L'_j(a,b,c)=L_j(sigma_j(a,b,c)). Because sigma_j is a bijection of N^3,

    { L'_j(a,b,c) : a,b,c in N } = { L_j(a,b,c) : a,b,c in N }.

Hence changing load-a/load-b/load-c references consistently within that row leaves the set of native axiom codes exactly unchanged. For a row using only two coordinates, any ordered pair of distinct coordinates gives the same conclusion. This is an equality of numerical code sets, including zero and accidental formula-code aliases; no decoding hypothesis is involved.

## Row order

For any permutation pi of the seven row positions, composing the closed row blocks in order pi changes their stack order and the selector numbers that retrieve them. It does not change the family of available axiom codes. For every former selector number there is a unique new selector selecting the same row. The accepted proof-instruction enumeration ranges over all selectors and all natural parameter triples, so finite proofs translate by this fixed selector relabeling and the inverse coordinate permutations. Both translations are primitive recursive. Thus native refutability, and the existing Con(ZFC) calibration, are preserved.

A machine implementation must still check all-register block contracts, absence of control edges crossing a moved block boundary, and that any zero/out-of-range selector behavior remains the original harmless behavior. The source DAG census by itself is not that check.

## Commuting the seed conjunction

If the exact gated seed output is the conjunction of the seed core S(a,b,c) and membership-vacuity V(a,b,c), then changing its body from S and V to V and S preserves consistency calibration. The same all-code classical basis derives both directions of conjunction commutation, so either native bundle gives both required projections. The upper model validates both bodies under the unchanged arithmetic gate. This does not change the private role c or any code/label coupling, and is consequently different from replacing the bundle by arbitrary equality-free reinterpretations. A source implementation must retain the exact gate and all its parameter roles.
