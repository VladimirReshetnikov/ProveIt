# Author record: the literal length2011 kernel

`controller_certificate` authored `CurrentKernel2011.lean` and its focused
checks. ROOT assigned the work and requested the public transition-family
mass API. The table itself is supplied by `WangTiles942Core`, authored by
`complemented47_review`. This is an author verification record; independent
review and replay are separate roles.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentKernel2011.lean | 6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55 |
| CurrentKernel2011Checks.lean | e8225d12a427aa82845b34e86e5d48483ec1831351873b37972d12345695aaa4 |
| WangTiles942Core.lean | 7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85 |
| WangTiles942Data.lean | ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125 |

The maintained page and preserved
`candidates/one-page-padding-staircase-carrier65-2011/equation.tex`
have the same SHA-256
`a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`.
The exact formula is

```
rho = 2^47
K = rho^18 + rho^1004 + rho^2020 + 2*rho^1005*Phi(1/rho)
Phi(x) = sum_i chi_i*x^pi(i)
       + 2^10*x^969*(x^9+2^17)*G8(2*x)
       + 2^18*x^942*(x^18+2^17)*G9(2*x).
```

`phi_printed` proves this complete compact Phi expansion over every
commutative semiring. The selector family has all 942 actual abstract
tiles and their actual printed floor ranks. Its weight is
`1+2^10*(1+west+2^8*north+2^17*east+2^25*south)`.
The 34 control entries use the actual packed coefficient orientation:

| Packed color | Positions | Unscaled weights |
|---|---|---|
| West | 978+j, 0<=j<8 | 2^(10+j) |
| North | 960+j, 0<=j<9 | 2^(18+j) |
| East | 969+j, 0<=j<8 | 2^(27+j) |
| South | 942+j, 0<=j<9 | 2^(35+j) |

The zero-weight physical dummy977 and marker1004 are absent from Phi.
The bare marker monomial at1004 remains in K. The shared bare18 term
has coefficient1, even though it serves two copy families. The 976 Phi
entries and three unit entries give 979 indexed stencil terms. This is
not a claim of 979 distinct exponents: coincident terms are added.

`physicalPosition_le` derives the coarse bound942 directly from the
printed rank formula and each selector-weight bound. All control
positions are at most985. These bounds prove every exponent in
`rho^1005*Phi(1/rho)` cancels to a nonnegative integer exponent.
`rawWord_printed` and `K_printed` prove the rational Laurent expression
equals the natural-number stencil. `K_pos` derives strict positivity
from its positive bare term. No rank injectivity is assumed for these
identities or the subsequent mass bounds.

The exact mass is computed from the complete unsorted abstract table.
Sixteen-row kernel-checked batches are composed using opaque generic
list equalities. The public `transition_mass` reuses the full 430-row
transition total so later tail proofs need not evaluate it again.

| Family or total | Mass |
|---|---:|
| Start | 34876427265 |
| All430 transitions | 11139798681006 |
| Both copy families | 29755760447492 |
| Right signals | 3151578377695630 |
| Left signals | 379496611276890 |
| Tail rows | 240316907829267 |
| All942 selector weights | 3812322332357550 |
| All34 control weights | 17592186043392 |
| Complete unscaled Phi | 3829914518400942 |
| Complete K stencil | 7659829036801887 |

For every nonzero cyclic length, `folded_word` identifies the folded
coefficient word with K modulo `rho^n-1`. `convolution_terms` and
`convolution_eq` give the exact action of every monomial, preserving
collisions and exponents beyond the cyclic window. Boolean input digits
and temporal digits at most `2^46` imply raw digits at most
7730197780979551. Adding carry57 remains strictly below `58*rho`.
`exists_normalization` therefore obtains bounded cyclic carries and the
exact positive residue word from the explicit transport congruence and
strict residue bound.

A separate standard-library numerical reconstruction of the complete
715-digit decoder, all430 actions, all942 tiles, all floor ranks and the
actual stencil matched the preserved page's complete K bytes:
11868 bytes, SHA-256
`64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7`.
This numerical cross-check is supplemental; the Lean proof obtains its
mass and displayed-formula identity from the actual formal definitions.

Development initially exceeded the 6GB cap while rewriting closed table
sums. Those failed runs were not accepted. Generic list aggregation,
explicit direct telescope terms, and generic finite-sum aggregation
removed those costly conversions without changing a numerical datum.
The final source was fully reread and freshly compiled with
`lake env lean -M6000 -j1 -o ...`; its log was empty. The focused checks
also freshly passed, including the actual packed color slots, absence of
dummy/marker from Phi, the single shared18 coefficient and integer K
positivity. All eleven axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

The module supplies literal kernel binding and arithmetic carry
normalization. It does not establish count recovery, phase alignment,
tile matching, native acceptance, or equivalence of the equation with
Con(ZFC). These remain separate obligations.
