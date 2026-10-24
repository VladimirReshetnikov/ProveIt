# Short guard with compact integer-coordinate shears

These three complete circuits combine the round12 short-guard prefix with
the earlier compact final-coordinate translations. All ten unknowns range
over unrestricted integers.

| Literal | Live operations | Exact degree | Round12 alternative at this degree |
|---|---:|---:|---:|
| linear.json | **475** | 1,179,788 | 485 |
| cubic.json | **478** | 1,114,252 | 496 |
| sixterm.json | **512** | 1,080,888 | 545 |

The471-operation parent at degree1,245,324 remains a separate shorter
choice. Counts charge every live binary addition, subtraction and
multiplication, including squares and fixed scalar products; numeral
leaves and shared reuse are free. All nodes and inputs are live.

## Ordinary correctness

The new short-guard parent and all twelve actual fixed leaves are pinned
to `ConZFC_Direct_Centered_Round12_2026-10-24.zip`, arrival43ac596e36.
Its source/guard proof is retained under `source/`, including the TeX.
The fixed manifest and all coefficient recipes are byte-identical to the
retained norm10 whole tuple in `../norm-tail-sharing/source10/`; every
signed payload is authenticated during replay.

The source-aware guard replaces the old approximation polynomial by

```
delta = g*(cap-g)*K²-cap²*(C-KL)².
```

The unchanged initial square-factor/residue argument of the integer
representation gives positive b,Q, hence cap>0, before invoking this
guard. For arbitrary integers with cap>0, delta>0 forces K nonzero and
0<g<cap. Since4g(cap-g)<=cap², it also gives4(C-KL)²<K², the bound needed
by the inherited representation. Completeness uses canonical source codes:
the positive coordinate at the largest weight116 is at least3, so
g>=B^116; the digit bound gives g<cap=b*B^116 and B^116>=b². Consequently
g³>=cap². The existing strict approximation |C-KL|<|K|/(4g), with K nonzero,
then implies

```
delta/K² > g*(cap-g)-cap²/(16g²) >= 15g/16 > 0.
```

This is a source-existence argument. The old and new guard polynomials
are not claimed identical or equivalent on every noncanonical assignment.
The original signed Pell/norm reliability and native/compiler/refutation
interfaces remain the parent's named ordinary dependencies.

Write the parent's final norm as

```
P(v,m)=[t²+s*(a0-a1)]²-4s*a0*t²,
t=Sigma*m-Theta, s=Sigma².
```

For each retained compact polynomial R(v), the new literal is exactly
P(v,m+R(v)). Translation is an integral polynomial automorphism with
inverse m=m_old-R(v), including when scales vanish. Thus it preserves the
entire integer zero set bijectively, with no new positivity premise.

The first two shifts are

```
R0=2*A*E*G*H,
R1=2*A*E0*(D-2*C²)*G*H.
```

The six-term R6 is the earlier26-monomial polynomial in h=A/2,B1,C,xi,y;
h is the actual integer polynomial halfA. Its full formula and exact
defect are pinned to the previous shear parent in
`../norm-tail-sharing/source10/parent_sixterm.json` and its arriving
ROOT_CERTIFICATES.json. No division by A, C or xi is introduced.

The builder transplants only the indicated earlier registers. Exact
integer-polynomial normalization verifies the complete R at those cuts.
Every parent gate is then checked after replacing the one m leaf by m+R.
The prefix induction and local shear identity cover every child node.
This proves substitution universally; sixty actual-coefficient signed
modular controls per variant are extra transcription diagnostics.

## Exact degree

The source registers used by each R are unchanged from the earlier shear
construction. They have deg(A)=16,384, deg(B1)=7,942, deg(C)=1, deg(xi)=2
and deg(y)=1. Also deg(Sigma)=81,922 and deg(Theta)=81,925. All three R
have degree229,409; their exact radical defects a1-R² have upper degrees
426,050,393,282 and368,449, by the earlier full coefficient identities.

The new guard lowers deg(a0) from294,619 to294,382, while deg(a1)=458,818
is unchanged. If Z=Sigma*m-Theta, expansion of the translated norm gives

```
[Z²+2*Sigma*R*Z-Sigma²*(a0+(a1-R²))]²-4*Sigma⁴*a0*a1.
```

The first two squared defects dominate and give degrees1,179,788 and
1,114,252, with the same nonzero leading forms as before. For R6, the
square has degree at most1,064,586 and the cross term has exact degree
4*81,922+294,382+458,818=1,080,888. Their degrees differ, so the cross
term survives. Its leading coefficient is nonzero with the actual whole
tuple. These are total polynomial degrees after cancellations, separate
from the unreduced DAG bounds.

## Replay and scope

```sh
python3 Computability/DiophantineConsistency/tools/build_short_guard_shears.py --check
python3 -O Computability/DiophantineConsistency/tools/build_short_guard_shears.py --check
```

Only inert parent JSON is used. No historical emitter or Lean command is
executed. The round12 authored normal/optimized release replay separately
checks the short-guard parent, source data, whole payload reconstruction,
exact parent degrees and mutation controls. This candidate adds exact
shear/substitution certificates and deterministic literal DAGs.

The resulting ordinary no-integer-zero equivalence composes with the
parent's syntactic Con(ZFC) calibration. A new Lean proof or encoded
object-ZFC derivation is not supplied; formalization remains paused.
