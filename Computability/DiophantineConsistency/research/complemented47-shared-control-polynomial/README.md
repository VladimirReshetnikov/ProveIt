# Shared control and support polynomial for the complete complemented47 page

The complete alternative [equation.tex](equation.tex) is **17 bytes shorter**
than the preserved complemented47 source: 5128 instead of 5145 UTF-8 bytes.
It defines exactly the same four integers and the same equation. The useful
structural simplification is that MC no longer scans 3297 digits of Phi:
one shared control polynomial supplies both the controls and their support.
The gain is small; this is a representation result, not a new coefficient
encoding or a global shortest-page claim.

The [one-page PDF](equation.pdf) uses exactly the parent's fonts, margins,
line-height settings and full finite language. The fifteen-variable front,
all 943 tile definitions, full action decoder, 62-character alphabet,
436-character seed and footer are literal copies. None was shortened or
omitted. The rendered page was visually inspected and has no overlapping
content or overfull boxes.

## Exact shared definition

With the existing geometric polynomial `G_m(x)=sum_(j=0)^(m-1) x^j`, define

```text
Psi(x,t) = x^1003*(x^20+t^17)*G_8(t*x)
         + t^8*x^983*(x^30+t^17)*G_9(t*x)
         + t^34*x^1095*(1+x^1100+x^2201).
```

Here x,t are formal arguments, not extra equation unknowns. Replace only the
three control lines in Phi and the support scan in MC:

```text
Phi(x) = sum_(i=0)^942
           [1+2^10*(1+w_i+2^8*n_i+2^17*p_i+2^25*s_i)]*x^i
         + 2^10*Psi(x,2),

MC = beta+rho-(rho+3)*rho^1063-G_943(rho)-Psi(rho,1).
```

MF, beta, K's complete remaining spelling and every other definition remain
literal. In particular K still uses `Lambda*Phi(1/rho)`, and MF is still the
once-shifted source mask.

To prove the entire Phi identity, expand the first two geometric sums. Their
exponent/coefficient pairs in `2^10*Psi(x,2)` are

```text
(1023+j, 2^(10+j)), (1003+j, 2^(27+j)),  0<=j<8;
(1013+j, 2^(18+j)), (983+j, 2^(35+j)),   0<=j<9;
(1095,2^44), (2195,2^44), (3296,2^44).
```

These are all 37 old nonselector coefficients. Every selector coefficient
is unchanged verbatim. Thus the full formal polynomial Phi, not just some
values or residues, is identical.

At t=1 the 37 disjoint control monomials all have coefficient one. They are
disjoint from the 943 selectors. Therefore the complete nonzero support is
`G_943(x)+Psi(x,1)`. Both dummy positions 1063 and 1064 are absent from it.
Every old coefficient is between zero and rho-1: the selector field uses
8/9/8/9-bit old labels, giving the sufficient bound
`0<c_i<=2^44+1<2^47=rho`; the controls are at most `2^44`.
Consequently each base-rho digit of Phi(rho) is its formal coefficient, and
the old ceiling expression returns precisely its nonzero-support indicator.
This proves the complete MC identity, including the existing forbidden-bit
and dummy corrections. No native carry theorem is used in this identity.

The four integers, their aggregate **207214 raw bytes**, the polynomial's
integer coefficients, every witness and every solution are unchanged
pointwise. All existing controller residues, proof contracts and limitations
are consequently preserved. This does not reduce the 66-operation integer
evaluator or degree157, and does not supply a new native or formal proof.

## Exact verification and measurements

The newly authored standard-library [audit.py](audit.py) was read before
execution. It does not import or execute any repository implementation.
It checks every control coefficient at t=2, the whole support at t=1, the
full MC integer, the unchanged complete finite-language suffix and front,
and deterministic candidate/source hashes. The computed 51742-byte MC has
the independently certified minimal big-endian SHA-256
`f9d3e993386834f3e57b964481c32bb0928645524f089dda517c64fb5fcfcd3f`.

Normal and optimized Python checks both passed:

```sh
python3 Computability/DiophantineConsistency/research/complemented47-shared-control-polynomial/audit.py
python3 -O Computability/DiophantineConsistency/research/complemented47-shared-control-polynomial/audit.py
```

These commands are read-only. Add `--write` to regenerate only equation.tex
and AUDIT.json after inspecting changes. The saved [AUDIT.json](AUDIT.json)
binds the complete parent source, auditor and candidate.

| Complete-source variant | UTF-8 bytes |
| --- | ---: |
| Preserved complemented47 parent | 5145 |
| Shared control/support polynomial | 5128 |
| Shared polynomial plus factored bare kernel | 5134 |

The last variant factors
`rho^30+rho^62=rho^30*(1+rho^32)` and
`rho^1100+rho^2201=rho^1100*(1+rho^1101)`. These are valid full identities,
but they add six source bytes, so that variant was not selected. No source
gain is attributed to renaming variables, changing fonts, deleting comments,
or changing whitespace.

The selected source builds with

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error equation.tex
pdftotext -layout equation.pdf equation.txt
```

It remains one letter-sized page. There are no overfull/underfull boxes;
the retained small-font substitutions are the original template's settings.
The parent and new PDF text extractions have 2734 and 2731 non-whitespace
Unicode characters, respectively: a reduction of three in this extraction
proxy. This is not asserted to be a font-independent printed-glyph metric.
PDF file size is also not treated as an equation-complexity metric.

The parent is the complete
`candidates/one-page-complemented47-independent/equation.tex`, SHA-256
`f28911a9c96e53cd5c3b2e94bdd72322fc065e05d0ace617edff26a5d2322ebd`.
The new complete source SHA-256 is
`b767b4b702e3d5d8368039d52a7d1c6f9bfefbd96856559a0a9e7b57ee2ec382`.
The source of the finite-support idea is the separately read
[`compact66-three-anchor-radix47-layout-identities` note](../compact66-three-anchor-radix47-layout-identities/README.md),
section 1. Its geometric support identity applies here because the
complemented layout has the same support. The new bivariate sharing is what
makes that identity shorter on this complete page; the old note did not
measure a complete source or claim a printed saving.

No maintained page, frozen parent or coefficient file was edited. There is
no shorter seed or smaller raw coefficient tuple in this proposal.
