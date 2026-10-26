# Independent manuscript review: sparse syntax and signed minimum-2 growth

## Scope and verdict

Reviewed the sparse-constructor, finite-marker, global-growth, local CRT bound,
signed-horizon, and cofinal-completeness sections of `report/main.tex`.
The final reviewed source SHA-256 is `1693c2996a99ee393bafe0ccffbe54f8c8beb383202d649384ef2f2cf7a857ea`.

No substantive mathematical inconsistency or unsupported novelty claim was
found in those sections. The proof is an ordinary mathematical proof composed
with the expressly identified inherited calibration and Pell/CRT theorems. It
is not an end-to-end proof-assistant verification, and the manuscript correctly
states that limitation.

## Items checked

1. **Finite-marker substitution.** The sparse shell ranges are disjoint, each
   nonzero constructor output is larger than both inputs, and the only
   zero-output normalization is `I(0,0)=0`. Reference Cantor coding is
   zero-generated. With `L=max(D,k)`, the chosen marker trees all have height
   `L+1`; atom-free source trees have image height at most `D`; compound trees
   containing an atom have image height strictly above `L+1`. This separates
   the only new collision cases. Constructor disjointness and injectivity
   prove the remaining cases by induction. The proof correctly uses a finite
   substitution, not an impossible global reverse injection. The guarded
   arithmetic witness is reselected after recoding.

2. **Sign bootstrap.** The slice `t=2+4z` implies even nonzero `t` and
   `|t|>=2`. The divisibility row gives `|F|>=2^20` before any positive-center
   Pell classification. Thus the retained shared frame is already large
   enough. Since `C,F` are even, `2(C+F+1)` is a nonzero even integer. The
   first signed power request gives `x>=0`; the endpoint beta modulus excludes
   `x=0`; hence the next power request orients `t`, proving `t>=2`. There is
   no use of a growth estimate at a possibly negative center.

3. **Global label growth.** The local constructor recurrence yields
   `L=16^(d-1)t^d`, `d=2^19`. With center `8t+1`, the congruence modulo `8t`
   and exact 2-adic valuation force the canonical Pell index to be at least
   `dt`. The comparison `(16t)^(dt-1)>=L^t` reduces exactly to
   `16^(t-1)>=t`. Consequently the updated center covers the sparse labels.

4. **Local CRT exponent budget.** The nine source depths are
   `[4,3,3,3,3,5,4,3,19]`. For `R>=16`, the constructor exponent recurrence
   is `e -> 2e+1`, giving ordinary exponent 63 and bundle exponent 1,048,575.
   The squared axis product is below `R^1092`, the joint bundle/guard term
   below `R^2097157`, and each beta square below `R^12`. The product of the
   first two terms, plus both beta squares, is below `R^2098250`, strictly
   inside the retained `R^(2^23)` budget. The lower
   bound on `F` supplies `x>2^32`, and the beta inequalities give `R<2x`.
   Thus the final `<2^x` comparison is valid, including the minimum horizon.

5. **Completeness and parity.** The cofinal progression
   `t == 2 (mod 2^23)` lies in the affine slice, has valuation one, and clears
   bit 20. The initial Pell ordinate divided by `dt` is an odd integer.
   Applying the retained residue-permutation theorem at the composed center
   produces arbitrary large positive odd indices with
   `F == 2^20 (mod 2^N)`, where `2^N>t`. This makes the binary supports of
   `F` and `t` disjoint and the required binomial coefficient odd. The growth
   witnesses are explicitly reconstructed. Including all odd primes at most
   `t` in the beta spacing makes the moduli with indices 1 through `t+1`
   pairwise coprime; the prime 2 already divides `F`. Subsequent witness
   choices follow the inherited noncircular order.

6. **Claims and scope.** The manuscript distinguishes unrestricted integer
   roots of the quartic from strictly positive roots of the compact equation,
   distinguishes source semantics from exact finite compilation checks, and
   does not claim worldwide priority, global minimality, consistency of ZFC,
   or a newly checked full formal dependency closure.

## Portability of the depth checker

`check_sparse_depth.py` accepts one or more explicit source paths and an
optional `--function` name. It contains no workspace-specific absolute paths.
It extracts literal schema ASTs and evaluates only constructor depth; it does
not import a compiler. Both ordinary and optimized Python executions passed
on `sparse_source.py` and the sparse local producer. Its receipt authenticates
those historically inspected source bytes. The final packaged source was also
checked as recorded below.

## Editorial corrections already applied

The initially missing backslashes on two `\qquad`/`\quad` commands were
corrected. The explicit `F>2^32` lower bound, beta index range, beta-square
bounds, and reconstructed growth witnesses have been added to the manuscript.
No further correction is requested by this review.


## Final editorial and packaging review

The final `report/main.tex` was compared with the retained prior manuscript.
The subsequent changes are editorial: the canonical equation path is now
`direct208/equations/principal208/equation.json`; citation markers have been
added; the `Ref` macro has been renamed `RefZ` without changing its expansion;
constructor formulas have been split across lines; and path typography uses
`nolinkurl`. None changes a polynomial, quantifier domain, hypothesis, bound,
or mathematical argument. The original manuscript review bound source hash
`de7c50734aa68db914f2a129e49db38d5edd3ca10d6ea21d0ca357f08b3e3b09`; the heading above binds the final source bytes.

### Historical producer names and the packaged source

The references to `sparse_work/prototype.py` in the historical sparse-source
review and its original receipt refer to the development version of the
producer now packaged as `direct208/local_compiler.py`. The packaged file has
SHA-256
`702d4d4fa03983b43e3e0060ddc2ffe0c385f26b81ae894b3ada6aeb110a933b`.
The producer changed packaging and path handling; the release's independent
`direct208/check_local.py` verifies the actual emitted schema identities and
whole graft against the pinned parent, without importing that compiler.

The final portable depth check was rerun in ordinary and optimized Python
modes on `reviews/sparse_source.py` and `direct208/local_compiler.py`.
Both passed with the same nine depths
`[4,3,3,3,3,5,4,3,19]` and local exponent `2098250 < 2^23`.
The exact local source checker was also rerun and passed: 75 acyclic local
gates, nine constructor trees, eleven Horn factors, interface coordinates
79 and 95, and all 154 graft residuals. These checks establish the link from
the historically reviewed prototype to the packaged literal source.

The historical proof notes and their source hashes have been retained without
rewriting them. This note supplies the current packaging correspondence.
