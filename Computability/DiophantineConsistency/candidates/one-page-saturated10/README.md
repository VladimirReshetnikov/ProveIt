# Complete saturated Pell equation on one page

[equation.pdf](equation.pdf) and its standalone [TeX](equation.tex) give a
complete equation in ten strictly positive integer unknowns. Its exact
polynomial degree is **283** and its complete live straight-line evaluator
uses **92 binary arithmetic operations** (55 multiplications, 20 additions,
17 subtractions). All four fixed integers, every tile and action, the full
436-character numeral, alphabet and decoder are printed on the same Letter
page. No external table or program is part of the equation's specification.
The body uses 9-point type. The extracted page has 3,129 nonwhite characters.

Compared with the preserved [98/360 page](../one-page-index-weight10/equation.pdf),
this saves six operations and lowers degree by 77 at the same unknown count.
The fixed recipe is also shorter: it uses the separately proved indexed
selector enumeration, whose whole constant body is copied verbatim from
[its sealed page](../../research/indexed-tile-enumeration/equation.tex).
Every earlier complete page and its TeX remain preserved.

The [ordinary proof](../../research/ten-positive-saturated-pell/PROOF.md)
proves soundness and positive completeness. It saturates a coprime Pell
product, recovers both integral roots, and uses a fresh main Pell period
and explicit auxiliary growth in the converse. Its formal Laurent argument
establishes the global degree and a nonzero highest homogeneous coefficient.
Finite ray tests supplement that proof. The sharp center gives a separate
93-operation degree-278 alternative; the direct chart gives 98/258 and
99/254. No global minimum is claimed.

This page uses the SECOND whole specialization in that proof's section 7:
the indexed tuple, whose native, selector and controller calibration is
proved in the [indexed packet](../../research/indexed-tile-enumeration/PROOF.md).
Its K differs from the primary incoming BFS K. We do not identify two
specialized polynomials or transfer their native words pointwise. The
coefficient-uniform saturated theorem composes with the whole indexed
native theorem. All four ports, their raw bytes and compressed payloads
are bound jointly in polynomial.json and SOURCE_PINS.json.

The page's abbreviation A denotes mu*Y*(X+1), the zero-offset register
Am1 in the source circuit. Thus Delta=A*(A+2) and C_g=(A+2)*U*E.
The proof's Pell base is A+1. The page's E denotes the coprime factor
Dtau. These notation changes are bound to the complete actual graph.
All abbreviations are polynomials in the ten unknowns; fixed quotients,
remainders and sums occur only in the definitions of constants.

The [renderer](../../tools/render_saturated10_page.py) binds every live
gate over four FREE coefficient ports modulo associative/commutative
arithmetic, checks both complete source seals, copies all four indexed
payloads together and renders deterministic standalone TeX. Normal and
optimized receipts retain its full symbolic binding and page checks.
PEER_FRONT_AUDIT.py independently parses the actual TeX and template,
including the boxed formula, rather than trusting the renderer's formula
list. It also checks the whole constant body, seed, payloads and actual
PDF text, and rejects mutations of the printed mathematics. See
PEER_REVIEW.md and PEER_BINDING.json for its exact scope and results.
The closed MANIFEST.json pins every candidate file except itself.

Replay from the repository root, sending stdout outside the sealed packet:

```sh
PYTHONDONTWRITEBYTECODE=1 python Computability/DiophantineConsistency/tools/render_saturated10_page.py > /tmp/saturated-page.json
PYTHONDONTWRITEBYTECODE=1 python -O Computability/DiophantineConsistency/tools/render_saturated10_page.py > /tmp/saturated-page-optimized.json
```

The ordinary equivalence is absence of positive solutions iff syntactic
Con(ZFC). Neither side is asserted. Internal-ZFC formalization and native
calibration remain open Lean work, currently paused at the owner's request.
The page is the entire finite equation specification; its proof is retained
separately. No Lean file or earlier sealed packet was changed.
