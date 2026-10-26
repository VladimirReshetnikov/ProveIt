# ProveIt comparison audit: pinned incoming scope

Repository: VladimirReshetnikov/ProveIt. Comparison commit:
`536c08e7913e59bd42e8fca66e89944c920884ad` (25 October 2026).
All twelve ZIP files listed by the contents API at that exact commit were
downloaded; their Git blob SHA-1 and lengths match the pinned listing.
`PINNED_INCOMING.json` records the listing and
`new_construction/PROVENANCE.json` additionally records SHA-256 and URLs.

The initial unpinned listing had eight incoming archives. Pinning the final
comparison discovered four further packages: Integral Projection Lattice,
Linear CRT, Pooled Powers, and Quadratic Projection 234. Those four materially
change the frontier and the novelty assessment. This report uses the pinned
twelve-archive scope throughout.

## Read scope

Every incoming top-level README was read. The maintained Hilbert Tenth Problem
README, forms README, latest proposal review, and construction READMEs 140–147
were also retrieved. Deeper ordinary-proof and code review concentrated on
Factorial-Free Binomial CRT, Shared Factorial Error, and the parts needed to
compose their signed Pell/frame arithmetic; the independent projection checker
and reducer in Quadratic Projection 234 were read and replayed on the new
source. Linear CRT was examined to distinguish its arithmetic from ours.
Other agents separately review Pooled Powers and compact carrier formulas.
This is not a claim to have independently proved every theorem or rebuilt
every transitive proof-assistant dependency in all twelve packages.

## Direct quartic comparison

All dimensions in this table count unrestricted integer coordinates. Heights
are maxima of absolute coefficients in the collected polynomial, not maxima
of coefficients in the quadratic residuals. Rows count quadratic residuals.
The table lists representative supplied endpoints, not every variant.

| Incoming package | Variables | Rows | Collected terms | Height | Relevant mechanism |
|---|---:|---:|---:|---:|---|
| Cofinal Witnesses and Centered Carriers | 246 | 178 | 12,541 | 12,227 | Even cofinal horizon and beta carrier contraction |
| Digit Recovery | 247 | 182 | 4,755 | 8,815 | Signed digit recovery and paired product signs |
| Factorial-Free Binomial CRT | 242 | 178 | 5,018 | 7,968 | Remove factorial authenticity; generalized binomial selector |
| Integral Projection Lattice, principal | 240 | 177 | 5,803 | 6,404 | Integral nonunit projection and positive definite residual Gram form |
| Integral Projection Lattice, low height | 240 | 177 | 9,357 | 4,160 | Alternate positive definite Gram form |
| Joint Norm | 245 | 181 | 5,304 | 128,446 | Joint factorial-error and remainder norm |
| Linear CRT, principal | 238 | 174 | 13,149 | 6,144 | F=t^t, R=F, linear beta multiplier and semantic radix recovery |
| Linear CRT, sparse | 239 | 175 | 4,963 | 7,968 | Alternate final affine projection |
| Linear CRT, low height | 239 | 175 | 6,723 | 4,432 | Alternate residual basis |
| Nearest Factorial, principal | 242 | 178 | 17,026 | 38,432 | Nearest-factorial and centered signed representations |
| Nearest Factorial, sparse | 243 | 179 | 6,877 | 11,856 | Alternate affine projection |
| Normalized Residues Round19 | 244 | 176 | 5,212 | 3,968 | Direct residue normalization and row-basis optimization |
| Pooled Powers | 225 | 162 | 7,867 | 128,446 | Pool requests at each common base using two residuals |
| Quadratic Projection 234, principal | 234 | 171 | 19,050 | 4,480 | Six common-Hessian-radical polynomial integer projections |
| Quadratic Projection 234, factorial-free | 235 | 170 | 18,550 | 4,576 | Radical projections, cofinal two-square beta spacing, final affine exposure |
| Quadratic Projection 234, sparse | 236 | 171 | 4,947 | 16,866 | Alternate factorial-free projection |
| Shared Factorial Error, principal | 240 | 177 | 21,482 | 6,144 | Signed affine radix and shared factorial error |
| Shared Factorial Error, sparse | 241 | 178 | 5,351 | 15,107 | Alternate final affine projection |
| Shared Factorial Error, low height | 241 | 178 | 9,544 | 4,512 | Residual-basis tradeoff |

The Lucas Corrections and Witness Elimination package additionally supplies
a 248-variable quartic and higher-degree projections, including 153 integer
variables at degree eight and 125 at degree sixteen. These cannot be compared
by variable count alone to the fixed-quartic, small-coefficient family.

The maintained construction 147 has a 258-variable quartic (186 rows,
5,319 terms, height 47,281), so relying only on maintained-directory READMEs
would substantially misstate the current incoming frontier. The 225-variable
pooled equation is the smallest dimension among the direct small-coefficient
quartics displayed in these incoming READMEs. Other repository architectures
already use fewer variables with very different coefficient or degree costs.

## Compact formulas and alternate compilation targets

The maintained positive-integer compact construction has a 15-variable
66-operation degree-157 expression. The Cofinal Witnesses package gives
10-positive-variable points at 79 operations/degree 382 and 80/338, and
signed integer points at 14 variables/degree 88/110 operations and
13 variables/degree 156/117 operations. Nearest Factorial gives
14 integer variables/degree 82/113 operations, 13/152/126, and
11/298/150. Lucas Corrections gives a 10-positive-variable point at
87 operations/degree 304. Shared Factorial Error gives a 10-positive-variable
point at 78 operations/degree 454. These are separate Pareto tradeoffs;
none determines a universal notion of simplest equation.

Integral Projection Lattice also gives an explicit eleven-axiom finite
theory with eight fixed function symbols, 2,736 arithmetic gates and 107,353
syntax nodes, equiconsistent through its calibrated polynomial. Translating
that theory into the exact compact binary-relation calculus and constructing
a smaller Diophantine equation remain open. It is a concrete future target,
not a new completed equation point.

## What survives the priority audit in this contribution

Our independently developed diagonal source uses
t=16+2h², F=t^t, R=F, y=F(2v+1), q=6z+3, and
H=3+6 times the sum of actual CRT representatives. The Linear CRT submission
already contains F=t^t, R=F, and y=F(2v+1). We explicitly attribute that overlap
and make no discovery claim for the diagonal choices.

The q congruent to 3 modulo 6 bootstrap is a distinct alternative: both q
and q+1 are nonunit before signs are recovered, avoiding an even chart for
one CRT representative. Its completeness uses an automatically odd multiple
of three for the semantic radix base. The even-horizon bound
lcm(1,...,t)² <= t^(2*pi(t)) <= t^t is particularly short. All boundary and
negative-radix cases are proved in `new_construction/PROOF.md`.

Common-Hessian-radical projections are imported directly from the incoming
Quadratic Projection 234 package and composed with this distinct source.
Pooling, if composed, is likewise attributed to the incoming Pooled Powers
package. The value of such a composition is its actual measured and proved
result, not a claim to have invented its inherited parts.

## Proof status

Every claimed consistency equivalence here is an ordinary mathematical
argument intended to be formalizable in ZFC, composed with the named inherited
interfaces `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Finite Python audits
check literal polynomials, maps, frame membership, coefficient expansions,
and deterministic reproduction. They do not prove an unbounded theorem or
decide consistency. A new end-to-end Lean/Rocq build and an encoded object-ZFC
proof string are not supplied. No unconditional consistency assertion,
global minimality claim, or literature-wide novelty claim follows.
