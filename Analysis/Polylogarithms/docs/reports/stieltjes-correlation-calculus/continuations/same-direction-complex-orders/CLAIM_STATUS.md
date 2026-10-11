# Claim status

“Proved” below refers to the analytic or algebraic proof in `article.tex`.
It does not mean proof-assistant checked or independently peer reviewed.

| Claim | Status | Exact scope |
|---|---|---|
| Entire connected double-Hurwitz coordinates | Proved, Theorem 2.1 | Both order indices arbitrary complex; Re(q)>0; normalized Mellin continuation is explicit. |
| Shift/stuffle/interpolation laws | Proved, Theorem 2.2 | Entire extension of laws inherited on positive integral indices. |
| Two-order same-direction spectral representation | Proved, Theorem 3.2 | z,w>0; Re(N)>0; -2<Re(beta)<Re(N); s,t arbitrary complex. |
| Recovery of integer connected master | Proved, Theorem 3.4 | Exactly the inherited two-cone formula, not a new integer conjecture solution. |
| Beta–Newton and mixed derivatives | Proved, Theorem 4.3 | Equal positive scales normalized to 1; stated beta strip; absolute local normal convergence. |
| Polynomial–Hurwitz finite closure | Proved, Theorem 5.1 | One nonpositive integer order; N integer >=1; b integer from -1 to N-1; other order arbitrary; Re(a)>0. |
| Coalescing Gamma generator | Proved, Theorem 6.1 | Initial residue series for Re(s)>3 and a punctured small lambda disk; paired lambda limit; entire s continuation supplied by the ordinary integral. |
| All logarithmic moment coefficient/depth formula | Proved, Theorem 6.2 | Every r>=0; convergent multiple-zeta expression for Re(s)>2; entire continuation of the whole expression; depth at most r+1. |
| All dilogarithm logarithmic moments | Proved specialization, Corollary 6.3 | Every nonnegative integer logarithmic weight; classical-method special case, no priority claim. |
| Ordinary Stieltjes–Gamma kernels and anchored primitives | Proved, Theorems 7.1–7.2 | Every Stieltjes index; Re(q)>0; absolutely convergent final integrals. |
| Rational-shift root-of-unity formulas | Proved specialization | Classical exact Fourier filter followed by order differentiation. |
| Source Q8 representation target | Resolved in the stated domain | Does not assert generic finite closure or complex-scale cut continuation. |
| Generic finite classical/double-zeta closure | Open here | No positive or negative claim for arbitrary noninteger orders and scales. |
| Arithmetic minimal depth/independence | Not claimed | A functional depth upper bound is not an independence result. |
| Gaussian S6 and revised S8 | Not resolved | Existing canonical status is preserved. |
| Exhaustive review of incoming ZIPs | Not performed | Six listed archives were not opened; see SOURCE_AUDIT.md. |
| Global novelty of every special case | Not claimed | Contribution is relative to the inspected research question; further literature reconciliation is needed. |

## Verification

824 exact finite assertions passed, including two corruption controls.
32 numerical diagnostics passed with recorded per-test tolerances.
Neither set replaces the analytic proofs. Numerical values are not rigorous
interval enclosures. There is no Lean or other proof-assistant formalization.

## Corrections

No counterexample to the inspected integer master was found. The appropriate
upstream change is a scope/status extension, not an invented erratum.
Section 8 documents mathematically essential safeguards: resonant residues,
paired Gamma poles, the even-zeta Gamma factor, inclusive harmonic indexing,
whole-expression continuation, and the distinction between a depth upper
bound and arithmetic minimality.
