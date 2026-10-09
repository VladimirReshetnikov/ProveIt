# Theorem ledger

**Article:** *Beyond Geometric Progressions: Supergeometric Sequences and All Infinite Linear Recurrences*  
**Date:** 8 October 2026  
**Main source:** [supergeometric_and_recurrence_avoidance.tex](supergeometric_and_recurrence_avoidance.tex)

This ledger records the mathematical dependency structure and the scope of the novelty claims. LaTeX labels are used because numerical theorem references can change during integration. “New” means added relative to the inspected repository snapshots and primary literature listed in [provenance.json](provenance.json). It does not certify worldwide priority. All proofs are ordinary mathematics; the package has separate AI audits and finite checks, no external referee report, and no new proof-assistant formalization.

## Dependency map

| Input or step | Classification | Used for |
| --- | --- | --- |
| Finite ordered routing tree, independent selector and terminal tables, first-default tests, local grid counting, open repair | Inherited method, with the needed estimates reproduced | Both core extensions |
| **Core A: growing-budget lemma** | New quantitative extension of the inherited method | Fixed sequences with long blocks and growing maximum logarithmic gaps |
| **Core B: uniform signed polynomial block lemma** | New uniform extension of the inherited method | Stable real recurrences including oscillation, zero terms, and collisions |
| Finite full sign-condition bound | Classical Basu–Pollack–Roy input | Core B's uniform parameter count |
| Stable companion families and null-tail reduction | Explicit support arguments using classical linear algebra | Simultaneous recurrence theorem and effectivity |
| Bounded-recurrence torus decomposition | Classical structure, proved here in the required bounded case | Compact avoidance for all infinite-range recurrences |
| Finite-pattern universality and finite-state recurrence argument | Classical elementary facts | Exact classification of recurrent value sets |

## Core A: fitting the routing construction into a finite block

### A1. Growing-budget lemma

**Label:** `lem:growing-budget`  
**Proof:** `sections/03_growing_budgets.tex`  
**Status:** New core lemma relative to the inspected sources.

For fixed $0<p,\mu<1$, consider decreasing positive blocks of length $L$ with upper adjacent ratio at most $\mu$ and largest logarithmic gap $G=o(\log\log L)$. The routing parameters can be chosen with base window $r_1=1$, simultaneously satisfying the local uniform failure bounds and the global span constraint. In particular,

$$
\log\sigma_d=O_{p,\mu}\bigl(\sqrt{\log L}\,\log\log\log L\bigr)=o(\log L),
$$

so the whole tree uses only terms of the given block. The proof makes the branching number grow with $\log\log L$. Its essential point is to account for depth, every descendant window, and every separating gap before applying the bound $G$; no terms beyond the available block are used.

**Inherited inputs:** `prop:finite-blocker`, the exact conditional test identity `lem:conditional-tests`, and the local scale count from `sections/02_finite_routing.tex`. Their role and attribution to the OpenAI finite-routing construction remain explicit.

### A2. Long-block avoidance theorem and prefix criterion

**Labels:** `thm:block-main`, `cor:prefix`  
**Statement:** `sections/01_results_and_sources.tex`  
**Proof:** `sections/03_growing_budgets.tex`  
**Status:** Main theorem and corollary obtained from core A.

A fixed positive null sequence whose values contain blocks $b_{j,1}>\cdots>b_{j,L_j}$ with $L_j\to\infty$, one fixed upper ratio $\mu<1$, and

$$
\max_{k<L_j}\log(b_{j,k}/b_{j,k+1})=o(\log\log L_j)
$$

admits, for every $0<\varepsilon<1$, a closed symmetric 1-periodic avoiding set of measure greater than $1-\varepsilon$ in each unit interval. For every translation, nonzero scale, and original tail, a point of that tail lies outside the set. Consequently each affine pattern has infinitely many distinct omitted values.

For an eventually uniformly contracting positive sequence, the sufficient prefix hypothesis is

$$
\liminf_{N\to\infty}G_N/\log\log N=0,
\qquad G_N=\max_{n_0\le j<N}\log(a_j/a_{j+1}).
$$

The pointwise little-oh gap condition is a further sufficient condition. Finite blocks need not be consecutive original indices; no restriction is imposed on gaps between chosen blocks. The set depends on the fixed sequence. Finite head deletion, scaling the input sequence while keeping blocker period one, and a summable countable assembly supply all scales and all tails.

**Examples, not extra independent core theorems:** `prop:examples`, `eq:rational-example`, and `ex:separated-blocks`. They include the displayed supergeometric exponential examples, an exactly specified dyadic-rational sequence, and widely separated geometric blocks showing the local hypothesis is stronger than the prefix criterion.

### A3. Refined normalized finite budget

**Label:** `thm:optimized`  
**Proof:** `sections/07_quantitative_budget.tex`  
**Status:** Additional quantitative refinement within the routing scheme.

For fixed $p,\tau,\mu\in(0,1)$ and sufficiently large maximum block gap $G$, a block satisfying

$$
\log\log L\ge G/p+C(p,\tau,\mu)G^{3/4}
$$

inside a positive pattern accumulating at zero is enough for a normalized-scale periodic blocker of density at most $p+5\tau$. The proof biases the selectors and shortens the relative descendant span.

**Restriction:** The leading coefficient $1/p$ is approached within the stated exponential-count/complete-tree parameter balance. The argument gives no lower bound for arbitrary avoiding sets, no optimality claim for the main sequence criterion, and no all-scale conclusion from merely avoiding scales in $[1,2]$. In particular, it does not replace the zero liminf hypothesis by a positive constant.

## Core B: signed finite-dimensional families

### B1. Uniform signed polynomial block hitting

**Label:** `sr:lem:block`  
**Proof:** `sections/04_stable_recurrences.tex`  
**Status:** New core lemma relative to the inspected sources.

Let $\Theta\subset\mathbb R^d$ be compact and let the real polynomials $f_n$ have degree at most $A(n+1)^D$, for fixed $A,D\ge1$. For a fixed block length $m$, assume uniformly that

$$
V_n(z)=\max_{0\le i<m}|f_{n+i}(z)|,
\qquad V_0=1,\quad V_{n+1}\ge\alpha V_n,\quad V_n\le C\beta^n,
$$

with $0<\alpha,\beta<1$ and $C\ge1$. For every compact positive dilation band $[u,v]$ and $0<p<1$, an open 1-periodic set of density at most $6p$ meets every translated and dilated parameter sequence at a **nonzero** original value.

No scalar monotonicity, sign restriction, or monotonicity of the block norm is assumed. A first crossing of $V_n$ at each geometric threshold, followed by the least maximizing coordinate, supplies separated signed values. Their original indices are distinct even though their index order need not be increasing.

**Critical new uniformity details:** Threshold signs determine first crossings; squared-coordinate comparisons determine tie-breaking; local grid signs determine every table address. Zero signs are retained. Stability excludes every earlier-grid boundary from a closed symmetric interval around the center. Representatives are chosen before the remaining random entries are exposed. The residual center set is defined using the original continuous polynomials, not the discontinuous selections.

With largest selected level $B$ and local window length $r$, the representative count is bounded by

$$
C_3(B+1)^{(D+2)(d+1)}Q^{-2(d+1)r}.
$$

The polynomial factor may depend on $B$; the exponential factor depends only on the local span. This distinction makes the probability comparison work.

### B2. Stable companion families and simultaneous recurrence avoidance

**Labels:** `sr:lem:matrix-control`, `sr:lem:stable-tail`, `sr:thm:universal`  
**Statement and proof:** `sections/01_results_and_sources.tex`, `sections/04_stable_recurrences.tex`  
**Status:** Main uniform consequence of core B; the matrix inequalities and spectral reductions use classical algebra.

The rational compact sets of companion matrices and norm-one initial states in `sr:eq:Theta` impose a norm bound, determinant bounded away from zero, and contraction of a fixed power. They exhaust every invertible stable real companion matrix. The output polynomials have degree at most $n+1$, and the recurrence representative bound becomes

$$
C_4(B+1)^{3(2m+1)}Q^{-2(2m+1)r}.
$$

Zero roots are removed by passing beyond their finite transient. Shift operators isolate active exponential terms, proving that a null recurrence's remaining active roots all have modulus below one. Countably many compact families and dilation bands yield one closed symmetric 1-periodic set, independent of the recurrence, missing infinitely many distinct points from every affine copy of every convergent recurrence that is not eventually constant.

This answers the oscillatory-recurrence question in the inspected ProveIt report. That report already suggests consecutive state coordinates; the present contribution supplies the signed selection proof, full sign-condition count, compact exhaustion, and all-parameter assembly.

### B3. Effective closedness and computable measure

**Label:** `sr:thm:effective`  
**Proof:** `sections/04_stable_recurrences.tex`  
**Status:** Effective consequence of core B and rational semialgebraic exhaustion.

For rational $0<\varepsilon<1$, the periodic recurrence avoiding set and its compact section may be effectively closed with computable measure. Real quantifier elimination decides each finite rational blocker condition; existence with spare measure budget and compactness ensure a terminating enumeration. A summable tail bound provides the measure modulus.

This is an existence algorithm. The package does not implement it, give a practical running-time bound, or establish a computable distance function or Hausdorff approximation algorithm.

## Classical inputs and acknowledged prior cases

| Item | Exact role and boundary |
| --- | --- |
| OpenAI family 084, pinned October 2026 geometric manuscript | Source of the ordered finite tree, selectors, first-default testing, local address count, and exceptional-center repair. The needed estimates are reproduced; the original theorem is not used as an unexplained black box. |
| ProveIt `uniform-geometric-avoidance`, pinned commit | Already proves simultaneous geometric-ratio and positive-real-root exponential-polynomial avoidance, and a polynomial-family theorem. Singleton families already cover fixed two-sided bounded ratios. First-crossing extraction also makes a fixed positive eventual lower ratio bound an inherited corollary, not a new result here. |
| Basu–Pollack–Roy, arXiv `math/0603256v3`, Section 3.2, equation (3.3) | Supplies a finite bound uniform in polynomial degree and including zero sign conditions. The proof does not substitute a fixed-degree asymptotic when degrees grow. |
| Jordan form, shift annihilators, Cayley–Hamilton | Establish active-root restrictions, transient removal, polynomial output degree, and closure under arithmetic subsequences and affine coordinate maps. |
| Bounded-recurrence torus structure, related to Gerhold (2009) | `ar:lem:bounded` is proved in full using a rational basis, finitely many residue classes, and an elementary Fourier proof of the needed Kronecker density. Only the bounded/unit-root structural step is used. |
| Finite-pattern universality and deterministic finite recurrence states | Translation continuity proves `prop:finite-universal`. Repeated finite states prove finite range is equivalent to eventual periodicity. These facts are not claimed new. |

## Consequences of core B and classical structure

| Result | Label | Precise conclusion |
| --- | --- | --- |
| All infinite-range real recurrences | `ar:thm:all` | One compact nowhere dense $K\subset[0,1]$, of measure greater than $1-\varepsilon$, omits infinitely many distinct points from every affine copy of every real constant-coefficient recurrence with infinite range. No spectral or convergence restriction. |
| Classification of recurrent value sets | `cor:classification` | Measure universal range if and only if finite range if and only if eventual periodicity. One compact set witnesses all the infinite cases simultaneously. |
| Matrix-orbit images | `cor:vector` | For each $d$, one compact $K_d\subset[0,1]^d$ of arbitrarily large measure omits infinitely many points from every translated infinite image $\{AT^nv\}$, independently of the matrix dimension and parameters. |
| Joint countable avoidance | Final subsection of `sections/05_consequences_and_limits.tex` | One compact set can avoid all infinite-range recurrences together with any prescribed countable list satisfying core A's sequence hypothesis. |

These are valid further results, but their proofs are consequences rather than separate new routing mechanisms. In the all-recurrence proof, unbounded patterns are handled by compactness. A bounded pattern either has a nondegenerate interval of tail limits, impossible in a closed nowhere dense set, or has a nonconstant convergent recurrence residue subsequence to which `sr:thm:universal` applies.

## Limitations that must survive integration

1. The all-recurrence conclusion is for the compact section, not the full periodic set. A nonempty periodic set contains a translated integer progression.
2. Infinite range is essential. Finite patterns occur inside every measurable positive-measure set after suitable nonzero affine scaling.
3. Core A is a fixed-sequence result and uses maximal finite-block gaps with one fixed upper ratio. It is not an arbitrary-average-gap theorem or a simultaneous result for every sequence in an uncountable class.
4. The supergeometric examples do not cover all ratios tending to zero. In particular, $e^{-n^2}$ and $1/n!$ fail the required long-block gap bound; $e^{-n\log\log n}$ also falls outside the displayed little-oh criterion.
5. The refined normalized budget is not an unrestricted optimality theorem and does not prove all-scale nonuniversality from a fixed positive normalized-scale measure budget.
6. The effective theorem gives no practical full blocker construction and no computable distance function. Its rational search is distinct from the finite Python checks.
7. Separate AI audits and finite experiments are not external refereeing or formal proof verification. The continuum of parameters and the infinite assembly are justified by the written proof.
8. Source comparison is pinned and limited. No general Erdős similarity solution, absolute priority certificate, or original authorship of the inherited routing scheme is asserted.

## Computational evidence

`make check` runs three Python standard-library scripts. The supplied recurrence report contains 12,266 exact rational/integer checks over seven cases, and the budget/examples report contains 60,982 exact checks. The routing report includes complete finite probability enumerations, deliberately failing independence predictions under collisions or exposed gates, exact signed boundary cases, and integer tree spans. Its large logarithmic-budget calculations are explicitly labelled floating-point sanity checks.

The scripts exercise mechanisms that could otherwise hide mistakes: conditioning order, fresh versus reused addresses, zero signs, endpoint conventions, first-crossing ties, repeated and nonreal roots, disappearing zero-root modes, and original-index distinctness. They do not enumerate the continuum of real recurrences, execute the astronomical complete tree from the asymptotic proof, implement the universal blocker search, or certify novelty.
