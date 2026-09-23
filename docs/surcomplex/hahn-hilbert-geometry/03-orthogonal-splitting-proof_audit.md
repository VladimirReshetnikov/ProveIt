# Proof-audit ledger

This is an internal review ledger accompanying an unrefereed research manuscript.
It records which delicate steps were checked; it is not an independent referee
report or a formal-verification certificate. The PDF and TeX contain the proofs.

## Standing mathematical choices

The ordinary coefficient spaces H and G are set-sized real or complex Hilbert
spaces. The main scalar field is R((t^Gamma)) or C((t^Gamma)); Gamma is an arbitrary
nonzero set-sized ordered abelian group. Strong summation requires a well-ordered
union of supports and finitely many nonzero contributions per exponent.

The class extension in Section 12 is explicitly separate: H and G remain sets,
scalar exponents can be all surreal numbers, and each vector and operator code
still has set support. Class replacement is invoked in NBG class theory.

## Main theorem ledger

| Result | Delicate step checked | Dependency / limitation |
|---|---|---|
| Proposition 3.1, positive norm | The least squared-norm coefficient is positive at twice the vector valuation; the needed square root is a binomial unit times a monomial. | Does not require roots of arbitrary positive Hahn scalars. The basic construction is repository background. |
| Theorem 3.3, spherical completeness | A descending sequence in the assembled support would lie in one ball center's fixed truncation. | Set-sized balls and group; no claim about arbitrary class-indexed families. |
| Theorem 5.1, automatic adjoints | Closed graph makes each ordinary coefficient map bounded; Baire gives a common well-ordered support; testing constants identifies the whole map. | Existing repository theorem, restated in rectangular form. Both maps are everywhere defined. |
| Lemma 6.3, integral projections | A nonzero self-adjoint leading coefficient cannot square to zero, so idempotence forces valuation zero. | Ordinary coefficient positivity is essential to this argument. |
| Theorem 6.5, normal form | Direct-rotation identities W*W=WW*=D and WP0=PW; positive-support inverse square root; residue uniquely determines the ordinary subspace. | Rotation formula is classical. Near-identity unitaries representing a subspace need not be unique. |
| Proposition 7.1, graph criterion | Nearest-point orthogonality gives (I+A*A)x=f. A bijective self-adjoint inverse is itself self-adjoint algebraically. | Does not import a general Hahn bounded-inverse theorem. |
| Theorem 7.2, amplification threshold | For Tx=b y with integral x,y and v(b)=eta>0, coefficients 0 and eta give x0 in ker T and y0 in ran T. Conversely (k+b u,T u) realizes every residue pair. | Scalar multiplier a is infinite in the necessary direction; T is an ordinary bounded map. |
| Example 7.4, no nearest point | The leading coefficient required by (q^2+T^2)x=q^2 h would be (n), which is not in ell^2. | Proves no attained minimum, not a statement about the existence of an infimum. |
| Theorem 8.2, no lattice | Both large subspaces are split graphs/constant summands; the intersection has nonclosed ordinary residue. Every line in it is a split lower bound. | The last line argument is needed to prove no meet in the split poset, rather than merely failure of closure under intersections. |
| Theorem 9.1, Schur reduction | Explicit LAR=diag(B,S), with L,R and inverses integral; B inverse uses a positive-order Neumann series. | Ordinary Fredholm residue supplies finite-dimensional N and C and an invertible regular block. |
| Theorem 10.1, Moore–Penrose existence | Exact range identity ran A=(ker A*)^perp follows through the Schur factors; finite codimension alone is not used as a substitute. | Orthogonal finite-dimensional geometry handles S, ker A and ker A*. |
| Theorem 11.2, exact inverse valuation | Integral equivalences preserve operator valuation. Compression by projections gives one bound; a forced inverse diagonal pivot gives the reverse bound. | Rank-zero and zero-operator edge cases are stated separately. No general infinite-dimensional singular-value theorem is used. |
| Theorem 12.2, full-class descent | The image of the set of constant vectors is a set by class replacement; hence the union of its supports is a set before applying Baire. | Do not silently apply a set theorem with a proper-class value group. Each actual calculation is reduced to a set-sized subgroup. |
| Proposition 12.3, fine nets | A set of nonzero difference valuations has a surreal strict upper bound. A sufficiently small fine radius forces the tail to be constant. | Not a statement about arbitrary class-indexed nets, and not the intrinsic workspace topology. |

## Edge cases and distinctions

All zero blocks are allowed in the Fredholm formulas. If S=0 and T0 is nonzero,
the inverse is integral with residue T0-dagger. If S=T0=0, then A=0. Finite
coefficient dimension has the full algebraic subspace lattice. The infinite-
dimensional failure needs a nontrivial scale group.

The real form of the theorems uses transpose instead of complex adjoint.
Finite Gram–Schmidt only takes square roots already known to exist as vector
norms. Neither a real-closed scalar field nor a divisible group is assumed.

Set-sized scalar enlargement preserves the constructed operator identities even
when the original group is not cofinal in the larger one. No claim is made that
topological completions commute with such enlargement.

## What was actually executed

`checks.py` passed all 16 named finite checks. The Penrose test uses a genuinely
complex rational rank-two matrix; the direct-rotation test includes its q^8
binomial jet. The pole example is exact, and 125 positive integer exponent
triples satisfy the triangular inverse-valuation formula.

The PDF was compiled with pdfLaTeX via latexmk. All references and citations
resolved; there were no overfull-box or LaTeX-error diagnostics. Rendered pages
were visually reviewed, including the main formula pages and final appendices.

## What was not executed or certified

No Lean formalization, independent proof checker, external peer review, exhaustive
bibliographic search, or exhaustive audit of unintegrated repository manuscripts
was performed. Finite symbolic checks cannot validate Baire category, class
replacement, or arbitrary-rank support arguments. The novelty assessments remain
qualified candidates, and the mathematics remains subject to independent review.
