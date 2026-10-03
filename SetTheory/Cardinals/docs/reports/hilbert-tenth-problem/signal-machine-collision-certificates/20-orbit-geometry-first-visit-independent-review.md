# Independent review of the canonical first-visit compiler

Reviewed 3 October 2026. Reviewed `PROOF.md` SHA-256: `5835adeab6118bbed16bca1dbae480b122d2fddf53f7073a6efdd9f31f7542ad`.

**Verdict: passed. No mathematical defect or unresolved issue was found in the reviewed proof.** This is an independent argument audit, not a new audit of the underlying CA classification or an assertion that numerical tests prove the theorem.

## Passed arguments

1. **Disjoint spatial clauses.** Effective Presburger elimination followed by complete sign and residue outcomes yields genuinely disjoint conjunctions of integer affine inequalities, equalities, and fixed-modulus congruences. Strict signs are correctly converted using a unit offset. Assigning an overlapping original cover's least cell preserves the specified function. No uniqueness of semilinear generator coefficients is assumed. The stated bounds `B ≤ 3^a ∏m_k`, `I+H=aB`, and `C=cB` hold for the full-outcome clauses before redundant atoms are removed.

2. **Canonical membership witnesses.** Natural selectors summing to one select exactly one branch. An active inequality fixes its nonnegative slack. Each congruence fixes an integer quotient, and the product-zero condition gives its unique signed natural pair. Inactive slacks vanish; inactive quotient pairs have equal entries and product zero, hence both entries vanish. Disjointness determines the selector. All residuals have total degree at most two, counting external coordinates, so their squared sum has degree at most four.

3. **Time output without higher degree.** The shared square lifts have a unique natural value for every signed integer site. Polarization correctly expresses every quadratic cell polynomial as an affine expression in the site and lift variables. The common denominator explicitly clears polarization halves. The pooled time residual has degree at most two, enforces precisely the selected cell's value, and leaves no inactive auxiliaries free. Internalizing time adds one uniquely determined natural witness.

4. **First-arrival selection.** The expanding-tail argument correctly removes prefix-visited sites and selects the lexicographically least cycle and offset in a Presburger relation before applying the quadratic clock. The graph-generator proof of piecewise rational affineness is valid, including multiple output coordinates and extension from a proper rational input subspace. Affine/periodic/independent tails admit direct Presburger earliest-time selection, including stationary rays and repeated visits.

## Exact counts and conventions

For nonempty branch lists, with `I,H,C` counting atom occurrences in the final clauses:

- Membership: `W = B+I+2C`, `R = 1+I+H+2C`
- External time: `W = B+I+2C+M`, `R = 2+I+H+2C+M`
- Internal time: add one witness to the preceding count; residual count unchanged
- The universal square-lift choice is `M=d(d+1)/2`; affine timing permits `M=0`
- All-natural canonical external site encoding adds `d` residual slots and no witnesses

These are literal residual-slot counts before omitting identities. Empty sets are separately and correctly handled by `P=1` with no witnesses. The zero-dimensional conventions are sound. Naturals include zero, and the original theorem quantifies natural witnesses while allowing signed integer external sites. The degree bound is at most four, not necessarily exactly four.

## Hypotheses and scope

The algebraic theorem requires effective Presburger domain data and, for a time output, an effective finite semilinear cover carrying a specified nonnegative integer-valued function represented by rational polynomials of degree at most two. Integrality is needed on the assigned cells only.

The dynamical application remains conditional on the reviewed fixed-CA, fixed-input orbit normal form and actual affine phase-time data. Its cycle starts must be genuine increasing chronological boundaries, with offsets in the stated half-open cycles; those requirements are inherent in the normal-form use of cycles. The clock measures actual elapsed time.

The proof correctly limits the expanding-tail application to stationary-frame sites. It expressly rejects deriving original-frame first visits by substituting into a stationary first-visit certificate. Affine-tail frame restoration remains valid. No arbitrary decidable-set single-fold theorem, generic MRDP strengthening, real/rational-witness assertion, efficiency bound, or novelty claim follows or is claimed.

Only this review file was written; the reviewed proof and all predecessor folders were left unchanged.

## Addendum: final shared-cycle specialization and application theorem

Reviewed 3 October 2026. This addendum pins the final `PROOF.md` SHA-256 `131cbed81e731e3fd4f345060625d1b4c1299f496f0667989a1813d28cd6860b`, including the application theorem at the start and new §6.4. This final pin supersedes the earlier proof-version pin; the preceding general-compiler review remains valid.

**Verdict: passed, with no new issue.** Retaining the selected affine data `n_i=n_*` and `k_i=T_0+h_*` gives the same common quadratic clock `τ=c n_i²+b n_i+k_i` on every tail cell. Prefix first-visit cells correctly use `n_i=0` and their actual first time as `k_i`, so the same identity holds without a special clock gate.

With independently chosen positive denominators `A,D`, the residuals

    A N − Σ_i e_i a_i(y),
    D t − Dc N² − Db N − Σ_i e_i K_i(y)

are integer polynomials of total degree at most two. The first determines the unique natural `N=n_i(y)` from the unique active cell; the second then determines precisely the first-arrival time. Negative `b` or signed affine coefficients cause no problem. The common branch refinement retains the necessary affine data, and no branch-private clock witness is introduced. Squaring and adding these residuals therefore preserves both ordinary degree at most four and singleton natural witness fibers.

The sharpened nonempty-domain counts are exactly:

- External expanding first time: `W=B+I+2C+1`, `R=3+I+H+2C`
- Internal expanding first time: `W=B+I+2C+2`, with the same residual count

The initial application theorem correctly distinguishes these counts from the affine-tail construction and from the general piecewise-quadratic square-lift construction. Only the additional clock-witness overhead is dimension-independent; the full arity is still dependent on the fixed input and final clauses. Empty-set and stationary-frame restrictions remain intact. No changes to the proof or any other file were made during this addendum review.

## Addendum: fixed observation schemas, final version pin

Reviewed 3 October 2026. The final reviewed `PROOF.md`, now including §6.5, has SHA-256 `3247951ca7afa4d65bd3eb90d99bfb48fcb43dbf0eaa067c3e9380cdfbcebbda`. This supersedes both earlier version pins.

**Verdict: passed.** Section 6.5 correctly extends the construction to a fixed, time-independent Presburger predicate of an external finite tuple and the full stationary-frame labeled configuration. Under the assumed complete phase description, substituting the phase's finite labeled coordinate list and quantifying phase parameters produces a Presburger occurrence relation. The mass bound permits a fixed finite configuration encoding; lexicographic ordering, distinct occupied sites, fixed finite label codes, and zero padding are Presburger constraints.

The prefix correction is essential and is handled correctly: each fixed prefix time may satisfy infinitely many external tuples. Subtracting all earlier prefix predicates gives disjoint Presburger first-hit domains; excluding their union before tail minimization prevents later hits from replacing prefix first hits. These domains carry `n_i=0,k_i=t`, so the same shared-clock identity and witness/residual counts continue to hold after the effective common refinement. The certificate has a unique natural **witness tuple**, rather than asserting that its full auxiliary arity is one.

Complete canonical configuration targets satisfy the interface. Fixed finite pattern anchors also satisfy it: zero entries use absence of every occupied support site at the requested offset. The all-zero-pattern example correctly rules out transferring the site's quadratic-distance growth conclusion. This extension does not assert an arbitrary absolute-time predicate interface, an unbounded externally encoded pattern interface, or a general original-frame expanding-tail result. No issue was found, and only this review file was changed.
