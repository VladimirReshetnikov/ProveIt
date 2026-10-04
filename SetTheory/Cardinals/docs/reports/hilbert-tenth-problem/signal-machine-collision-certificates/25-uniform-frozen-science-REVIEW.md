# Independent structural review: uniform four-mass charts

4 October 2026. Reviewed `PROOF-NOTE.md` and the specified source-17/source-18 passages in the pinned inherited article. Final proof-note SHA-256: `2e6484f4a2dbc0419e9662bf1ca02d4154469a1f4dcf93f4320f9951c9124962`. The final reread confirmed the requested radius/no-unit and congruence-pullback clarifications, together with the scoped review status, reported arithmetic-check summary, and fixed-output-label-case or tagged/padded-output convention for the quartic; these do not change the accepted theorem's scope. No upstream code was executed. This review concerns the mathematical reduction and arithmetic interface, not a new CA construction, an implemented rule compiler, or publication priority.

## Verdict

**PASS, conditional on the imported finite section mechanism and fixed-input chart theorem, for the precisely stated residue-cell/quotient-lift version.** I found no remaining nonlinear domain guard, hidden third free evolution parameter, or unbounded input-dependent stage in the argument. This does not validate a stronger claim of two total auxiliary variables with purely affine domains over unrestricted raw input coordinates.

The essential repair is explicit: input residue restrictions are allowed, or are represented by at most three uniquely determined gap quotients. The two-parameter bound then concerns free evolution parameters. Bijectivity is fiberwise in the fixed initial configuration, as required; a global bijection to `(time, final configuration)` alone would be wrong for a noninjective CA.

## Checks of the main proof

1. **Uniform contact selection.** In a fixed periodic phase, a site-pair contact is an interval condition `-2S <= A(x)+d k <= 2S` with fixed integer drift `d`. Its earliest natural solution is an affine expression after a fixed congruence refinement and a disjoint maximum-at-zero split. Validity of that candidate, and comparison of finitely many candidate times, use affine tests. Fixed transient times are finite extra cases. Actual occupied-site tests, now used in the note, are important: a compact mass-three phase can have holes, so its expanded hull alone is not an exact contact test. Contact-time ownership passes because independently evolved components are still disjoint at the first contact time.

2. **Initial dispatch.** The component partitions exhaust mass four. Each connected component has a uniformly bounded normalized shape. Initial `2+2` or `2+1+1` evolution contributes at most one unbounded first-contact flight, followed by a fixed seed resolution and possibly one compact flight. A compact mass-three object either escapes or enters a bounded complete encounter; it cannot carry a second unbounded control gap through an ordinary reset. Entry time, stationary-frame anchor and live gap are therefore affine on the refined input cells.

3. **Complete guarded cycle count.** Put `Delta=-a<0` and `b=min_{0<=s<=m} c_s`, including `c_m=Delta`. Cycle `n` is wholly live exactly when `a n<d+b-N`. Consequently

   `K=max(0,ceil((d+b-N)/a))`

   is exactly the number of completed cycles. This handles `K=0`, exact divisibility and strict threshold equality correctly. If `K>0`, the endpoint guard of the last completed cycle proves that the cycle-`K` start is still live. If `K=0`, this follows from the entry assumption `d>N`. The first failed endpoint is therefore one of `1,...,m`, not an already-invalid start. Omitting the last endpoint or any interior endpoint would invalidate this argument; the note includes both.

4. **Reset data.** On a residue/sign cell, `K` is affine. The first failed edge starts with gap greater than `N` and ends with gap at most `N` after a fixed additive decrement. Thus its endpoint gap belongs to a fixed finite set. The whole endpoint launch is ordinary, with finitely many normalized shapes. Its anchor `l+K E+constant` is affine. Refining the residue and failure-prefix cases fixes the normalized shape; no hidden input-dependent geometry survives.

5. **Clock degree.** Summing complete-cycle durations gives

   `n(A d+B)+A Delta n(n-1)/2`.

   Adding the finite edge prefix gives the note's `S_s(n)`. These expressions have total degree at most two jointly in initial coordinates and evolution parameters. Substituting affine `K(x)` also has degree at most two. The correct contracting domain is `n<K(x)`, which is affine; testing `t<Q(x)` as a new domain guard would instead introduce an unnecessary quadratic guard. The note uses the former.

6. **Zero-net cycles.** A cycle with `Delta=0` can have period `A d+B` depending on the input. It is correctly retained as a cycle/flight chart with two parameters and the bilinear term `n d`, rather than incorrectly treated as a fixed-period uniform one-clock tail.

7. **Composition and uniqueness.** After the first ordinary reset, all later dynamics comes from one of finitely many fixed-input normalized templates. The substitution is additive: `Q(x)+t_o(z)` and `a(x)+v_o(z)`. It is not composition of two quadratic clocks, so there is no degree multiplication. Half-open stage boundaries, the first failed endpoint, Euclidean phase quotients and strict affine sorting give exactly one chart point per time for each input. A potentially enormous template prefix is rule-dependent finite data and does not reintroduce input-dependent materialization.

8. **No-unit case.** This also has a direct elementary justification. When every nonzero weight is at least two, an isolated symbol of weight two or three cannot split and has finite label/displacement control. A mass-at-most-four input has at most two occupied sites; the two-site case is `2+2`. Its first encounter is covered by the contact lemma, and every bounded encounter belongs to a finite normalized core. Exiting that core starts two finite-phase walkers, whose fixed-input excursion either terminates independently or returns to the finite core. Thus the separate no-unit treatment needs no shuttle counter. The final proof note includes this finite-core argument and explicitly defines its geometric radius parameter as `S=max(1,R)`.

## Arithmetic interface and consequences

The final proof note explicitly implements the correct congruence pullback: on the existing integrality cell, `(a dot g+c)/d = rho mod M` becomes `a dot g+c = d rho mod dM`. It then chooses `H` as a common multiple of the pulled-back moduli `dM`. This correctly clears denominators **inside each congruence**, rather than merely taking the least common multiple of the denominator and original modulus separately. For example, `(D/2) mod 2` requires information modulo four in `D`. The earlier exposition request is resolved.

The canonical gap quotient equation `g_i=H u_i+r_i` gives exactly one natural `u_i` for each chosen residue and ordered input. It consumes at most `m-1` input-determined variables and creates no duplicate witnesses. All remaining guards are affine after clearing positive denominators. Removing time therefore does give a uniform Presburger relation for stationary-frame complete configurations. Fixed finite-pattern queries, including required vacancies, follow by finite Presburger constructions.

The updated quartic paragraph includes a necessary repair absent from a naive direct application of source 18: external quadratic input terms must not be multiplied by the chart selector. The private natural copies `X_hi^+-e_h x_i^+=0` and `X_hi^--e_h x_i^-=0` are quadratic residuals; using only private variables in chart polynomials restores the source-18 constant-term lift. Copies are uniquely fixed on the active chart and zero on inactive charts. All residuals remain degree at most two, including canonical signed-pair tests, so their squared sum has degree at most four. This supports a finite-arity consequence with the additional copies and slacks counted; it does not support a two-total-witness claim or an optimized arity claim.

## Scope left open

- The dynamical source-17 hypotheses and source-18 fixed-input templates remain imported; this is not a fresh independent proof of those results
- No general rule-to-chart compiler has been implemented or formally verified here
- Finite arithmetic tests can check formulas but cannot establish the all-rules theorem
- Literal two-total-variable affine-domain charts over raw input coordinates are neither proved nor refuted by this review
- External published novelty and priority are unverified
