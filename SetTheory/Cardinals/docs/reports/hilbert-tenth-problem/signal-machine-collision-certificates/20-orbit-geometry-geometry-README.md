# Sparse-orbit geometry: exploratory successor packet

Status: derived corollary with explicit weighted-alphabet sharpness examples and finite arithmetic/local-rule audits; 3 October 2026. No claim of novelty, reversibility, binary rank-two sharpness, or changes to earlier releases.

## Main conclusions

- In the stationary-unit frame, every fixed mass-at-most-four orbit visits an effective semilinear set within finite width of a rational plane of rank at most two
- Centered-box distinct-site counts are effectively eventually quasipolynomial, with sharp possible degrees 0, 1 and 2; multibox counts are piecewise quasipolynomial
- In an expanding shuttle, the count degree is exactly rank(E,ν), and rank-two tails lie in a bounded-width pointed rational sector
- Complete-cycle counts are quasipolynomial; ordinary-time distinct-site counts grow as √T+O(1) or linearly with O(√T) error
- First-visit times are piecewise rational quadratic on effective semilinear cells, with quadratic radius-to-first-visit growth in expanding tails
- Restoring δt can destroy both site semilinearity and box quasipolynomiality, and can require rank-three containment
- An explicit conservative four-symbol CA realizes the exact wedge {(x,y):y≥0,0≤x≤k+y}; the same CA followed by a vertical shift has exact floor-root box counts 3N−3√N+O(1)

## Files

- `PROOF.md`: full theorem, proofs, explicit radius-6 CA construction, exact examples and source notes
- `counting-review.md`: independent detailed check of the counting and inversion consequences; the main proof selects the most relevant subset
- `audit.py`: executable sparse simulator, cellwise evaluation strategy using the same action predicates, and arithmetic checks
- `audit-results.json`, `audit-results-optimized.json`: byte-identical typed receipts from ordinary and optimized Python runs
- `MANIFEST.sha256`: file integrity hashes

Run audits with `python audit.py` or `python -O audit.py`. Explicit `RuntimeError` checks remain active under optimization. The cellwise comparison reuses the action predicate and is an evaluation-strategy/locality check, not a separately reimplemented local rule. They cover malformed configurations, locality agreement, cycle clocks, exact stationary-frame wedge counts and original-frame floor-root counts. These are finite tests; unrestricted conservation is proved by disjoint write supports in PROOF.md.

Primary contextual sources were checked directly: Woods (2015), Lacalle–Gajardo (2014 preprint), and Blum–Sakoda (1977). The central Delorme–Mazoyer (2002) article was not obtained in full. The close two-pebble geometry is acknowledged explicitly, and no literature-search result is treated as a priority proof.
