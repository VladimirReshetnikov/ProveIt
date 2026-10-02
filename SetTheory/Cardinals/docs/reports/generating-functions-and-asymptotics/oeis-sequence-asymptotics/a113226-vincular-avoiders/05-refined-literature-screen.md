# Focused source and overlap screen

Checked 1 October 2026, approximately 23:05–23:15 UTC. Read-only work; no external repository writes.

## Positive attribution

BCK, European Journal of Combinatorics 126 (2025), 104117, Proposition 7, provides the precise labelled binary word model. Its proof identifies the number of nonempty 0/1 pairs with the number of distinct nonempty strict downsets, and the final 0 block with isolated elements. This is explicit, not an inferred interpretation.

https://arxiv.org/html/2311.08023v2
https://doi.org/10.1016/j.ejc.2024.104117

Their Proposition 11 has other catalytic statistics, lowest ascent top and final entry, and their earlier bivariate functions concern the broader class of 3-free naturally labelled posets with a minimum-count marking. Those are different refinements. The paper contains no distribution theorem for the statistic studied here. Its Section 4 cites refinements of ordinary interval orders/Fishburn structures; those are a different labelling/counting convention, so they do not automatically give the present theorem.

OEIS A113226 still presents the existing pattern-avoidance recurrence and references. It does not display this two-parameter EGF or the refined local large deviations. Elizalde's 2006 Section 5 concerns upper/lower bounds for total 12–34 avoidance rather than this exact marked EGF.

https://oeis.org/A113226
https://math.dartmouth.edu/~sergi/papers/pp05_aam_elizalde.pdf

## ProveIt

The authorized GitHub connector's default-branch code searches returned:

- A113226: no result
- 12-34: no result
- Bevan Cheon Kitaev: no result
- naturally labelled posets: unrelated finite-poset enumeration and ordinal/order-theoretic files, no matching pattern-avoidance/refinement material among the ten returned hits

The connector reported current head 63b9d68407f21832316eb296fd0885e40e033c90, authored 2026-10-01 22:32:47 UTC.

https://github.com/VladimirReshetnikov/ProveIt/commit/63b9d68407f21832316eb296fd0885e40e033c90

This is a keyword/index screen, not a complete scan of archive attachments or every mathematical equivalent in the repository. No new binary archive download was made.

## Public keyword screen

Queries covered A113226 with blocks/asymptotic terms; 12–34 avoiding with bivariate/distribution/Poisson terms; and naturally labelled posets with downsets/limit/distribution terms. The relevant results were BCK, Elizalde, and OEIS. No earlier matching complex-uniform refinement or local large-deviation formula was found. Sparse search hits cannot establish priority.

## Assessment

The Gaussian and Poisson limits by themselves are routine consequences once a sufficiently uniform marked coefficient theorem is proved. An addendum is justified by the exact marking, genuinely complex-uniform all-orders coefficient theorem, marking-phase aperiodicity gap, and all-orders two-stage local large deviations with stretched-saddle corrections. The conditional Poisson law and its explicit n^(-2/3) correction give an additional structural consequence. Phrase all priority claims as a focused search finding, not as exhaustive novelty.
