# Separate review and native matrix probe, 12 October 2026

The placement commit preserved the delivery without executing it. This later
algorithm-improvement review ran the 52 delivered unit tests on a temporary
copy; all passed in 0.491 seconds. The originals remain unchanged. The
standalone exhaustive audit and timing experiments have not been rerun.

The ordered-state proof was checked at its principal transitions: a matched
edge reverses row-to-column orientation, matching flags prevent reused
endpoints, and equal boundary total orders admit an amalgamated topological
order at a join. Feasible-plan replay remains weaker than an optimum proof.
The complete compressed-power checker has not undergone a native review.

A separate source adapter inspected all 120 native corpus cores. It compared
source geometry against the independent reference reconstruction and
independently replayed each fixed maximum-weight top reduction. It then
optimized the raw matrix on all original lower columns, before choosing a
lower forest. No production module or checker was patched by this probe.

118 cores peel completely without any DP. The remaining two have residual
incidence decompositions of heuristic widths 4 and 3. Their optimal unit-cost
deferral is exactly one row each, confirmed by an independent direct
column-sum subset oracle. The optimizer selects source row 24 for
`nested_1_4_6/interior_links` and row 0 for
`interior_loop/interior_links`. Their peaks are 3,840 and 132 DP states.
The source-specific optimum follows from the independent oracle; the
heuristic widths are validated upper bounds, not minimum-width claims.

This is a native-source matrix plan, not executed geometric cancellation.
The deferred two-handle remains real. No passive attaching curve or protected
boundary data has been transported, and no new handlebody or unknot verdict
follows. The concrete next problem is authenticated geometric handling of
that remaining row and of the full annular interface. A faster matrix
optimizer alone does not resolve it.

Evidence: `synthesis/data/gap-prefix-pivot-width-probe.{py,json,txt}` and
`synthesis/data/gap-prefix-report110-tests.txt`. The driver records runtime
and delivered-module pins, source labels, top proofs, plans, width limits,
and the independently checked nonzero optima.
