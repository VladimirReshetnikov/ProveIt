# Exact Potts Jones filters

This research extension adds opt-in Jones obstruction backends to the
8 October 2026 ProveIt snapshot. The existing matching backend remains the
default.

## Commands

From this directory:

    python -m fastunknot jones examples/conway.json --backend potts-exact
    python -m fastunknot recognize examples/conway.json --jones-backend potts-exact-factorized
    python -m fastunknot jones examples/conway.json --backend potts-exact --potts-colors 7

The exact backends default to six colors. They compute with integer pairs
in Z[x]/(x² − (q−2)x + 1), with no floating point. The factored version keeps
separate tensors for connected components of the processed Tait graph and
joins their color orbits only when an edge connects them.

An unequal Jones value proves KNOTTED. Equality is INCONCLUSIVE and the
recognizer retains its existing fallback. Local filter budget exhaustion
also remains inconclusive; a global resource limit gives UNKNOWN.
The standalone Jones command exits 3 on a resource limit, 2 on invalid
input/options, and 0 on a completed computation.

## Available Jones backend selectors

| Selector | Description |
|---|---|
| matching | Existing modular matching transfer; unchanged default. |
| potts5 | Modular five-color equality-pattern transfer. |
| potts-exact | Exact quadratic one-tensor transfer, q=6 by default. |
| potts-exact-factorized | Exact quadratic transfer factored over processed components, q=6 by default. |

Use --jones-backend with recognize and --backend with jones. The existing
--backend on recognize still selects a Khovanov implementation.
The recognize flags --jones-max-states and --jones-max-transitions bound
local filter work. The jones command uses --max-states and --max-transitions.
State budgets count represented keys, not total process memory.

## Mathematical guarantees and limitations

For any crossing order of a validated connected plane knot diagram,
2f ≤ w, where f counts active vertices of either fixed Tait graph and w
counts cut diagram edges. Equality patterns have at most q^f states.
The one-tensor algorithm therefore has poly(n,w) q^(w/2) complexity for
fixed q. Exact coefficient lengths are O(n log q) bits.

The factored algorithm has poly(n,g) q! q^(g+2) arithmetic work, where g is
the largest active frontier of one processed component. Its aggregate
color-orbit divisions are exact integer divisions checked coordinatewise.

These are bounds for a scalar filter. They do not establish a complete
quasi-polynomial unknot recognizer or guarantee small width on every input.
The classical Potts/Jones correspondence and bounded-width algorithms have
substantial prior literature; see the accompanying research article.

Five colors have a proved infinite blind family:
closure((sigma1 sigma2^-1)^m) for odd m≥5 with 3 not dividing m.
Its exact q=5 Jones value is 1. Every exact q≥6 detects every nontrivial
knot in that weaving family. Equality at q=6 is still inconclusive in
general.

## Evidence and APIs

Raw evaluators return integer pairs and exact counters:

    from fastunknot.potts_exact import potts_exact
    from fastunknot.potts_factorized_exact import factorized_potts_exact

Both accept colors, order, shade, max_states, max_transitions, and check.
Obstruction wrappers return None on equality. Otherwise their JSON-safe
evidence uses partition_function_hex and unknot_partition_hex, each a
two-element list of canonical signed hexadecimal strings. This avoids
Python's decimal digit ceiling on long narrow inputs.

The research package includes a q=6 certificate replayer, a separate
full-smoothing Jones oracle, raw benchmarks, and a detailed article.
The replayer recomputes the selected exact backend and is explicitly not
an independent algorithm or a signature verifier.

## Validation and measured scope

The integrated suite passed 172 tests. Independent cube enumeration checked
4,464 cases per exact backend over q=5,6,7, two shadings, and three orders;
the expected values were constructed independently of Tait graphs.

The 29-input kernel benchmark includes gains and regressions. On one fixed
poor order, factorization reduced exact q=6 peak keys from 4,111 to 205
and transitions from 30,197 to 1,558. Its median speed ratio against the
one-tensor exact backend was 23.843 on that input. Several other orders favor
the existing matching backend. A separate normal-pipeline run supports no
overall speedup claim. Keep the new backends opt-in pending broader evidence.
