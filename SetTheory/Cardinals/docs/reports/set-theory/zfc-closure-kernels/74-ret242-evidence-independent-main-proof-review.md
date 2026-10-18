# Independent ordinary review of the 242-state reduction

Date: 18 October 2026.

## Verdict and scope

**PASS: no mandatory mathematical correction identified.** This is an
independent ordinary mathematical review of the new 243-to-242 reduction,
not a proof-assistant certificate or a new kernel-checked consistency endpoint.

The reviewer read Sections 1–6 of the main report, the local audit in its
research working version `research/verify_borrowed_return.py`, the exact
delivered transition tables and renumbering, and the pinned combined243
README. The new reduction and main report were authored by other members of
the research team. The reviewer separately authored the optional semantic
extensions, which are not part of this independent main-proof review.

A separate read-only parser checked the table facts below without importing
the supplied audit. The review did not repeat the 8,390-case regression or
the expanded symbolic replay, and it did not independently reconstruct the
full inherited consistency calibration.

## Exact artifact checks

The reference table agrees byte for byte with ProveIt commit
`e58338db7545909907e07a7603e8eb88625c527a`'s inherited combined243 table.

| Artifact | SHA256 |
| --- | --- |
| Inherited combined243 baseline | `4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300` |
| New table in inherited labels | `6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0` |
| New canonical table | `64ddeb2c01c3e9c7feffaffaad87266a270716c9307892a0445bf869b988984d` |

The only removed row keys are `(15,0)` and `(15,1)`. The only changed
retained keys are `(11,0)` and `(27,1)`, with exactly the actions stated in
the report. The complete incoming-edge inventories for states 15, 18, 47,
65, and 27 agree with the report. The new table has 242 working states and
484 total binary transitions, and its only target outside the working
states is the separate halt state. Every write is binary and every move
is left or right.

The canonical table is exactly the stated bijective renumbering. Its
working states are 0 through 241, initial state is 0, dispatcher is 86,
and halt target is 242. Both directions of the mapping were checked.

## Mathematical obligations checked

The old-side invariant

\[
q\in\{18,47,65\}\Rightarrow T(h-1)=0,
\qquad q=27\Rightarrow T(h)=0
\]

is inductive for arbitrary binary function tapes. Entering a protected
state writes zero immediately left of the new head. Entering state 27
moves left from a protected state, onto that known zero. The invariant is
vacuous at the shared start 95 and at dispatcher 96. Its proof uses the
actual combined243 incoming rows, so it does not silently assume the
predecessor's other patches are absent.

Each exceptional block reads only the two stated cells. The two zero
cells remain zero in the four-step detour; the one branch preserves its
two input cells in two steps. Both blocks preserve the entire tape and
finish with the stated head position, at state 21 or 22. No blank
background, finite-support condition, or register-layout premise is
needed, and no exceptional interior state is halting.

The two transition edits are handled simultaneously. The invariant is
required on the old side at comparison checkpoints. The new machine's
permitted entry to `(27,1)` is inside an exceptional block, and the
comparison resumes only after equality of the entire configuration has
been restored. Thus the new use of the formerly unreachable row creates
no gap in the simulation argument.

The ordinary-row classification excludes the only incoming edge to
deleted state 15 and the impossible old row `(27,1)`. All remaining rows
have identical actions. Both machines' comparison blocks have strictly
positive bounded durations. This yields both directions of halting
equivalence and rules out halting inside an uncompleted exceptional
block. Exact clock accounting is valid: if the old halting computation
uses `k` exceptional zero blocks in `t` transitions, the new time is
`t + 2*k`, and `2*k <= t` gives the bound `t <= t' <= 2*t`.

## Consistency dependency and limits

The requested ZFC theorem follows by composing the new ordinary relative
theorem with the pinned baseline's documented ordinary consistency
calibration. The latter is an explicit dependency of the contribution,
not a result inferred from execution tests. This review accepts that
dependency at its stated ordinary-proof scope and does not independently
reprove its proof enumerator, source, set-theory calibration, runtime,
and initialization chain.

The report distinguishes the inherited relative Lean theorem from the
still-uncompleted exact combined243 Lean consistency endpoint. It does
not transfer the different compensated244 table's endpoint, claim an
internal PA development, infer unconditional nonhalting, or assert
two-sided independence from bare consistency. No new Lean or Rocq
endpoint was produced or checked in this review.

The positive verdict concerns the exact tables and mathematical argument
specified above. Final ZIP assembly, document rendering, and the claimed
large execution totals are separate delivery checks.
