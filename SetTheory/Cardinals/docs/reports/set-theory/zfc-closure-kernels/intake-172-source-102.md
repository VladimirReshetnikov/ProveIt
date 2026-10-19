# Source 102: delayed erasure, the same 239-state machine found independently

Package `ZFC239_Companion_2026-10-19.zip` (arrival `83fd358548`, placement
`07194e5b4d`, prefix `102-delay239-`). Pinned to ProveIt
`13ec39ed43148b1807f51ed6e6528e1c84659562`. The main report, its PDF and the delivery
README are archive-only. Members are mapped in [the placement map](data/intake172-placement.json).

## The machine is Source 101's

Its canonical and inherited tables are **byte-identical** to
[Source 101](intake-172-source-101.md)'s: canonical `4447a242…`, inherited `76a9574a…`.
The placement therefore stores them once, at `data/101-coord239-machines-*`. The same
three edits are described as a **delayed erasure**: at `91/1` the 1 is kept briefly, so
that the existing states 167 and 151 can tell the original caller from the context of
deleted state 169.

The two packages reached this table independently, by different searches and with
different local proofs:

- **Local proof** ([`data/102-delay239-evidence-local239_certificate.json`](data/102-delay239-evidence-local239_certificate.json)):
  six exceptional comparisons, with old/new durations 1/5, 1/1, 1/3, 1/5, 1/1 and
  3/11. All unspecified exterior cells are independent symbolic variables. An
  independent review is in
  [`…local239_independent_review.json`](data/102-delay239-evidence-local239_independent_review.json).
  Source 101 uses four blocks with a five-cell footprint; this proof uses six
  comparisons with a maximum new block of 11.
- **Guard** ([`data/102-delay239-evidence-selector_guard_certificate.json`](data/102-delay239-evidence-selector_guard_certificate.json)):
  `q = 169 ∧ tape[h] = 1 ⇒ tape[h+1] = 1` over the exact old initialization and every
  unbounded instruction case of the old 240 table: 8,386 cases, 2,322,575 rules. At
  the 32 symbolic entries the right-hand 1-run has length `G + K` with `G ≥ 0` and
  `21 ≤ K ≤ 59`.
- **Block clock** ([`…block_clock239.json`](data/102-delay239-evidence-block_clock239.json)):
  the old 409,691-step initialization plus exactly 144 block steps gives the same full
  initial frame.
- The direct runtime proof of the 239 table and a packaged full replay both pass:
  8,386 cases, 2,330,575 rules, ending `FULL_239_MATHEMATICAL_REPLAY_PASS`.

## Further contributions

- **The discovery search** (`research/search/`, C++17) jointly chooses a shared control
  state and compensating helper rows. Its recorded run examined 28,680 state pairs and
  1,318,621,440 helper-row actions, and found three delayed-erasure variants. Its
  radius-5 tape domains are finite under-approximations used for discovery only.
- **Logical-basis obstructions** (`research/formalisms/`): two exact non-derivability
  results for specializations of the fourth input of the inherited classical axiom.
  They cover every implication-only reconstruction `U(a,b,c,Truth)`, and `U = ¬b`.
  The three- and four-valued matrices validate the retained seven logical rows, MP,
  GEN, atomic fresh vacuity and IR, and invalidate Peirce's law. **They are not
  asserted to satisfy CP or GIC.**
- **Eighteen diagnostic compiler outputs** on the public 281-state backend. They keep
  its known missing `1.inc/read1` row, and **are not consistency machines**; no count
  is transferred to 239 or 240.
- **A permutation-quotient obstruction.** Relaxing twelve selector targets independently,
  which includes every register permutation, leaves only the diagonal exact-step
  quotient. Context-sensitive sharing, such as the delayed erasure itself, lies outside
  this family.
- **Source reachability intervals**, which exclude five guarded cases. The main proof
  does not use them.
- **An exact NIP source specialization.** The source shrinks from 6,455 to 6,449
  leaves under the local precondition `R6 = 0`, with a source certificate over 8,369
  outside edges. **The binary candidate still needs its state-72 route repaired**
  (`UNVERIFIED_NIP_LAYOUT_REQUIRES_72_ROUTE_REPAIR`), so no smaller machine is claimed.
  The NIP strategy has prior art.
- **A different 240-state layout** (`cluster_variant1`) with source depth 48 rather
  than 51. Its source relation has 1,932 pairs, its bisimulation and full initialization
  were replayed independently, and its unbounded runtime passes.

## Non-claims (kept from the package)

- No new Lean or Rocq theorem for the 239 table. The internal PA endpoint is separate.
- Compensated244 was the smallest closed external Lean consistency endpoint at the pin.
- Actual non-halting follows only under Con(ZFC). Two-sided independence needs more,
  for example Σ₁-soundness.
- No minimality claim.
- The supplementary results are not premises of the 239 result.

## Open lead

The NIP specialization is a possible further source-level saving. Its binary repair
is the missing step: re-route state 72, then run the unbounded runtime check.
