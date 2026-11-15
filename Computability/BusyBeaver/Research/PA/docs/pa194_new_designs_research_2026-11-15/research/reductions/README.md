# Physical reduction investigation and exact rejection certificate

## Status

**No accepted machine with fewer than 194 states is provided by this packet.**
The file `rejected193/REJECTED_16_to_38.native.tm` is an explicitly **rejected
diagnostic candidate**. Its blank-tape run enters an exact 52-step cycle, which is
an elementary nonhalting certificate and defeats its proposed simulation of the
PA-consistency search.

Temporary research storage was lost during this session. The complete negative
search receipts and search programs from the earlier run did not survive. The
record in `previous_run_record/search_summary.json` is consequently labeled a
retained **previous-run summary**, not a freshly replayed exhaustive-search
certificate. This distinction does not affect the exact cycle certificates: the
candidate table and both cycles have been rebuilt and independently replayed
from the surviving, hash-pinned primary table.

## Exact candidate construction

The primary native table has SHA-256
`e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`.
Delete native control 16, redirect every target 16 to 38, and replace both rows at 38
with the former rows at 16:

```
38 0 1 L 1
38 1 0 L 1
```

All other rows remain as before apart from target redirection. The resulting
193-state, 386-row table has SHA-256
`cb53ad33e8812dc2ebfb6a1a1b452962eeba0cf6b851d398d403a192ea0e6b80`.
State 74 is the blank start, and 254 is the halting state (excluded from the state
count). Tape positions range over all integers; every unlisted position is 0.

## Fresh complete-configuration cycle replay

Run from this packet's directory:

```sh
python3 recover_rejected.py
python3 replay_cycles.py
```

Only the Python standard library is needed. The second script reconstructs the
candidate mutation independently, checks all row lookups and read bits in both
traces, and compares the complete configuration after the cycle to its entry.

| Initial configuration | Preperiod | Period | Repeated state | Head | Ones |
|---|---:|---:|---:|---:|---:|
| Blank tape, state 74, head 0 | 28217 | 52 | 1 | 1 | 46 |
| Source site 3661, positive decrement of logical T | 0 | 52 | 84 | 0 | 18 |

The second frame has path `101100`, physical registers
`[0,0,1,0,0,0,0,0,0]`, spare values `[0,1]`, and header distance 48. The complete
initial tape is part of the certificate and is also independently reconstructed
by the replayer. Checking only the state and head would not suffice; this
certificate explicitly checks the complete finite support of the binary tape.

## Earlier search scope

The retained summary covers a box-inclusive offset-merge search with offsets
−2,0,+2 and a separate 17424-proposal source-macro merge screen. These are finite,
restricted searches. In particular, the 11812 bounded concrete runs that did not
reach their target in 5000 steps are **inconclusive bound exits**, not proofs of
semantic inequivalence. A symbolic checker failure likewise need not be a
counterexample. No global impossibility claim follows from any recorded count.

The previous local window set used only a prefix of 301 source sites, with 398
source outcomes, combined with filed non-box contexts. Enlarging a set of hard
constraints after it has no survivor cannot introduce a survivor, but that fact
does not enlarge the scope of the finite synthesis model itself.

## Source interval certificate

The sibling folder `../root_research` contains a freshly reconstructed interval
analysis and its explicit postfixed-point check. It begins at source site 25
with logical registers `[2,0,0,0,0,0,0,0,0]`. It checks 4774 abstract successor
edges, finds sites 8, 3635, 3636 unreachable under the invariant, and forces zero
decrements at sites 7 (register 6) and 3634 (register 1). It is a sound
overapproximation of the source execution; it is not a proof of PA consistency.
The separate `../root_research/verify_intervals.py` checks the complete
certificate without importing the invariant computation.

## Polynomial MP witness clock

`check_clock_bound.py` independently audits every regenerated MP duration
vector. `mp_clock_bound_receipt.json` records the fresh result: 4778 contracts,
nonnegative coefficients, minimum constant 3, and step bound `694 + 18*j`.
Summing yields the physical bound `58066 + 685*t + 9*t*t`. The short TeX
derivation identifies the separately required startup, source bookkeeping,
address closure, and uniform physical simulation premises. The contracts are
supplied in the positive MP construction packet; their SHA-256 is checked in
the receipt. For a complete fresh check, pass that packet's
`verification/runtime/contracts.json` to this script's `--contracts` argument.

## Provenance and licenses

The base table and source descriptions were recovered from the filed
`pa194_conpa_2026-11-13` / `pa_sub194_research_2026-11-13` packets in the surviving
repository cache. Their hashes are checked in the accompanying scripts.
Upstream license copies appear in `licenses/`. Newly reconstructed scripts and
the explanatory text in this recovery packet are supplied under the MIT terms
in `licenses/LICENSE.ProveIt`; the original upstream notices remain applicable
to the copied inputs.
