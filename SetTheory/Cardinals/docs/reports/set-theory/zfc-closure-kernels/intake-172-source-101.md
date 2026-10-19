# Source 101: coordinated reuse, a 239-state machine

Package `BusyBeaver239_Research_2026-10-19.zip` (arrival `83fd358548`, placement
`07194e5b4d`, prefix `101-coord239-`). Pinned to ProveIt
`13ec39ed43148b1807f51ed6e6528e1c84659562`, specifically
`Computability/BusyBeaver/Research/ZFC/candidate-rotation240`. The main report
(`report.tex`, `report.pdf`) and the delivery README are archive-only; every other
member is placed or aliased as recorded in [the placement map](data/intake172-placement.json).

## The machine

A 239-state, two-symbol, one-tape machine with blank-tape initialization. Its tables
are [`data/101-coord239-machines-zfc239.tm`](data/101-coord239-machines-zfc239.tm)
(canonical: start 0, dispatcher 84, halt 239, SHA-256 `4447a242…`) and
[`data/101-coord239-machines-zfc239_old.tm`](data/101-coord239-machines-zfc239_old.tm)
(inherited labels: start 95, dispatcher 96, halt 254, SHA-256 `76a9574a…`).

Starting from the 240-state candidate (Source 80), delete state 169 and change three
retained rows. The register source and the physical register map are unchanged.

| Row | 240 | 239 |
| --- | --- | --- |
| `80/0` | `0 R 25` | `0 L 106` |
| `91/1` | `0 L 50` | `1 L 167` |
| `147/0` | `0 R 169` | `0 R 80` |

Old 169 maps to new 80. Under guarded tape contexts, four exceptional old steps
become positive new blocks:

| Old row | New path | Steps |
| --- | --- | ---: |
| `80/0` | 80 → 106 → 92 → 107 → 125 → 25 | 5 |
| `169/0` | 80 → 106 → 93 → 57 | 3 |
| `169/1` | 80 → 91 → 167 → 151 → 173 → 56 | 5 |
| `91/1` | 91 → 167 → 151 → 24 → 36 → 54 → 71 → 82 → 94 → 50 | 9 |

Each block reproduces the whole old tape, head and mapped state; every other old
step commutes in one step. The package's stated new idea is **changing a shared
helper's return while merging control states**. The helper keeps its old behaviour
in the old contexts and serves the merged role in a distinguishable context.

The local proof uses a syntactic left-bit invariant (states 67, 80, 91 and 169),
closed on 121,536 finite windows. It also needs one extra guard: whenever old state
169 reads 1, the cell to its right is 1. That guard is certified over every unbounded
instruction frame of the old 240-state machine: 8,386 cases, 2,322,575 rules, 32
symbolic visits, minimum one-run constant 21. It is also checked on the exact blank
prefix, which takes 409,835 = 409,691 + 4·18 + 2·12 + 4·6 + 8·3 steps.

Independently of that local proof, a **direct** unbounded runtime proof of the 239
table on the unchanged source passes: 8,386 cases, 2,330,575 rules, all 478 rows,
minimum instruction duration 13.

## Further contributions

- **Two variant 239-state tables** ([`data/101-coord239-research-variants-*`](data/)):
  row `80/0` goes to target 12 or 142 instead of 106. Both have full unbounded runtime
  receipts and exact startups, of 409,943 and 409,967 steps.
- **A 946-bit complete equational packet** (`foundations/`). It improves Source 79's
  1,169-bit packet: class NAND is shared with native cons (`J = P`), a false-class
  witness slice serves as `Pick`, and the earlier truth fusion is reused. It has 14
  equations, 215 term nodes, 13 operation symbols and four-bit opcodes. A complete
  fair ground-rewrite certificate search is included; its finite run over 65,536
  certificates is inconclusive. **No binary state count is claimed for it.**
- **A survey of alternative formalisms**: SIR, EPSC and hereditary saturation,
  Collection and Separation, native clauses, direct first-order proof enumeration,
  combinatory and tag representations, and universal-machine input costs. It compares
  Source 42's 901-bit native-clause packet (1,998 bits with equality completed) and
  Source 44's 881-bit template.
- **Register permutations** (`research/source_compression/RESEARCH_NOTE.md`). All 36
  physical transpositions pass a 313-case discovery sample. In a 5,000,000-step
  bootstrap census, 31 reach clean frames and swap (6,7) actually halts. Swap (0,1)
  reaches an all-zero logical frame after 68,835 steps, and its full unbounded
  runtime passes; it is still a **240-state** table. Same-head and incoming-only fold
  searches on the 19 simply safe variants found nothing.
- **Six concrete traces** falsifying a naive NIP implementation, a zero-specialization
  screen, and the C++ discovery search with its negative controls.

## Non-claims (kept from the package)

- No new Lean or Rocq theorem, and no serialized object-theory ZFC derivation, for
  the 239-state table. The calibration is inherited, and its proof-assistant chain
  was not rebuilt.
- No minimality, unconditional non-halting or broad priority claim.
- The finite discovery profiles do not exhaust future runs; acceptance uses the
  unbounded proofs. The restricted negative results are not lower bounds.
- The equational packet's bit counts do not translate into working states.

## Relation to the other sources of batch 172

Source 102 delivers **byte-identical** tables, found independently.
[Source 103](intake-172-source-103.md) saves a state elsewhere. The two savings
compose into the [238-state candidate](intake-172.md#the-combination-238-states).
