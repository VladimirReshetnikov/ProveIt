# Independent review: current2011 local tile-cell construction

Verdict: **PASS**, with no requested source corrections. Reviewer:
`circuit_reduction`; author: `controller_certificate`. The reviewer did not
author this packet or its direct dependency CurrentCellLabels2011. The
reviewer did author earlier prerequisites including DecimalMachine215,
CurrentSparseDigits2011, CurrentHighDigits2011, and native geometry/copy
modules; this is disclosed rather than treating the entire dependency chain
as independently authored.

Both complete frozen sources and the author receipt were read. The direct
CurrentCellLabels2011 source was also read in full, and the actual mask,
reflected coefficient positions/weights, clause mask arithmetic, and
physical-permutation interfaces were compared against the new construction.
No frozen source was modified. Both new modules were freshly compiled in an
isolated overlay, in sequence, with the checks using the replayed main.

## Exact bindings

Paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | ---: | --- |
| `CurrentCellConstruction2011.lean` | 256 | `03344f81c7817f625633470218727176f975ee7617154589534a0b94feb9bd0a` |
| `CurrentCellConstruction2011Checks.lean` | 107 | `847c5e2b22d2c985419087a057c91d7db3238992e0ddc7c180af49e9bc154c7a` |

The hashes match the frozen author receipt and were unchanged before/after
replay. Relevant exact dependencies are:

| Dependency | SHA256 |
| --- | --- |
| `CurrentCellLabels2011.lean` | `88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d` |
| `CurrentMasks2011.lean` | `72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06` |
| `CurrentKernel2011.lean` | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| `WangTiles942Permutation.lean` | `3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef` |
| `CurrentClause2011.lean` | `a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566` |
| `DoubledClause2011.lean` | `1285bb4332ad2dfabaee2a99eb1c7624d9a4c7c10e82dc3f25a2e6af92e6733f` |

## Mathematical and interface findings

`bitDigit m j=m/2^j%2` is proved Boolean and connected to the actual natural
testBit. The finite-prefix reconstruction uses the exact modulo-power
recurrence and includes the zero-length case. The bounded version removes
the remainder only under the stated bound.

The physical layout agrees with the kernel weights, not a convenience color
name: South942..950, North960..968, East969..976, West978..985. The packed
order is West, North, East, South with shifts0,8,17,25. The corresponding
kernel control coefficients are doubled powers at exponents10+j,18+j,
27+j,35+j. Thus the construction puts precisely the complemented color bits
in the fields read by the actual clause. In particular, West978 is the low
packed block, and East969 is the third block. The Start controls independently
distinguish these: West253 has bit0=1 while East252 has bit0=0; South510 has
bit0=0 and bit1=1. This addresses the historical orientation hazard directly.

The selector is placed at the actual `physicalPosition i`. Its range and
injectivity are imported proved theorems, so `localDigit_at_physical`,
`localSelected`, count1, and weighted payload do not assume a supplied
permutation or abstract/physical index equality. Physical index0 is recovered
from the proved Start position0. No forbidden old selector slot is silently
reintroduced.

Every local digit is Boolean and vanishes outside the actual lowSupport
`range951 ∪ Ico960 986 ∪ {1004}`. The construction sets dummy977 and marker1004
to zero initially; this is an explicit base cell, not a claim about their
final global values. Other gaps, including951 and986, are verified zero.

The four binary reconstructions are exact finite words. The actual tile
color bounds justify all natural subtractions and the complement identity:
selectorPayload+copiedWord=2^34. `cellClauseBalance` retains the bare
selector1 contribution, yielding exactly `2^45+2+localDigit i 1`.
`cellClauseMasked` tests the full mask2^45-4 and proves the raw value below
radix2^47. The Boolean bare bit is essential to the bound2..3 in the unmasked
low bits. The theorem does not drop an actual global incoming carry or
unaligned temporal contribution; those are outside this local statement.

The compatibility helpers bind to the existing cyclic definitions with an
explicit pointwise equality on e<986 except e=977. Hence dummy977 is exempt,
and marker1004 lies outside the premise. These helpers do not require a
cyclic alignment assumption, selected-word assumption, or mask theorem:
they derive the selected index and payload from the supplied local data.
They also do not assert that such data have already been assembled globally.
The N=1 checks instantiate all three cyclic conclusions. A further check
changes dummy and marker to arbitrary natural values and still reconstructs
the same copied word. This freedom is scoped to that word identity and does
not assert those arbitrary values are globally Boolean or mask-compatible.

There is no finding requiring correction. The author receipt accurately
limits the result to a local Boolean cell and its cyclic compatibility.
Global marker placement, all high-mask tests, carry normalization, safe
mutations, controller arithmetic, and positive polynomial witnesses remain
separate obligations; no equation converse is claimed here.

## Isolated fresh validation

The replay directory is `/tmp/current-cell-construction-peer-lax8tqar`.
Unchanged dependency bundles were linked into its namespace; the two
reviewed module bundles were excluded and built freshly. `LEAN_PATH` placed
this overlay before the existing lake path. No shared object was overwritten.
Both commands used the source's `Elab.async false` and the bounded form

```sh
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lean -M6000 -j1 \
  -o /tmp/current-cell-construction-peer-lax8tqar/DiophantineConsistency/MODULE.olean \
  /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/MODULE.lean
```

| Module | Result | Seconds | PeakKiB | Fresh object SHA256 |
| --- | --- | ---: | ---: | --- |
| CurrentCellConstruction2011 | PASS | 5.31 | 3290516 | `6c3b6096cd8089db4fdfdcf5140c84781f1a719c0dc6defe69f67af8c62e38b4` |
| CurrentCellConstruction2011Checks | PASS | 3.10 | 3259260 | `219a36d9318a95fcb5c4ad3946e1ea6bb7a4f94750c7214d6d3612157c30ed70` |

Both fresh objects are byte-identical to the frozen author objects. The main
emits no Lean diagnostics. All fifteen check axiom reports contain only
subsets of `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, new
axiom, or `native_decide` occurs in the reviewed new sources. This replay
reuses existing prerequisite objects and does not claim a fresh rebuild of
the full machine or arithmetic import closure.

Logs in the same replay directory:

- `CurrentCellConstruction2011.log`: SHA256 `42ca580d3d5f568afbbed9f5a43d124c8eed32424585b1a5dc3964cc7981e867`.
- `CurrentCellConstruction2011Checks.log`: SHA256 `12cd55068574e3e4ffe8795233dbad1b152b1cf22a99ce2956c9a30be0518a68`.

The exact commands, before/after source checks, output hashes, and shared
object comparisons are recorded in `REPLAY.json` in that directory, SHA256
`872ffabd2bc896e827adcc457db8e232f4e9912f790ffa963d0d728261663e69`.
Only this new peer receipt was added to the repository. No frozen source,
author receipt, shared document, or git state was changed.
