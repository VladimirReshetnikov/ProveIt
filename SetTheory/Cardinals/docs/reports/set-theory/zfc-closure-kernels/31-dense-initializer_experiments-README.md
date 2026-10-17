# A 29-state blank initializer for the unchanged 286-state Mira runtime

This experiment reduces the complete, editable clean-assembler control from
**341 to 315 working states** by replacing its 55-state compact initializer
with a 29-state initializer. The runtime is the same 286-state table: all
572 named runtime rows are preserved exactly under the recorded renumbering.
The older literal printer used 122 initializer states and produced a
408-state control. Thus 408 to 315 is a 93-state reduction from that older
baseline; **341 to 315 is the relevant 26-state improvement over the newer
incoming initializer proposal**.

The 315-state table is a component experiment, not a new smallest machine
whose nonhalting is proved equivalent to Con(ZFC). It is larger than the
attributed public 253-state construction, and the required full simulation
and consistency bridge for this editable runtime remain open.

## Exact result

The model is a deterministic single-tape, two-way-infinite, binary Turing
machine with L/R moves, initial state 0, blank symbol 0, and no input. The
complete table has 315 working states, 630 transition rows, and a separate
halt target numbered 315. Every initializer state and both of its rows are
charged. The standalone initializer has 29 working states and a separate
handoff/terminal target; in the combined table that handoff goes into the
runtime instead of halting.

Two independently implemented literal-table simulators reached the first
runtime entry after exactly **47,189,196 transitions**, in numeric state 5
(named `d:0`), with the head at -44. The complete set of one-cells is

```text
-45, 12243, 12245, 12247, 12249, 12251,
12253, 12255, 12257, 12259, 12261
```

Every other tape cell is zero. There are 12,287 zero-cells between the left
marker at -45 and the header at 12,243, exceeding the runtime's minimum gap
of 102. The nine blocks after the header are `(01)^9`, representing nine
zero registers in the frozen runtime's physical register order.

The independent Python replay also checked the entire intermediate tape
after 47,176,870 transitions, immediately after the five-state preprocessor
would ordinarily halt. At that point the head is 12,242 and the one-cells are

```text
{-45, 12243} union {-44 + 3*k : 0 <= k <= 4095}.
```

This is a checked finite computation; no claim about the global optimality
of BB(5) is needed for this initializer.

## Reproduce

Python 3.10 or newer is sufficient. The default verification command also
uses `g++` or `clang++` when available; `--python` selects the Python
fallback. No Coq, Lean, network connection, external Python packages, or
unpublished `source.py` is needed for these component checks.

Run the following from this directory. To reconstruct the frozen runtime,
provide a ProveIt checkout or finite snapshot containing the two pinned
Python files, and an upstream checkout or snapshot containing `ZF/m254/`:

```sh
python3 extract_runtime.py \
  --repo /absolute/path/to/ProveIt \
  --upstream /absolute/path/to/busy-beaver \
  --output /tmp/bb5-runtime-rebuild.json
```

The ProveIt vendored snapshot can also serve as `--upstream`:
`/absolute/path/to/ProveIt/lib/jeff-busy-beaver-zfc254`. A sparse checkout must
first have the four listed input files available locally. The extractor
verifies the exact byte hashes below, so a different repository HEAD is
acceptable only if those files have the pinned contents. It does not infer
source identity from the directory name or an unverified JSON field.

`extract_runtime.py` executes the two verified ProveIt modules from memory
and reads the upstream DAG and literal machine as data. It reconstructs the
default **408-state, 816-row** machine, removes exactly its **122 initializer
states**, and compares the resulting **286 states and all 572 rows**, together
with the entry, gap, register order, and initial values, to `runtime_286.json`.
It does not edit either source tree, create source-tree bytecode, run upstream
Python or Coq, invoke Git, or fetch missing files. Its optional evidence path
must be outside the supplied source roots.

Regenerate the literal initializer and full control, then run both execution
checks:

```sh
python3 build_bb5_initializer.py --output output
python3 verify_initializer.py --output output
python3 independent_python_audit.py --directory output
```

The last command parses the emitted 630-row table independently and imports
neither the generator nor either C++ simulator. It determines the unique
initializer-to-runtime exit from the literal rows and stops at the first
entry into the runtime. It verifies the intermediate preprocessor profile,
the exact final support on the infinite tape, and every retained runtime
row. The independent audit deliberately refuses Python's `-O` mode because
its assertions must remain enabled. The runtime extractor instead uses
explicit checks that remain active under `-O`.

If no C++ compiler is available, the explicit fallback command is:

```sh
python3 verify_initializer.py --python --output output
```

The saved successful evidence is in
`output/initializer_verification.json`,
`output/independent_python_replay.json`, and
`output/independent_runtime_rebuild.json`.
Host resource failures abort these checks; they are never treated as a
successful proof or as an ordinary rejected proof candidate.

## Adapter proof and general register count

Let `L = -45`, `H = 12243`, and `G = H-L-1 = 12287`. Redirect the published
preprocessor's halt action into the adapter while retaining its write and
move. For any fixed positive number `r` of zero register blocks:

1. Two setup states write an auxiliary one at `H-1`, retain the header at
   `H`, and reach `H+1`.
2. Exactly `2r` printer states write `(01)^r` to the right of the header.
   The last printer moves left, so the return begins at `H+2r-1`.
3. Two preserving return states detect the **first adjacent pair of ones
   encountered from the right**, namely the header and auxiliary. They
   retain the header, erase the auxiliary, and reach `H-2` after `2r+1`
   transitions. The pair need not be globally unique: the source work tape
   still contains its left adjacent pair, and the last periodic one with
   the auxiliary and header forms a triple of ones.
4. Two eraser states erase the periodic work tape while moving left. Its
   periodic ones have two intervening zeros, so the first adjacent pair in
   this remaining work region is `L,L+1`. The right member is erased; the
   left marker is retained. The final move reaches `L+1` in the runtime.
   This phase takes exactly `G` transitions.

The endpoint support is exactly `{L,H} union {H+2j : 1 <= j <= r}`. The
working-state and transition counts are therefore

```text
initializer states = 5 + 2 + 2r + 2 + 2 = 2r + 11
handoff transitions = 47,176,870 + 2 + 2r + (2r+1) + 12,287
                    = 47,189,160 + 4r.
```

For `r=9` these give 29 states and 47,189,196 transitions. This parameterized
statement concerns the initializer component; the supplied frozen runtime
expects exactly nine registers. It initializes zero values only. Arbitrary
nonzero startup data require a separately charged extension.

`independent_review.md` records the independent proof review in more detail.
The ordinary adapter argument is conditional on the explicitly stated
finite preprocessor endpoint; the two full replays check that endpoint for
the literal table. No proof-assistant theorem for this new prefix is claimed.

## Hashes and source pins

SHA-256 hashes of the delivered tables and frozen runtime:

| Artifact | SHA-256 |
|---|---|
| `output/bb5_initializer_control_315.tm` | `cf68ed84e9e51f1776d32666f9e3a843cd522621a1cd011a36ce0ef9ed30a097` |
| `output/bb5_initializer_29.tm` | `09ecdc4c9837c6eabb19abb67b1bafc43f2bd6d61fd778cec011f376578ff3c5` |
| `runtime_286.json` | `5e939b9b89b7d74f40101162ed1eb263c37e558d7366d652db90fac1c26321b9` |

The ProveIt source pin is
[`4747142d5d15213eb711bdadfa3cc7e769fcb7a7`](https://github.com/VladimirReshetnikov/ProveIt/tree/4747142d5d15213eb711bdadfa3cc7e769fcb7a7).
Both files below are under `Computability/BusyBeaver/Research/ZFC/`:

| Source file | SHA-256 |
|---|---|
| `mira_backend.py` | `39508fea4786276dd3655737b07f29f827c06fc5653499a24941b1866d690836` |
| `recover_wade_dag.py` | `caa4996be46f9201991dba07f81d4673f14e874ac682226c29fce9e0cea851f1` |

The upstream input pin is
[`jeff87654/busy-beaver` at `297ab8df7e5de329605c3875b4934643b371a5e3`](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3):

| Upstream input | SHA-256 |
|---|---|
| `ZF/m254/coq/prog/Dag254.v` | `538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3` |
| `ZF/m254/machine/zfc_254.tm` | `d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb` |

The newer 341-state comparison is recorded in the incoming
[`zfc_epsc2_proposal.zip`](https://github.com/VladimirReshetnikov/ProveIt/blob/47e8871089dd8d5b5a912350f3285734041528bb/docs/incoming/zfc_epsc2_proposal.zip),
whose `engineering/compact_initializer.py` supplies the 55-state initializer.
Its ordinary initializer formula and results are prior work in the inspected
repository corpus.

## Attribution, license, and proof boundary

The five-state preprocessor is **Heiner Marxen and Jürgen Buntrock's
published machine**, using the orientation on
[Marxen's primary simulation page](https://www.turbotm.de/~heiner/BB/simmbL5_1-m.html).
The adapter and the new extraction/audit scripts are the contributions of
this experiment. The 286-state runtime is reconstructed from ProveIt's
editable assembler around **Mira-Cult's single-marker engine and program**;
Jeff (`jeff87654`) supplies the attributed upstream verification snapshot.
The imported source-specific 254-state bootstrap is not reused by this
control. Andrew James Wade's separate MIT-0 backend is part of the historical
compiler provenance; his generator modules are not executed by this
extraction command.

The newly authored adapter, scripts, and explanatory text in this directory
are supplied under the ProveIt MIT No Attribution terms in `LICENSE.new-code`.
The two ProveIt assembler modules retain their existing
[MIT No Attribution license](https://github.com/VladimirReshetnikov/ProveIt/blob/4747142d5d15213eb711bdadfa3cc7e769fcb7a7/LICENSE).
This grant does **not** relicense pre-existing upstream machine/program data,
the published BB5 machine, or the pre-existing transition rows retained in
`runtime_286.json` and the combined control. The pinned `busy-beaver` tree has
no upstream-wide license declaration; ProveIt's
[snapshot notice](https://github.com/VladimirReshetnikov/ProveIt/blob/4747142d5d15213eb711bdadfa3cc7e769fcb7a7/lib/jeff-busy-beaver-zfc254/README.proveit.md)
explicitly excludes that imported snapshot from its blanket MIT-0 grant.
The same authorship and license boundary is retained here.

The evidence establishes an exact blank-tape prefix and exact runtime-row
preservation. It does not prove arbitrary executions of the frozen runtime,
the proof enumeration/compiler correspondence, the conventional ZFC
consistency bridge, or an internal ZFC proof of a final machine equivalence.
In particular, the 315-state control does not implement the new scope-total
EPSC2 decoder or the dense QNAND codec discussed elsewhere in the report.
Those logical/compiler proposals and this initializer reduction are separate
contributions with separate obligations.
