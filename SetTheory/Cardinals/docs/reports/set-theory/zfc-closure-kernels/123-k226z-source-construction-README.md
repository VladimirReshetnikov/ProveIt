# A reproducible source construction for K226 and K227

This packet reconstructs a **226-state, two-symbol Turing machine** from the
released K230 source and table. It retains the independently useful 227-state
intermediate, every selected source transformation, and both rejected address
layouts. The final source is also related directly to the original K230 source
by a small offset-aware checkpoint certificate.

The canonical final table is
[`generated226/02_k226/k226.tm`](generated226/02_k226/k226.tm). It has 226 working
states numbered 0 through 225, starts in state 0 on a blank binary tape, and
uses the separate halt outcome 226. Each line after the start header is
`state read write direction target`; directions are `L` and `R`. The halt
outcome is excluded from the working-state count.

## Reproduce the selected construction

Python 3.10 or later is sufficient. No third-party Python package, network
access, optimization solver, or original repository checkout is required.
Run with assertions enabled:

```sh
python3 -B reproduce.py
```

The command rebuilds the tables and source trees from `inputs/`, proves the
eight local decoder blocks on an arbitrary outside tape, checks the complete
duplicate-state quotient, and regenerates the two source checkpoint
certificates. A successful run writes `reproduction.json` with status
`PORTABLE_K226_AND_K227_SOURCE_REPRODUCTION_PASS`.

The checked-in selected outputs are deterministic. Intermediate directories
make each change inspectable; they are not independent claims of calibrated
machines. In particular, `generated/rejected227_zero7` and
`generated226/01_unrepaired226` are deliberately retained failing layouts.

## Exact outputs

| Artifact | K227 | K226, selected |
|---|---:|---:|
| Working states | 227 | **226** |
| Transition rows | 454 | **452** |
| Source leaf occurrences | 5,121 | 5,121 |
| Source guarded cases | 6,656 | 6,656 |
| Distinct source subtrees | 212 | 211 |
| Distinct decision subtrees | 189 | 188 |
| Distinct primitive subtrees | 23 | 23 |
| Maximum source path length | 40 | 41 |
| Maximum consecutive-zero run | 6 | 6 |
| Deleted states in original K230 numbering | 79, 140, 175 | 65, 79, 140, 175 |
| Changed surviving rows relative to K230 | 36 | 52 |

Canonical K226 table SHA-256:

```text
b58279b8b2e2cf029dd94e084d47cd6097772d7bce2a62653767895123d29599
```

Final K226 source (`generated226/02_k226/sites.json`) SHA-256:

```text
47f5cfac0ec765c6f84f9d29973d4c9b3d79f12482a2cd1268d582e85c814bd3
```

Canonical K227 table SHA-256:

```text
ce179dae58b737c508c6a3b360cad0fb4ff722165a34aa9e903a8877c0e89d34
```

The table builders retain original K230 state numbers until the final dense
renumbering. `renumbering.json` gives the complete bijection in each selected
output directory. State references in the source proofs and transformation
certificates always use the original K230 numbering.

## What changes

`build227.py` first replaces four copies of the closed transfer-plus-one loop

```text
((CD6, (CI5, CC2)), CI5)  ->  (CI5, (CD6, CC2)).
```

For any natural initial values `(R5,R6)=(a,b)`, both versions terminate with
`(a+b+1,0)` and preserve the other registers. The source loses four leaves.
The corresponding H decoder fold and the inherited delayed-erasure fold
remove K230 states 79 and 140. Two boundary rotations and five rotations of
closed chunks then prepare a combined decoder-role reassignment that removes
state 175. The boundary rotations include a final `CB1` chunk and are checked
by complete source-graph equality; they are not described as rotations of
three closed chunks.

`verify_roles.py` independently checks the final role reassignment. It fixes
only the predecessor bit and the currently read bit, rejects any access to an
outside cell, and checks positive matching blocks for all eight role/bit
cases. Old blocks have lengths 1 or 3; new blocks have lengths 1, 3, or 5.
The incoming-row audit proves the predecessor tags inductively from the
literal table. Every outside tape cell and the complete head position are
preserved in the matched blocks.

`build226.py` then rotates one closed subtree at all ten occurrences. This
makes the two rows of state 65 literally identical to those of state 98.
The quotient `65 -> 98` is checked on **all 454 old transition rows**, including
the deleted state, with no tape or source invariant. Five further closed
rotations repair source addresses that otherwise collide with the inherited
separator scanner. Every selected rotation preserves all 6,656 guarded
source successors.

The complete sequence therefore has four H block substitutions, two boundary
rotations, eleven rotations of three closed chunks, two earlier native
folds, the decoder-role reassignment, and the final exact duplicate quotient.
See `source_roles227.tex`, `source_duplicate226.tex`, and
`transfer_matrix.md` for the mathematical explanation and historical
accounting.

## Proof boundaries

The checks in this directory establish precise source identities, exact
literal construction, local block equivalence, and finite source-certificate
validity. They are one part of the complete proof chain.

The companion native verification packet checks the unbounded interpreter
protocol, the complete blank startup, the H and delayed-erasure native
folds, canonical renumbering, and the retained scanner counterexamples.
Finite runtime fixtures were used for discovery, but do not replace the
unbounded protocol proof.

The companion Rocq packet provides the kernel-checked source and literal
runtime endpoints. `build_offset_certificate.py` produces an **untrusted**
certificate list for its generic offset-aware checker. The certificate
relates candidate and reference registers by equality except for a possible
`+1` in register 5. It tests register 6 whenever that offset is present. For
K226 there are 2,376 checkpoint pairs and 4,750 branches, with exactly eight
offset entries; the longest straight-line segment has five instructions.
For K227 there are 2,373 pairs and 4,744 branches, again with eight offset
entries. The two certificates relate their sources directly to the frozen
K230 source, independently of the discovery history.

The consistency calibration is inherited from the pinned K230 theory and
Rocq development. This directory does not reaxiomatize set theory, claim a
global minimum state count, or turn an empirical runtime check into a
consistency theorem. The enclosing research archive supplies the complete
calibration, runtime, and formal endpoint together with these source files.

## Inputs and provenance

The two exact K230 inputs are pinned to commit
[`3142e4dd980f0be12f4abb636c4ae2528afc17eb`](https://github.com/elliotglazer/k230-rocq/tree/3142e4dd980f0be12f4abb636c4ae2528afc17eb).

| Input | SHA-256 |
|---|---|
| `inputs/k230.tm` | `e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8` |
| `inputs/sites230.json` | `400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487` |

The transformation ideas draw on the ProveIt 243-to-235 sequence, including
the 235-state packet at commit
[`0128d662fd46f72dc84505176ae8ec28affb2d9d`](https://github.com/VladimirReshetnikov/ProveIt/tree/0128d662fd46f72dc84505176ae8ec28affb2d9d).
The transferred savings are not arithmetically additive across different
axiom packets and decoder layouts; `transfer_matrix.md` records exactly what
survived, what was combined, and what remains open.

`source_math.py` adapts the source-tree and control-graph utilities from that
235-state packet. The original normalized program lineage includes Wade's
register-machine compiler and Jeff's set-theoretic source, as recorded in
the retained notices. See `licenses/` for the corresponding licenses,
attribution, and provenance notices.

## Discovery artifacts

`discovery/repair_zero226.py` is an optional, bounded beam search for the five
final address repairs. It uses the same closed-rotation checker, keeps the
helper states required by the K227 proof fixed, and searches at most ten
levels with beam width 16. Its score is only the number and length of bad
source addresses, followed by maximum source depth. The fixed construction
requires no search. The original discovery log and selected history are
retained for review; their wall-clock measurements are not proof premises.

Run the optional search from any directory with:

```sh
python3 -B discovery/repair_zero226.py --out discovery/replayed
```

`SHA256SUMS` covers the delivered source, inputs, receipts, and selected
generated artifacts. Reproduction intentionally overwrites generated files
and receipts with freshly checked copies.
