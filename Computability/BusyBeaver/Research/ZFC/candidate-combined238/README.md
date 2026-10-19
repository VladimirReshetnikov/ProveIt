# Combined 238-state candidate

This binary, single-tape machine has **238 working states**, including blank-tape
initialization, plus a separate halt state. It starts in state 0 at head 0 on an
all-zero two-way infinite tape, and every transition moves left or right. The
canonical 476-row table is [zfc_combined238.tm](zfc_combined238.tm) (start 0,
dispatcher 84, halt 238); [zfc_combined238_old.tm](zfc_combined238_old.tm) is the
same machine with inherited labels (start 95, dispatcher 96, halt 254), and
[renumbering.json](renumbering.json) is the bijection.

It was found during the intake of batch 172 by combining the two **different**
239-state constructions delivered in that batch. Its status is that of those
constructions: an ordinary mathematical argument with executable, unbounded
certificates, **not** a Lean or Rocq theorem. See [what is claimed](#status).

| Table | SHA-256 |
| --- | --- |
| `zfc_combined238.tm` (canonical) | `909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08` |
| `zfc_combined238_old.tm` (inherited labels) | `ab1f12ceb0b1cbc167977286652dd3be3407e9b24fcd3f8e7c9ac630166514b9` |
| `sites_logical.json` (register source) | `7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6` |

## Two independent savings

Both ingredients start from the [240-state candidate](../candidate-rotation240/README.md)
(inherited table `547dd69d…`), and both were delivered on 19 October 2026, pinned to
ProveIt `13ec39ed43`. They are Sources 101–103 of the
[ZFC closure-kernels host](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-172.md).

**Delayed erasure (Sources 101 and 102, one identical table, `ingredients/delayed239_old.tm`).**
Delete state 169 and change three retained rows:

| Row | 240 | delayed239 |
| --- | --- | --- |
| `147/0` | `0 R 169` | `0 R 80` |
| `80/0` | `0 R 25` | `0 L 106` |
| `91/1` | `0 L 50` | `1 L 167` |

The register source is unchanged. Old state 169 merges into 80. The helper row
`91/1` now keeps its 1 for a moment, so that the shared states 167 and 151 can tell
the original caller from the merged role. Four exceptional old steps become positive
blocks of 5, 3, 5 and 9 new steps. The proof needs one runtime guard: whenever old
state 169 reads 1, the cell to its right is 1.

**Source boundary (Source 103, `ingredients/boundary239_old.tm`).** Reparenthesize
the register source, in 13 stages with 25 rotations, without changing any of its 6,455
instruction occurrences, operands or successors (DAG 225 → 224 nodes). Re-encode the
decoder for it (37 rows of 20 decoder states change). Then split old state 218 by the
bit behind the head, reuse helper 223 for one role, and merge the other with 179.
That fold is proved for every binary tape at the start state, with no runtime guard.

**The combination.** The two constructions touch disjoint rows. None of
`80/0`, `91/1`, `147/0` or the rows of 169 changes in boundary239. Neither do the
rows of the 18 states on the delayed-erasure blocks (106, 92, 107, 125, 25, 93, 57,
167, 151, 173, 56, 24, 36, 54, 71, 82, 94, 50). The incoming edges of 67, 80, 91
and 169, which carry the fold's syntactic invariant, are also unchanged. Applying the
delayed-erasure edits to boundary239 gives this table
([code/build238.py](code/build238.py)): **240 − 1 − 1 = 238 states**.

Disjoint rows alone prove nothing. The delayed-erasure guard is a property of whole
runs, and boundary239 has a different source and different decoder paths. The table
is therefore accepted only by the checks below.

## Verification

All runs used Python 3.14 on copies of the delivered packages. The ingredient
packages' own checkers were used unchanged. The drivers under `code/` were written
during the intake.

| Check | Result |
| --- | --- |
| **Direct unbounded runtime** of this table on the boundary source: Source 103's `validation/check_literal_runtime.py`, unchanged ([receipt](evidence/runtime238.json), [cases](evidence/runtime238_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: all **8,386** guarded instruction cases, **2,255,513** symbolic rules, all **476** rows, minimum instruction duration **13** |
| **Exact blank startup** ([code/boot.py](code/boot.py), sparse run and independent dense replay) | The complete initial frame after **409,835** steps: dispatcher, head −5, marker −6, header 176, logical registers (3,0,0,0,3,0,0,0,0), 167 value-one spares, 351 one-cells, zero elsewhere |
| **Second route, local fold** boundary239 → 238 ([code/fold_any.py](code/fold_any.py), [receipt](evidence/fold_boundary239_to_238.json)) | Invariant closed on **121,024** windows; all four blocks on all 22 admitted windows with exact paths; **474** commuting rows; blank prefix compared checkpoint by checkpoint; clock 409,691 + 4·18 + 2·12 + 4·6 + 8·3 = 409,835 |
| **Second route, guard** on boundary239 over all runtime frames ([code/guard_any.py](code/guard_any.py), [receipt](evidence/guard_boundary239.json)) | `PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD`: all **8,386** cases, 2,247,513 rules, **32** symbolic 169/read-1 visits, each with a right-hand 1-run of constant term at least **23**; all 6 blank-prefix visits checked |
| Positive control: the same runtime checker on boundary239 ([receipt](evidence/control_runtime_boundary239.json)) | Reproduces Source 103's published **2,247,513** rules |
| Positive control: `guard_any.py` on rotation240 with its own source ([receipt](evidence/control_guard_rotation240.json)) | Reproduces Sources 101/102's 2,322,575 rules, 32 visits, constant 21 |
| Positive control: `fold_any.py` on rotation240 → delayed239 ([receipt](evidence/control_fold_rotation240_to_delayed239.json)) | Reproduces Source 101's **121,536** windows and 22 admitted block windows |
| **Negative control**: this table without the `91/1` change ([receipt](evidence/control_runtime_without_91_1.json)) | `NOT_PROVED` at the 49th case (site 35, an increment of register 4): the helper change is necessary |
| Source 103's own quick replay on a fresh copy | All eight checks pass, including the source-rotation certificate and the identification with the pinned Lean source and seed |

The runtime checker is an induction engine, not a test over sampled values. Its
cases quantify over all natural values of the nine registers, an arbitrary gap, an
arbitrary first spare value and an arbitrary finite list of further spares. Unary
runs and spare lists are traversed by induction over block lemmas re-proved from the
literal table. Its 4,000-rule cap bounds the construction of a proof, not the
machine's running time. The [Source 101 audit](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/101-coord239-evidence-UNIVERSAL239_AUDIT.md)
explains the rules.

The two routes are independent of each other at the binary level. The direct route
needs only the runtime and startup checks. The second route transfers the 238-state
machine's behaviour from boundary239, which Source 103 accepts by its own runtime
proof, through the local fold and the guard.

## Status

The argument composes four parts. Three are inherited:

1. Source 103's source certificate: the reparenthesized source halts exactly when
   the calibrated Rotation240 source does, for every register file.
2. The calibration of that source: [`CalibratedRotation240`](../calibrated_rotation240.md)
   (halting iff a ZF/ZFC refutation) and the Lean source identification.
3. The ZFC endpoint argument of the 240-state candidate, which this table shares.

The fourth is new: the binary simulation and startup checks above.

**What is claimed.** An ordinary mathematical proof, formalizable in ZFC, that this
238-state machine fails to halt from the blank tape if and only if ZFC is consistent.
The proof is at the evidentiary level of the 239-state packages it combines.

**What is not claimed.**
- No new Lean or Rocq theorem for this table. The checked Lean endpoints are for the
  [240-state candidate](../candidate-rotation240/README.md) and earlier machines.
- No internal PA proof.
- No minimality, no absolute consistency, no unconditional non-halting, and no
  two-sided independence from bare consistency.

The intake that found the combination did not re-run the inherited calibration.

## Reproduce

From this directory, Python 3.10 or later with assertions enabled (no `-O`):

```bash
python -B code/build238.py ingredients/boundary239_old.tm rebuilt238_old.tm
python -B code/boot.py zfc_combined238_old.tm
python -B code/fold_any.py ingredients/boundary239_old.tm zfc_combined238_old.tm fold.json
```

The runtime and guard checks need Source 103's checker. Extract
`ZFC_239_State_Construction_2026-10-19.zip` from commit `83fd358548` into a fresh
directory, copy this table into its root, and run there:

```bash
python -B validation/check_literal_runtime.py --table zfc_combined238_old.tm --sites candidate239/sites_logical.json --states 238 --output runtime238.json
```

The guard check, `guard_any.py`, imports that package's `validation/symbolic_runtime.py`
unchanged:

```bash
python -B /path/to/code/guard_any.py --engine validation --table candidate239/zfc_boundary239_old.tm --sites candidate239/sites_logical.json --output guard.json
```

Each unbounded run takes about 8–15 minutes on one core.

## Attribution

The original calculus, set theory, source program and 254-state machine remain
credited to Mira-Cult; the upstream Rocq verification to Jeff Ketchersid; the
compiler framework to Andrew James Wade. ProveIt and its incoming reports keep credit
for the reductions that produced the 240-state candidate. The delayed-erasure fold is
the contribution of Sources 101 and 102, which found it independently. The source
boundary rotation, decoder repair and 218/223/179 split are the contribution of
Source 103. The intake of batch 172 contributes only the observation that the two
compose, the combined table and the checks above. The inherited notices are under
[licenses/](licenses/).
