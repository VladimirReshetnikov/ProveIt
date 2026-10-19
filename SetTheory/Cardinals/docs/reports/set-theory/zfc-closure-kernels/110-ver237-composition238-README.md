# A 238-state binary Turing machine for ZFC consistency

Prepared for Vladimir Reshetnikov and the ProveIt project, 19 October 2026.

This package supplies an explicit **238-working-state**, binary, single-tape
machine, including its complete initialization from the all-zero tape, and an
ordinary mathematical proof of

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}(M_{238},0^{\mathbb Z})
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

The proof combines the exact construction and fresh simulation certificates
in this package with the specifically identified inherited ProveIt
source-to-consistency calibration. **No newly compiled Lean or Rocq endpoint
for this exact 238-state table is supplied.** The archived Lean source files
identify and explain the inherited interface; they are not a standalone
dependency checkout. This package does not claim a serialized internal PA
proof, unconditional nonhalting, or a globally minimal state count.

Start with `report.pdf` for the complete mathematical argument and
`research_status.json` for the precise evidence level. All editable LaTeX,
the complete transition table, checkers, source certificates, and fresh
receipts are included.

## Exact machine and counting convention

| Item | Value |
|---|---|
| Canonical machine | `machines/zfc_composed238.tm` |
| Working states | `0` through `237`, exactly **238** |
| Transition rows | **476**, two per working state |
| Separate halt outcome | `238`, with no outgoing rows |
| Total control labels including halt | 239 |
| Tape | One tape indexed by the integers, alphabet `{0,1}` |
| Initial configuration | State `0`, head `0`, every cell `0` |
| Moves | Exactly one cell left or right |
| Dispatcher | Canonical state `84` |
| Inherited labels | Start `95`, dispatcher `96`, halt `254` |

The requested strict bound is achieved under the working-state convention
used by the supplied baseline: **238 < 239**. No input word or external
initialization is charged separately. All working states are reachable in
the directed transition graph; this does not assert that the actual blank
execution visits every working state.

Each row has the format `state read write direction target`. The canonical
machine's SHA-256 is:

```text
909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08
```

The inherited-label table, `machines/zfc_composed238_old.tm`, has SHA-256:

```text
069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c
```

## What produced the saving

At the inspected ProveIt checkpoint,
`ce192939372ac7944fe2a0208c68a96d49fb5e3b`, the incoming research contains
**two distinct 239-state constructions**. The BusyBeaver239 Research and
ZFC239 Companion archives describe the same delayed-erasure construction.
The ZFC 239 State Construction archive describes a different machine using
source-boundary reassociation and a decoder-context split. Their identities,
archive hashes and original notices are preserved under `reference/`.

This work composes those two reductions, checks every local dependency,
reproves the selector condition for the changed source, and directly verifies
the final 238-state runtime. The savings do not follow merely from the edits
being disjoint: changing source paths can invalidate a semantic guard.

Relative to the supplied `reference/boundary239_old.tm`, delete working state
`169` and change exactly these inherited-label rows:

| State/read | Predecessor action | Final action |
|---|---|---|
| `147/0` | `0 R 169` | `0 R 80` |
| `80/0` | `0 R 25` | `0 L 106` |
| `91/1` | `0 L 50` | `1 L 167` |

The other **473 retained rows are unchanged**. The erased cell's temporary
one, together with a predecessor tape bit, preserves the control distinction
that state `169` previously carried. The whole-tape local proof has six
special blocks and 472 ordinary rows, including `147/0` after state-map
identification. Its one additional reachability condition is:

> When the boundary239 predecessor reaches state `169` reading `1`, the
> cell immediately to the right also contains `1`.

The fresh unbounded predecessor check establishes this guard for startup
and every source instruction interface. A second exact reconstruction uses
the original rotation240 table and the complete 43-retained-row edit list
in `reference/row_edits_from_rotation240.json`, deleting states `169` and
`218`. Both recipes produce exactly the same canonical bytes.

## Proof chain and completed checks

The report proves the following interfaces, with the final calibration
explicitly inherited:

1. The all-zero run reaches the exact initial dispatcher frame.
2. Every final-machine instruction block implements the changed source
   instruction for arbitrary natural registers and arbitrary allowed frame
   padding, without a hidden halt or zero-time transition.
3. The changed source has the same complete ordered control-descriptor graph
   as the calibrated rotation240 source, including break/continue successors
   and zero-padding behavior.
4. The original source and seed are the literal source data named by the inherited
   calibration, whose halting is equivalent to a finite ZFC refutation.

| Obligation | Fresh result |
|---|---|
| Exact construction | Two independent edit recipes; 238 states, 476 rows, identical bytes |
| Source control | 13 stages, 25 individual rotations, 6,455 ordered instruction occurrences, all successors and guards |
| Source data interface | All 203 pinned lookup rows and all 6,455 original-source leaf triples; exact logical seed |
| Direct final runtime | **8,386 guarded cases**, **2,255,513 symbolic rules**, all **476 rows** used, minimum duration **13** |
| Independent local composition | Six whole-tape blocks, structural invariant, all incoming-edge implications |
| Independent selector guard | **8,386 cases**, **2,247,513 symbolic rules**, 32 runtime guard events and 6 startup events |
| Complete blank initialization | Sparse and dense implementations agree after **409,835** steps on all 351 one cells and the all-zero exterior |
| Supplementary K/S obstruction | **11,690** finite obligations; explicitly scoped to the logical basis |
| Relocated quick replay | Construction, source, local proof, initialization and finite obstruction replayed through the packaged entry point |

The direct runtime proof allows arbitrary independent natural register
values, arbitrary nonnegative extra header gap, and an arbitrary nonempty
finite spare list. Its affine symbolic rules include literal transition
steps, unary-loop induction, and four rederived finite-list schemas. It is
an unbounded argument, rather than a bounded simulation of a few register
values. Full details and the individual case results are included.

The exact initial logical registers are `(3,0,0,0,3,0,0,0,0)`. The physical
register tuple is `(0,0,0,3,0,0,3,0,0)`, with 167 spare values equal to one.
The final startup reaches dispatcher `84` at head `-5`, marker `-6`, and
header `176`, with additional gap `117`.

The inherited source calibration is pinned to
`13ec39ed43148b1807f51ed6e6528e1c84659562`, principally
`CalibratedRotation240.halts_iff_zfc_refutation`. The report explains its
native-theory/ZF and ZF/ZFC bridges and their formalizability in ZFC. The
new work does not rebuild that ancestor library or use a general assertion
that ZFC proves the soundness of Lean.

## Reproduce

Python **3.10 or later**, its standard library, and assertions enabled are
sufficient. The replay uses no network, SMT solver, proof-assistant install,
or absolute path from the preparation workspace. Run from the extracted
package, using a new or empty output directory **outside** the package:

```bash
python3 -B reproduce.py --output /tmp/zfc238-replay
```

This includes a fresh complete unbounded proof on the final table. That
proof took about 222 seconds in the initial preparation run; timing depends
on the machine. The receipt explicitly identifies which checks ran.

For a short replay that omits the fresh complete runtime execution:

```bash
python3 -B reproduce.py --quick --output /tmp/zfc238-quick
```

Quick mode still binds the archived complete-runtime result to the exact
table, source, engine, helper and adapter hashes. Its output explicitly says
`runtime_replayed: false`. To also regenerate the independent predecessor
guard proof, use:

```bash
python3 -B reproduce.py --with-guard --output /tmp/zfc238-with-guard
```

Each subprocess is accepted only after its expected JSON status is checked.
Do not use `-O` or `-OO` with the main replay or inherited symbolic engine.
The supplementary obstruction checker uses explicit exceptions and has also
been replayed under `-O`.

For reconstruction alone:

```bash
python3 -B build.py --output /tmp/zfc238-build
```

To rebuild the PDF in a working copy with a normal LaTeX installation:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

An additional pass may be requested by LaTeX to stabilize page references.
The integrity manifest binds the delivered bytes, so recompiling or editing
the delivered files changes their hashes. It is an integrity manifest, not
a digital signature.

## Formalism investigation

The report compares the existing CP/GIC/irreflexivity presentation, finite
NBG-style class theories, condensed detachment, ground contextual rewriting,
and the finite arithmetic presentation `Q0 + Con(ZFC)`. It distinguishes an
internal consistency calibration from a complete binary implementation with
all initialization and proof-search costs charged. No new machine-state
bound is inferred from an uncompiled axiom list.

A concrete supplementary result is a **six-valued logical counterinterpretation**
on `C3 × C2`. It validates `K`, `S`, the other seven published logical rows,
modus ponens, generalization, actual atomic equality, atomic fresh-variable
vacuity, and irreflexivity, while falsifying Peirce's law, double-negation
elimination, full vacuity, and the original four-input classical axiom.
The witnesses are values of actual formulas, not merely inaccessible matrix
assignments. **CP and GIC are excluded from this obstruction.** It rules out
the indicated derivation of the missing logical basis; it does not establish
the consistency strength of a complete modified set theory.

The report also states and proves the fixed-finite-fragment reflection
obstruction: assuming ZFC is consistent, a fixed finite bundle of ordinary
membership-language ZFC theorems cannot have its consistency provably
equivalent in ZFC to `Con(ZFC)`. Its nonuniform, fixed-fragment scope is
essential and is made explicit.

## Package layout and incorporation

| Path | Contents |
|---|---|
| `report.tex`, `formalism.tex`, `transition_table.tex`, `report.pdf` | Complete report, editable sources, printed 238-state table |
| `machines/` | Both labelings, their bijection, exact changed source leaves |
| `build.py`, `reproduce.py`, `render_table.py` | Portable construction, replay, and appendix generation |
| `source/` | Source rotations, control certificate, pinned calibration data |
| `verification/` | Exact local, startup, selector and universal-runtime checkers |
| `evidence/` | Actual fresh receipts, runtime cases, logs and packaged replay |
| `formalism/` | Six-valued obstruction proof, checker and result |
| `reference/` | Exact predecessor tables, alternate patch, historical notices and source pins |
| `reviews/` | Independent mathematical review notes |
| `licenses/` | Inherited terms and original notices |
| `PROVENANCE.json`, `MANIFEST.sha256`, `research_status.json` | Identity, integrity and evidence-level records |

A suitable future repository location is
`Computability/BusyBeaver/Research/ZFC/candidate-composed238/`. The earlier
candidates and their original proof histories should retain their identities.
The next proof-assistant step is a concrete one: port the compact local
simulation together with its selector guard, or instantiate the direct
runtime framework on the new table and certified source. It is not claimed
as completed here. No remote repository write was performed.

The original calculus, set theory and 254-state machine remain credited to
Mira-Cult; the Rocq verification to Jeff Ketchersid and contributors; the
compiler framework to Andrew James Wade; and prior ProveIt and incoming
reductions to their original contributors. See `ATTRIBUTION.md` and the
preserved original notices.
