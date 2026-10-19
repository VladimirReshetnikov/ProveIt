# A 239-state binary machine calibrated to Con(ZFC)

**The primary machine has 239 working states, including its blank-tape initializer.**
It has one two-way infinite tape, alphabet `{0,1}`, blank symbol `0`, and only
left/right moves. It starts in state `0`, with head at `0` and every cell zero.
Working states are `0..238`; entering the separate halt state `239` stops it.

The ordinary mathematical proof in `report.pdf` establishes, in ZFC and using
the explicitly inherited source calibration,

\[
\neg\operatorname{Halt}(M_{239},\mathrm{blank})
\quad\longleftrightarrow\quad \operatorname{Con}(\mathrm{ZFC}).
\]

This package supplies the exact table, reproducible executable mathematical
certificates, a short local simulation proof, and the complete LaTeX source.
**It does not supply a new closed Lean/Rocq theorem or a serialized object-theory
ZFC derivation for this exact 239-state machine.** The new proof uses ordinary
finite calculations and natural/list inductions formalizable in ZFC. Existing
source-equivalence and consistency theorems are inherited and identified
precisely; their proof-assistant dependency chain was not rebuilt in this task.

## Start here

| Artifact | Purpose |
| --- | --- |
| `report.pdf` | Complete mathematical report, full 239-state table, alternative-formalism survey and 946-bit appendix. |
| `report.tex`, `sections/*.tex` | Complete editable LaTeX sources. Run `pdflatex report.tex` twice. |
| `machines/zfc239.tm` | Canonical 478-row table: start 0, dispatcher 84, halt 239. |
| `machines/zfc239_old.tm` | Same machine with inherited labels: start 95, dispatcher 96, halt 254. |
| `machines/renumbering.json` | Exact state bijection, including the halt. |
| `machines/construction.json` | Checked table edits, counts, conventions and hashes. |
| `machines/sites_logical.json` | Unchanged 6,455-leaf calibrated register source. |
| `verify_all.py` | Portable reproduction entry point. |
| `evidence/UNIVERSAL239_AUDIT.md` | Independent review of the quantified runtime and full consistency composition. |

The input is ProveIt commit
`13ec39ed43148b1807f51ed6e6528e1c84659562`, specifically
`Computability/BusyBeaver/Research/ZFC/candidate-rotation240`.
The exact old table is retained at `inputs/zfc240_old.tm`.

## The saving: one merged state and one coordinated helper change

Use inherited state labels. Delete state **169** and make these three retained-row edits:

| Row | Baseline 240 | New 239 |
| --- | --- | --- |
| `80/0` | `0 R 25` | `0 L 106` |
| `91/1` | `0 L 50` | `1 L 167` |
| `147/0` | `0 R 169` | `0 R 80` |

All **475 other retained rows** are unchanged. In particular `80/1` stays
`1 R 91`. The source, physical register map and initial logical seed are unchanged.

The state map sends old 169 to new 80. Under proved tape-context guards,
four exceptional old steps become these positive new blocks:

| Old row | New state path | New steps |
| --- | --- | ---: |
| `80/0` | `80 → 106 → 92 → 107 → 125 → 25` | 5 |
| `169/0` | `80 → 106 → 93 → 57` | 3 |
| `169/1` | `80 → 91 → 167 → 151 → 173 → 56` | 5 |
| `91/1` | `91 → 167 → 151 → 24 → 36 → 54 → 71 → 82 → 94 → 50` | 9 |

Each block reproduces the old step's **entire tape, head and mapped state**.
Every other old row commutes in one step. The old predecessor invariant gives
the local left bits. The extra fact—old 169 reading 1 has a 1 immediately to
its right—is separately proved over every valid unbounded instruction frame
and the exact blank initialization.

The new idea in this concrete reduction is to change a shared helper return
while merging control states. The helper retains its behavior in the old
contexts and serves the merged role in a distinguishable tape context.
Finite runtime profiles guided discovery; the accepted proof does not assume
that those profiles exhaust future runs.

## Completed evidence

| Check | Fresh result |
| --- | --- |
| Direct 239-state unbounded runtime | **8,386** guarded cases; **2,330,575** symbolic rules; all **478** rows; minimum constant instruction duration **13**. |
| Universal extra-guard proof on old 240 | **8,386** cases; **2,322,575** rules; all **480** rows; **32** explicit 169/read-1 symbolic visits; minimum one-run constant **21**. |
| Syntactic local invariant | **121,536** admitted finite Boolean windows, proving closure for arbitrary exterior tapes. |
| Four local blocks | All **22** admitted five-cell assignments; independent symbolic-open-tape checker also passes. |
| Exact startup | Sparse/dense full-tape agreement after **409,835** new steps. |
| Relative startup | All **409,692** old checkpoints compared, including full tape support. |
| Source identity | Actual pinned Lean row definitions and lookup tree independently parsed; root 202 expands to the exact **6,455** leaves. |

The unbounded runtime is a mathematical induction engine, not a large set of
numerical tests. Its variables represent nine independent arbitrary natural
register values, arbitrary additional gap, arbitrary first spare value and
an arbitrary finite remaining spare list. Exact one-block lemmas are rederived
from the input table before arbitrary list traversal is allowed. The rule cap
bounds construction of the proof, not the machine's runtime or its parameters.

The startup frame has head `-5`, marker `-6`, header `176`, 351 one-cells,
logical registers `(3,0,0,0,3,0,0,0,0)` and 167 spare blocks of value 1.
All other tape cells are zero. The old exceptional visit counts are
`(18,12,6,3)`, giving an exact extra clock of
`4*18 + 2*12 + 4*6 + 8*3 = 144`, hence `409691 + 144 = 409835`.

The source bridge reads the actual definitions of `ProgramRouting245`,
`ProgramRotation244` and `SourceRotation240`. It does not infer the program
from a theorem conclusion. The unchanged source's consistency endpoint is
`CalibratedRotation240.halts_iff_zfc_refutation`, reproduced as a pinned source
snapshot in `reference/`. The report explains the clean-pointer/zero-padding
bridge needed to concatenate the proved leaf cases into the whole source run.

## Reproduce

Python 3.10 or newer and its standard library suffice (tested with Python 3.12). No network, compiler, proof assistant
or package installation is needed. Run with assertions enabled.

```sh
python3 verify_all.py --output-dir replay
python3 verify_all.py --full --output-dir replay-full
python3 build.py --out rebuilt
```

The default replay checks construction, source extraction, local blocks,
initialization, all ten frontend packets and the semantic/certificate fixtures.
It writes `QUICK_REPLAY_PASS`; it does not pretend to rerun the unbounded proofs.
The `--full` replay additionally runs both complete unbounded proofs and compares
the new per-case/guard data to the delivered evidence. Each unbounded pass took
about 3.5 minutes in the research environment. All new outputs go to the chosen
output directory, leaving delivered evidence unchanged.

The direct runtime invocation is:

```sh
mkdir -p replay
python3 verification/symbolic_runtime.py \
  --table machines/zfc239_old.tm \
  --sites machines/sites_logical.json \
  --output replay/runtime239.json
```

Inspect the result's `status`: it must be `UNIVERSAL_MATHEMATICAL_PASS`, with
8,386 cases and the counts above. This inherited lower-level driver can return
a `NOT_PROVED` receipt without a nonzero exit code; the top-level driver handles
that explicitly. `python -O` and `PYTHONOPTIMIZE` are unsupported and rejected.

`SHA256SUMS` records the final delivered files, excluding itself and transient
replay/build outputs. The primary table digests are:

```text
Canonical: 4447a2423907f2b96e8bcd6c88ed2d1e353f925fb8cf36ca913224ddce5914ba
Old labels: 76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b
```

## Alternative formalisms and the 946-bit frontend

`foundations/` supplies an ordinary model-theoretic proof and exact generator
for a **946-bit complete equational packet**, improving the inspected Source 79
packet from 1,169 bits. It shares class NAND with native cons (`J=P`), uses a
false-class witness slice as `Pick(x)=W(x,d)`, and reuses the earlier truth fusion.
The 14 equations have 215 term nodes and 13 operation symbols; together with
three local variables they fit into four-bit opcodes. All headers and the two
ground endpoints are charged.

The EPSC schema matrices are equality-free pure-membership formulas with arbitrary
finite parameters. The finite stack equations themselves use native equality.
The ordinary upper/lower model argument preserves that distinction and imports
the existing raw-EPSC/ZFC calibration explicitly.

The exact search target is the ground equation `N(d,d)=d`. Bare consistency of
the equations would be useless because a one-element algebra always exists.
`ground_rewrite.py` gives a complete abstract fair certificate search, including
both orientations, arbitrary contexts and substitutions for the union of the
variables on both sides. Its finite run over 65,536 certificates is inconclusive.
This program has no claimed binary-machine state count.

The report also compares SIR, EPSC/hereditary saturation, Collection and Separation,
native finite clauses, direct first-order proof enumeration, combinatory/tag
representations and universal-machine input costs. Earlier Source 42 has a
901-bit **native clause** packet, requiring a different inference interface;
the same variant is 1,998 bits with equality completed. Another variant is
917/1,703 bits. Source 44's 881-bit count is a template with external signature
and arities. None of these bit counts automatically translates to working states.

## Other artifacts and integration

`research/variants/` contains two more 239-state tables, with target 12 or 142
instead of 106 in row `80/0`. Both have full unbounded runtime and exact startup
receipts. Their startup times are 409,943 and 409,967, respectively.

`research/search/` records discovery-only profiles, the C++ search code and
negative controls. `research/source_compression/` includes the register-permutation
census and six concrete traces falsifying a naive NIP implementation. These
restricted negative results are not lower bounds. Historical exploratory
harnesses and logs retain some original paths; the core `verify_all.py` workflow
and the discovery commands in `SEARCH_PROVENANCE.md` are portable.

The intended repository integration is a new research intake plus a candidate
directory such as `Computability/BusyBeaver/Research/ZFC/candidate-coordinated239`.
Retain the old table as the exact baseline and preserve the table bytes and
source pins. Formalizing the new binary theorem remains a separate integration
task, for which both a short local proof and direct runtime certificates are
provided.

Original calculus, source and machine credit belongs to Mira-Cult; upstream
verification to Jeff Ketchersid; compiler work to Andrew James Wade; preceding
reductions and calibration to ProveIt and its incoming reports. See
`ATTRIBUTION.md`, `PROVENANCE.json` and the unchanged original notices under
`licenses/`. No state minimality, unconditional nonhalting or broad historical
priority is claimed.
