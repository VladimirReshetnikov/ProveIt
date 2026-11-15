# Two new 194-state PA consistency machines

**Result:** no validated machine with fewer than 194 working states was found. This bundle delivers the requested fallback: **PA194AX11GH** and **PA194AX11GHS**, two new literal 194-state binary, single-tape machines, together with a written iPRA proof of the requested blank-nonhalting/Con(PA) equivalence.

The proof uses the exact latest incoming AX11H mathematical calibration, retained in `references/`, and proves the new command, source, and literal-machine transfer. The new tables have full finite implementation certificates. This is **not a new completed Lean or Rocq formalization**. The inherited proof audit and precise dependency boundaries are in the report and `proof/audit.md`.

## Start here

- `report/report.pdf`: complete report, both full transition matrices, all 111 historical table classes, and all 86 delivery descriptions.
- `report/report.tex`: main LaTeX source; it includes the supplied `proof/`, `comparison/`, and transition-table fragments.
- `machines/PA194AX11GH/machine.tm` and `machines/PA194AX11GHS/machine.tm`: the two new dense transition tables.
- `verify.py`: self-contained offline reconstruction and verification replay.
- `comparison/comparison.md`: detailed comparison of the whole current corpus and its proof-status distinctions.
- `research/`: exact unsuccessful reduction experiments, with code, inputs, receipts, and logs.
- `SHA256SUMS`: all delivered file identities, except the checksum file itself.

## Exact machines

Each dense table has working states `0..193`, start `0`, terminal `194`, alphabet `{0,1}`, initially all-zero two-way infinite tape, and head position `0`. Each of its 388 rows is `state read write L|R next`. A transition always writes a symbol and moves one cell, including a transition into the terminal control. No input or prewritten initialization is required.

| Quantity | PA194AX11GH | PA194AX11GHS |
|---|---:|---:|
| Working states | 194 | 194 |
| Fixed + readers − folds | 134 + 67 − 7 | 135 + 67 − 8 |
| Primitive source sites | 3,671 | 3,668 |
| Certified source outcomes | 4,778 | 4,774 |
| Complete blank startup | 57,922 steps | 57,768 steps |
| Independent symbolic steps | 1,106,693 | 1,110,639 |

SHA-256 of `machine.tm`:

```text
PA194AX11GH   513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1
PA194AX11GHS  7a4738a9eedd3f53674d67568b3197d38237d11d0fc08fa3d41251a8faf8052c
```

`machine.native.tm` uses construction labels (start 74, terminal 254); `labels.json` is the exact dense-to-native map. Every working control is graph-reachable from the declared start. This statement concerns the transition graph, not visitation by the single blank execution.

## Mathematical contribution

The new interface combines the supplied Q, N, G, H, and AX11 mechanisms. In the eleven-entry AX command, the saved generalization becomes `U(c,h)`, with explicit AX binder `c`, instead of offset binder `U(d,h)`. The fourth operand is actually consumed. Shift tests the cache `h=1`, and successful MP leaves its visible result without a dummy push. The new generalization word has 25 commands instead of 26. Its full compiler handles zero Cantor-stack aliases and ends a refutation with **Pop**, not an insufficient single Shift.

PA194AX11GHS implements the same abstract command interface with symmetric Shift input preparation feeding the same destructive comparison routine. It is a second physical implementation, not a second logical consistency encoding. Both literal graphs are new against all recognized historical tables under arbitrary state renaming, any spanning start, reflection, global bit exchange, and ignored final write/move decorations. Complete canonical tuples, rather than only their hashes, are compared.

The theorem is for the inherited `nativePAConsistency` sentence. The exact endpoint identities and Foundation submodule pin are recorded in `proof/endpoint_identity.json`. No assumption of PA's consistency is used to prove the equivalence, and the negative transfer requires no Markov principle.

## Reproduce the result

Python 3.10+ and its standard library suffice. From any working directory:

```bash
python3 -B /path/to/pa_conpa_research_2026-11-14/verify.py \
  --output /absolute/path/to/new-replay-directory
```

Full mode performs:

1. Integrity checks if `SHA256SUMS` is present.
2. Reconstruction of both machines from frozen attributed source inputs, including local simultaneous-fold cases, construction contracts, complete blank startup, and byte-for-byte comparison of ten core files.
3. Independent source/arithmetic-template binding and symbolic command-word checks.
4. Independent literal-row reconstruction of all four generic list lemmas and all 9,552 source outcomes across the two machines; output certificates must reproduce the delivered bytes.
5. Positive-duration, source-frame closure, and tape-map audit.
6. Exact novelty replay against all 111 historical representatives.
7. A **quick** replay of the retained incoming AX11H packet's finite bindings, arithmetic proof constructors, and source identities. This is separate from the full literal replay of the two new machines.

The output directory contains logs, freshly reconstructed files, certificates, and `summary.json`. Full replay can take several minutes. The report's expensive unsuccessful searches are not rerun by this command.

`--quick` explicitly skips construction-runtime and independent-literal contract replay; it retains reconstruction, startup, source, command, certificate-binding, and novelty checks. `--skip-baseline` explicitly omits the inherited packet replay. Both omissions are recorded in the summary. **Run with assertions enabled; do not use `-O` or `PYTHONOPTIMIZE`.**

Individual entry points are documented by `--help`. To reconstruct one machine:

```bash
python3 -B construction/build.py --family PA194AX11GH --output /tmp/new-AX11GH
```

The independent checker imports neither the construction compiler nor its arithmetic-box shortcuts. Its symbolic inductions range over nine arbitrary natural register values, an arbitrary nonempty finite spare list, and an arbitrary nonnegative gap. The uniformly proved arithmetic templates are distinguished from their supplemental finite duration examples.

## Comparison scope

Repository: `https://github.com/VladimirReshetnikov/ProveIt`.

Pinned revision: `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

The unified census verifies 13,109 selected source blobs, reads 18 distinct ZIP payloads through 30 references, and covers 82 filed plus four current incoming delivery payloads. It recognizes 908 occurrences of complete 194-state tables: 597 `.tm` and 311 additional explicit JSON occurrences. They yield 111 table classes, of which 110 have a spanning root and one is a disconnected diagnostic. It does not execute arbitrary generators or extract prose-only tables.

Evidence labels are 56 principal constructions, seven supplementary constructions, 36 research auxiliaries, four research seeds, seven rejected classes, and one diagnostic. These are attributed classifications, not counts of independently re-proved arithmetic theorems. The incoming AX11H archive is especially important: its tables repeat filed tables, but its written proof is substantially newer than the filed packet and the top-level status README.

`comparison/check_novelty.py` is self-contained. `comparison/rebuild_census.py --source /path/to/ProveIt` optionally rescans the exact pinned source universe; see `comparison/README.md` for scope and required local files.

## Reduction searches and limitations

Fresh work found no sub-194 candidate:

- Two 300-second grammar searches performed 8,308,353 total iterations; both retained effective-reader score 60, while 59 was needed.
- Direct contextual quotient searches tested all 18,721 control pairs on each new machine at radii four and six, with zero hits.
- A heuristic neutral-row-then-quotient screen completed all 639 variants, 15,175,055,004 row-action trials and 86,584,484 joint row pairs, with zero hits. It reused original contexts after the first rewrite; any hypothetical hit would still require fresh full verification.
- A corrected Runtime193 startup repair search through five encountered-row edits examined 1,214,781 computations and 5,462,651,667 literal transitions: 465,448 certified outward rays, 717,898 exact repeated configurations, 31,435 unresolved fuel cutoffs, and zero complete source-frame hits. The through-four statistics are a subset, not additional coverage.

These are bounded or heuristic searches, not a proof that 194 is minimal. The user-requested improvement below 194 remains unsolved by this work. No timed-out computation is labeled a certified infinite run.

## Build the PDF

The supplied PDF is already compiled. A standard TeX Live installation with pdfLaTeX, Latin Modern, AMS, `geometry`, `booktabs`, `longtable`, `microtype`, `fancyhdr`, and `hyperref` suffices to rebuild it:

```bash
python3 report/render_tables.py
sh report/build.sh
```

The TeX includes are relative to the extracted bundle. Keep its directory structure intact. `report/build.sh` invokes pdfLaTeX twice.

## Attribution and proof status

See `NOTICE.md`, `PROVENANCE.json`, component notices, and retained licenses. The new work builds on ProveIt contributors and the supplied research packets, including the literal runtime lineage attributed to James Chang and Andrew James Wade. Inherited archives are preserved byte for byte. This bundle claims new composition, literal realization, relative proof, census reconciliation, and search evidence, not invention of all inherited mechanisms.

The written iPRA theorem has an explicit inherited mathematical proof dependency. The Python programs check finite bindings and executable symbolic proof obligations; they are not a proof-assistant kernel, and this work does not claim a completed end-to-end Lean proof.
