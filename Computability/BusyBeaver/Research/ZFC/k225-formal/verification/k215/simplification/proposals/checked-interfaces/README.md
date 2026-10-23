# K215 proof simplification: checked interfaces and normalization

Research contribution for Vladimir Reshetnikov's ProveIt project, based on
commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

Read **report.pdf** for the mathematical argument, current-source audit, and
integration plan. Its editable sources are **report.tex** and **results.tex**.

## Recommendation

1. Adopt the small Lean normalization patch after the project's normal
   affected-client gates. It rewrites five proof bodies, removes 836 bytes,
   adds no helpers or imports, and preserves the printed public types and
   assumptions. A fresh Lean 4.32.0 component replay is included.
2. Keep today's Rocq list checker as the production default. The supplied
   direct checked-tree component has a simpler semantic interface than the
   older balanced/list-refinement proposal and removes 9,167 bytes from that
   proposal's generic checker/facade stack. It is 3,030 bytes larger than
   today's list stack and was slower in the focused measurement. It is an
   optional backend/interface contribution, not a demonstrated production
   speedup or source reduction over the current default.
3. Make complete semantic runtime coverage the larger next project: combine
   the existing structural decoder-prefix theorem with exact residual
   contracts for all 4,751 leaves / 6,176 branch outcomes. Retain the existing
   checker as a producer while incrementally replacing repeated prefix runs.

The exact 215-state transition table and endpoint statements are unchanged.
The current static Lean import census is 174 project modules / 1,752,650 source
bytes. Older checkpoint summaries describe a different source state.

## What is checked here

| Component | Executed verification | Boundary |
|---|---|---|
| Lean normalization | 25 successful fresh Lean 4.32.0 invocations; original/proposed module; six identical public type/axiom reports; patch applicability | No full K215 endpoint rebuild |
| Direct Rocq source checker | 18 successful fresh Coq 8.18.0 module invocations; exact 1,426-row certificate; all-register theorem; same-name source facade and typed client; eight boundary controls; recursive `coqchk SourceClient` | Coq 8.18 compatibility import recorded; production Rocq 9.1 branch and binary/ZFC endpoint not rebuilt |
| Source census | Current transitive project imports, per-file SHA-256, disjoint layer accounting, site counts | Static source analysis, not compilation |

The new concrete Coq theorems are closed under the global context. The six
compared Lean reports retain precisely `propext`, `Classical.choice`, and
`Quot.sound`. Neither component changes the machine or formalizes an internal
PA/ZFC derivation of the final endpoint sentence.

## Contents

- `report.tex`, `results.tex`, `report.pdf`: full report and editable sources.
- `lean-normalization/`: integration patch, proposed source, audit client,
  source manifests, replay script, compiler logs, and failed-edit history.
- `rocq/`: generic checked-lookup proof, tree adapter, exact source instance,
  facade, client, boundary controls, inherited dependencies, source metrics,
  replay script, licenses, and final compiler/recursive-check evidence.
- `experiments/rejected-helper/`: rejected Lean abstraction with its actual
  source-size cost. It is excluded from the accepted patch and replay.
- `evidence/architecture_metrics.json`: complete source census and hashes.
- `evidence/snapshot.json`: repository pin and retrieval provenance.
- `evidence/*-review.json`: independent static component reviews.
- `tools/architecture_metrics.py`: reproducible census analysis.
- `MANIFEST.json`, `verify_packet.py`: delivered-file and evidence verification.
- `NOTICE.md`, `LICENSE`: attribution, scope, and licensing.

## Reproduce

Use Python 3.11 or newer. Every build directory below must be fresh. Compiler
binaries and compiled objects are deliberately not shipped.

From this packet directory:

```sh
python3 verify_packet.py
python3 verify_packet.py --repo /path/to/ProveIt

python3 lean-normalization/reproduce.py \
  --repo /path/to/ProveIt --lean /path/to/lean \
  --out /new/lean-output

python3 rocq/build.py --out /new/rocq-output --baseline --recursive

pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`verify_packet.py` verifies the original delivery and recorded evidence; it
does **not** execute proof kernels. Rebuilding the PDF can legitimately change
its hash, so run the verifier before rebuilding or modifying artifacts.
For component-specific flags and assumptions, see the two component READMEs.
The Lean replay uses a matching ProveIt checkout and writes only to `--out`.
The Rocq replay uses the inherited sources shipped in this packet and likewise
writes to its output directory. The source census script's `--help` describes
its checkout and output parameters.

Suggested integration location:
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/checked-interfaces-normalization/`.
Unpack the contents of this packet's outer directory there. Keep proposed code
as a detached research component until its affected production descendants
have passed the current project toolchain gates.

## Recorded negative results

The initial guarded-subtype helper saved 272 bytes in its client but added a
1,176-byte helper: net growth of 904 bytes. It was rejected. The accepted Lean
patch instead normalizes existing subtype operations before transporting
witnesses.

The direct tree source module took 11.135 seconds and 527,844 KiB peak RSS in
the final serial run, compared with 8.968 seconds and 456,896 KiB for the list
baseline. The recursive check passed in 259.463 seconds. These are local
single-run observations with Coq 8.18.0, not full endpoint benchmarks. A packed
payload variant was also rejected; its recorded experiment is under `rocq/`.

The repository already contains the general checked-lookup idea in Lean and
prior Rocq designs. This packet supplies a checked current Rocq component,
an independently useful Lean proof edit, and a current-source integration
analysis; it does not claim priority for the general verification principle.
