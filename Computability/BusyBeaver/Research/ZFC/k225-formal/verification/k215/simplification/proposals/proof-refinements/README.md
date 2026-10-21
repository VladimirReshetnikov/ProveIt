# K215: verified proof refinements

Research packet for ProveIt, 21 October 2026.

**Three new checked proof components; no verified 214-state machine.**

Read report.pdf for the complete mathematical explanation and report.tex for editable source. Repository baseline: aa66d0a33f1f8237a348899eb8095b045a502832, including the three newest incoming research archives.

## Results

1. **Balanced normalized source proof.** The 1,426-entry normalized certificate is checked through balanced lookup. The exact all-register theorem preserves K215F.Source215.p215_dagPerm. Seventeen modules were freshly compiled with Coq 8.18.0, the new printed assumption reports are closed, and recursive coqchk of the concrete client passed. Lookup traversal is 32,961 tree nodes versus 2,033,059 normalized list cells; this is not a full-build speedup claim.
2. **Automatic decoder contexts.** A new Lean theorem covers every internal path of the supplied 202-node source DAG, assuming only its actual pointer bits and initial marker. It restores the whole arbitrary tape and proves positive duration for nonempty paths. Six modules, including a typed audit, freshly compiled with Lean 4.32.0 and zero warnings.
3. **Early-halting row selection.** One theorem handles all nine AX rows without nonfalsity assumptions used solely to force normal selection return. The production adapter is checked against actual command definitions and AX stack; its eleven-module fresh build and recursive coqchk passed. Replacing maintained clients and rebuilding the full endpoint remain separate.
4. **Five bounded state searches.** The final R41 table was tested in the one-row family omitted by its original packet, along with shallow-context and GC-ZC layouts. All specified runs found no survivor. These are not lower bounds, semantic counterexamples, or counts of distinct complete machines.

## Contents

- balanced_normalized/: source checker composition, dependencies, facade, typed client, metrics and proof receipts.
- decoder_context/: generic context/source-link theorems, exact K215 instance, foundations, independent audit and fresh proof receipts.
- early_halt/: generic and numeric selector, actual-command adapter, exact dependency sources, build receipts and finite corroboration.
- search214/: unchanged upstream algorithms, exact inputs, five run receipts and compressed rejection records.
- reviews/: scoped independent reviews.
- incoming-provenance.json: exact incoming archive identities.
- MANIFEST.json and verify_packet.py: integrity and evidence checks.

## Reproduce

Lightweight integrity, source/log binding and finite corroboration:

    python3 verify_packet.py

Fresh source proof (coqc/coqchk on PATH):

    python3 balanced_normalized/build.py --out /tmp/k215-source-fresh --recursive

For an unpacked Coq toolchain, use that driver's optional --toolchain argument. Coq 8.18 is the executed lane; the supplied Rocq 9.1 branch is not a recorded production endpoint build.

Fresh Lean component:

    python3 decoder_context/build.py --lean /absolute/path/to/lean --out /tmp/k215-context-fresh

Fresh selector proof and production adapter:

    python3 early_halt/build.py --output /tmp/selector-fresh
    python3 early_halt/build_production.py --output /tmp/selector-production-fresh

Optional bounded search replay:

    python3 -B search214/reproduce.py --output /tmp/fold-fresh

Rebuild the PDF with pdfLaTeX:

    python3 build_report.py --output /tmp/K215_Proof_Refinements.pdf

Use fresh output directories. Compiler objects and toolchains are omitted. Historical logs preserve actual original paths; portable scripts use relative package inputs. The report distinguishes inherited results, new kernel-checked results, finite evidence, and remaining integration work.

## Suggested integration order

Preserve the accepted table and public endpoint. First install the source facade under the production toolchain. Then adopt the actual-command selector at the existing leaf and GEN clients. Finally bind the decoder literals/tape model into the maintained runtime and compose primitive/return contracts.

For a second 215-state proof, M124/FM215 has a small local marker argument; CM215 may integrate fastest because of its already advanced Lean adapter. ZC215 is attractive for a cleaner independent scheduler. These are existing candidates, not newly constructed machines in this archive.

See NOTICE.md and component licenses for attribution.
