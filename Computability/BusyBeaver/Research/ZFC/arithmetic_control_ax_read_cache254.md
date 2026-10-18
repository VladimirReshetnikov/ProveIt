# Internal AX cache read, controls 122–136

`ArithmeticControlAXReadCache254` proves the next parameter read of the literal
register interpreter, from catalogue control 122 to control 136. In every model
of IΣ₁, for every encoded nine-register file whose two scratch registers are zero,
there is an internal positive time at which the complete output file equals the
input file with exactly these updates:

- `cache := old cache + first(old PL)`;
- `PL := second(old PL)`.

All seven other physical coordinates are retained, including TW, WS, S1 and S2.
The paired-stream client accepts arbitrary internal `x` and `rest` with
`old PL = cantor x rest`; it adds `x` to the old cache and leaves `rest` in PL.
No standard-natural-value restriction, fixed loop fuel, zero-cache hypothesis or
formula-wellformedness assumption is used. The finite catalogue controls are
indices in the shared register interpreter, not states of a binary machine.

The proof instantiates the checked `ReadShape` contract at this literal occurrence.
All fourteen instruction edges and nineteen resolved successors are bound in Lean;
an independent source review also compared the complete 6,459-row program with
its 6,460-leaf tree and checked these particular paths and successors. The read
starts at the GEN constructor's next control, but this unit does not itself
compose the preceding constructor, complete AX or Enum, or establish the PA
consistency equivalence for a binary machine.

The source and audit passed under unchanged Lean proof limits, one thread and a
4 GiB limit, sharing a 120-second deadline. Source took 74.431289 seconds and audit
2.168268 seconds. All seven axiom probes and eleven typed callers passed, with
zero warnings. The two finite source facts use `propext`; the five arithmetic
facts use only `propext`, `Classical.choice` and `Quot.sound`.

The runner reuses 93 exact project source/object pairs, six explicit cached
Foundation/Mathlib boundaries and two toolchain objects. Both the Dispatch and
ReadTemplate parent records predate explicit pre-audit object capture. Their
successful source/audit commands and final object identities are pinned and
cross-checked; that missing historical field is not invented. This new unit
records its own fresh object and first-provider identity before the audit and
checks all 224 inputs and the fresh object again afterward.

Evidence and provenance:

- [Actual verification](results/arithmetic-control-ax-read-cache254-verification.json)
- [Existing-evidence review](results/arithmetic-control-ax-read-cache254-review.json)
- [Publication bindings](results/arithmetic-control-ax-read-cache254-publication.json)
- [Exact history](results/arithmetic-control-ax-read-cache254-history.json)
- [Provider proposal, retained with its original source-only scope](results/arithmetic-control-ax-read-cache254-provider-proposal.json)
- [Independent literal review](results/arithmetic-control-ax-read-cache254-literal-bindings.json)

History includes the initial handwritten-path rejection before any Lean file or
compiler call, the corrected source, the unbuilt preparation, raw successful
source/audit logs, independent source and guard reviews, and reviewer-script
corrections. The existing-evidence reviewer also authored the audit and guard;
root independently read them and exclusively ran the proof. A separate peer
source/guard/audit review is preserved unchanged in history.

From the repository root, with the recorded dependency caches available:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_read_cache254.py \
  --repo "$PWD" --dependency-root /home/codex/src/Proofs \
  --dispatch-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-dispatch254-verification.json" \
  --read-template-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-read-template254-verification.json" \
  --output /tmp/read-cache254-recheck --prepare-only
```

Use a fresh output directory for every invocation. Omit `--prepare-only` to run
source and audit. Preparation does not invoke Lean, query its version, download
or rebuild dependencies. Historical cache paths remain prerequisites; this
packet contains source and exact textual evidence, not compiled objects or a
fresh-build attestation for the transitive external dependency cache. Maintained
default preparation is recorded separately after installation.

The literal interpreter and its machine lineage retain the repository's existing
attribution to Mira-Cult, Jeff Ketchersid and Wade.
