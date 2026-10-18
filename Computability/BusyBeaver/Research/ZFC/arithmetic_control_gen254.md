# Internal GEN constructor, controls 93–122

`ArithmeticControlGEN254` proves the literal register interpreter's universal
formula constructor for every model of IΣ₁ and every internal encoded register
file with both scratch registers zero. A positive internal runtime takes
catalogue control93 to122, replacing TW with `wal (first WS) TW` and WS with
`second WS`; all other coordinates are retained. There is no bound on the
internal values or runtime and no formula-wellformedness premise.

Checked generic contracts supply the unpair core at93–103, pair at104–113,
scaled transfer at114–119, and two literal tag increments at120–121. The new
unit introduces no new induction. Its complete-file compositions also prove:

- From control67, cache push followed by GEN restores the original WS and
  sets TW to `wal oldTW oldCache`.
- From AX entry41, the two-parameter prefix followed by GEN sets TW to
  `wal oldP1 oldCache` and WS to `cantor oldTW oldWS`.

Both compositions require initially zero S1 and S2. These are register-program
catalogue indices, not binary-machine state numbers. The separate
[cache-read fragment](arithmetic_control_ax_read_cache254.md) starts at122 and
reaches136; neither module alone claims the composed41→136 run, the complete
AX/Enum comparison, internal245/246 binary simulation, or PA consistency endpoint.

The source and audit passed9 axiom probes and13 typed callers, with zero warnings,
under default Lean proof limits, one thread and a4 GiB limit. They shared a120s
deadline and took30.894679s and2.197849s. The three finite boundary facts use
`propext`; the six arithmetic facts use only `propext`, `Classical.choice` and
`Quot.sound`.

The guard checks102 exact project source/object pairs, six cached
Foundation/Mathlib boundaries and two toolchain objects. The inherited MP record
captures its source object before audit but lacks the separate newer
first-provider field; its recorded search path is resolved and checked without
inventing that historical field. This new unit records both its fresh object
and first-provider identity before audit and rechecks all237 inputs afterward.

- [Actual verification](results/arithmetic-control-gen254-verification.json)
- [Existing-evidence review](results/arithmetic-control-gen254-review.json)
- [Publication bindings](results/arithmetic-control-gen254-publication.json)
- [Exact history](results/arithmetic-control-gen254-history.json)
- [Original source-only provider proposal](results/arithmetic-control-gen254-provider-proposal.json)

History retains the source-only drafts, independent source/API review, original
guard and failed preparation before compilation, the three-line canonical-path
repair, corrected unbuilt preparation, and successful source/audit logs. The
actual-evidence review discloses its author's guard role; root independently read
and exclusively executed the proof. No failed preparation is presented as a
failed Lean theorem or successful proof.

With the recorded caches available, run from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_gen254.py \
  --repo "$PWD" --dependency-root /home/codex/src/Proofs \
  --ax-cache-push-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-cache-push254-verification.json" \
  --mp-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json" \
  --output /tmp/gen254-recheck --prepare-only
```

Each invocation requires a fresh output directory. Omit `--prepare-only` for
source and audit. Preparation does not invoke Lean, query its version, download
or rebuild dependencies. The publication contains exact textual evidence and
source, not compiled objects or a clean rebuild of the transitive dependency
cache. Maintained default preparation is recorded separately after installation.
The interpreter retains existing attribution to Mira-Cult, Jeff Ketchersid and Wade.
