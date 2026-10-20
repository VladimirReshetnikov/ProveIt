# A 217-state marker relay and a concrete return conflict

This is an exploratory table, **not an accepted 217-state construction**.
A temporary marker repairs the ordinary right-neighbor-one use of state 36,
and six decoder returns can avoid the changed helper by an exact local proof.
The root's full symbolic runtime attempt nevertheless stopped at source ordinal
4569 (`CC2`) after 5,932 cases. Its 4,000-rule proof-construction bound did not
close that case. A subsequent literal counterexample confirms a wrong source
endpoint for that primitive interface. Blank execution also has no calibrated root seed within the
retained two-million-step run. Neither bound is a divergence proof.

## Exact proposal

[relay217.native.tm](relay217.native.tm) has 217 working states and 434 rows,
start state 0 and halt label 254. It retains the accepted
[primary K218 source](../../candidate-k218/sites218.json). Relative to that
machine, it deletes state 301 and changes these eleven retained rows:

```text
87/0 = 0 R 88      88/0 = 0 L 51      51/0 = 0 R 122
36/0 = 1 R 16     16/1 = 1 L 56
42/1 = 0 L 122    47/1 = 0 L 122     57/1 = 0 L 122
126/1 = 0 L 122  139/1 = 0 L 122    141/1 = 0 L 122
```

The first three changes and state deletion come from Source 146's initialized
core. The marker relay and six-return repair are new work by `drop_contract`.
The root independently adapted and ran the full runtime checker. The exact
[local proofs](proof.md) establish complete-tape endpoints for the marker's
right-one branch and the six returns. They deliberately leave the remaining
`108 → 10 → 16` route and the right-zero bootstrap branch open.

## Actual evidence

- The initial relay without the six return changes reaches a wrong fifth
  source frame. Adding the six redirects matches all twenty saved accepted
  source endpoints, in 26,450 physical steps. These are finite initialized
  checks, not a generic runtime proof.
- The fixed relay's first syntactically clean dispatch is at step 81,103:
  source ordinal 148, logical registers `[1,9,0,2,0,1,0,2,0]`, head −3,
  header 61, gap 0 and 59 spare blocks with values zero or one. This is an
  intermediate arithmetic configuration, not a completed initializer.
- Continuing the same blank run to 2,000,000 physical steps records 996
  complete-looking source frames without a root-shaped seed. The last complete
  frame is ordinal 168. This is a bounded observation.
- A separate source-level continuation from the first frame executes
  1,000,000 primitive source instructions, reaching ordinal 305 without an
  outer root boundary. Its transfer to the binary table is conditional on
  the missing runtime proof. At source step 613, ordinal 154 has registers
  `[1,0,67,2,0,1,0,0,0]`; the stack 67 decodes to `Q_0(F), F`. The usual
  theorem-stack invariant cannot be assumed for this intermediate data.
- The [root runtime record](evidence/runtime-attempt/runtime/runtime.json)
  reports `NOT_PROVED` for ordinal 4569, path
  `110100100111011100000101`, `CC2`, after 5,932 prior cases. The process
  exited 1 after 140.9568 seconds. The earlier per-case proof objects were
  not written on failure; the record and stdout retain the progress census.
  The [literal counterexample](evidence/runtime-attempt/literal-counterexample.json)
  uses all-zero primary registers, spare list `[0]` and gap zero. Accepted K218
  reaches the correct next source ordinal 4567 in 66 steps; the relay returns
  after 88 steps with an invalid source address and differing cells 19, 22,
  24 and 25. This refutes the unchanged source-interface contract, not every
  possible calibration of a modified source. No successful full runtime check
  is claimed.

The [seed review](seed-review/review.json) independently checks the first 629
source transitions and the stack-67 interpretation. It distinguishes the
inherited ordinary macro correspondence from a fresh binary or Lean theorem.

## Reproduction and history

The original scripts and JSON records are preserved as exact UTF-8 texts in
[history/actual-texts.json.gz](history/actual-texts.json.gz), with their paths
and SHA-256 values. Actual compressed traces are retained separately. The
longest [blank trace](evidence/blank-2m.trace.json.gz) and
[source trace](evidence/source-1m.trace.json.gz) are complete within their
stated bounds. [publication.json](publication.json) binds every file.

Two narrow recording corrections are explicit. The first prefix census stopped
at any dispatch-state return; its successor distinguishes a complete control
return from intermediate marking passes. The source-level bound record
originally reported `len(trace)-1`, a configuration index. Its corrected
[summary](evidence/source-1m.json) reports the 1,000,000 executed instructions;
the exact original source and record remain in history. No mathematical
success is inferred from either correction. An own metadata-reader AST comparison
also needed a narrow bound-expression correction; its failure and corrected
[audit](metadata-audit.json) are retained. This was not a candidate execution.

From the repository root, use fresh output directories:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/diagnose.py \
  --repo . --mode initialized --step-bound 30000 --output /tmp/relay-initialized-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/diagnose.py \
  --repo . --mode blank --step-bound 2000000 --output /tmp/relay-blank-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/source_continue.py \
  --repo . --step-bound 1000000 --output /tmp/relay-source-fresh
```

These portable successors preserve the relevant executed proof-free bodies;
path, mode, bound, input-pin and counter differences are retained beside the historical
sources. They run only literal simulations. The root's unchanged actual
runtime driver, dependency pins, stdout, stderr and failure record are under
[evidence/runtime-attempt](evidence/runtime-attempt/). Its `--baseline` input
is the recovered K221 package described in the
[accepted K218 reproduction](../../candidate-k218/README.md); its source and
table pins remain mandatory. No proof assistant, dependency rebuild, alternative
start census or further row search was run for this packet.
