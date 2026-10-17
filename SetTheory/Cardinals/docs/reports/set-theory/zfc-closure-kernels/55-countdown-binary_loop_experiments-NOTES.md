# Binary countdown acceleration: 181 new guarded contracts, no full survivor

This extension proves **181 source-case contracts** that the earlier constant
offset oracle rejected. It does not produce a fully verified machine below
252 states. The useful advance is an executable, universally checked binary
countdown rule that can express a register transfer or clearing operation as
an affine matrix. The earlier source-loop catalogue alone did not supply this
binary execution proof.

All state labels below are the frozen old labels. Inputs come from ProveIt
commit `43026ff42f0939f09b9e95495248cfadcad38e38`; the baseline hashes are checked
by `binary_experiments/common.py`. A fold `d -> r` deletes working state `d`
and redirects its incoming transitions to `r`. Every used protected box row
is checked unchanged. The proof boundary remains the inherited full-tape
box contracts and ordinary symbolic reasoning, without a new kernel proof.

## Exact scope and results

The input is the completed uniform-fold ledger in
`loop_experiments/final/journal.jsonl`. We select its 51,290 first rejected
cases whose previous result was either exhausted symbolic fuel or an
undetermined sequential decrement guard. Each diagnostic has a budget of
1,000 symbolic rules. If a decrement guard is unknown, the diagnostic
explicitly restricts the original input interval to its positive branch.
The complementary inputs are not thereby certified.

| First diagnostic result | Cases |
|---|---:|
| Countdown-shaped first repeated interface | 9,253 |
| Repeated interface with zero net primary effect | 4,193 |
| Repeated interface with another primary effect | 1,006 |
| Blocked before an observed recurrence | 36,838 |
| Total selected first failures | 51,290 |

The blocked group consists of 36,659 exhausted budgets, 157 unsupported box
operations, and 22 unknown affine-run lengths. These are checker outcomes,
not conclusions about concrete halting.

All 9,253 countdown-shaped bodies pass a separate universal replay under a
preserved register invariant. Of these, 9,239 also have a universally
verified clean zero exit. The other 14 fail this zero-exit rule: two repeat
an abstract zero-exit interface and twelve encounter a blocked symbolic
execution. Among the 9,239, exactly 9,101 retained prefixes cover their full
original source-case domains. Exactly 138 endpoints match an exact positive
source summary, including the PC, gap, and all nine affine matrix rows.
All 138 also satisfy full prefix coverage.

We then resume each of those 138 folds on its remaining affected source
cases, using the same narrow rule again whenever the conventional checker
fails. This is an adaptive continuation, not a one-case override. In five
rounds, 568 conventional affected-case checks yield 58 fresh countdown
candidates and 43 additional complete source-case contracts. Every recipe
eventually fails the stated rule:

| Final remaining-case result | Recipes |
|---|---:|
| No countdown shape at the new failing case | 123 |
| Clean accelerated endpoint fails exact source comparison | 15 |
| All affected cases pass | 0 |

The first group contains 108 exhausted budgets, four unknown right-run
lengths, and eleven zero-primary recurrences. The total number of newly
proved guarded contracts is **138 + 43 = 181**. No bootstrap or complete
machine theorem follows from these local certificates.

## The rule actually checked

An observed cutpoint contains the exact working state, which side of the
head is being normalized, and the entire canonical tape interface relative
to that head. The finite left context, PC/header/gap information, and plain
box status must all recur. Only the nine primary-register effects are
erased when comparing shapes. The spare suffix and absolute head witness
are existential in the frame relation. Translation equivariance permits
the next interface to use its actual head as witness; no physical reset or
tape reconstruction is inserted into the machine execution.

For a candidate counter `r`, one cycle must have net primary shift `d` with
`d[r] = -1` and all other entries nonnegative. We derive an invariant `J`
consisting of natural lower bounds and, where necessary, fixed values on
unchanged noncounter registers. A zero-tested noncounter may not grow over
the cycle. Every counter guard in the positive body must hold even when
its entry value is one. The positive body is replayed with counter interval
`[1, infinity)`; the zero exit is separately replayed with counter exactly
zero. Unknown guards are rejected in both replays.

If both replays pass, induction on the current counter gives

`R_r := 0; R_i := R_i + R_r(entry) * d_i` for `i != r`,

followed by the verified zero-exit constant effect. Each cycle has positive
literal binary progress, and each positive decrement appends a valid zero
spare. The preserved complete relative interface permits iteration for an
arbitrary finite counter. See
`proof_audit/binary_countdown_acceleration.md` for the precise theorem.

This lemma is distinct from a whole source-case certificate. We additionally
check that every input allowed by the original source-case intervals is
allowed by the retained prefix constraints, and that its current register
image satisfies `J`. Finally the output must equal an exact source target:
same PC, same gap constant, and identical affine matrix after substituting
only singleton entry-register facts. Source target clocks have a positive
lower bound. Positive-branch selection alone never passes this coverage
check.

## Worked new contract: fold 78 -> 11, case 8231

The original source case is `CC 2` at path `111010010111111`. The observed
cutpoint is already its initial dispatch, so this example has no selected
prefix. The invariant for its binary countdown is simply that all nine
primary registers are natural numbers.

For every gap parameter `g >= 0`, the exact positive-cycle replay returns
to the same complete dispatch interface with

`R_8 := R_8 - 1; R_7 := R_7 + 1`,

and every other primary register unchanged. It explicitly counts 451
literal binary transitions per cycle, in addition to protected box and
affine-scan steps. The separate zero exit explicitly counts 209 literal
transitions and returns to PC `111010011` with gap constant 40. Thus for
`m = R_8(entry)` the complete matrix effect is

`R_8 := 0; R_7 := R_7 + m`,

with all other rows unchanged. The exact source summary reaches this same
frame in `3*m + 2` source instructions. Its positive source clock is
therefore uniform, including `m=0`. The full trace, invariant, body, zero
exit, and source target are retained in `worked_certificate.json`.

This is a valid new guarded contract of the 251-state folded table. The
fold still fails the later case 8227 (`CC 2` at path
`1110100101110111`): after 1,000 diagnostic rules it has made 664 explicit
literal transitions without reaching an eligible repeated plain-box
interface or accepted endpoint. The local contract therefore does not
establish the requested 251-state construction.

A useful contrasting diagnostic is fold `10 -> 14`, case 2/path `001`.
Its universal positive body clears physical register 1 with 114 explicit
literal transitions per cycle, but its gap has become a run of ones.
The zero branch repeats an abstract interface instead of supplying the
required clean exit. A repeated counter loop alone is insufficient.

## Artifacts and reproduction

The retained result JSON uses compact whitespace so individual files remain
practical for repository storage; no certificate fields are omitted.
Paths in the stored main manifests are relative to the archive root.

| Artifact | Purpose |
|---|---|
| `trace_cutpoints.py` | AST observer of the inherited literal/scan executor |
| `positive_traces/journal.jsonl` | Every selected diagnostic outcome |
| `positive_traces/results.json` | Counts, exact examples, all 9,253 cutpoint records |
| `check_countdowns.py` | Universal invariant/body/zero-exit replay and matrix comparison |
| `certificates/results.json` | All 9,253 replay results and the 138 first contracts |
| `certificates/matrix_reference_targets.json` | Exact source targets used by those comparisons |
| `screen_remaining.py` | Adaptive remaining-case continuation of the 138 recipes |
| `remaining_cases/results.json` | Every final rejection and all 58 fresh countdown records |
| `remaining_cases/matrix_reference_targets.json` | Combined source targets for the continuation |
| `verify_diagnostics.py` | Freshly replays all 181 proved contracts and checks accounting |
| `verification.json` | Successful ordinary replay, including 8,391 baseline observer comparisons |
| `worked_certificate.json` | Complete worked 78 -> 11 case and its later obstruction |

From the extracted archive root, the quick verification is:

```sh
python -B binary_loop_experiments/verify_diagnostics.py
```

It compares the instrumented executor against the inherited original on all
8,391 baseline guarded cases, then freshly replays the 181 retained prefixes,
positive bodies, zero exits, domain-inclusion checks, and full source matrix
comparisons. It also checks the 51,290-entry diagnostic accounting and the
remaining-case totals. It writes no bundled file. This run passed in about
11 seconds in the development environment.

The complete bounded search can be reproduced into fresh directories:

```sh
python -B binary_loop_experiments/trace_cutpoints.py --output /tmp/p252-loop-traces
python -B binary_loop_experiments/check_countdowns.py --input /tmp/p252-loop-traces/results.json --output /tmp/p252-loop-certificates
python -B binary_loop_experiments/screen_remaining.py --input /tmp/p252-loop-certificates/results.json --references /tmp/p252-loop-certificates/matrix_reference_targets.json --output /tmp/p252-loop-remaining
```

The first search took about 66 seconds, the universal replay and target
comparison about 53 seconds before compact serialization, and the adaptive
continuation about nine seconds. Timings are informational. The reproducible
claims are the exact bounded scope, retained universal contracts, accounting,
and final lack of a surviving recipe in this continuation.
