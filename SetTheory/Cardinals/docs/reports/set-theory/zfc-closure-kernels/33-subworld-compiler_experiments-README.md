# Complete-logic compiler experiments

These experiments retain equality and the two atomic-vacuity components.
The 268 control is prior ProveIt work, reproduced here. The protected
quantifier-basis variant measured here reaches 269 working states.
Neither is a new literal machine with a proved ZFC consistency endpoint.

The driver uses the pinned source closure under ../sources/proveit.
All dependencies are recorded in UPSTREAM.json and checked by the root
reproduce.py driver. ProveIt sources have exact Git blob checks; Wade's
five original inputs and the published logical spec have SHA-256 guards.

## Fixed, quick replay

From the archive root:

~~~sh
python3 -B compiler_experiments/basis_experiment.py \
  --basis original \
  --recipe compiler_experiments/original_expanded/results.json \
  --iterations 0 --output /tmp/zfc-original-replay

python3 -B compiler_experiments/basis_experiment.py \
  --basis protected \
  --recipe compiler_experiments/protected_correct_cost/results.json \
  --iterations 0 --output /tmp/zfc-protected-replay
~~~

Expected counts are 268 = 206 decisions + 62 framework states, and
269 = 207 decisions + 62 framework states. The general cost is decisions
+ 55 + max(2, maximum consecutive zero-edge dispatcher depth).

Each replay verifies the symbolic AX output, the silent/closed macro contract,
exact grammar expansion, re-extraction of all compiled decision edges, and
the literal table count. It does not prove unbounded register-machine or
Turing-machine simulation.

The original search used 80,000 proposals; the protected search used 40,000.
Both use random seed 161026. The protected run predates the optional macro
expansion search dimension added for the original run; its recorded recipe
remains exactly replayable, but rerunning the final broader search driver
from its initial seed is not asserted to reproduce that earlier search
trajectory. The complete selected recipes and actual improvement histories
are preserved in results.json and search_checkpoint.json.

The one undefined 1.inc/read-1 transition is normalized to write 1, move R,
and enter the terminal state. This preserves the tape under the inherited
undefined-transition-halts convention, adding one final move.

## Protected basis

The alternative replaces the affected three quantifier/falsity rows by:

~~~text
Bottom -> B
((All x (All y (Not (All x (All y A))))) -> All x A) -> A
All x (All x A -> B) -> (All x A -> All x B)
~~~

The intended parentheses are fixed unambiguously by logical_rows_ast in the
results and by setup() in the driver. This follows the ordinary protected
Metamath ax467 / ax-5o basis with explicit Bottom elimination; all original
equality rows remain. It is an ordinary logical basis experiment, not a
new Lean theorem about the numerical engine. Removing the old rho6 without
restoring its falsity role would invalidate that basis argument.

The named, normalized, label-map and decision-graph artifacts are all included.
The final fixed replays reproduce their bytes exactly.
