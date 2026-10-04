# A bounded simultaneous two-producer search on complete84

No operation reduction occurs in the finite shared-fork grammar below. All **791** matching acyclic schedules have at least **84 live operations**: 335 have 84 and 456 have 85. This is an exact rejection certificate for the declared search, not a global lower bound, an optimization over all straight-line programs, or a new universality theorem.

The source is the actual [complete84 circuit](complete84_scaled_strong_output.md), with 84=47M+37A operations, 18 positive witnesses and exact degree187. Its complete unchanged packet is retained in the [receipt](complete84_shared_fork_scout.json). The [fresh helper](complete84_shared_fork_scout.py) reads the parent as inert bytes/JSON and executes no predecessor code.

## Authenticated source and prior scope

| Parent file | SHA-256 |
|---|---|
| `complete84_scaled_strong_output.py` | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |

The parent proof, actual84 instructions, local-producer scout, joint-root scout, joint auxiliary/strong cut and isolated first/auxiliary norm lower-bound notes were read to distinguish existing results. The earlier local scout replaces one producer with at most two gates using strictly earlier registers. The present search replaces two producers simultaneously, permits later original registers independent of both replacements, and allows a new shared intermediate with two output branches. It does not revisit independent-gamma aliases or delete any auxiliary square/product condition.

The seven excluded targets are exactly `norm_pair`, `norm_triple`, `norm_four`, `norm_product`, `all_units`, `seven_units` and `polynomial`: the six final factor-product gates and final subtraction. All other **77 producer rows**, including all seven norm/factor outputs, are targets. Thus there are **2,926 unordered target pairs**. All original finalizers remain part of the counted output cone.

## Exact finite grammar

The initial leaf list consists of all25 original free ports, all84 original output registers and exactly the six literal constants `-1,0,1,2,3,4`: **115 leaves**. A register later than a target may be used if its original dependency graph contains neither of the two target definitions. No new free port, coefficient, square or quotient is introduced.

For each pair of distinct targets, replace their definitions by this shape:

1. A shared value `u` is either a zero-gate alias to one original leaf or one binary `+`, `-` or `*` gate on two original leaves.
2. Each target output independently is a zero-gate alias to `u`, one gate `op(u,u)`, or one gate between `u` and one original leaf. Both subtraction orientations are allowed. Commutative operand-order duplicates alone are omitted.
3. Every original leaf used by the replacement must be independent of both original target definitions. All replacements are therefore acyclic after a dependency-respecting reorder.

There are at most three new binary gates. Both output branches use the shared value; an unrelated replacement circuit for one output is outside this shape. The output aliases, self-square and doubling branches are included. The explicit small constant list is a grammar restriction; arbitrary scalar constants are not being optimized.

The charge is the number of **named binary instructions reachable from the complete original output after replacing the two target definitions**, including every surviving old producer and finalizer. Aliases cost zero. The walk follows the new shared instruction and both new branches, and it discards old producers made dead by the replacements. This is not an unrestricted common-subexpression or subsequent algebraic-folding optimizer. In particular, it does not claim a lower bound for a second circuit obtained by applying additional transformations outside this named schedule.

## Exhaustive matching and rejection proof

The helper evaluates the actual full circuit at three recorded assignments, one in each of the prime fields with moduli 1,000,000,007; 1,000,000,009; and 998,244,353. All25 free ports, including the six compiler numeral ports, are assigned independently. The receipt saves the seed-derived assignments themselves. These are arithmetic diagnostics, not asserted valid compiler recipes.

For each of the **115 shared aliases** and **26,565 shared binary gates**, it constructs every possible matching branch in the grammar. The binary-prefix count is `115² + 2*(115*116/2)`: oriented subtraction and unordered addition/multiplication. For a fixed shared fingerprint u and target fingerprint t, the required existing leaf fingerprints are exactly

    t-u, u-t, t+u, t/u,

for `u+leaf`, `u-leaf`, `leaf-u` and `u*leaf`. The last division is used only in the finite-field search algorithm; it is not an instruction in any candidate arithmetic source. When any component of u is zero, multiplication cannot match: the helper explicitly requires every target to be nonzero in every field. It records **20,559** such rejected shared-value/target multiplication branches. All colliding leaves in a fingerprint bucket are retained. Alias and `op(u,u)` branches are tested directly.

The helper additionally verifies that the 77 target fingerprints are pairwise distinct and that no target fingerprint matches an original leaf independent of that target. Thus there is no missed independent original-leaf alias or reuse of the other target among the surviving branch matches. These checks do not assert general collision freedom for arbitrary polynomials.

All matching branches are paired, the exact dependency masks reject cycles, and the complete output liveness is recomputed for each remaining schedule. The result is:

| Quantity | Result |
|---|---:|
| Shared prefix schedules | 26,680 |
| Acyclic matching two-output schedules | 791 |
| Target pairs with at least one match | 148 |
| Matches with 84 live operations | 335 |
| Matches with 85 live operations | 456 |
| Matches below84 | 0 |

Here is the logical force of the finite calculation. Every all-ring polynomial identity in this grammar must agree at all three field assignments. Therefore any true two-output rewrite appears among the retained fingerprint matches. Fingerprint collisions can only add candidates, and every added candidate is still charged. Since **none** of the retained candidates has fewer than84 live instructions, no true identity in the declared grammar lowers the cost. The surviving matches need not be proved polynomial identities to obtain this negative conclusion. The procedure uses exact field arithmetic, not cryptographic hashes as equality tests for expressions.

Relations valid only for selected fixed-program numerals or only on the parent's positive zero set need not survive these arbitrary free-port assignments and are deliberately outside the conclusion. So are positive-coordinate charts, four or more new gates, a branch depending on the other new output, larger simultaneous cuts and unrestricted later arithmetic synthesis.

## Replay and status

The standard-library CLI requires `--root` and exactly one of `--expect` or `--output`. It authenticates the full parent trio and the receipt's parent self-source pin. Duplicate JSON keys and nonfinite JSON numbers are rejected; receipt equality is recursively type-exact, and all checks remain active under optimized Python.

```sh
fork_wip=/absolute/path/to/native-stream-queue
python3 "$fork_wip/complete84_shared_fork_scout.py" \
  --root "$fork_wip" --expect "$fork_wip/complete84_shared_fork_scout.json"
python3 -O "$fork_wip/complete84_shared_fork_scout.py" \
  --root "$fork_wip" --expect "$fork_wip/complete84_shared_fork_scout.json"
```

Fresh normal and optimized exact receipt replays from `/` both pass. No frozen source or repository file is modified. The established universal bound remains84; this packet records a larger but still sharply limited failed sharing search.
