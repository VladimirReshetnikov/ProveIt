# Intake 184: three alternative 221s and their reduction research

Placement [`abae578c29`](https://github.com/VladimirReshetnikov/ProveIt/commit/abae578c2944f6475341cca519bf1249d52187ad) imports `K221_Alternatives_2026-10-20.zip` from arrival [`a27b5391bb`](https://github.com/VladimirReshetnikov/ProveIt/commit/a27b5391bb) as **Source 137**, prefix `137-k221a-`, and retires that ZIP. This batch brings the host to **137 sources**, with the collection unchanged at **290 reports**. The [placement map](data/intake184-placement.json) accounts for all **191 members**:

- 156 new ancillary files: 4 at the host root, 19 code files and 133 data files;
- 31 exact aliases to existing files;
- one history alias, the vendored Source-132 K221 archive at arrival `c011e44bc2`;
- three archive-only originals: the main report, its PDF and the delivery README.

The placement commit explicitly deferred analysis and verification. This reconciliation completes its written account. A later read-only intake check compared every member with the original arrival bytes: all ordinary targets match both the placement tree and snapshot `a17e6c8f99`, and the vendored ZIP matches its recorded arrival object. No missing or changed placement payload was found. That file accounting is separate from the machine proofs and replay receipts below.

## Three tables, the same size and source

Source 137 gives three literal alternatives to [Source 132's K221](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k221/README.md). Each retains 221 working states, 442 rows, the same 4,744 primitive occurrences and guarded source program. Native labels in the following table are not canonical state numbers:

| Variant | Old row | New row | Canonical table |
|---|---|---|---|
| `row103` | `103/1: 0 L 162` | `103/1: 0 L 142` | [table](data/137-k221a-machine-row103-k221.tm) |
| `row157` | `157/1: 1 L 148` | `157/1: 1 L 187` | [table](data/137-k221a-machine-row157-k221.tm) |
| `both` | Both rows above | Both replacements | [table](data/137-k221a-machine-both-k221.tm) |

The canonical tables differ from one another and from the baseline; they are not state renamings. Each uses working labels 0–220, start 0, dispatcher 22 and separate halt label 221. Native dispatcher 84 and terminal 254 are inherited labels. Raw transition-graph reachability does not assert that the blank computation visits every state.

The state-103 change uses an inductive invariant: whenever the old run reaches that state, the left neighbor is 1. After the changed first step, states 162 and 142 therefore both read 1 and both take `0 L 27`. Two old and two new steps reach the same state, head and entire tape.

For state 157, split on the left neighbor. On 0, states 148 and 187 both take `0 R 186`, giving a two-step join. On 1, the new route takes `187/1: 1 R 76`, then `76/1: 1 L 148`. Three new steps reach exactly the configuration after one old step; the initial write supplies the required current 1. No other tape cell changes.

The [macro checker](code/137-k221a-portable-verify_alternate_rows.py) derives and separately checks the old constant-bit invariant from unrestricted state 0. It checks the simultaneous variant as well as the two individual variants. The [independent window checker](code/137-k221a-portable-check_joint_fold.py) starts with every radius-five binary window, verifies transition closure and requires positive common-endpoint blocks before any read beyond the window. Its untouched exterior is arbitrary. These are ordinary universal local-simulation arguments, not agreement on selected numerical runs.

The resulting claim is **halting equivalence from state 0 for every initial binary tape and integer head position**. It is not equivalence from arbitrary control states. Positive block lengths prevent an infinite execution from being hidden by zero-progress matches. Composition of the two changes is checked explicitly: individually neutral rewrites cannot generally be combined without checking their intervening helper paths.

The delivered [macro receipt](data/137-k221a-verification-alternate_rows_proof.json) and independent receipts record the proof checks. The [clean replay record](data/137-k221a-verification-clean_replay.json) reports six native/canonical startup checks reaching the complete old frame after **409,835 steps**. These remain **delivered results** in this reconciliation; the intake's read-only source and placement review did not execute that driver or rederive those results. The full-tape startup check is additional evidence, not a replacement for the unbounded equivalence argument.

## Retained research beyond the three alternatives

The secondary material contributes more than search counts. Its limitations remain part of the record.

**Neutral rewrites and allocation.** A [separate catalogue](data/137-k221a-research_sub221-runtime-neutral_universal_audit.json) certifies 516 single-row replacements individually under an all-tape window invariant. These are reusable local lemmas, not a simultaneous replacement theorem. The corrected allocator retains intermediate helper dependencies and distinguishes decoder validity from primitive-entry validity. Ten grammar layouts and a rho6 parameter-swapped source have decoder/source evidence but lack candidate-specific binary runtime and startup proofs; see the [exploratory README](137-k221a-exploratory-README.md).

**Seed-relative source simplification.** The [specialization audit](data/137-k221a-research_sub221-specialization_audit-AUDIT.md) gives an abstract invariant with exact buckets 0–7 and one bucket for every natural value at least 8. It checks closure of every enabled guarded edge. This supplies `R6 = 0` at the comparison entry and identifies two reachable zero-branch no-ops with unreachable bodies. Their quotients preserve the other register operations and collapsed successors; removed reachable segments are finite, nonhalting and leave all registers unchanged.

The same audit replaces the twelve-leaf constant-one comparison by a six-leaf test. Under the essential entry premise `R6 = 0`, it halts exactly when initial `R5 = 1`; otherwise it returns, with `R5 = R6 = 0` and every other register preserved. The clear-loop argument is an induction on arbitrary natural input, beyond the supplementary finite samples. The counterexample `R5 = 2, R6 = 1` refutes an unrestricted equivalence claim. The full replacement already contains one of the no-op deletions, so its saving cannot be counted again. Combining it with the other cleanup requires the literal combined control-flow check.

**An admissible alternative startup, with a remaining runtime failure.** Removing native scanner state 50 produces a 220-state experiment and a complete clean startup after a reported 108,420 steps, with logical seed `(4,3,0,0,3,0,0,0,0)`, header gap 8 and 61 value-one spares. The [shortened-startup audit](data/137-k221a-research_sub221-specialization_audit-shortened_boot_audit.json) and the specialization note explain why this seed is sound and complete for the current calculus: code 3 is equality reflexivity, and the compiling refutation candidate is at least 32, above the enumeration cutoff 4. These arguments retain the inherited logical calibration and clean-boundary premises. **They do not certify that table:** the unchanged source still fails a required six-zero-address runtime case. Nor may its startup be reused automatically after changing the source layout.

**Negative and incomplete searches.** Source 137 distinguishes exhausted finite proposal families, heuristic beams, capped searches and interrupted frontiers. Its register permutations retain fixed handlers; its relaxed-spare screens use bounded finite frames and run budgets; the five-zero parser and annealing search remain partial. These are useful restrictions on the tested designs, not state lower bounds. The [research README](137-k221a-research_sub221-README.md) and [decoder status](data/137-k221a-research_sub221-decoder-FINAL_STATUS.json) retain the scopes. The current metadata map also preserves historical scripts, raw logs, counterexamples and failed specimens without treating them as accepted machines.

## Relation to the new 220 deliveries and formal work

The paper's statement that no correct construction below 221 had been obtained belongs to its pinned snapshot. Two newer K220 packages are being reconciled in batch 185. Source 137 itself does not save a state, and its failed scanner experiment must not be confused with that newer construction. Its continuation variants and source-specialization techniques remain useful independently of the superseded record count.

The inherited mathematical endpoint is an ordinary equivalence formalizable in ZFC between blank nonhalting and `Con(ZFC)`. The unchanged calculus/source and the new all-tape equivalence transport that endpoint to the three variants. The package supplies **no newly compiled exact-byte Lean or Rocq endpoint for those variants, no internal PA endpoint, no unconditional nonhalting theorem and no minimality result**.

The baseline Source-132 table subsequently acquired a [closed Rocq endpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/README.md), independently rechecked with `coqchk`, as recorded in the maintained candidate README. Preserve that established result beside the new ordinary reductions. It does not by itself make Source 137's rewritten tables, or the newer 220 tables, newly checked kernel endpoints. The K-family Lean program/calculus work has its own explicit scope and evidence.

## Attribution and recovery

The paper reviewed ProveIt at `c011e44bc2df6238940bb600833730873b308334`. Its formal predecessor is Elliot Glazer's k230-rocq commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`. The equality merge, witness-request source and K221 reduction retain their predecessor credits. Source 137 contributes the continuation alternatives and the secondary research identified above; see its [NOTICE](137-k221a-NOTICE.md) and [provenance](data/137-k221a-PROVENANCE.json).

Recover the complete original layout outside the repository from:

```sh
git show a27b5391bb:docs/incoming/K221_Alternatives_2026-10-20.zip > /tmp/K221_Alternatives_2026-10-20.zip
```

The placement map records every original member, destination or history alias. The parent ZIP is also independently recoverable from `c011e44bc2:docs/incoming/K221_Construction_2026-10-20.zip`. Delivered files were not edited to accommodate flattened placement names. Run any reproduction on a disposable extraction in its original layout, with output outside it and Python assertions enabled. Some secondary research paths refer to the author's original workspace and are not standalone release drivers; the paper and research READMEs distinguish those from the portable alternatives replay. No checksum-manifest or line-ending validation is part of this intake.
