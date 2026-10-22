# Fifteenth K215 proof-simplification checkpoint

Both incremental checks pass for shared transfinite recursion, shared quotient
syntax, a smaller PowerSets import boundary and the shorter dense-machine proof.
The exact 215-state machine and both endpoint statements are unchanged.

The nine selected Lean files remove **11,809 bytes and 283 lines**. Synchronizing
the maintained quotient producer adds **1,307 bytes and 12 lines**, leaving a net
maintenance reduction of **10,502 bytes and 271 lines**. There are ten checked
writes and no retirements. The endpoint shrinks from **178 to 176 project modules**,
selecting **2,052,142 source bytes**, 40,970 fewer than phase14. Five decoder-prefix
modules remain separate. These dependency and physical-source measurements have
different scopes and must not be added together.

The proof changes share four arguments:

- `InternalRank` proves relation-parametric transfinite recursion once and
  specializes it to the cumulative hierarchy; `TransRec` specializes it to
  the operation hierarchy. The original
  semantic formulas, existence, uniqueness, specification and monotonicity
  interfaces remain available. Definability, set-section and regularity premises
  are retained where needed. Uniqueness requires neither definability nor the
  set-section premise; monotonicity follows from predecessor inclusion and does
  not assume the operation itself is monotone.
- `QuotientModel` supplies the hypothesis-free formula translation and
  satisfaction syntax also used by `KQ1Model`. Pointwise membership
  indiscernibility gives equal quotient environments, so both congruence proofs
  follow from their existing satisfaction theorem. The weak lane still assumes
  only `QHyp`; it does not acquire CP/GIC hypotheses. Membership well-definedness
  precedes satisfaction, so this argument is not circular.
- `PowerSets` moves one definition into a small module while preserving its
  qualified name and body. The endpoint model imports that module instead of the
  full calibration. An explicit client still imports and checks the complete
  calibration interface, accounting for three additional primary project modules.
- `KDenseBridge.blank_iff` uses one stopped-or-synchronized invariant for both
  directions. The Source193 ending evaluates it one step after a sparse stopping
  witness. It saves another 204 bytes/eight lines over the initially selected
  Source192 ending, with the same generic hypotheses and statement.

The recursion proposal comes from `55f600fe7e`, retained in the
[phase13 arrival history](../phase13/upstream-merge/later-c3caaf/merge.json).
The `7f3942117f` quotient-sharing proposal is preserved in the
[phase14 merge history](../phase14/upstream-merge/later-406c/merge.json).
The [Source192 reconciliation](../../../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-214.md)
records the PowerSets/dense proposals. [Source193](../../../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-215.md)
supplies the further dense ending. Its residual-site replacement, subtree
abbreviation and Source194's scheduler refactor remain separate proposals.

| Scope | Actual selected compilation evidence | Typed checks |
| --- | --- | --- |
| Primary: 184 project modules plus ten API clients (194 providers) | 45 fresh records: 19 from run1, 25 from run2 and one from run3; 149 exact phase14 providers | 34 retained and 28 new API reports; two fresh endpoint clients with ten unchanged reports |
| Compatibility: 69 project modules plus two clients (71 providers) | Six fresh, 54 current-primary and 11 phase14 records | Ten old model/native client reports and five existing WFTheory reports |

Together the scopes bind **199 distinct project modules**, with observed outer
exit zero for both successful runs. The primary project scope is the 176-module
endpoint, five prefix modules and
three full-calibration continuity modules. All nine site batches preserve their
exact source/import/object bindings and **6,176 outcomes**; they were inherited,
not recompiled in this checkpoint. Source changes force affected descendants to
be checked even when an intermediate object is byte-identical.

The 28 new API reports comprise four empty profiles, three using only
`Classical.choice`, four using `propext` and `Quot.sound`, and 17 using exactly
`propext`, `Classical.choice` and `Quot.sound`. Three definitional-shape clients
contain `Classical.choice` through the chosen definitions appearing in their
types; they are not claimed axiom-free merely because their equality proof is
reflexive. The 34 older API reports and ten endpoint reports keep their exact
profiles. API and endpoint clients have zero warnings. The primary project logs
contain 19 warning occurrences: nine in fresh records and ten inherited.
Compatibility has seven warning occurrences, all inherited; its fresh modules
and clients have none. Its ten client profiles and five WFTheory profiles retain
their exact previous assumptions.

Two failed primary attempts remain failures. Run1 exposed an existing reliance
on a transitive import in `KQ1ZF`: after the import cut, the required completeness
theorem needed an explicit `FirstOrder.Completeness` import. The narrow repair
changes no declaration body or statement. Run2 reached all production candidates
but the new quotient API client lacked namespace openings. Its correction changes
only those openings. The accepted selection combines the exact successful records
from both runs with the corrected final client; no failed output or `sorryAx`
report is treated as a certified provider. The third run also freshly checks both
unchanged endpoint clients. All raw failures, snapshots, logs and initializer
bindings are retained without rewriting their statuses.

The inspected maintained `generate_kq1.py` successor changes only the shared
syntax branch and preserves all six output destinations. Its isolated reproduction
checks are separate from the proof compilers. Neither a supplied renderer nor
archived executable is used as proof evidence.

[Adoption](integration/adoption.json) identifies the nine exact checked source
writes and reproduced producer, retaining their before-bytes. The
[root actual review](integration/root-actual-review.json) and
[current-source binding](integration/current-review.json) check the selected
records and adopted tree. The [Lean execution packet](lean/README.md) is complete:
collection and both the owner and independent saved-reader checks with `--repo`
pass against all 199 current project sources. Its 343-member archive distinguishes
accepted records from both failed proof attempts; predecessor phase14 evidence
remains referenced in place. The first metadata capture also remains a failed historical record: it
needed explicit hash-bound references for two predecessor audit logs. That routing
correction changed no proof source or compiler result. The saved-reader checks
verify recorded evidence and current bytes; they do not rerun Lean.

The [previous checkpoint](../phase14/README.md) remains an immutable historical
record. No Rocq production source, literal machine, endpoint axiom profile or
internal PA/ZFC proof claim changes. The broader proof-shortening goal remains
active.
