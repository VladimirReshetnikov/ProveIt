# Primitive-recursive evaluator for the PA194 Foundation LK budget

`treeOf` turns any actual current-Foundation LK derivation into a finite
annotated tree recording the sequent-depth contribution and the budget effect
of each inference. `treeOf_correct` proves that evaluating this tree computes
exactly `listFoundationBudget` from the list-based PA194 LK compiler.

`treeCode` gives these trees an explicit natural-number code. `budgetCode` is
a total numeric evaluator; Lean proves it primitive recursive by a coded
recursion table and proves `coded_treeOf_correct`:

```
budgetCode (treeCode (treeOf d)) = listFoundationBudget d
```

for every actual Foundation LK derivation `d`. The earlier source-depth
package proves primitive recursiveness of computing the individual node
annotations from lists of encoded formulas.

The evaluator, table-step and coded-correctness theorems report
`[propext, Classical.choice, Quot.sound]`; `treeOf_correct` reports
`[propext, Quot.sound]`. The ordered local overlay check passed with no
`sorryAx`. The full nested standalone script has not yet been replayed.

The tree code is an auxiliary annotated skeleton, not yet a primitive-recursive
translation from a fixed encoding of Foundation derivations. This package does
not prove the whole budget or proof compiler primitive recursive as a function
of proof codes, internalize correctness in PA/PRA, or establish PA194 machine
calibration. No relation is asserted for invalid skeleton codes.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-lk-budget-primrec/check.sh`.
