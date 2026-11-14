# IΣ₁ PAeq translation of finite-set sequents

`sequentCode` is the actual internal finite-set image of arithmetic formula
codes under `formulaCode 0`. In every arithmetic model satisfying IΣ₁,
`sequent_graph` gives its Σ₁ graph and `mem_sequentCode` characterizes its
members, including for nonstandard codes. The module proves validity,
monotonicity, empty/insert/singleton equations and compatibility with the
Foundation `setShift` operation on internally valid formula sets. The
companion `formulaCode_neg` proves compatibility with NNF negation for every
internally valid source formula.

The pinned PA196 proof was adapted to the current Foundation and PAeq
presentation. This is a sequent-image operation, not a finite PRA code or a
translation of whole LK proof histories. It does not establish a formula-graph
witness bound or either PA194 machine/consistency implication.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-sequent/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
