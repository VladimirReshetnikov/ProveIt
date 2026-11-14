# Conditional PA194 source/parent halting equivalence

`PA194SourceHalting.lean` adapts the upstream source-halting induction to the
exact unfolded PA194 parent. Given the explicit `Coverage` premise for every
source instruction, `source_halts_iff_parent` proves standard-Lean halting
equivalence between any source configuration and its corresponding parent
frame, for arbitrary valid full register files and gap parameters.

The `Coverage` premise is not discharged here. The full checker in
`../pa194-coverage` is designed to establish it after all 3,673 site checks
succeed. This theorem does not itself establish a blank-start result, an
internal PA/PRA/iPRA statement, or consistency equivalence.

A fresh pinned-source rebuild can be run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-source-halting/check.sh
```

The source module was Lean checked against independently rebuilt private
upstream and machine dependencies. The full rebuild is provided for a later
sequential check while the larger coverage run is active.
