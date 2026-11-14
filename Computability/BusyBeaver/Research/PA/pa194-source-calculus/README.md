# PA194 source-syntax and quantifier compatibility

This package ports the PA196 snapshot's relational source encoding and
finite-proof components to the PA194 calculus, using the repository's
Lean 4.32 `LO` Foundation API. It checks source formula encoding and
substitution, fresh-name allocation, universal instantiation,
generalization over a negative context, pointed formulas, negation, and
existential instantiation. The quantifier results construct finite PA194
calculus derivations; their source formulas are actual `LO.FirstOrder`
semiformulas. The full source LK proof compiler, PA/induction supplier,
refutation reduction and internalization in PRA remain open.

The two source-syntax files adapt the pinned upstream M6PA files by changing
`FFL` to `LO`, removing an unused arithmetic-interpretation import and using
the current Foundation syntax directly. The PA194 relational files adapt
the pinned upstream PA196 files to the independently checked PA194
interfaces. `SourceNegation` additionally includes the upstream elementary
double-negation introduction and explicitly types two intermediate steps
for Lean 4.32. The source hashes in `upstream.sha256` identify the adapted
inputs, not a claim that the two Foundation versions are identical. In
particular, the old arithmetic named-interpretation module has not been
ported.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited
Lean 4.32 Foundation objects and run `bash
Computability/BusyBeaver/Research/PA/pa194-source-calculus/check.sh`. The
script builds in tmpfs, rebuilds the entire relational prerequisite chain,
checks source pins and rejects `sorryAx` in printed theorem dependencies.
The full nested `pa194-source-separation/check.sh` replay passed, including
this package and all of its prerequisites. The checked theorems are
ordinary Lean theorems, not proofs internal to PA, PRA or iPRA.
