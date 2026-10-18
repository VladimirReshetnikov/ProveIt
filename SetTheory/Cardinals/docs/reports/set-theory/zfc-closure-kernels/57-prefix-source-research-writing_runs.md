`WritingRuns.lean` proves arbitrary-length self-loop scans for a caller's
actual Core machine when the bit written can differ from the bit read.
The rightward theorem moves a repeated run onto the left context with its
new value; the boundary-left theorem gives the converse direction. Both
retain the absolute head and the entire finite contexts. Their Core
corollaries use the existing whole-tape `ZipRep` soundness theorem, including
all exterior cells. The zero-length case is covered.

This generic layer extends `ZipperRuns` independently and assumes only the
stated literal transition equality. It does not assume or prove a dispatch
site, reachable program counter, register operation, or consistency claim.
The immediate application is the attributed Mira-Cult/Jeff/public253 machine:
its old42 state writes ones across a zero run during literal site000.

The source compiled with the explicit absolute Lean4.32 executable in0.594s.
Four axiom audits and three caller checks passed in0.536s, including the
actual public253 right0→1 and left1→0 self-loops and the empty-run case.
Only standard `propext` and `Quot.sound` occur in the audited axioms.
No dependencies or bootstrap were rebuilt; the scoped check used the
parent's source-verified pinned cache. Exact commands, source identity,
scope and scratch logs are recorded in
`results/writing-runs-verification.json`.
