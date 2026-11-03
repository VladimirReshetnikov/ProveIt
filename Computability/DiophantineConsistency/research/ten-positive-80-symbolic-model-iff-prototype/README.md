# Symbolic-port 80-graph model equivalence

`Direct80SymbolicModelIff.symbolic_positive_model_iff` proves, in each
supported IΣ₁ model, that a positive zero of the selected 80-operation Lean
graph exists if and only if the represented machine halts. It assumes the
three natural port equalities for beta and the low/high masks, the exact
integer tuple equality `integerPorts p = CompactSymbolicModelIff.p`, and the
model cast `(p 1 : V) = paramKernel rho`. The proof derives the beta and
low/high model casts from the natural equalities and composes the independently
checked forward and reverse directions.

The explicit integer-tuple and second-port model-cast assumptions are part of
the theorem. This is a conditional model-level equivalence, not a Lean proof
of an internal iPRA proof. In particular, the symbolic second port differs
from the K0 coefficient in the retained 80 JSON/PDF proposal; no equivalence
for that displayed coefficient or external file binding is asserted here.

The accepted guarded run is `observations/iff-attempt04/`, which produced
`/tmp/direct80-symbolic-model-iff-r1y1zrmn/Direct80SymbolicModelIff.olean`,
SHA-256 `938e75e9120099512d87aebebb847c60d6aa06d6820eef5b7ce4f46110345fe7`.
The source and runner hashes are respectively
`61bb5f1125775ff0d0245e2b0170919c7818b3990441288621056ff92ab83097` and
`399a7ae6fe99de4098b594d31152145be491bb4ecf52401b04140569a0895661`.
Earlier observations retain the missing-provider failure and attempts that
hit the 3-GiB kernel limit while trying to discharge the complete port tuple.
The accepted check reports the listed standard Lean axioms and no `sorryAx`.
Its runner checks direct-import paths and hashes before and after Lean and
retains resource samples; transitive source/object, package and dynamic
dependency provenance remains inherited.
