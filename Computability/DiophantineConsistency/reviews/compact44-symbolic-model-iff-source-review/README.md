# Source review: conditional compact symbolic model equivalence

Reviewed `research/ordinary12-ipra-bridge/compact44-symbolic-model-iff-prototype/CompactSymbolicModelIff.lean`
at SHA-256
`481b94d4cb0eeb5d3aec2f4a48ce1ec2844dabdf22eac19089353efec4f28042`.
The live source and `/tmp/compact44-symbolic-model-iff-author-7_4gafyu/CompactSymbolicModelIff.lean`
matched that hash; the live object SHA-256
`b7d9867f6437385a7f7f51478337d08317b2beed660d5f63050b545c3272805a`
matched the successful author receipt. This is a source/interface review, not a
fresh Lean replay or a full dependency-closure audit.

The local definition `p` is exactly the pointwise integer cast of
`ports betaNat (paramKernel rho) lowNat highNat`. The `ports` definition has
fourth entry `betaNat+highNat`, so the already shifted fourth port is used
once in both local directions. `FixedGraphMarkedHaltDraft.graph_halts` accepts
the same symbolic tuple, the same positive 12-coordinate valuation and
`InternalZero`, and produces an actual model time at which the 215-state
machine's first component is zero. Conversely,
`halt_positive_zero_of_ports` supplies a positive zero of the same literal
for the supplied halt time, and the caller provides `hbeta T` and the other
three port hypotheses exactly as required.

The theorem retains `hbeta` for every internal model time and explicit K,
low-mask, and once-shifted high-mask difference-ring cast equalities. The
reverse theorem does not need those extra assumptions. These hypotheses are not
proofs of displayed-coefficient calibration, and the result is an equivalence
in arbitrary `IΣ₁` models, not yet an iPRA derivation. No local mismatch was
found. Review independence is limited: this reviewer authored the upstream
halt-to-positive-zero client and several graph bridges; the reverse graph-halt
source and this two-line composition were authored by others. No independent
reconstruction of the reverse provider, package-transitive/dynamic dependencies,
or retained equation bytes was performed.
