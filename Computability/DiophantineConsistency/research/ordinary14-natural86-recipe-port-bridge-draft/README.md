# Natural-86 closed recipe-port bridge: source draft

This proposed source adapter instantiates the natural-input 86 graph at
`CompactBytePortsModelIff.byteP`, the tuple of four base-256 decodings of
closed Lean lists. `byteP_eq` identifies that tuple with the exact
`CompactSymbolicModelIff.p` used by `Natural86EndpointDraft.expression`.
Rewriting that equality proposes the same model bridge and native, standard,
and equality-only biconditional declarations for the recipe expression. No
additional positivity shift is applied.

The underlying `CompactFourPortByteAssembly2.decode_ports` combines the
individual beta, kernel, low and shifted-high recipe decoding declarations.
The fourth decoded value is `betaNat + highNat`; it is not shifted again.
These source declarations avoid expanding the huge integers. The existing
historical P72 recipe-endpoint review records an earlier Lean run for its
own adapter, with its stated provider limitations; it is not a compilation
of this draft or a coherent-provider audit for the natural-86 chain.

`check_source.py` checks literal interfaces and pins the named source files;
its receipt does not elaborate Lean, inspect transitive object ancestry, or
prove the declarations. All natural-86 and endpoint source dependencies
remain unelaborated in this route. No operation-count or degree theorem is
established here. The closed lists are internal recipes: the source does not
read or identify physical raw, gzip, JSON or PDF bytes. A physical binding
requires separately modeled and justified connections; external hash and
payload checks alone do not establish one in Lean.

Independent source review: [natural86 recipe-port bridge](../../reviews/ordinary14-natural86-recipe-port-bridge-draft-independent/README.md).
