# Trace75 direct-BFS anchor parity

`Trace75BFSSimpleParity.graph_simple_parity` is Lean checked in every
`IΣ₁` model. Under the four exact symbolic direct-BFS port equalities and
a positive trace75 zero, it obtains one common positive repunit length N,
the radix and residual-power identities, indexed carry input, and the
carry bound and evenness conclusions at phases 2195 and 3296. The proof
identifies the independently selected lengths through the common radix.

The author check passed with tool-observed outer exit 0 and child, Lean,
and header exit 0. `observations/attempt01/result.json` has SHA-256
`b02af2fb1a9610dc523c1d3e6582a680811bb0966fe6cdf463bddd5435d99b01`;
`observations/outer-attempt01/terminal.json` has SHA-256
`9cccfed92c8af9105c754b8e083f824903598e82ab9995742ab12a2e2e25252e`.
The object `/tmp/trace75-bfs-simpleparity-klgreprj/Trace75BFSSimpleParity.olean`
has SHA-256 `c6067db34633e8bb3bd9e0efbd11c61effabd3564346f0877430b51a21944b67`.
Independent post-audit passed in
`reviews/trace75-bfs-simple-parity-result-independent/`.

The pinned runner checks the fresh support, carry and fixed-slots results,
the 1,977-object fresh union and 80 outside providers, and the captured BFS
`DirectBFSRawParity` and `ParityColumns` subtrees including companions.
The preflight and 18 policy controls passed. Historical unrebuilt-source,
package and dynamic ancestry and external coefficient-file binding remain
outside this check. This is not a machine-halt or iPRA theorem.
