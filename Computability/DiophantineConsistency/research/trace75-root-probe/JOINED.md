# Trace75 strong and auxiliary Pell indices

`Trace75Joined.strong_and_auxiliary_indices_with_graph_residue` is checked in
every `IΣ₁` model for arbitrary natural ports with `0<beta`, positive
witnesses and a zero of the Lean trace75 ring value. It returns one coherent
tuple of positive `tau,f0,V0,y,I,j` and a natural `h` with the two K2 roots,
`I=2*U*tau*f0`, `c²∣I`, the strong Pell index `j`, the auxiliary index
`2*h+1`, and signed residues relating the same `V0`, `c`, and auxiliary
ordinate. It does not assert `h>0`. The `Z0` square witness is internal to
the construction and is not exported by this theorem.

This is not yet main-ordinate equality, an alignment of the two indices,
a trace74 positivity guard, a halt equivalence or an iPRA theorem. JSON and
fixed-byte binding remain external.

Accepted source `Trace75Joined.lean` SHA-256
`2c460b7dcf2306ee987d4fc7350a32f6fa35b5eb43c4ec1277c330eb71ae7a46`;
`run-joined.py` accepted `observations/joined-attempt01/`, object
`/tmp/trace75-joined-ketw_770/Trace75Joined.olean` SHA-256
`be92565d27f2893ed85e46c44d726a7a699d51ee9019105f932446831be7b305`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. Direct
providers and selected adjacent arithmetic dependencies are pinned. Project,
package and dynamic transitive ancestry are inherited; no complete selected
closure audit or independent replay is claimed.
