# Trace75 signed-square representatives

`Trace75RootNonzero.roots_of_positive_representatives` removes both signed
square-representative assumptions from the preceding conditional K2 theorem.
In every `IΣ₁` model, for arbitrary difference-ring ports and a zero of the
Lean trace75 ring value, it assumes positive natural representatives of each
of the actual Δ, U, E and M registers. It proves that the signed V register
is nonzero, constructs natural square representatives of V and Z internally,
and concludes positive `tau,f0` with `E=tau²` and
`1+Delta*U²*E=f0²`. No assumptions about 74-coordinate guards, K0 or halt
are made. The four positive register representatives remain explicit in this
module; no graph-zero existence, machine equivalence, literal JSON binding or
iPRA endpoint follows.

Accepted source `Trace75RootNonzero.lean` SHA-256
`9879c7cf5c385cc6aafdb00e3b59f20fbaf5183ea537e34d61f2e009958c5cc1`;
`run-nonzero-v2.py` accepted `observations/nonzero-attempt02/`, object
`/tmp/trace75-nonzero-8vawxqqm/Trace75RootNonzero.olean` SHA-256
`35e467ec9e32fb7e0e0b02f917c576811341e89d4a593ccc8dcd8603a5474802`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
The first failed attempt and source snapshot are retained. Direct providers
are pinned and resource guards sampled; package, project-transitive and
dynamic ancestry remain inherited.
