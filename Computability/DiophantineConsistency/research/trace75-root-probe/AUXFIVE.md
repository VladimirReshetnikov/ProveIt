# Trace75 auxiliary index is at least five

`Trace75AuxFive.graph_auxiliary_index_ge_five` is Lean checked in every `IΣ₁`
model. For arbitrary natural ports satisfying `2≤beta` in the model and ten
positive witnesses at which the Lean trace75 ring value is zero, it returns
one tuple of model witnesses `I,j,h` with `0<I`, `0<j`, `2≤h`, `c≤I`, `c²∣I`,
the strong Pell x/y coordinates at j, and the signed residue relating c to
`ycoord (2*h+1) (A-1)`. Thus the indicated odd auxiliary index `2*h+1` is at
least five; the theorem directly exports `2≤h`.

The proof establishes `2*c<F` from the strong norm and c²∣I, uses
`c>4*Delta+3`, and excludes auxiliary indices one and three via the signed
residue and the exact small ordinates. The c bound is independently obtained
from the same graph valuation; no identity is claimed between the existential
strong witnesses used internally for that bound and those exported here.
`A=X*Y+Y`, `F=1+2*Delta*U²*E`. This is a necessary consequence of a trace75
zero, not index alignment, a halt/iPRA equivalence, a trace74 guard, or a
formal binding of external JSON/payload bytes. The beta bound is explicit.

Accepted source `Trace75AuxFive.lean` SHA-256
`0b7f298d51f2058f45842b4bdb46444c9b8563e9fd0e01d8a5fbc4de0f82ec22`;
`run-auxfive-v2.py` accepted `observations/auxfive-attempt02/`, object
`/tmp/trace75-auxfive-osyxc83j/Trace75AuxFive.olean` SHA-256
`4cedad6c7e803f3d9c262f2b90910fb8988850075b628708e9468c84d8d15381`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
The initial failed source and diagnostic are retained. Direct selected
providers are pinned; project/package transitive, historical source/object and
dynamic ancestry remain inherited, without a full closure audit or replay.
