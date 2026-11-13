# Independent 80-row index and residue review

For a positive zero of the exact 80-row Lean graph in an indicated IΣ₁ model
with positive beta, the checked index theorem constructs a positive strong
Pell index and an odd auxiliary index. The joined theorem adds the graph's
signed residue. It obtains `V0` and the actual signed-graph square equality
from one `graph_adjacent` witness tuple, then passes **that same `V0`** and
equality to `graph_signed_residue`; the odd-quotient transfer also uses that
`V0`. The consequence applies signed-congruence symmetry and transitivity to
those two relations and derives `c ≤ I` from `c² ∣ I` and `I > 0`.

There is an important distinction between the strong norm and the missing
main norm. The joined source derives `F² = 1 + D*I²` directly from the root
equations and uses it to establish the hypothesis of `quotient_mod_norm`.
It does not assume or invoke the desired main equation
`d² = 1 + D*c²`, and the reviewed sources do not call `half_index`. They do
import the module named `ArithmeticPellHalfIndex`: its current source proves
`quotient_mod_norm` earlier in that file from a strong-norm hypothesis and
recurrence lemmas; the later `half_index` theorem explicitly assumes the main
norm. The selected module object matches the independently audited 90-provider
record, but a complete historical source-to-object reconstruction of that
object is not part of this audit.

The retained independent check verifies all five accepted source snapshots,
object hashes, logs, axiom reports, sampled resource guards and explicitly
pinned predecessor objects. It checks six earlier failed or warning-rejected
attempts separately and verifies current direct import resolution and relevant
90-provider companions. No mathematical or receipt mismatch was found. The
audit exited zero with empty stderr and did not replay Lean.

The result is a necessary signed-coordinate consequence, not the missing
all-index fold, proof that `c` is the relevant Pell ordinate, graph-to-halt
equivalence, iPRA endpoint, or JSON/PDF binding. Package-transitive, dynamic,
and full historical source-to-object ancestry remain inherited; resource
observations are sampled rather than continuous.
