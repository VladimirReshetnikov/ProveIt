# Current status of the two-norm parent bridge

The relaxed two-norm graph is still **not** known to have the same zero
existence status as its shifted 85-row parent. The results below concern
standard integers, and none is a checked Lean or iPRA proof.

For a two-norm zero with main Pell ordinate `c=y_m(A)` and actual rank `R`,
the [odd-index construction](../ordinary13-shifted-two-norm-parent-odd-index-general-A/README.md)
provides a parent completion preserving the first/main data if
`c | R + (-1)^((m-1)/2)*m`. This sufficient congruence is not known for
arbitrary zeros. The construction has explicit auxiliary witnesses and does
not require the Pell index to equal the rank.

For even `m`, the [kernel-gcd obstruction](../ordinary13-parent-even-index-kernel-gcd-obstruction/README.md)
shows that a parent completion preserving the same data is impossible when
`gcd(c²,d*t) | c`, where `A²-1=d*t²` and `d` is squarefree. The hypothesis
includes the earlier squarefree and discriminant-coprime cases, but is not
known for any actual compact zero. This does not rule out a different
two-norm witness or establish an existential difference between the graphs.

The source-only [Pell period specialization](../ordinary13-explicit-pell-period-model-draft/README.md)
and [bounded formula draft](../ordinary13-pell-period-bounded-formula-draft/README.md)
identify reusable model and syntax interfaces. Their Lean elaboration,
evaluation and witness-bound bridges, provider closure, and relationship to
an internal iPRA derivation remain open. The separate historical endpoint
for the displayed 14-variable equation retains its own qualifications.
