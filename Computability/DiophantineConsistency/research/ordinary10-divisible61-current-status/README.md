# Status of the 61-operation divisible-carrier route

The [61-operation graph](../ordinary10-two-norm-divisible61/README.md) is
standard-integer equivalent, by the documented witness maps, to the relaxed
nine-input two-norm graph. Its reverse bridge to the parent equation remains
open, as does the requested Lean proof of an internal iPRA equivalence. The
61-operation graph is not established as a consistency equation.

The proposed [60-operation carrier rewrite](../ordinary10-carrier60-inverse-boundary/README.md)
is not a valid replacement via its direct coordinate inverse. An explicit
[universal zero](../ordinary10-carrier60-universal-zero-independent/README.md),
also [independently evaluated](../../reviews/ordinary10-carrier60-all-ports-second-independent/README.md),
works for every natural port tuple, including the compact parameters. Its
inverse coordinate is negative. Consequently the 60-operation equation is
always solvable at those parameters, regardless of the original question.
This does not decide existence for the 61-operation graph or eliminate every
possible, different witness transformation.

The [positive-J example](../ordinary10-carrier60-positive-j-mask-bounds-counterexample/README.md)
shows that requiring positive J and only the usual coarse mask bounds still
does not imply the inverse coordinate is positive. Its ports are not the
actual compact ports; the scope of this particular example is those coarse
bounds.

Separately, a [guarded directed-log calculation](../ordinary9-compact-partial-directed-log-bound/README.md)
and a [separate derivation](../ordinary9-compact-partial-log-interval-independent/README.md)
exclude one fixed compact first-norm witness family from satisfying the
main norm. Both use MPFR, and neither excludes other graph solutions or
constitutes a Lean proof.
