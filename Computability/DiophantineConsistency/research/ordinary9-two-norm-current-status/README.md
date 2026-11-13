# Nine-variable two-norm candidate: current status

The [two-norm equation](../ordinary9-shifted-free-aux-two-norm64/README.md)
has nine natural inputs, 64 live operations and exact degree 60 for fixed
nonzero beta. Its standard-integer zero existence is equivalent to that of
the separate shifted-zeta graph with a **free** auxiliary-square input. The
graph, degree and this limited equivalence have been [independently reviewed](../../reviews/ordinary9-shifted-free-aux-two-norm64-independent/README.md).

This is **not yet an equation proved equivalent to Con(ZFC)**. The original
85-row parent requires an actual square auxiliary witness. The [reverse
Pell criterion](../ordinary13-shifted85-free-aux-square-criterion/README.md)
has not been proved for every relevant two-norm zero. In fact, subject to
the stated retained exact-index theorem, a [noncompact coarse-port
example](../ordinary9-two-norm-coarse-no-same-data-lift/README.md) cannot be
completed to a parent zero while preserving its nine inputs. That conditional
example does not rule out another witness map or decide the fixed compact
tuple.

The [general completion](../ordinary13-free-aux-square-general-nonsquare-completion/README.md)
explains why relaxing the auxiliary square removes the strong and auxiliary
existence constraints: any first/main-norm valuation with positive c can be
completed with a nonsquare free input. It does not establish that the first
two norms have a zero at the fixed tuple.

The candidate uses the symbolic compact beta `2^(67*8807)-1`; it is distinct
from the 2011 tuple displayed in `equation.pdf`. None of these new results
has been coherently elaborated in Lean or establishes the requested internal
iPRA consistency equivalence.
