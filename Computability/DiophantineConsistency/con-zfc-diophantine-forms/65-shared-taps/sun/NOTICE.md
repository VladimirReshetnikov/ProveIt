# Provenance and attribution

This component is built on Vladimir Reshetnikov's ProveIt repository at
commit `beb0192cb8dc36f78c369c080f2adfbc1887a486`.

The arithmetic DAG implementation `circuit.py` is copied from
`59-degree-separated/sun/circuit.py`. The function in `tail.py` is unchanged
from `59-degree-separated/sun/build.py`; its exact abstract syntax tree is
verified against the preserved source. The 59 local polynomial identities
and elementary norm/borrow/population checks in the verifier are adapted
from `59-degree-separated/sun/independent_check.py`.

The shared-tap layout, unique kernel table, and coefficient audit come from
the companion shared-kernel-tap construction in this work. The original
65-gate source is
`31-sun10/quartic31/upstream/quartic31_system.json`. The full fixed tuple is
the original old31 tuple, preserved with its source metadata and hashes.
No compact native tuple is substituted into that source.

The upstream repository, compiler, Wang tiles, and K215 notices and licenses
are preserved under `coefficients/licenses/`. This note attributes the new
source composition and does not assert original authorship of the inherited
compiler, Sun bridge, fixed numerals, or finalizer.
