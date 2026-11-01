# Mixed Lean providers are not validated by a successful import

[`probe.py`](probe.py) creates two disposable modules and deliberately mixes
their artifacts using Lean 4.32.0. First it compiles `B.valid : p` when
`p := True`. It then changes only `p` to `False`, compiles the new `A.olean`,
and imports the old `B.olean` together with that new object. Lean accepts
`theorem contradiction : False := valid`; `#print axioms contradiction` says
it has no axioms. The same attempted theorem fails with the original `A`, and
rebuilding `B` against the changed `A` fails. Two separate runs and the
negative controls are recorded in [receipt.json](receipt.json).

`lean --deps` on the client reports the direct `B.olean` but not the
transitively imported `A.olean`. Thus a successful client compilation, a
clean axiom report, and checks limited to direct imports do not establish that
historical project objects are compatible with a replacement Foundation
provider. This controlled experiment does not assert that any actual project
proof derives a contradiction. For a credible mixed-provider replay, either
verify identity of the relevant complete dependency inputs against their
historical compile-time identities, or rebuild the affected project closure
from authenticated sources against a coherent provider. Package-transitive
and dynamic ancestry require their own accounting.

Reproduce with `python3 probe.py` after moving aside any existing receipt;
the script never changes an existing provider or project object.
