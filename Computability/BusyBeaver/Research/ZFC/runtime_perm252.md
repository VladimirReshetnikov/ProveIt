The global runtime argument and its whole-frame instantiation passed the
pinned Lean 4.32.0 kernel. The concrete conclusion is conditional on complete
decoder coverage: given a checked instruction at every actual leaf, the
register program halts exactly when the literal permutation252 machine halts
from a related dispatch frame. The finite all-sites proof is a separate input
to these generic modules. It is now discharged by `SitesPerm252`; the
[closed binary endpoint](binary_perm252.md) proves actual blank nonhalting iff
Con(ZF), including Foundation and Power.

`RuntimePerm252.lean` is generic over a deterministic partial logical step and
the existing Core machine. Its `PositiveSimulation` relation requires active
binary endpoints, positive binary execution for every logical successor,
actual binary halting at logical terminal states, and a proof that a failed
logical step is terminal. That last obligation prevents an exhausted decoder
or missing branch from being treated as a halt instruction.

The forward proof composes finite segments. Its prefix lemma also proves that
the accumulated binary clock is at least the number of logical steps. For
halting reflection, Core's absorbing halt semantics implies that an active
segment endpoint occurs strictly before any later halting time. Subtracting
the positive segment clock permits strong induction on the remaining time.
No infinite Choice, fairness premise or uniform clock bound is used.

`RuntimeInstancePerm252.lean` discharges these obligations using the actual
instruction proofs. Its relation contains `RegisterPathClean.Clean` and the
entire dispatch frame: PC, gap, marker, nine primary registers, arbitrary
spares and the blank exterior. Source normalization uses the exact consumed
prefix, including zero extension beyond the stored path. Positive decrement
retains every old spare and appends a zero block. A successful logical step
also establishes the next clean-path invariant.

The instance accepts either an explicit `Covered` predicate or a literal
decoder-tree equality plus `SiteCoverage.allSites checkSite [] tree = true`.
Coverage proves that a walk exists and that its exact consumed leaf is checked.
It rules out internal-node instructions; the remaining execution cases prove
that a failed step is precisely a halt leaf. The final equivalence uses the
existing `RegisterPath.Halts`, not a replacement stuck-state semantics.

Both modules passed their first source check in 0.59 and 0.53 seconds.
Seventeen module theorem axiom audits and five callers passed; the caller
audit took 0.45 seconds. Only standard `propext` and `Quot.sound` occur.
The callers include the actual 82,552-step blank bootstrap, all spare blocks,
and removal of the finite binary prefix. That composition still takes the
coverage proof as an explicit premise.

Commands, source hashes, exact axiom outputs and the reusable caller source
are in `results/runtime-perm252-verification.json`. Dependencies came from the
source-verified scoped cache recorded there; this did not repeat a fresh full
source closure or the finite bootstrap calculation.

This historical checkpoint supplies the generic runtime bridge. Its closed
all-sites application is now checked in `BinaryPerm252`. The standard-ZFC
consistency calibration and its internal PA formalization remain open.
