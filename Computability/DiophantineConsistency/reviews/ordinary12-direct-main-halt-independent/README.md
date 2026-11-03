# Independent review of the direct graph's fixed-port model halt bridge

`DirectMainHalt.positive_model_iff` states that, in every IΣ₁ model, the
fixed-symbolic-port direct graph has a strictly positive zero if and only if
the encoded machine has an internal halt. Its separate `shifted_model_iff`
replaces each positive witness with `x+1`, and `shifted_byte_model_iff` uses
the closed Lean byte-recipe port tuple. Witnesses and the halt time may be
nonstandard model elements. This is a **model theorem**, not an internal iPRA
derivation or a Lean theorem about external files or PDF bytes.

The positive theorem obtains the fixed beta and low/high-port inequalities
from `CompactFixedBeta.bounds`, instantiates the bounded-port direct/XQ91
existence equivalence, and composes it with the checked XQ91 model-halt
theorem. `DirectPortBounds.bounds` proves the generic cast step for the high
port, whose tuple value is `beta+H`; its hypothesis retains that single beta
shift. The shifted theorem transports positive witnesses in both directions,
and the byte theorem rewrites by the existing `byteP_eq`.

The first two halt builds failed: the first had a high-port cast mismatch and
a kernel memory error, and the second still hit the kernel memory limit. The
third, using the separately compiled generic port helper, exited zero without
reported warnings or `sorryAx`. Its three axiom reports contain
`[propext, Classical.choice, Quot.sound]` in Lean's metatheory. The reviewer
checks the exact statements, source/log/object/Lean-binary hashes and both
failed source/log/receipt snapshots, verifies first-resolved helper,
equivalence and XQ91-halt objects, and checks inherited producer pins.

The direct selected union contains 1,291 objects; the XQ91-halt union contains
1,294. The checker independently rehashes every selected path and symlink
before and after and verifies that all 1,291 shared names have identical
hashes. It reruns the bounded-port equivalence and XQ91-halt reviews. The
accepted preflight observed no Lean process; its recorded execution samples
saw at most one. Sampling does not rule out shorter overlaps or memory dips.

Run `python3 -I -S -B check.py` from this directory or give its path from any
directory. The captured exit-zero, empty-stderr run and input hashes are in
[`observations/attempt01`](observations/attempt01/). The review requires the
retained `/tmp` provider paths and launches no Lean process. The selected
union comparison and producer checks do not authenticate full serialized
project imports, historical source-to-object origin, package-transitive or
dynamic ancestry, or a fresh independent kernel replay. Imported first and
main norm sources locally suppress unused-variable and unused-simp-argument
linters. Graph/Lean, payload and any display correspondence remain outside
the Lean file/PDF semantics boundary.
