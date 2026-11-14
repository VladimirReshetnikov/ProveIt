# Typed internal closing of a PA194 membership branch

`PA194ClosedMembershipInternal.lean` composes the exact PA194 source child
binding with the fixed-template internal closing environment. The source
membership order is container first and element second, while Foundation's
bit template takes the element before the container.

Assuming candidate-PRA certificates for the two source-child decoder codes,
`modelClosedMembershipInternal` identifies the positive and negative code
values at an arbitrary model-valued input with Foundation's typed substitutions
of the fixed bit template into the corresponding closing environment.
`modelClosedMembershipConstructorInternal` specializes the result to every
model-valued PA194 membership constructor `4 * cantor(a,b) + 1`. The closing
label and fields may all be nonstandard.
`modelClosedMembershipComplement` additionally identifies the two typed
outputs as a formula and its negation.

These typed-syntax identifications explicitly require IΣ₁ in the arithmetic
reduct. The corresponding numeric code equations need only candidate PRA and
are proved in [the closed-membership package](CLOSED-MEMBERSHIP.md). The
substitution is into an externally fixed template, not a represented
traversal of an arbitrary model-valued formula. No machine consistency
implication is claimed.

Recheck with:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/objects \
IPRA_FOUNDATION_OVERLAY=/path/to/Foundation/objects \
  Computability/BusyBeaver/Research/PA/pa195-calibration/check-closed-membership-internal.sh
```
