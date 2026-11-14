# Closing a PA194 membership branch

`PA194ClosedMembership.lean` connects the fixed positive and negative bit
closure templates to the exact source child decoders. `closedMembershipDual`
takes the closing label and source formula code; it passes the second decoded
field as the bit index and the first as the container, matching the source's
membership argument order. It returns the Cantor pair of the two template
codes.

Given candidate-PRA certificates for both child decoders,
`modelClosedMembershipValue` proves the exact numeric equation for every
source code and closing label in every candidate-PRA model, including
nonstandard values. `modelClosedMembershipConstructor` specializes this to
all model-valued source constructors `4 * cantor(a,b) + 1`.
`PRA_has_membershipComponents` supplies suitable certified decoders
existentially; it does not serialize the chosen function codes.

`modelClosedMembershipQuote` identifies both components with Foundation's
quotes of the actual capture-avoiding `closeLabel` rewrites. That theorem
requires standard labels and fields and a model of IΣ₁. The underlying numeric
equations need only candidate PRA. This result covers the fixed membership
atom and its negation; it does not implement closing arbitrary source syntax,
prove the recursive translator correct, or prove a consistency implication.

Recheck with:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/objects \
IPRA_FOUNDATION_OVERLAY=/path/to/Foundation/objects \
  Computability/BusyBeaver/Research/PA/pa195-calibration/check-closed-membership.sh
```
