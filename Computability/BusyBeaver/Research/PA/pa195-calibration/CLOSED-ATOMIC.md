# Closing PA194 atomic source constructors

`PA194ClosedAtomic.lean` combines the closed membership and equality code
pairs with PA194's actual tag and child decoders. The explicit binary PR code
`closedAtomicDual` takes `[closing label, source formula code]`; it selects
the membership branch when the tag is 1 and the equality branch otherwise.
Its intended domain is atomic input: no correctness claim is made for the
other tags.

Given candidate-PRA certificates for the tag and both child decoders,
`modelAtomicMembership` and `modelAtomicEquality` prove the exact equations
for the corresponding PA194 constructors in every candidate-PRA model,
including nonstandard fields. `PRA_has_atomicComponents` proves that suitable
certified decoder codes exist; their code numerals are not serialized here.
For membership the source element/container fields are passed to Foundation's
bit template in the reverse of their source order.

For standard labels and fields in an IΣ₁ model,
`modelAtomicMembershipQuote` and `modelAtomicEqualityQuote` identify the
results with the exact Foundation quotes of positive and negative
capture-avoiding closure. `modelAtomicMembershipComplement` additionally
identifies the negative membership component as the syntactic negation of
the closed positive component. The underlying numeric equations require only
candidate PRA. This is a fixed atomic component, not an arbitrary or
nonstandard syntax traversal, a complete recursive translator, or an iPRA
consistency implication.

Recheck with:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/objects \
IPRA_FOUNDATION_OVERLAY=/path/to/Foundation/objects \
  Computability/BusyBeaver/Research/PA/pa195-calibration/check-closed-atomic.sh
```
