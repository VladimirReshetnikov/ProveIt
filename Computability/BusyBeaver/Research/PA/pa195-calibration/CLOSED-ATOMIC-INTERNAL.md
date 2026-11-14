# Typed internal closing for PA194 atomic constructors

`PA194ClosedAtomicInternal.lean` composes the source-tag dispatcher with the
positive/negative typed internal meaning of the membership and equality
branches. For membership, it uses the exact bounded-bit template and the
model-valued closing environment. For equality, it constructs each of the two
closed variable terms and their equality atom directly.

Assuming candidate-PRA certificates for the source tag and both child
decoders, `modelAtomicMembershipInternal` and
`modelAtomicEqualityInternal` prove the dispatcher outputs the code pair of a
typed formula and its negation for every model-valued closing label and source
field, including nonstandard values. `modelCloseEqComplement` also handles
any externally fixed binder depth. Their arithmetic reduct must satisfy
IΣ₁, since the result uses Foundation's typed syntax and substitution. The
atomic numeric code equations without that additional assumption are proved
in [the closed-atomic package](CLOSED-ATOMIC.md).

The result covers the two source atomic constructors only. It does not give
a general closing operation for arbitrary model-valued syntax, a complete
recursive translator, or either machine-consistency implication.

Recheck with:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/objects \
IPRA_FOUNDATION_OVERLAY=/path/to/Foundation/objects \
  Computability/BusyBeaver/Research/PA/pa195-calibration/check-closed-atomic-internal.sh
```
