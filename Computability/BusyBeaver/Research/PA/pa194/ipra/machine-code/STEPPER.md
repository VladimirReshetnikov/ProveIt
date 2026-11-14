# PA194 iterator from an arbitrary configuration

`PA194Stepper.lean` defines an explicit `Code 2` that iterates the packed
PA194 transition from a supplied initial packed configuration. Its zero and
successor equations hold in every model of candidate classical PRA. Open
induction proves that starting from packed zero agrees with the explicit
blank-input clock at every model time. `modelStepperDecodedSucc` combines the
decoder inverse with the concrete step semantics: the decoded successor is
one step from the decoded current configuration, including for nonstandard
model times and starting codes. This provides an arithmetic interface for
future source/register segment simulation; it does not yet establish that
simulation or either consistency implication.

Replay using the dependency overlays described in the machine-code README:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-stepper.sh
```

The script rebuilds the pinned PA194 table and dependency chain in a private
directory and rejects `sorryAx`. Transitive prebuilt overlay objects are
assumed to match their recorded sources; they are not all rebuilt here.
