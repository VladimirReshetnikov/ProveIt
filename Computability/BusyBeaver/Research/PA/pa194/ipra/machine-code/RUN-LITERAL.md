# PA194 literal transition along arbitrary model runs

`PA194RunLiteral.lean` combines the explicit arbitrary-start packed iterator
with the all-model PA194 literal-step theorem. At every time and from every
encoded start in any model of candidate classical PRA, if the decoded control
is working, the proof identifies a concrete literal transition row and shows
that the decoded successor equals its state and tape effect. The time, start,
and tape contents may be nonstandard model elements. The theorem is an
all-model Lean result; it is not a source-register simulation or a proof of
an iPRA consistency direction.

Replay with the same dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-run-literal.sh
```

The script rebuilds the pinned PA194 table and dependency chain in a private
directory and rejects `sorryAx` in printed dependencies. Transitive prebuilt
overlay objects are assumed to match their recorded sources; this replay does
not rebuild all of them.
