# PA196 bounded halting in the iPRA language

`PA196Bounded.lean` implements a primitive-recursive simulation of the literal
PA196 machine using natural numbers for the two binary tape halves. Its finite
table is proved equal, row by row in the Lean kernel, to the imported
`PA196.Literal.transition`. The simulation treats **every** state at least 196
as an absorbing state, matching the exact domain of the upstream machine's
partial step. It proves that encoding commutes with this totalized zipper step,
and hence that its bounded-halting predicate has a witness exactly when the
upstream `M6.Zip.Halts PA196.Literal.machine blankZip` holds.

The file also obtains a primitive-recursive function code and a corresponding
one-variable term in the existing iPRA language, and proves the same binding
for its interpretation over the standard natural numbers. The code is chosen
using an existence theorem; it is not an explicitly serialized code. These
standard-model results do **not** prove either reduction inside iPRA, nor do
they prove an equivalence with PA consistency. In particular, they do not
formalize the correctness of the machine's proof search.

## Checking

The check uses Lean 4.32.0 and the root project's Lake environment. It checks
source hashes for the imported zipper, literal machine, table, and two direct
iPRA sources; rebuilds the upstream zipper and literal modules and this bridge
in a private temporary directory; and prints axiom dependencies. Its two
dependency overlays must already exist and must themselves be built from the
matching sources and toolchain. It does not rebuild or independently verify
their transitive dependencies.

For the local caches used in the original check:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa196-vs-u208/ipra/check.sh
```

The iPRA overlay's `state.json` records that exact Foundation provider. These
temporary paths are machine-specific; substitute equivalently built overlays
when reproducing elsewhere. The Foundation checkout used for this check was at
revision `32e1a0956a8622fad067328ca1959729a7634428`.
