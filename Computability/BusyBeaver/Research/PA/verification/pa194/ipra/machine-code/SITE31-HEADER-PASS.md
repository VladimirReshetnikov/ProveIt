# Site-31 first physical header pass

`PA194Site31HeaderPass.site31HeaderPass` executes the first site-31 physical
header pass from control 24 back to control 24 in every PRA model. Its input
contains the actual source-site-31 path, at least two zero cells, and a source
file with arbitrary model-valued register slots and an arbitrary complete
suffix. Its output is the exact transformed right half displayed in the theorem;
the source-file suffix is carried through the `fileCode 9` argument and is not
assumed blank. The exact clock is explicit. This is a root-to-root header pass,
not yet the complete site-31 register-0 increment.

`check-site31-header-pass.sh` rebuilds the path theorem and the six site-31
header modules in a shared temporary output. It checks source hashes and
selected direct prebuilt object hashes both before and after compilation and
rejects `sorryAx` in theorem audits. The replay passed with exit 0 in
`/tmp/pa194-site31-header-pass-replay.log`. The site-27 machine baseline and
general foundations remain prebuilt; selected object hashes do not establish
their full transitive source closure.

From the repository root, replay with:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site31-header-pass.sh "$PWD" \
  /dev/shm/pa194-site27-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
```
