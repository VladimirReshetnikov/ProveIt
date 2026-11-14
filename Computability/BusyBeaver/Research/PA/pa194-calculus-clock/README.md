# PA194 clocks and separate-diagonal calculus

`PA194CalculusClock.lean` proves that each exact PA194 clock reaches 1 if and
only if code 1 has a finite derivation in the separate-diagonal numerical
calculus defined by `../pa194-derivation-compiler`. The result composes the
standard scheduler/calculus equivalence with the checked clock/scheduler
bridge. Both theorems print `[propext, Classical.choice, Quot.sound]`.

This is a standard-natural-number Lean theorem for the displayed numerical
calculus. It does not identify that calculus with PA, translate PA refutations,
or establish either direction inside PRA/iPRA. The source retains the pinned
Python grammar-translation boundary documented in `../pa194-source-tree`.

The module was checked against independently rebuilt temporary source,
scheduler, calculus, clock, coverage, and startup objects. On the checking
machine, the command from the repository root was:

```sh
LEAN_PATH="/dev/shm/pa194-ax-probe:/dev/shm/pa194-merge-fresh:/dev/shm/pa194-coverage-preserved:/tmp/current14-standard-fresh-build-20261104/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib:$(lake env printenv LEAN_PATH)" \
  lean -M6000 -j1 Computability/BusyBeaver/Research/PA/pa194-calculus-clock/PA194CalculusClock.lean
```

These overlays are temporary and not distributed. The neighboring packages
record the separate component checks; a single combined fresh build of this
final composition has not yet been provided.
