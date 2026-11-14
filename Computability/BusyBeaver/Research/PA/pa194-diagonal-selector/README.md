# PA194 separate diagonal-head selector

`PA194Diagonal.selectDiagonal_total` gives an explicit finite command word
which, from an arbitrary top and stack with clean caches, returns the separate
diagonal formula `c → ∀x_c c` as its top, preserves the incoming stack, and
clears the caches. This is the extra axiom head of the PA194 source calculus.
The result prints `[propext, Quot.sound]`.

The supporting words use the PA194-specific interpreter and its extra head:
pop takes 11 Shifts after AX, push takes nine, and discard and generalization
use ten. The source/interpreter connection is checked in
`../pa194-command-source`. This standard-Lean selector does not itself prove
that the diagonal head is valid in PA, compile arbitrary derivations, or
establish an internal PRA/iPRA reduction. The source tree retains the pinned
Python grammar-translation boundary documented in `../pa194-source-tree`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-diagonal-selector/check.sh
```

The script rebuilds the source/command prerequisites in a private tmpfs
folder and checks the selector. The full standalone fresh build and selector check have passed.
