# One-page compact54 tuple binding

`OnePageModesData54.lean` defines the 457 modes in the order printed on the
page. The first 430 action modes decode the literal integer in
`NativePackedMachine54`; its independent certificate identifies all 215 rows
with `KDense215.rows215`. The other 25 tail modes are fixed literal templates.

`OnePageModes54.lean` proves that the page's fixed sum of integer quotients
computes the position of every mode in `NativeModesData54.modeList`. It proves
the strict key order, key bound below `2^40`, exact signed quotient indicator,
rank bound, and mode equality at the computed rank. A finite permutation and
its inverse occur only in the proof: `arithmeticRank` itself uses the printed
quotient sum and no choice operation.

`OnePageLowPort54.lean` binds the page's fixed assignment-position list to the
actual stencil, proves that its 520 positions are distinct, and identifies the
page's arithmetic low port with `NativeLowPort54.lowPort`. It does not expand
the large radix power. `NativeSparseDigits54` subsequently uses this binding
to decode actual source assignments.

The dedicated `Lean/checks/OnePageModes54.lean` and
`Lean/checks/OnePageLowPort54.lean` audit the universal identities. Their axiom
lists contain only `propext`, `Classical.choice`, and `Quot.sound`, or subsets.
The finite certificates use kernel reduction, not a native-decision axiom.

`OnePageTuple54.lean` additionally proves that the literal integer equality
indicator `floor((2^40-(i-j)^2)/2^40)` gives the two receiver flags. Its signed
coefficient expression is exactly the actual nonnegative local selector
coefficient. It identifies every auxiliary-entry block, then reindexes the
selector sum by the proved arithmetic ranks. The resulting `stencilWord` is
equal to `NativeStencil54.rawWord` for **every natural radix**. The proof uses
fixed finite sums and symbolic powers; it never expands the 434054-bit port.
The seven additional audits are in `Lean/checks/OnePageTuple54.lean`.

This checkpoint binds finite arithmetic data. It does not assert the remaining
native tableau calibration or the object-ZFC consistency biconditional. The
compact rational geometric display in the PDF also has a separate Python
identity receipt. The Lean `stencilWord` identity uses its equivalent direct
integer sum of nonnegative target-minus-position exponents; it does not yet
formalize that rational geometric refactoring.
