# PA194 recursive translation with concrete atomic branches

`PA194ConcreteRecursion.lean` instantiates the history-aware primitive-recursive
source translator with the checked membership and equality branch codes.
Candidate PRA proves existence of the five tag, child and pair-projection codes
needed by the construction; their particular numerals are not fixed here.

For every candidate-PRA model, the resulting code satisfies the exact source
constructor equations: zero selects the supplied truth code; membership and
equality evaluate to the checked explicit numeric syntax codes; nonzero
implication applies the supplied implication operator to both recursive child
translations; and universal quantification applies the supplied binder operator
to the correct bound label and recursively translated body. These model
statements include nonstandard codes and assume no IΣ₁.

Separate theorems identify the atomic numeric codes with Foundation's internal
syntax in models satisfying IΣ₁. That additional assumption is explicit. The
truth, implication, and binder-closing operations remain parameters; the
recursive translation's syntax correctness, PA calibration, machine
internalization, and consistency equivalence are not proved by this package.
The zero alias has its own branch and still requires a proof that its intended
truth meaning is compatible with the exceptional implication constructor.
Rebuild all dependencies with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-concrete-recursion.sh
```
