# The complete high mask of the current equation

Date: 2026-10-25. Author: circuit_reduction. Independent whole-source review
and fresh replay: ROOT.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentHighDigits2011.lean | ff6eb32b735f59989d7b21ed835f4c64b5a8bed206a9a4b96a54f25016c35d02 |
| CurrentHighDigits2011Checks.lean | 74eefe31ffee21b84a50ec9d035d60db7a75c85227c06eb290c1cf789e0d20f6 |

ROOT read all161 module and61 check lines before executing either file.
Fresh direct `lake env lean -M6000 -j1` runs both exited0; the module
output was empty. All four axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The author independently checked
the same frozen files. No full transitive or umbrella rebuild is claimed.

The field formula follows symbolically from ten append/replicate blocks,
covering every field and every gap. It proves origin4, padding8 at1..916,
copy1 at960..968 and987..994, marker1 at1004, clause2^45−4 at1005,
and zero everywhere else. Every digit is strictly below2^47.

The exact repeated word is `highPort*repunit(width,N)−1`. Subtraction
changes only the global origin digit4 to3, with no propagated borrow;
all later cell origins remain4. The checks include adjacent field
boundaries, the later origin, and low-bit controls that distinguish the
actual subtraction from the unadjusted mask.

`polynomial_zero_mask_test` starts from every strictly positive zero of
the literal current65 polynomial, with K>0. Its canonical source window
derives the positive length, exact q and J, and the F mask test against
this entire repeated word. Neither an F digit word nor carries, phase
alignment, one-selector occupation or native semantics is assumed.

The mask-word identity is ready for the source carry normalization.
Binding the exact K recipe and deriving the physical count, phase,
tile/controller and internal-ZFC links remain required.
