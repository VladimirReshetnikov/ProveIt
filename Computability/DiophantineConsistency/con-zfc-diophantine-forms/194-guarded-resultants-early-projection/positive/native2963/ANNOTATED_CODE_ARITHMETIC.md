# Supplied arithmetic programs for annotated certificates

`Lean/DiophantineConsistency/AnnotatedCodeArithmetic.lean` supplies literal
`ScalarPRCode.Realizes` data for the first arithmetic operations needed by the
direct sealed-ZFC certificate route. Its source imports the numeric codec and
`DirectScalarArithmetic`; it does not import the old proof enumerator. Program
data are assembled with pairing/projections, predecessor, conditional branches
and primitive recursion, rather than extracted from a theorem asserting that a
function is primitive recursive.

The tree programs implement the exact frozen numeric format: outer-kind
classification, atom payload, fork-child codes, and numeric atom/fork
construction. The kind test classifies only the outer constructor; it is not a
recursive formula- or certificate-validity test. Checked equations identify
these operations on every literal tree quotation.

The reference programs use an explicit workspace list representation:
`[]` is zero and `x :: xs` is `Nat.pair x (listCode xs) + 1`. This workspace
format is separate from the external tree-list encoding. A guarded head
returns zero for an absent element and `x+1` for a present element, so a stored
zero is never confused with a missing parent. Primitive recursion on the
supplied backward index applies the guarded tail operation. The proved
`lookup_listCode` theorem identifies its result with the original optional
list lookup, including indices beyond the history's length.

`referenceCheck` takes `(history,(index,expectedValue))` in nested pairs and
returns one exactly when that backward reference retrieves the expected
value. Judgment values quote both the complete context and the conclusion.
Their code is proved injective, and `referenceCheck_judgments` establishes
that numeric reference checking is exactly lookup of the expected original
`AnnotatedProofChecker.Judgment`. A different context or a different formula
is therefore rejected.

The following tree sizes are checked for the actual supplied scalar programs.
They are counts of primitive-recursive program constructors, not polynomial
variables or scalar operations of a Diophantine equation.

| Program | Nodes |
| --- | ---: |
| Tree left/right outer component | 17 each |
| Tree left child | 29 |
| Tree kind | 45 |
| Atom/fork constructor | 7 each |
| Guarded head | 31 |
| Guarded tail | 29 |
| Indexed drop | 37 |
| Guarded lookup | 69 |
| Single expected-reference check | 225 |
| Certified optimized reference check | 209 |

`referenceProgram_primrec` applies the generic constructor theorem to the
supplied finite program; the program exists as data before that theorem is
applied. The checked specification and instruction counts remain distinct.
The checks also execute the supplied lookup and optimized reference programs
on present-zero and out-of-range examples.

The next arithmetic layers remain open: numeric syntax tables for all formula
constructors; certified renaming, instantiation, bounds, closure and actual
sealed axiom expansion; local verification of all seventeen rule annotations;
and the bounded proof-line loop. A promising route supplies finite tables of
these syntax computations and checks their local equations and backward
references, instead of expanding the typed recursive decoder at every use.
It still needs soundness/completeness for those tables, a supplied arithmetic
program or graph for their validator, and an exact bridge to the frozen
numeric checker or to the same existential certificate language. This first
stage does not certify the full checker primitive recursive, compile a closed
refutation predicate, or prove the arithmetic checking algorithm correct
inside an arbitrary model's omega.
