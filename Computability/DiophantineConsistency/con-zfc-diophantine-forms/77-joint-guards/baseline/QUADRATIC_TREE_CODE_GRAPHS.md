# Composable quadratic graphs for annotated-checker tree operations

`QuadraticRegisterComposition.lean` adds two data-valued operations to the
shared-register quadratic compiler:

- `System.conjunction` concatenates constraint rows in one existing program
  and auxiliary-input context. Its predicate is exactly conjunction, the
  stored register bank is retained, and the register-witness count is unchanged.
- `System.instantiate` maps a gate-free local scheme's input ports to existing
  input or register slots. Its correctness theorem evaluates those ports at
  their actual natural values. Earlier computations are retained as register
  references; their arithmetic expressions are not substituted into the rows.

Auxiliary coordinates are allocated in a shared finite context. Instantiation
reuses the supplied coordinates; `System.scopedRep` hides the declared block
once at the final boundary. These operations support preallocated scopes;
a general compiler that allocates and renames fresh scopes remains future work.

The checks include a nonempty register bank storing `x`, `y`, and `x*x`.
Instantiating the predecessor scheme at the stored square gives exactly
`y=pred(x*x)`, with the original three register witnesses. This exercises
register reuse rather than only raw input substitution.

## Actual checker functions

`QuadraticTreeCodeGraphs.lean` supplies graphs for these exact functions from
`AnnotatedCodeArithmetic.lean`:

```
treeLeft code  = (Nat.unpair code.pred).1
treeRight code = (Nat.unpair code.pred).2
listTail code  = if code=0 then 0 else treeRight code.
```

The pairing is Mathlib's max-square pairing used by the direct annotated
checker. No reference to the older EnumPerm Cantor encoding occurs here.

A predecessor output `p` is characterized by the two quadratic rows

```
code*(p+1-code),  p*(p+1-code).
```

Their simultaneous vanishing is exactly `p=code.pred` for every natural code,
including zero. In a single shared context, these two rows are conjoined with
the four sharp `Nat.pair` rows from `QuadraticNatPairing.lean`.

For the left projection the auxiliary vector is
`(predecessor,otherComponent,branchBit,branchSlack,maximumComponent)`;
the right projection swaps the two pair-component ports. Squaring and adding
these six rows produces one explicit polynomial of degree at most four.
Each resulting graph has five natural witnesses, hence seven natural
variables including its output and input, and exactly 62 binary operations
in the supplied expression recipe.

`listTail_eq_treeRight` proves that the zero guard agrees with this second
projection's value at zero. Therefore the same polynomial data represent the
actual guarded workspace-list tail for every code. The separate list-head
relation still needs its successor marker to distinguish a missing entry
from a found entry equal to zero.

## Checked local costs

The existing `AnnotatedCodeGraphs` baseline is retained. These operation
counts and degree bounds are kernel-checked in
`checks/QuadraticRegisterComposition.lean`:

| Function | Earlier witnesses | Earlier operations | Earlier degree bound | New witnesses | New operations | New degree bound |
|---|---:|---:|---:|---:|---:|---:|
| tree left projection | 4 | 115 | 16 | 5 | 62 | 4 |
| tree right projection | 4 | 115 | 16 | 5 | 62 | 4 |
| workspace list tail | 9 | 3879 | 512 | 5 | 62 | 4 |

The earlier degree entries are certified bounds from the expression syntax;
no assertion about their exact normalized polynomial degrees is made. The
new degree entries are also upper bounds. The first two rows trade one extra
witness for fewer operations and a lower certified degree bound. The local
list-tail recipe reduces both its witness count and its operation count.
These measurements are not a size certificate for a complete proof checker.

## Verification and limits

Both source modules and their checks compile cleanly. The twenty-four dependency
audits use only `propext`, `Classical.choice`, and `Quot.sound`. The proofs
include complete natural-zero equivalences for the actual checker functions,
the nil-output characterization, nonempty-register attachment, and the finite
baseline cost comparisons. No new axiom, admitted lemma, or coefficient choice
is introduced.

Program and row data remain executable; `MvPolynomial` supplies their ordinary
algebraic semantics. These local operations avoid scalar primitive-recursive
program inlining, but the complete parser, reference loop, rename checker,
and bounded iteration compiler still need their own compositional proofs.
No new closed consistency equation or internal object-ZFC consistency
biconditional is claimed by this checkpoint.

The next [guarded arithmetic checkpoint](QUADRATIC_GUARDED_GRAPHS.md)
now represents the actual list head with7 witnesses and76 operations at
degree≤4, preserving both nil and a found entry equal to zero.
