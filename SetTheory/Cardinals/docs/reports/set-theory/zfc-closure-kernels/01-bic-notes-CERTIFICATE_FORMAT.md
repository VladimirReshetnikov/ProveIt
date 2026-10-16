# Reference certificate format

The format is JSON for auditability, not for a proposed minimal machine.
All variable labels are nonnegative integers; Boolean values are rejected.
Executing formulas are tagged arrays:

```text
["E", x, y]                 membership x in y
["not", A]
["imp", A, B]
["all", x, A]
```

Equality (`=`) and the schematic matrix placeholder (`phi`) are rejected.
A certificate is a nonempty array of the following record arrays. Each record
constructs one formula; it never accepts an unchecked alleged conclusion.
References i,j are zero-based indices strictly below the current line number.

```text
["L1", A, B]       A -> (B -> A)
["L2", A, B, C]    (A -> (B -> C)) -> ((A -> B) -> (A -> C))
["L3", A, B]       (not A -> not B) -> (B -> A)
["Q1", x, y, A]    (all x A) -> A[y/x], capture-avoiding
["Q2", x, A, B]    (all x (A -> B)) -> (A -> all x B), x not free in A
["MP", i, j]       use line i as antecedent, line j as implication
["GEN", x, i]      all x (line i)
["ALPHA", i, A]    A, only if alpha-equivalent to line i
["N"]             inhabitedness
["CG"]            membership congruence for the same-members relation
["BIC", matrix]   a generated, universally closed BIC instance
```

In a BIC matrix, free variable 0 is the input slot and free variable 1 is the
output slot. All other free variables are universally closed parameters;
bound occurrences of 0 or 1 are left bound. Generator binder labels are
fresh above every variable label in the matrix, with capture-avoiding
substitution.

There is no assumption or admission rule. All theory axioms are closed, so
unrestricted generalization in these theorem-only proofs is sound. Standard
classical Hilbert reasoning connects the proof system to first-order logic;
a machine-checked verification of the implementation is not supplied.

The final formula is compared modulo alpha-renaming with
`["not", ["all", 0, ["imp", ["E", 0, 0], ["E", 0, 0]]]]`.
A valid certificate need not be a refutation: the CLI reports both properties.
The provided identity example is valid and not a refutation.
