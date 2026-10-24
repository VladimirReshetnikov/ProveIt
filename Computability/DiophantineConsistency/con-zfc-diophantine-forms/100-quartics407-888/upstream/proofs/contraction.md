# Certified contraction of exported nonnegative quadratic systems

This is a new exact algebraic postprocessing pass over the root agent's
`stage_synchronized/equation.json`. It does not inspect the compiler's cache,
gate annotations, or intended meaning of a variable. Its inputs are the
literal exported quadratic residuals and their nonnegative-integer domain.

## Elementary elimination lemma

Let every coordinate of `(x,y)` range over the nonnegative integers. Suppose
one residual is `epsilon*(x-P(y))`, where `epsilon` is 1 or -1 and `P` is an
integer polynomial with nonnegative coefficients and without `x`.
Delete this residual and substitute `P(y)` for `x` in every other residual.

Projection from the old simultaneous zero set to the new one is a bijection.
Its inverse is `(y -> (P(y),y))`: this is an integral point and `P(y)>=0`, so
it belongs to the correct domain. Direct substitution proves all residual
identities. This argument does not merely preserve rational or integer zeros;
it specifically preserves nonnegative integer zeros.

If `P` is affine, substituting into any quadratic residual leaves a quadratic.
If `P` is quadratic and `x` occurs only in singleton monomials in the other
residuals, the same degree conclusion holds. The second condition is checked
from all current residuals, after all previous substitutions. In particular,
eliminating a quadratic gate and later discovering it was multiplied by another
variable is not permitted.

The final ordinary equation is the sum of the squares of the surviving
quadratic residuals. Over the integers its zero set is their simultaneous zero
set. Every delivered final polynomial is expanded exactly, so its exact degree,
monomial count, and coefficient height are computed from actual coefficients,
not estimated from the DAG.

## Certificate and replay

`affine_contract.py` exposes

```
contract(equation, support_cap=4, protected_variables=(),
         terminal_quadratic=False)
```

It returns the target equation and a certificate. Setting `terminal_quadratic`
enables the second case of the lemma. The support cap counts nonzero terms in
each local restoration, including a constant term when present. It does not
truncate a polynomial or change any coefficients.

The elimination order is deterministic: current source rows, then original
variable indices. All original indices remain unchanged during contraction.
Only the final export renames the retained coordinates consecutively. Each
step records its current exact residual, pivot sign, eliminated original
coordinate, and complete restoration polynomial. To reconstruct all original
witnesses, insert the retained coordinates and execute the recorded
restorations in reverse order. Each composed restoration remains an integer
polynomial with nonnegative coefficients. Thus no extra existential witnesses
are hidden in the certificate or reverse map.

`independent_verify(source,target,certificate)` uses a separate literal-list
expansion algorithm. It invokes neither the contraction routine nor its sparse
substitution or multiplication functions. It checks each monic pivot identity,
every restoration's coefficients and support, all substituted rows, degree at
most two after every step, every original-index/target-index correspondence,
and the source/target canonical JSON hashes. It reconstructs the entire target
residual list exactly. There is no finite-box inference in this check.

For the emitted examples no unused coordinate and no nonpivot zero residual
is dropped. Consequently the repeated elementary lemma gives a literal
bijection of simultaneous nonnegative zero sets, not just an existence
equivalence. The generic checker also handles genuinely unused coordinates,
in which case it restores them to zero and claims existence equivalence or
a bijection after ignoring those free factors.

## Measured tradeoffs on the 1,151-coordinate synchronized source

The input has 987 quadratic residuals, and its single sum of squares has
6,088 monomials and maximum absolute coefficient 63,908,952.

| Mode | Support cap | Variables | Residuals | Exact degree | Expanded monomials | Maximum absolute coefficient |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Affine only | 4 | 1,010 | 846 | 4 | 9,063 | 63,911,233 |
| Affine only | 8 | 974 | 810 | 4 | 11,192 | 2,445,790,974,704 |
| Affine and terminal quadratic | 4 | 765 | 601 | 4 | 8,660 | 63,910,647 |
| Affine and terminal quadratic | 8 | 723 | 559 | 4 | 11,605 | 2,445,790,974,704 |
| Affine and terminal quadratic | 16 | **698** | **534** | **4** | **12,386** | **211,184,624** |
| Affine and terminal quadratic | 32 | 693 | 529 | 4 | 20,444 | 83,905,351 |
| Affine and terminal quadratic | 64 | **691** | **527** | **4** | **22,199** | **83,905,699** |

Cap 128 also leaves 691 coordinates but has 25,219 monomials and a larger
maximum coefficient, so it is dominated by the cap-64 version. The cap-16
version is a useful smaller expression; cap 64 wins on coordinates among the
tested deterministic choices. No optimality of contraction order or globally
minimal polynomial is asserted. These figures are direct reductions of the
synchronized polynomial, not a separate consistency encoding.

## Semantic boundary

This pass proves an exact polynomial equivalence over the stated domain and
therefore composes with the synchronized compiler's semantic theorem. It does
not reprove the direct proof-calculus calibration, CRT batch theorem, factorial
or power graph theorems, or ZFC consistency. Its contribution can be checked
without trusting any of those interpretations, and that independence is
precisely why it runs after literal equation export.
