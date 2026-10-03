# Five natural witnesses for a congruence truth atom

For a fixed integer modulus `d≥1` and an already evaluated signed affine input `L`, replace the six-witness congruence gadget in the [sparse-lattice report's post-elimination compiler](review_sparse_lattice_aebfa386e.md) by five natural witnesses `(q+,q−,b,s,h)` and five quadratic residuals:

```
q+q−,
L − d(q+−q−) − b(s+1),
b(s+1) + h − (d−1),
b(b−1),
(1−b)s.
```

The truth output is the affine expression `1−b`. Every integer `L` has exactly one natural witness tuple. If `q,r=divmod(L,d)`, it is

```
(max(q,0), max(−q,0), [r>0], max(r−1,0), d−1−r).
```

The Boolean row forces `b` to zero or one. Put `a=b(s+1)`. Then `0≤a<d` follows from naturalness and the third row. The second row fixes the unique Euclidean quotient/remainder, and the product `q+q−=0` uniquely splits its signed quotient. For `a=0`, `b=0` and the last row forces `s=0`; for `a>0`, `b=1` and `s=a−1`. This covers negative `L`, zero quotient, and modulus one without an inactive free slack.

This is an exact projection of the original six-witness gadget: restore the deleted remainder as `a=b(s+1)`, a natural value for every natural new tuple. Under that substitution the first four old residuals equal the new ones, and the last equals `(1−b)s`. The chosen implementation computes its negative, which has the same square. Hence the complete old sum of squares on the restoration graph equals the new polynomial identically, even off zero. The general post-elimination circuit ledger improves from `2I+6C+G` to **`2I+5C+G` natural witnesses** while retaining **`2I+5C+G+1` quadratic residuals**. Both truth and falsehood have a unique internal assignment; only the final Boolean output guard chooses acceptance.

## Actual arithmetic schedule

The [source](presburger_congruence_five.py) emits and evaluates a literal binary gate list, rather than estimating expanded monomials. Share `bs=b·s`, form `a=bs+b`, reuse `b−1`, and compute the last residual as `bs−s`. The five residuals cost `4M+8A`. Five squares and four additions give **`9M+12A=21` operations** for their sum of squares. Every multiplication by the fixed modulus and every used addition/subtraction of a constant is charged; fixed constants such as `d−1` are compiler constants. No constant folding at `d=1` is used in this displayed schedule.

The helper also emits a six-witness baseline that shares `b−1` when forming `2b−1`. That chosen baseline costs `9M+13A=22`. Thus this is one fewer operation and one fewer witness than that explicitly implemented baseline, not an optimum over all possible congruence formulas. The cost of evaluating `L`, using the truth expression, other atoms, Boolean gates, and the complete final sum is separate. One must not multiply 21 by the number of atoms and silently omit shared outer compilation or final accumulation.

The [receipt](presburger_congruence_five.json) includes exact symbolic residual and full graph-polynomial identities, exact degree four, 328 complete bounded-fiber enumerations, 1,000 large signed canonical cases, 1,000 signed all-value circuit checks, and 5,000 rejecting coordinate mutations. The general uniqueness argument establishes the unbounded claim; those cases are implementation regressions. The [independent review](review_presburger_congruence_five.md) checks both proof and literal schedules, with its own pinned checker and receipt; it identified the stronger off-zero graph identity now verified by the source. Root reproduced that independent receipt.

```
python presburger_congruence_five.py --expect presburger_congruence_five.json
```

This compiler applies to any fixed quantifier-free Presburger predicate, including the mass-two reachability formulas after paid effective elimination. Quantifier elimination can be very large and is not implemented for arbitrary CA rules by the source report. No single-fold universal relation or improved universal87 bound follows from this decidable-subclass improvement.
