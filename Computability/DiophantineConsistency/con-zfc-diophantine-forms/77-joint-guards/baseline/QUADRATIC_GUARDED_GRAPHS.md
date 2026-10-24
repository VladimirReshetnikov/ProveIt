# Quadratic zero tests, conditional selection, and actual list head

The new data-valued local schemes attach to an existing natural register
bank using the frozen `System.instantiate` and `System.conjunction` APIs.
They copy slot indices, preserve previously shared registers, and hide a
single preallocated auxiliary scope at the final representation boundary.
Their correctness covers every natural input, including zero. They do not
compile the complete proof checker or prove an internal ZFC statement.

| Graph | Natural witnesses | Exact expression binary operations | Polynomial degree bound |
|---|---:|---:|---:|
| Zero test | 1 | 20 | 4 |
| `ifZero(test,yes,no)` | 2 | 32 | 4 |
| Actual annotated `listHead` | 7 | 76 | 4 |
| Existing scalar-graph annotated `listHead` | 11 | 8,231 | 1,024 |

Binary operations count every syntax-tree addition, subtraction, and
multiplication, including squares and scalar products. The old degree
1,024 is a checked syntax-derived upper bound; it is not asserted to be
the normalized polynomial's exact degree. All rows in the new local
systems have degree at most two. Their single polynomial is the sum of
squared residuals, so it has degree at most four.

For the zero test, on natural slots `(bit,n,s)` the three integer residuals
are

```
bit*(bit-1),   bit*n,   n-(1-bit)*(s+1).
```

Their joint zero set forces `bit=1` when `n=0` and `bit=0` otherwise.
Completeness uses `s=n.pred`, covering both the zero and positive cases.
For conditional selection, add the quadratic row

```
out-(bit*yes+(1-bit)*no).
```

The resulting six-slot context has the four visible inputs
`(out,test,yes,no)` and two auxiliary slots. It represents the total
conditional `out = if test=0 then yes else no`, with no supplied side
condition and no scalar primitive-recursion inlining. The reusable
`zeroSystem` and `conditionalSystem` can read stored registers through
the composition API.

The actual checker encodes a list cell by `Nat.pair head tail + 1`, using
Mathlib's maximum-square pairing. Its total function is

```
listHead code = if code=0 then 0 else (Nat.unpair code.pred).1+1.
```

The successor marks a found entry. In particular, nil has output zero
and a cell containing zero has output one. The sharper direct certificate
retains the frozen six-row tree-left scheme and adds only

```
code*(out-left-1),   code-out-slack.
```

At a positive code the first row forces `out=left+1`. At code zero the
second row, with natural `out,slack`, forces `out=0`. Completeness uses
`slack=code-listHead code`; the theorem `listHead_le` proves that this is
an exact natural slack for every code. No additional Boolean witness is
needed. One nine-slot context contains output, code, left projection,
predecessor, the other pair component, pairing selector, pairing slack,
maximum component, and output-bound slack. The seven hidden slots are
shared across all eight quadratic rows.

The new modules are
[`QuadraticBoolean.lean`](Lean/DiophantineConsistency/QuadraticBoolean.lean)
and [`QuadraticListHead.lean`](Lean/DiophantineConsistency/QuadraticListHead.lean).
Their separate checks establish universal zero-equivalence theorems,
both conditional branches, nil behavior, arbitrary list heads, and the
found-zero marker. Metadata and the existing baseline costs are checked
by the Lean kernel. The 26 audited theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom, or native
evaluation axiom is used.

The files add relational arithmetic certificates for actual local checker
operations. A complete data-valued graph for the checker, its coefficient
size comparison, and the internal object-ZFC proof remain further work.
