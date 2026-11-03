# Symbolic compact44 kernel residue: Horner draft

`SymbolicKernelResidue-DRAFT.lean` is **uncompiled**. It proposes proving
the actual `CompactSymbolicKernelOpaque.paramKernel rho` residue modulo
`342946332593` without expanding the roughly 593,000-bit integer. No Lean
theorem, file binding, model unit, graph construction, or iPRA conclusion is
claimed by this draft.

The draft follows the older checked `ArithmeticConstructionKernel` method.
For the exact `Compact943Data.rows` list, define

```
H(r) = sum_{i=0}^{942} selector(row_i) * r^(942-i).
```

Both selector bands then equal `H(r)*(r^3451+r^4553)`; the remaining 41
copy terms are computed independently in the same `ZMod` ring. A generic
Horner recursion has the same value as `H`. The intended calculation uses
only residues modulo `342946332593`, then converts the `ZMod` equality to
the natural-number remainder needed by `gamma_unit_nat` in the companion
[conditional unit client](../compact44-controller-unit-prototype/README.md).

`check_horner.py` externally parses the existing Lean row and slot lists and
uses a separately transcribed selector formula to check these residues:

| part | residue |
| --- | ---: |
| `rho = 2^67` | 139640128744 |
| `H(rho)` | 294576924025 |
| both selector bands | 33533167632 |
| both copy bands | 299839741459 |
| four bare terms and temporal term | 294472239397 |
| whole proposed `paramKernel rho` | 284898815895 |

The external script actually exited 0. Its reading and transcribed arithmetic
are evidence for the numbers, not the required kernel-checked equality.
The open work is to compile the draft on a coherent provider and repair all
elaboration or resource failures. In particular, the 943-step `decide
+kernel` may need bounded chunks: prove a list-append law for `run`, split
the literal list, and certify each intermediate state separately. Then compile
a client applying `gamma_unit_nat` to the *same* symbolic `paramKernel rho`.
Even that result would not identify the retained bytes or derive the rank
variation and dummy-location premises.
