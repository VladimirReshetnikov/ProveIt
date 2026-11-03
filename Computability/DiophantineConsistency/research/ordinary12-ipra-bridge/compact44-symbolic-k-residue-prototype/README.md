# Symbolic compact44 kernel residue: Horner calculation

`SymbolicKernelResidue.lean` proves the actual natural-number
`CompactSymbolicKernelOpaque.paramKernel rho` is `284898815895` modulo
`342946332593`, without expanding the roughly 593,000-bit integer. The
retained source is byte-for-byte the successful compiler input; its original
opening comment calling it an uncompiled draft is historical and outdated.
This is a single-author exploratory build, not a paired replay or a fresh
authenticated source closure.

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

The external script exited 0; its reading and transcribed arithmetic are
supplementary evidence rather than the Lean proof. The first bounded compile
exited 1 with a looping nil-case simplification, redundant cast rewrite, and
an unresolved `ZMod.val` simplification; its exact source and output are
retained and do not constitute a proof. After those issues were repaired,
attempt 02 exited 0 in 7.21 seconds with no warnings. Both final theorems
report only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`. The exact input, output, direct imported-object hash and command
are in `observations/`; package, transitive and dynamic ancestry are inherited.

The successful build uses a different symbolic-kernel provider from the
earlier conditional-unit client, and shared imported object hashes differ. A
client applying `gamma_unit_nat` to this same `paramKernel rho` requires a
coherent same-provider rebuild before the results can be joined. Neither the
symbolic residue theorem nor that prospective join identifies retained bytes
or proves the rank variation, dummy locations, graph zero, or iPRA theorem.
