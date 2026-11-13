# Independent source review: natural-81 iPRA endpoint draft

The [endpoint draft](../../research/ordinary14-natural-forcedj81-ipra-draft/README.md) connects the selected symbolic K0 assumptions, the proposed 81-to-82 zero transfer, and the existing endpoint interfaces in the correct directions at the source level. Both receipts reproduce. None executes Lean or establishes an endpoint theorem.

The J-shift source assumes port 1 is the image of a model element `κ` and that `κ>0`. The strict-K0 source proposes both statements for `κ=(paramKernel rho : V)` at `CompactSymbolicModelIff.p`; the endpoint supplies those two declarations with the same symbolic port tuple to `exists_zero_iff`. Its underlying positivity argument and the changed-valuation zero transfer have separate source reviews. Their assumptions, casts, proof tactics and providers remain unelaborated.

The proposed existence equivalence is oriented from an 81 zero to an 82 zero and conversely. Thus, given 81 no-zero, the endpoint excludes an 82 zero by taking `he.mpr`; given 82 no-zero, it excludes an 81 zero by taking `he.mp`. The endpoint then invokes the source `SameNoZero` bridge and proposes native, standard and equality-only derivability statements. The independent receipt pins the endpoint and eight cited source files, checks these directions and assumptions, compares the three target statement texts to the natural-82 endpoints, and inspects the adapter calls. This is a bounded source-interface check, not exhaustive import resolution or a type check.

The five `#print axioms` commands in the endpoint are unexecuted. Actual Lean must check all imported declarations, model instances, casts, the two existential `change` steps, provider coherence, and the reference adapter's reduction to the displayed equality-only target. Neither the `IΣ₁` model framework nor these source declarations alone establish iPRA derivability. No connection to external coefficient bytes or the different displayed Carrier65 PDF follows from this draft.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-forcedj81-ipra-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-forcedj81-ipra-independent/result.json
```
