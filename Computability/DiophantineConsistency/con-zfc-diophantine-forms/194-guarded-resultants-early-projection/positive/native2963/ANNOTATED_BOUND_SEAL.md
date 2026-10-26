# Numeric arithmetic certificates for bound and sealing

The new supplied programs compute and validate the actual additive formula
bound in `FirstOrder/Fol.lean`, then apply its literal universal closure.
For every external Lean formula `f`, `AnnotatedBoundScan.exists_seal_program_iff`
proves

```text
(∃ table length,
  sealProgram.eval (sealInput (formCode f) output length table) = 1)
↔ output = formCode (sealF f).
```

The program data use neither an axiomhood oracle nor a selected witness from
a primitive-recursiveness theorem. This is a further operation needed by the
independent annotated sealed-ZFC checker; it is not yet the entire arithmetic
checker or a new closed Diophantine equation.

## Exact operations and certificates

`AnnotatedClosure.lean` gives a literal program for iterating the existing
universal formula constructor. `closeCode_formCode` proves agreement with
`closeN` at every supplied length, and `program_sealF` specializes that length
to the actual `bound f`. A separate proof establishes `44 ≤ formCode f` for
all formulas. Consequently a universal constructor on valid formula codes is
exactly `c*c + 39`. The quadratic iterator agrees with the constructor-based
iterator on every actual formula, at every length. There is no claim that an
arbitrary small natural is a valid formula code.

`AnnotatedClosureGraphs.lean` supplies the graph equation
`output = input*input + 39`, with zero extra natural witnesses. This describes
one closing step. It is not a graph of the complete variable-length iteration.

`AnnotatedBound.lean` reuses the frozen six-field row codec and natural list
spine. Its named local conditions are:

- Atomic membership/equality: exact input constructor and output
  `(first+1)+(second+1)`.
- Bottom: exact fixed code and output zero.
- Binary connective: two guarded backward references, the exact input
  constructor, and the sum of their outputs.
- Quantifier: one guarded backward reference, zero in the unused second
  reference field, the exact input constructor, and its unchanged output.

The row depth field is unused by this operation. No recursive formula parser
appears in these local conditions. Induction over accepted rows proves
soundness; formula induction constructs finite accepted tables. Thus the
certificate language computes the actual additive `bound`, including its
unchanged value through both binder constructors. The bound is not replaced
by a maximum or a free-variable approximation.

`AnnotatedBoundLocal.lean` supplies literal `ScalarPRCode` data for every
local condition. `AnnotatedBoundScan.lean` supplies the complete guarded
numeric scan, root comparison, and sealing checker. Their exact equality to
the semantic table checks holds at every natural input, including malformed
codes. The scanner traverses the encoded list spine with numeric-code fuel;
its simulation theorem first proves that the spine decoder is total at that
fuel. The supplied sealing program evaluates the bound validator once and
uses its zero/one classification to branch.

## Checked size and validation

The following are Lean `decide` theorems about the actual supplied program
syntax, not estimates of a later polynomial or of runtime:

| Supplied scalar program | Nodes | Optimized nodes |
| --- | ---: | ---: |
| Constructor-based universal closure | 37 | 37 |
| Quadratic universal closure | 119 | 119 |
| Local bound validator | 1775 | 1551 |
| Whole bound validator | 2095 | 1807 |
| Whole sealing validator | 2279 | 1983 |

The quadratic step has a simpler direct polynomial graph, while the existing
primitive-recursive constructor program has fewer syntax nodes. The whole
bound scanner has 1867 nodes and its terminal comparison has 221.

Dedicated checks exercise both valid constructors, a quantifier preserving
the bound, a wrong bound, an out-of-range backward reference, a forbidden
tag, a wrong closing length, and a truncated scan. Nonempty runtime scan
controls use the supplied table length; only tiny zero inputs are executed
through the actual primitive-recursive whole programs. Canonical numeric
fuel and naive arithmetic recursion can be very slow on large code values.
No efficient-runtime claim is made.

## Remaining mathematical interfaces

The external supplied programs and their accepted existential languages are
proved. The [schema-specific programs](ANNOTATED_SCHEMAS.md) now compose
the exact maps `rsep`, `rf1`, `rf2`, and `ri` and assemble and seal the actual
Separation and Replacement formulas. The complete axiom-tag dispatcher
and proof-line validation loop remain separate.

The local arithmetic tables are also intended for a later interpretation over
an arbitrary model's internal omega. That requires an actual internal coding
relation, construction and validation of the finite tables there, and their
exact agreement with the existing `ObjectCodeBound`/`ObjectCodeSeal`
operations. External-natural correctness does not discharge these obligations.
The model-omega semiring laws can support this work, but supply no automatic
external-to-internal transfer. No claim about a measurable whole polynomial,
a new variable count, or the consistency equivalence follows from this layer
alone.
