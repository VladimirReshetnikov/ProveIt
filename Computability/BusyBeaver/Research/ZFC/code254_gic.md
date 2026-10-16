# Actual first-order GIC instances from encoded bundles

`Code254GIC.lean` proves
`modelsCPGIC_of_encBundle`: a model of all literal `EncBundle` formulas,
with global irreflexivity and a supplied valuation, satisfies the existing
`ProfileModel.ModelsCPGIC` interface. Together with `Code254Containers`,
this connects the numerical bundle theory to the existing profile and
bisimulation quotient modules. It proves no ZF interpretation, enumerator
correctness, binary simulation or ZFC endpoint.

The stronger intermediate theorem `collection_of_matrix` covers **every
actual `SetTheory.Form` matrix**, including primitive equality. It does
not assume collection for arbitrary semantic relations. The final
`ModelsGIC` interface only requests equality-free matrices, so it follows
as a restriction of this proved result.

## Hygiene and semantics

Source free slot i uses odd named variable `2*i+1`. A quantifier at depth d
uses even variable `2*d`. The recursive name map retains prior bound names
and shifts de Bruijn slots in the usual way. `names_ne_future` proves that
no old slot uses any future even binder, and `relate_under` checks the
environment relation under each quantifier.

All eight source constructors are translated: membership, equality,
Bottom, implication, conjunction, disjunction, universal and existential
quantification. Bottom becomes `Rel(0,0)`; the remaining Boolean
constructors use the original relative-falsity definitions. The first
even binder can bind label 0. Global irreflexivity, rather than a reserved
point convention, makes this safe: the falsity atom stays false under
every updated environment. `sat_toNamed` proves the full satisfaction
equivalence, and `botFree_toNamed` proves the resulting syntax is an
ordinary Bottom-free named formula.

The parameter environment puts source parameters at odd labels 5,7,...,
with names 1 and 3 overridden by the input and output. Its exact slot
equation is proved for every index. `matrix_relation` then identifies the
named relation with the existing `DeepPositiveClosure.MatrixRelation`,
including its actual input/output and parameter environments.

## Exact gates and the G component

Finite named formulas have positive encodings, and every bound or free
label is strictly smaller than the encoding (`occurs_lt_enc`). In
particular, the code itself is not free in its matrix. These statements
concern ordinary finite named formulas; they do not assert syntactic
freshness of arbitrary decoded code 0.

For a named matrix f use the equivalent padding `(f→f)→f`. `sat_pad`
requires no model assumptions or axioms, and `pad_code_gt_three` proves
that its code c exceeds 3. Thus the chosen input/output labels `a=1`,
`b=3` satisfy both machine gates, and c is absent from every matrix label.
This matters even for the false matrix, whose unpadded code 1 would fail
the first gate.

`bundle_mem` checks that the **whole original C/G/vacuity conjunction**
is a literal `EncBundle` formula. Its encoding identity is the generic
definitional theorem in `Code254Containers`; no unchecked semantic wrapper
is substituted for the emitted program. The G component is projected
under irreflexivity and interpreted by `collection_at_of_namedG`:

- Every member of the output set has an unrestricted supporting input.
- Every input in the domain that has any output has a selected output in
  that set.

The proof retains the distinct environment-update orders for support,
forward lookup and replacement of the selected output. Freshness removes
only the auxiliary collection-set assignment. Domain label 3 is restored
before each matrix evaluation. This gives `collection_of_model` and then
the actual formula-indexed result `collection_of_matrix`.

The finite container adapter supplies the other half of `ModelsCPGIC`.
The valuation is explicit throughout, so the empty-domain completeness
premise error is not reintroduced.

## Verification and remaining boundary

The complete 328-line module compiled using the explicit absolute Lean
4.32.0 compiler in 0.99 seconds. All 24 public theorem axiom audits pass;
dependencies are limited to `propext`, `Classical.choice` and `Quot.sound`.
The padding equivalence and its Bottom-freeness proof use no axioms.
Three callers also pass: an explicit inhabitant supplies the valuation,
a primitive-equality matrix obtains its collection instance, and the new
model adapter composes with actual quotient Extensionality. The compiler
agent independently read the complete source and found no defect in
hygiene, gates, matrix environments or scope. Commands and results are in
`results/code254-gic-verification.json`.

The result consumes literal encodable bundles. It does not establish that
all decoded bundles have a model, identify those two model theories, or
invert arbitrary numerical codes. In particular, the current decoder's
zero truth alias has syntactically free label 0, whereas upstream uses a
closed truth representative. The earlier `code254_containers.md` records
that distinction and the pinned upstream proof map.

The existing quotient now applies to these actual bundle models and gives
an extensional structure with checked satisfaction. Full formula-indexed
Separation and Replacement, the other quotient ZF axioms, the exact
infinity comparison and the opposite ZFC-to-source direction remain
separate proof obligations. No machine was changed or remeasured here.

The subsequent [QuotientSeparation development](quotient_separation.md) now
supplies the complete actual Separation schema, including arbitrary quotient
parameter valuations. [The enumerator audit](enum254_review.md) separately
checks the abstract enumerator/numerical-derivability equivalence. These
advances retain the remaining interpretation and concrete simulation gaps.
