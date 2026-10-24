# Alternative encodings: measure the verifier before compressing its variables

Neither K215 nor a Jones universal polynomial is required. The immediate
alternative implemented here is a **closed executable quartic** for actual
syntactic ZFC refutability, retaining its concrete graph variables instead
of applying the nine-variable Jones reduction. Its degree is at most four;
its exact variable and operation counts have not been numerically evaluated.
Lean now proves the conservative bound `nu < 2^300000` for this actual
closed recipe; see [NATIVE_QUARTIC_SIZE.md](NATIVE_QUARTIC_SIZE.md).
This is a different tradeoff, not a claim that it dominates every existing
candidate.

## Concrete comparison

All domain restrictions matter. “Closed” in this table means that no
program, coefficient representation, or compiler-correctness premise remains
in the external correctness theorem.

| Construction | Variables/domain | Degree evidence | Arithmetic cost evidence | Coefficient evidence/status |
|---|---|---|---|---|
| `ExplicitZFC` | 9 naturals | Fixed finite polynomial; numerical degree not materialized | Full evaluator count not measured | Closed executable coefficient recipe; external no-zero iff `ConZFC` checked |
| `NativeZFC` | 9 naturals | Same Jones compression, from direct arithmetic graph data | Source step has exactly 1,742 graph witnesses; this is not a final evaluator count | Closed executable recipe; external no-zero iff checked |
| New `DirectQuarticZFC` | `nu` naturals, **`nu < 2^300000`**, Lean checked upper bound; exact count unmeasured | **At most 4**, Lean checked | **At most `6*(nu+1)` syntax-tree binary operations**, Lean checked | Closed executable syntax, actual polynomial/evaluation identity, external no-zero iff checked; no Jones index construction |
| Generic `DAGQuartic` compiler | `n+2*m` naturals for `n` inputs and `m` stored nodes | At most 4, Lean checked | At most `12*m+4` tree operations, Lean checked | Signed intermediates and arbitrary constants allowed; sharing retained; no complete ZFC checker compiled through this yet |
| Generic `NaturalDAGQuartic` compiler | `n+m` naturals | At most 4, Lean checked | At most `6*m+4` tree operations, Lean checked | Source uses nonnegative constants, addition and multiplication, comparing two output wires; no whole-checker size claim |
| `ZFC.zfcQuarticPolynomial` | 58 naturals | At most 4, Lean checked | Not measured | Existence-based coefficient selection; not an exported executable coefficient recipe |
| Package 66 H2082 simple | 9 positive / 9 natural | Exact 1,845,940, finite certificate review | 444 / 451 live binary operations | Delivered source/circuit candidate; authentic source-to-refutation and internal ZFC obligations remain |
| Local H2082 compact54-sharp | 9 positive / 9 natural | At most 1,845,940 in Lean; exact degree in finite audit | **443 / 450 live binary operations**, Lean checked and bound to actual polynomials | Whole native tuple 215,492 raw bytes; eleven derived live fixed leaves 1,565,018 raw bytes; source arithmetic and circuit identity checked; native source/refutation and internal ZFC bridges remain |
| Package 59 compact54-sharp, shared powers | 9 positive / 9 natural | Exact 1,910,404 | 456 / 463 operations in the shared-power candidate | Native tuple 215,492 raw bytes; twelve derived live fixed leaves 1,672,725 raw bytes. Source-equivalent polynomial is checked; this is not yet a closed consistency endpoint |
| Inherited P67 | 15 positive | Exact degree 155 in its circuit audit | 67 binary operations | Four native coefficient ports; its full native-to-refutation semantic bridge remains separate |

The package-66 and package-59 figures are circuit-certificate measures,
where sharing is counted. The new quartic bound deliberately counts the
entire syntax tree and does not assume sharing. Raw coefficient storage,
gzip storage, source witnesses, final polynomial variables, arithmetic tree
operations, and live DAG operations are different measures. A low value in
one column cannot fill an unmeasured entry in another.

The current wave-nine frontier is recorded in
[PROPOSAL_REVIEW_WAVE9.md](PROPOSAL_REVIEW_WAVE9.md) and
[PROPOSAL_REVIEW_WAVE9_ARITHMETIC.md](PROPOSAL_REVIEW_WAVE9_ARITHMETIC.md).
Those source/circuit improvements remain useful in their own branch.

## Implemented quartic endpoint

[DirectQuarticZFC.lean](Lean/DiophantineConsistency/DirectQuarticZFC.lean)
uses the actual closed `NativeZFC.representation`. Split its integer
residual into natural expressions, simplify constants/zero/unit operations,
and remove unused original witness slots, as in the existing checked
`CompactedJones.left/right` preprocessing. The name of that preprocessing
module does not introduce a Jones polynomial into this endpoint.

Let `m` be the retained original witness count and `Gp,Gq` the two explicit
natural-expression gate counts. The exact recurrence is

```
nu = m + Gp + Gq + 1.
```

There is one variable per original witness, one per node of each natural
expression, and one normalization guard. The unused distinguished input is
specialized to one and removed. The equation is the sum of squares of all
quadratic gate residuals, the output equality, and the guard residual. Its
coefficients are specified by executable `Expr` syntax; the ordinary
`MvPolynomial` interpretation is proved equal to that syntax.

[QuarticCost.lean](Lean/DiophantineConsistency/QuarticCost.lean) proves that
each residual uses at most two binary operations. Squaring its tree costs
at most five, and adding it to the accumulator costs one. There are exactly
`Gp+Gq+2` residuals, hence

```
operations <= 6*(Gp+Gq+2) <= 6*(nu+1).
```

These are transparent, proved bounds for the actual supplied syntax, not a
claim that a large `nu` has already been printed. No universal Jones index,
its positional powers, or its derived fixed numerical payload is constructed
by this equation. The direct graph's own finite arithmetic constants remain
part of the recipe; their expanded aggregate byte count is unmeasured.

Two controlled count probes are recorded in
[data/alternative-encoding-measurements.json](data/alternative-encoding-measurements.json).
Evaluating the complete representation's witness-count projection with
`#eval` exceeded a 45-second cap; lazy `#reduce` hit a 200,000-heartbeat
limit. A separate formula-tree gate-count probe also exceeded 45 seconds.
These failures do not invalidate the finite definitions, and they do not
supply numerical counts. They do show why “the step has only 1,742 witnesses”
is insufficient to claim a small final quartic.

The checked [structural size recurrences](STRUCTURAL_SIZES.md) now supply
another measurement method. They propagate witness counts and expression
depth numerically and bound the raw quartic by `nu+1<=m+2^(2*h+2)` without
constructing its trees. The [closed-source metadata application](NATIVE_QUARTIC_SIZE.md)
now proves witness count plus one at most `2^22426`, depth at most 140000,
and actual compacted quartic variable count below `2^300000`. This is a
conservative upper bound, not an exact count or a size advantage over other
quartic constructions.

## Direct source: a supplied sealed-ZFC proof certificate

The direct route now has an annotated proof-certificate checker, replacing
exhaustive candidate enumeration at the semantic source. Its arithmetic
compilation must preserve sharing. It targets the repository's
**actual sealed ZFC calculus**, because its internal
axiom and derivation formulas already exist and quote the requested theory.
A checker for the smaller C222 calculus is a useful optional benchmark but
retains a separate internal calculus-to-ZFC translation obligation.

[`AnnotatedProofChecker.lean`](Lean/DiophantineConsistency/AnnotatedProofChecker.lean)
contains finite records with rule tags, backward parent indices, complete
context/formula annotations and schema parameters. Explicit tags construct
the actual sealed axioms; validation checks exact ordered premises and all
seventeen original calculus rules. Lean proves that an accepted certificate
exists exactly when `BProv ZFCax_s [] Form.fBot` holds. The source has no
K215/Jones dependency, axiomhood oracle or choice-based data. It does not
assume a refutation exists. See
[ANNOTATED_PROOF_CHECKER.md](ANNOTATED_PROOF_CHECKER.md). Its
[executable numeric coding](ANNOTATED_PROOF_CODE.md) now has checked typed
roundtrips, parser uniqueness, fuel truncation and the same exact refutation
existence endpoint. Primitive-recursive/arithmetic compilation is next.

[Local PR arithmetic](ANNOTATED_CODE_ARITHMETIC.md) now supplies literal
`ScalarPRCode` data for code constructors/projections, guarded list lookup
and checking an earlier judgment's complete context and formula. The lookup
program has 69 syntax nodes; the optimized reference check has 209. These
are PR-program sizes, not polynomial operation or witness counts, and do
not represent the whole checker.

For arithmetic compilation, pack the finite line columns, use explicit
quotient/remainder or beta-entry graphs for parent references, and compile
one bounded universal family of local checks. The existing bounded-forall,
power, factorial, remainder and trace representations can supply an initial
closed polynomial without passing through a universal polynomial. Then
measure the complete result before considering variable compression.

The sharing requirement is concrete. The natural formula constructor

```
Imp(a,b) = 2*(a+b)*(a+b+1) + 4*b
```

needs six binary operations if `a+b` is stored once, while its literal
binary expression tree contains seven. Nesting constructors repeatedly
multiplies this difference. The current source's bulk `axStack` additionally
inlines ten nested pair constructors. A line certificate does not need to
push every available axiom on every AX instruction. An explicit arithmetic
DAG can store and reuse each formula/pair intermediate, then introduce one
quadratic gate equation per DAG node. The repository's new
`ArithmeticDAG.Node`, `run`, `Topological` and polynomial semantics are suitable
reusable interfaces. A quantified trace still needs bounds and a proved
encoding; replacing a tree by an alleged DAG without its value theorem
would not establish correctness or a size improvement.

[`DAGQuartic.lean`](Lean/DiophantineConsistency/DAGQuartic.lean) now supplies
that shared-circuit-to-quartic primitive, including signed node values. Its
actual polynomial has `n+2*m` natural slots and at most `12*m+4` tree
operations, and its zeros correspond exactly to the circuit's zero outputs
under topology. The explicit gate witnesses split each integer into its
positive and negative natural parts. Leaf nodes are charged too; no final
checker size advantage is inferred from this generic bound. See
[DAG_QUARTIC.md](DAG_QUARTIC.md).

For nonnegative arithmetic, the checked
[`NaturalDAGQuartic`](NATURAL_DAG_QUARTIC.md) compiler compares two output
wires using only one natural variable per node: `n+m` slots and at most
`6*m+4` operations, still at degree at most four. Its source restrictions
are explicit. Both compilers retain sharing and charge all stored leaf
nodes. Their bounds do not measure the whole certificate checker.

The exact C222 benchmark source is especially clear:
[KCode222.lean](../BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean) has twelve
constructors: truth, modus ponens, generalization, eight named row families,
and the guarded bundle. An annotated proof-line checker can check a single
selected leaf/rule and earlier premises instead of executing the six-register
candidate enumerator or its ten-entry AX stack. Existing
`NativeFormulaSyntax` gives the actual polynomial formula constructors.
No numerical claim that the complete resulting polynomial has fewer than
1,742 witnesses is made until that construction is measured.

## Other concrete routes and their costs

**Direct bounded arithmetic/DPRM.** Start from the explicit certificate
relation, use supplied arithmetic syntax and bounded universal compilation,
and stop at its gate quartic. `BoundedForallRepresentation` and
`ScalarPRRepresentation` already show that executable data can be retained
through CRT/Pell-based constructions. This avoids nine-variable positional
coding. Its variable count includes all trace/CRT witnesses and every gate;
those costs cannot be replaced by the number of source registers.

**A different axiom system.** Changing the Hilbert calculus to a sequent or
annotated natural-deduction calculus may shorten local checking, but it
requires proved transformations of finite refutations in both directions.
A purported shorter finite axiom theory would additionally need the relevant
conservativity/equiconsistency proof in ZFC. No such new translation or size
advantage is supplied here. Reusing the actual sealed calculus avoids adding
that unsupported premise.

**Keep the supplied enumerator, improve its compiler.** This is the lowest
semantic-risk engineering alternative: replace tree duplication by a
certified shared-DAG compiler, retain direct Cantor quadratic graphs, and
stop at the quartic. The existing one-step 6,924→1,811→1,742 reductions are
real witness-count results, but denominator clearing and polynomial inlining
can increase subsequent gate counts. A measured shared-DAG compilation is
needed to decide whether those transformations improve the final equation.

## The object-language ZFC proof remains essential

`DirectQuarticZFC.noNaturalZero_iff_conZFC`, like the closed nine-variable
baseline, is an external Lean theorem. The user asks for equivalence
**provable in ZFC**. A complete replacement therefore also needs an actual
`BProv ZFCax_s []` derivation of an iff between the sealed internal
consistency sentence and the no-zero sentence for this supplied quartic.

`ObjectPolynomial.noZeroForm` already applies to any supplied finite `Expr`,
including this quartic. `ObjectCodeSeal.consistencySentence` already matches
the sealed axiom convention. What remains is uniform checker/encoding
correctness over every ZFC model's own omega, including nonstandard
certificates and tuples. Correctness only on external numerals is
insufficient. One must supply internal totality and functionality of the
coding operations, soundness and completeness of certificate checking, and
both directions of the arithmetic representation in those models; the
existing first-order completeness interface can then produce the requested
object proof.

A direct sealed-ZFC checker removes the need for some intervening calculus
translations, but does not automatically prove this uniform arithmetic
compiler theorem. No route here proves absence of zeros independently of
`Con(ZFC)`, branches on the truth of consistency to choose coefficients, or
uses a bounded-consistency family as a proof of unrestricted consistency.
