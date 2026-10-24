# A Diophantine equation for syntactic consistency of ZFC

Research started 23 October 2026, from repository commit `22e75dd6b8`.
This directory contains active research, its Lean proofs, and the delivered
manuscripts in [con-zfc-diophantine-forms](con-zfc-diophantine-forms/README.md).
The manuscript collection was moved here from the Cardinals reports tree
on 23 October 2026 at the repository owner's request.

The target is one integer-coefficient polynomial, with an exactly stated
witness domain, whose absence of zeros is equivalent to the absence of a
finite derivation of falsity from the repository's ZFC axiom predicate.
Neither consistency nor inconsistency is assumed.

The current priority is equation size and complexity. At the repository
owner's request, Lean formalization is paused. Research continues on
smaller arithmetic circuits, simpler complete printed coefficient recipes,
and alternative encodings. Completed proof checkpoints are retained;
unfinished formalization files are not being extended during this phase.
See [the active size-reduction plan](SIZE_REDUCTION.md).

The current [equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) print the **entire equation in10 positive
unknowns, exact degree408, with a105-operation evaluator**. Every fixed
constant is defined on the same Letter page, including the full436-character
numeral, alphabet, decoder and943 tiles. The body uses9-point type.
Compared with the preceding ten-positive123-operation degree816 display,
this halves degree and saves18 operations at the same unknown count.
The same coherent BFS-renamed compact44 tuple and complete constant recipe
are retained. The [page proof and checks](candidates/one-page-quadratic10/README.md)
include the exact free-port identity, recovered main Pell ordinate, complete
positive witness maps, inherited typed-color/native/controller proof and
independent whole coefficient reconstruction.
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) binds the displayed files.

The preceding [ten-positive degree816 page](candidates/one-page-scaled10/equation.pdf)
is preserved, along with the earlier
[thirteen-positive degree51 page](candidates/one-page-ordinary13/equation.pdf)
is preserved with its standalone [TeX](candidates/one-page-ordinary13/equation.tex).
It uses fewer operations and lower degree, with three more unknowns; the
new display does not claim a global optimum across these tradeoffs.

The previous [fifteen-positive page](candidates/one-page-compression/merged-mask-base62/equation.pdf)
and its other notation variants remain available. Its corrected recipe
has2297 nonwhite characters,8.8% below the corrected771-digit recipe.
State renaming reduces payload bits; changing numeral notation reduces
printed symbols. See
[SEED_COMPRESSION54.md](SEED_COMPRESSION54.md) and
[SEED_PREDICTORS54.md](SEED_PREDICTORS54.md) for those distinct gains, and
[INITIALIZATION_CORRECTION.md](INITIALIZATION_CORRECTION.md) for the
earlier transition-only calibration gap and its full tile-level repair.

The displayed `equation.pdf` and its TeX source are maintained research
outputs. After a substantial improvement to the displayed construction,
update them to the checked new equation and state its exact domain and
size tradeoffs. Minor circuit changes need not trigger a new rendering.
Preserve the previous page for comparison, and print the complete fixed
constant recipe on the updated page; an external coefficient table or
program is not a substitute for that recipe.

The [twelve-positive polarized equation](candidates/free-j-polarized-positive/README.md)
has96 live operations and exact degree70, improving the earlier100-operation
[ordinary-norm form](research/ordinary-unit-products/README.md). It materializes and checks an
arriving manuscript's ordinary-norm reduction, including its early rank
bound and two-way witness reconstruction. The coherent compact44 tuple is
retained; native calibration and the internal-ZFC proof remain separate.
Its [thirteen-positive companion](research/ordinary-unit-products/ORDINARY13.md)
has90 operations and exact degree51, lowering the preceding90/55 form's
degree at the same arithmetic cost.
The [Hilbert Tenth root-elimination transfer](candidates/fixed-root-elimination/README.md)
also gives fourteen-positive73-operation/degree342 and75-operation/degree293
equations, with a separately reviewed signed-root reconstruction.
Its [centered extension](candidates/fixed-root-centers/README.md) now gives
74/312 and76/191, including an ordinary strong-root integrality proof that
uses the early Pell bound before extracting either deleted root.
Over unrestricted integers, a
[centered joint-guard equation](candidates/joint22-centered/README.md)
has22 unknowns, degree14 and119 operations. Its complete integer zero set
is carried bijectively to the parent by an explicit polynomial shear.

The latest [size comparison](PROPOSAL_REVIEW_LATEST.md) records
[position-zero](candidates/position-zero-norm-sharing/README.md) nine-positive
419/1,472,168 and compact54 427/1,626,248 forms, plus a lower-degree
1,056/997,810 choice. The earlier953/999,518 remains a different cost option.
The [quadratic ten-positive equation](candidates/ten-positive-quadratic-projection-shared/README.md)
now reaches105/408. Its strong and auxiliary Pell equations recover the
omitted main root; a strict bound on the entire projection product excludes
extra branches. The former122/816 evaluator remains frozen;
eleven-positive111/211 is a different tradeoff.
Exact [shared norms](candidates/interpolation-shared-norms/README.md) give
thirteen-integer184/1,072.
[Fixed-prime separation](PROPOSAL_REVIEW_VALUATION_INTEGER12.md) and
[identical shared norms](candidates/valuation-shared-norms/README.md) lower
the twelve-integer choices to208/2,400 and202/2,912.
[CRT/valuation composition](reviews/congruence-certificates-peer.md) adds
fourteen-integer148/414 and sixteen-integer118/124 tradeoffs. It also
reduces the13-positive form to88/51 by freeing J. The preserved13-positive
page retains its90/51 evaluator.

The direct C222 route now supplies complete
[integer quartics in706/707/709 variables](candidates/projected-radius-mixed-projections/README.md),
with10,465/9,129/9,034 terms and common height2,445,790,974,704. Its
735-integer companion has6,017 terms and lower height63,905,891. A
complete mixed-domain theorem recovers the semantic prefix before
interpreting powers, then replaces signed comparisons by fresh positive
ones. Reverse integer restoration preserves every guard. The
[natural factorial-radius family](candidates/projected-factorial-radius/README.md)
now reaches399 variables,8,286 terms and height83,843,274, with complete
support/height alternatives. All are exact quartics with ordinary literal
coefficients, independent of K215 and Jones.

Retaining arithmetic wires now gives
[integer quartics with coefficient height427](candidates/retained-radius-bounds/README.md):
1,736 variables and6,172 terms. This dominates the older3776/7058
low-height points in all four measured sizes. Further exact projections
give1,089 variables/5,016 terms/height4,750, and944/880/866-variable
choices with larger coefficients. These are coefficient/variable/support
tradeoffs; the complete ten-positive page remains the displayed equation.

The [407/888/917 review](PROPOSAL_REVIEW_QUARTICS407888.md),
[1,190-integer projection](candidates/synchronized-signed-projections/README.md)
and earlier synchronized/batched families remain reproducible checkpoints.
Full ordinary proofs, normal/optimized finite replays and independent root
reviews distinguish the new arithmetic transformations from their named
C222/refutation calibration. Internal formalization remains open and Lean
remains paused.

The [two parity-family reviews](PROPOSAL_REVIEW_PARITY_FAMILIES.md) add
fifteen-integer128-operation/degree204 and124/352 choices, and
sixteen-integer119/112 and115/160. Both retain the complete calibrated
source34 tuple; their root/sign recovery and finite replay scopes are
recorded separately.

## Approach and comparison

There is no single established meaning of "simplest": number of variables,
total degree, arithmetic operations, and coefficient size give different
answers. We compare these measures separately, retaining constructions
with different tradeoffs, including direct quartics and proof-certificate
encodings. Global optimality is not asserted.

The new [wave11 review](PROPOSAL_REVIEW_WAVE11.md) covers arrivals
`c1a102936a` and`9a33342a03`, including stronger eleven-positive forms,
the saturated ten-integer equation and smaller signed-domain quartics.
It distinguishes full release replays from selected component audits.
The [Hilbert Tenth transfer note](SIZE_RESEARCH_H10.md) explains the
root-elimination arguments and their completed fixed-blank specialization.

Neither a K215 encoding nor a Jones universal equation is a requirement.
Direct proof-certificate and arithmetic-trace encodings are separate research
routes. The nine-variable comparison below is one working branch of a
multi-measure search, not a restriction on the final construction.

A direct parent-index checker for the actual sealed ZFC calculus now has
Lean soundness and completeness, with explicit axiom/schema tags and no
K215 or Jones dependency; see
[ANNOTATED_PROOF_CHECKER.md](ANNOTATED_PROOF_CHECKER.md). Its
[natural-number coding](ANNOTATED_PROOF_CODE.md) now passes Lean, including
roundtrips and malformed-input rejection. Exact numeric certificates for
renaming under binders, including shift and instantiation, also pass Lean;
see [ANNOTATED_RENAME.md](ANNOTATED_RENAME.md). The complete numeric renaming
validator now has a supplied, checked primitive-recursive program for all
input codes; see [ANNOTATED_RENAME_VALIDATOR.md](ANNOTATED_RENAME_VALIDATOR.md).
The exact additive formula bound and universal sealing now also have supplied
programs and numeric certificates; see [ANNOTATED_BOUND_SEAL.md](ANNOTATED_BOUND_SEAL.md).
The actual Separation and Replacement schemas now have checked constructor,
rename and sealing programs too; see [ANNOTATED_SCHEMAS.md](ANNOTATED_SCHEMAS.md).
[Context validation, shifting and the assumption rule](ANNOTATED_CONTEXT_RULE.md)
now have supplied numeric programs too, including soundness for arbitrary raw codes.
[Shared validated coordinates and literal output/premise programs](ANNOTATED_RULE_COORDINATES.md)
now cover all17 original rules.
The [complete numeric logical scanner](ANNOTATED_LINE_SCANNER.md) now checks
raw numeric proof lines and backward references for every original rule,
with supplied primitive-recursive code and an exact acceptance/provability
equivalence. The [complete sealed-ZFC refutation checker](ANNOTATED_REFUTATION_PR.md)
now includes actual axiom/schema dispatch, the full axiom-context scan and
an exact existential acceptance/refutability equivalence. Its literal
program has83281 nodes, or76313 after certified optimization. These are
program-tree sizes; its smaller shared quadratic graph and internal-model
interpretation remain in progress.
The [literal quartic compiler](OBJECT_QUARTIC_COMPILER.md) now has an actual
ZFC derivation of its source/target no-zero equivalence over the entire
internal omega. The [actual sharp pairing quartic](OBJECT_SHARP_PAIRING.md)
now also has internal totality, functionality and surjectivity proofs,
including unconditional derivations in ZFC. Internal verification of the
full checker encoding remains open. The [actual predecessor, tree projections
and zero-test quartics](OBJECT_NUMERIC_WIRE.md) now also have exact semantics
over every internal natural input, preserving the existing shared-register
expressions and witness counts.
A [complete one-page equation](candidates/one-page/README.md) now specifies
the15-positive-variable P69 and every fixed coefficient using one1294-digit
integer and fixed arithmetic formulas. The printed seed and all four coefficient
values are independently checked. The [arithmetic mode ranks and symbolic
coefficient sum](ONE_PAGE_TUPLE54.md) now bind in Lean to the exact native
table and whole stencil, without expanding the large ports. The full native/internal-ZFC calibration
remains open. Both TeX sources and the one-page PDF are included.
The independent [direct executable quartic](ALTERNATIVE_ENCODINGS.md)
already has a closed external consistency equivalence at degree at most
four; it retains the enumerator's arithmetic graph. Lean now bounds its
natural-variable count by `nu < 2^300000`; the exact count remains unmeasured.
See [NATIVE_QUARTIC_SIZE.md](NATIVE_QUARTIC_SIZE.md) for the checked metadata.
The new [natural-register builder](NATURAL_REGISTER_PROGRAM.md) preserves
sharing before quartic compilation, with one gate witness per stored
register. [Shared-register relations](SHARED_REGISTER_RELATIONS.md) now hide
explicit auxiliary inputs and implement the actual max-square pairing used
by the direct checker, as well as the older enumerator's Cantor pairing.
[Direct quadratic attachment](QUADRATIC_REGISTER_SYSTEM.md) now reduces each
local max-square inverse projection to four witnesses and46 operations;
guarded joint quotient/remainder needs one witness and16 operations. All
have degree at most four. [Composable tree/list graphs](QUADRATIC_TREE_CODE_GRAPHS.md)
now cover the actual numeric checker's predecessor-based projections and
guarded list tail at five witnesses and62 operations each. Recompiling the
complete checker remains open. [Guarded local graphs](QUADRATIC_GUARDED_GRAPHS.md)
also cover the actual list head (seven witnesses,76 operations,degree≤4),
zero tests and conditionals, including nil and found-zero behavior.

Wave-ten packages68–75 have now been reviewed; all eight full normal release
replays pass. They add38-integer quartics, an11-positive degree325/113-operation
equation, and a478-operation nine-positive equation of degree1,379,730.
An exact shared-product rewrite now reduces the compact54-sharp candidate
from443 to440 operations, retaining degree1,845,940 and every coefficient;
see [the new candidate](candidates/gap2082-shared-products/README.md).
This historical operation target is retained as a checkpoint; the current
size-only nine-positive target has433 operations, as recorded above.
The same algebra improves package71 to475 operations at degree1,379,730;
see [the lower-degree rewrite](candidates/order7-shared-products/README.md).
See [the combined wave-ten review](PROPOSAL_REVIEW_WAVE10.md)
for the domain-preserving comparison, coefficient costs and proof boundaries.

Wave-nine placement `a2cd79b912` has now been reviewed. All eight full normal
release replays pass. Within the nine-positive branch, the next delivered
cost target is package 66's 444-operation, degree-1,845,940 form. Package
66's separate [compact54-sharp instance](candidates/gap2082-compact54/README.md)
passes its sealed finite checks at **443 positive / 450 natural operations**
with the same degree. Its counted circuit and source-polynomial binding now
pass Lean. Package
65 offers direct source reuse and lower degree; package 67 reaches degree
1,494,006 at higher cost. See [PROPOSAL_REVIEW_WAVE9.md](PROPOSAL_REVIEW_WAVE9.md)
for the comparison, replay evidence and parallel alternative-encoding work.

The H2082 source arithmetic and its actual nine-variable polynomial now pass
Lean, including sharp port bounds, positivity, word/carry calibration and
unbounded witness construction. See
[GAP_NINE_POLYNOMIAL66.md](GAP_NINE_POLYNOMIAL66.md). Lean also identifies the
literal 443/450-operation DAGs with those polynomials, including all eleven
fixed-leaf recipes and the positive/natural root translation; see
[GAP_CIRCUIT_RECIPE66.md](GAP_CIRCUIT_RECIPE66.md). The cancellation-aware
degree bound of 1,845,940 is checked for both actual polynomials in
[GAP_DEGREE66.md](GAP_DEGREE66.md). Native source calibration and the internal
ZFC theorem remain open.

The previous wave-eight target, now a checked source checkpoint, was
package 59's free-coordinate degree-separated adjunct: nine
positive variables, 473 binary operations, degree 1,910,404 (480 operations
over naturals). It improves both measures over the former package-52 target.
Concrete instances bind that architecture to the entire compact
tuples from packages 54 and 57. The preferred instance of this recipe uses 54's
215,492-byte native tuple, retaining the same operation count and degree.
Its sharpened binding halves the radix floor and divides the threshold
scale by 256, saving one raw stored byte. A checked joint-power
rewrite reduces the same polynomial to 456 positive / 463 natural operations;
see [the candidate artifacts](candidates/split116-compact/README.md).
The selection, alternatives,
full finite replays and remaining proof obligations are recorded in
[PROPOSAL_REVIEW_WAVE8.md](PROPOSAL_REVIEW_WAVE8.md). The current closed Lean
equations remain the certified baseline until a replacement is fully checked.

The new split-form foundations now pass Lean: same-degree coefficient
extraction, the shorter rank's exact carry threshold, mask population,
signed-borrow decoding, coefficient bounds, the free-carrier finalizer,
and the assembled binomial-to-source-coefficient contract.
Their contracts and remaining assembly work are recorded in
[SPLIT116_FORMALIZATION.md](SPLIT116_FORMALIZATION.md).
The literal old-z source, all 89 kernel records and the complete unbounded
nine-coordinate arithmetic source equivalence now also pass Lean. The
equation and exact port hypotheses are recorded in
[SPLIT_SOURCE59.md](SPLIT_SOURCE59.md). The actual nine-variable
`MvPolynomial` and its evaluation/source equivalence also pass Lean; see
[SPLIT_NINE_POLYNOMIAL59.md](SPLIT_NINE_POLYNOMIAL59.md). Lean also identifies
the literal 480-operation natural DAG and its 463-operation replacement
with this polynomial, including all twelve fixed-leaf recipes; see
[SPLIT_CIRCUIT_RECIPE59.md](SPLIT_CIRCUIT_RECIPE59.md). The corresponding
473/456-operation positive DAGs and their exact positive/natural root
translation also pass Lean; see
[SPLIT_POSITIVE_RECIPE59.md](SPLIT_POSITIVE_RECIPE59.md). Native calibration
remains open.

The native arithmetic bridge now recovers the exact first Pell index, the
source register `X=2^R`, the binary block base and the common cubic scale;
see [NATIVE_PELL_POWER.md](NATIVE_PELL_POWER.md). The doubled half-binomial,
population and mask arguments now close the full forward bridge from the
literal source to the [native arithmetic window](NATIVE_SOURCE_WINDOW.md),
under explicit coefficient conditions. The [compact54 local decoder](NATIVE_CLAUSE54.md)
now proves exact empty-cell or single-tile acceptance from arbitrary Boolean
selectors, with no one-hot premise. The [whole-stencil carry step](NATIVE_CONVOLUTION54.md)
now derives pointwise mask tests with all temporal rotation phases retained.
The [origin radix digit](NATIVE_ORIGIN54.md) is now forced to one from the
actual source mask and exact low-MC recipe. The [sparse assignment](NATIVE_SPARSE_DIGITS54.md)
is now reconstructed from the source, including the positive cell count,
exact word, origin and Boolean/capacity bounds. The [literal clause bands](NATIVE_CLEAN_BANDS54.md)
now equal the corresponding local coefficient sums plus the explicit
temporal contribution, including cyclic collisions. The [exact high mask](NATIVE_HIGH_PORT54.md)
and [paired temporal support argument](NATIVE_TEMPORAL_SUPPORT54.md) now
derive the actual local clause-mask zero in every cell before phase alignment.
The coefficient interface remains explicit; phase synchronization, whole
compiler calibration and converse completeness remain open.

The package-52 formalization now checks its literal 60-gate, 22-row source,
all 136 quadratic coefficient records, exact selective positions, sharp
coefficient height, sparse low-mask decoding, ratio reparameterization, and
margin-first finalizer. The complete source-to-binomial-to-finalizer
arithmetic equivalence and literal multivariate-polynomial binding also
pass Lean, with explicit coefficient bounds and exactly nine natural
coordinates. See [SELECTIVE_SOURCE52.md](SELECTIVE_SOURCE52.md). Authentic
native calibration and the internal ZFC derivation remain open; this
checkpoint does not yet replace the closed consistency equation.

The wave-5 and wave-6 report packages explicitly distinguish their new final
equations from an end-to-end Lean certificate. The inherited P67 is a particularly short
candidate: 15 strictly positive witnesses, degree 155, and 67 binary
arithmetic operations. Its fixed coefficient tuple and native-window/Pell
compiler still need a formal semantic bridge. Nine-natural-variable forms
use the already formalized Jones reduction but introduce very large powers.
The ten-unrestricted-integer Sun construction is not formalized here.

The wave-6 packages arrived on `origin/main` during this research and were
merged at `2d7766807b`. Their direct quadratic/Sidon encodings improve the
reported low-variable degree and operation counts substantially; for example,
[package 45](con-zfc-diophantine-forms/45-multioutput/README.md) reports nine
positive unknowns at degree 129,875,980 in 788 operations. These were useful
comparison targets. The executable generic Jones route below
prioritizes a complete checked construction and does not claim to improve
those degree or operation counts.

The first formal route is now checked:

1. A concrete semidecision procedure halts exactly when ZFC has a finite
   refutation. Reuse the checked K215/program endpoint rather than assume
   that its halting predicate is computable.
2. Apply the proved MRDP theorem and Jones quartic compression.
3. Apply the proved nine-variable reduction and fix the ordinary input to
   1, obtaining one polynomial in nine natural variables.
4. Negate the solvability equivalence.

An existential representation chosen with `Classical.choose` is a useful
checked milestone, but is not a materialized explicit coefficient recipe.
These two levels will be reported separately. Likewise, a Lean theorem
about syntactic ZFC consistency is distinct from a derivation *inside* the
repository's object-level ZFC proof calculus. Portability of an arithmetic
argument to ZFC is not itself a checked object-level derivation.
The concrete remaining internalization obligations and the first actual
object-language arithmetic proofs are documented in [OBJECT_ZFC.md](OBJECT_ZFC.md).

See [STATUS.md](STATUS.md) for the current evidence and remaining work.

The main checked result is now
`ExplicitZFC.noNaturalZero_iff_conZFC` in
[ExplicitZFC.lean](Lean/DiophantineConsistency/ExplicitZFC.lean). It uses a
closed, executable nine-variable coefficient recipe and has no consistency,
compiler, program, or representation hypothesis. See
[EXPLICIT_EQUATION.md](EXPLICIT_EQUATION.md) for the equation and proof chain.
The earlier existence-based theorem in [ZFC.lean](Lean/DiophantineConsistency/ZFC.lean)
and its 58-witness quartic alternative remain available as separate milestones.
The checked shift in `PositiveZFC` gives the same variable count over strictly
positive integers. A second closed route in
[DIRECT_GRAPH.md](DIRECT_GRAPH.md) represents source arithmetic directly;
its final degree and operation comparison remains to be measured.

For a concrete small arithmetic circuit, see
[SHORT_EQUATION.md](SHORT_EQUATION.md): a 69-operation, degree-111 polynomial
with 15 positive unknowns, bound to the historical package-36 coefficient
tuple. Lean checks its complete positive zero set against the literal P67
baseline. The native-window compiler connecting those explicit circuits to
ZFC refutations remains to be formalized.

The lower-degree alternative in [SHORT_SYSTEM.md](SHORT_SYSTEM.md) uses
75 operations at degree 68, with the same 15 positive unknowns and fixed
coefficient tuple. Lean proves its degree bound and complete positive-zero
equivalence to P67. Grouping the main norm with the two coupled unit factors
saves two operations over the intermediate 77-operation sum of squares.

The checked tradeoff in [SHORT_FRONTIER.md](SHORT_FRONTIER.md) uses
73 operations at degree 80. It groups the six unit factors into three
residuals and has the same complete positive zero set. The present frontier
includes 69 operations/degree 111, 73/80, and 75/68.
The further reduction in [SHORT_REDUCED_STRONG.md](SHORT_REDUCED_STRONG.md)
uses 76 operations at degree 64. It adds a multiple of another vanishing
residual to cancel leading terms; Lean checks complete integer zero
equivalence to P75. Each of these alternatives uses 15 positive unknowns.

## Executable construction and further reductions

The current computability/MRDP interfaces hide the program and polynomial
inside propositions. Extracting executable polynomial data from those
propositions would require an unjustified elimination from `Prop` into
`Type`. The explicit route builds data-valued arithmetic syntax and
representation constructors, with separate correctness proofs. A
syntax-directed primitive-recursion compiler can then retain its polynomial
data throughout. The proved Jones nine-variable reduction accepts any
normalized quartic, so a direct gate-to-quartic conversion can avoid the
58-witness universal representation during this phase.
The detailed contracts and remaining links are tracked in
[COMPILER.md](COMPILER.md).

The supplied-data route now includes arithmetic graphs, Pell sequences,
power, binomial, factorial, and bounded universal quantification.
[`EquationFromRep.construct`](COMPILER_JONES.md) constructs a normalized
quartic and a nine-variable equation directly from supplied representation
syntax, with a checked equivalence for both presentations.
`ExecutableJones.fromRep` also gives a complete executable syntax path,
including its coefficient readers and index. The concrete refutation program
is now supplied by `DirectEnumerator.program`; `ExplicitZFC` closes the
executable equation construction with the actual syntactic endpoint.

## Reproducing the checked milestones

From the repository root, with Lean and Mathlib 4.32.0:

```sh
lake build DiophantineConsistency.ZFC DiophantineConsistency.ShortFrontier
lake env lean Computability/DiophantineConsistency/Lean/checks/ZFCAxioms.lean
lake env lean Computability/DiophantineConsistency/Lean/checks/ShortEquationAxioms.lean
lake build DiophantineConsistency
lake env lean Computability/DiophantineConsistency/Lean/checks/CompilerAxioms.lean
python3 Computability/DiophantineConsistency/tools/audit_short_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_sos_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_frontier_circuit.py
python3 Computability/DiophantineConsistency/tools/audit_reduced_strong.py
```

The axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`.
The finite circuit audit verifies operation count, liveness, source binding,
and exact degree independently of the semantic compiler obligations.

## Source interfaces

* `BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`: the literal
  215-state machine halts on blank tape iff `BProv ZFCax_s [] Form.fBot`.
* `Diophantine.Common.MRDPCore`: `MRDP.mrdp`, proved without a DPRM axiom.
* `Diophantine.Paper1982.RecursivelyEnumerableQuartic`:
  `Jones1982.rePred_quartic58`.
* `Diophantine.Paper1982.NineMain`: `Jones1982.nine_unknowns`.

All new mathematical statements must have complete proofs: no `sorry`,
`admit`, or additional axioms. Transitive axiom audits and reproducible
build commands will accompany completed milestones.
