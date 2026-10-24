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
unknowns, exact degree388, with a102-operation evaluator**. Every fixed
constant is defined on the same Letter page, including the full436-character
numeral, alphabet, decoder and943 tiles. The body uses9-point type.
Compared with the preceding ten-positive105-operation degree408 display,
this saves three operations and lowers degree by20 at the same unknown count.
The same coherent BFS-renamed compact44 tuple and complete constant recipe
are retained. The [page proof and checks](candidates/one-page-shifted10/README.md)
include the exact universal formula binding, full positive witness maps for
direct J, shifted strong input and shorter transport, inherited native/
controller transfer, and independent whole coefficient reconstruction.
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) binds the displayed files.

The preceding [ten-positive degree408 page](candidates/one-page-quadratic10/equation.pdf)
is preserved with its [TeX](candidates/one-page-quadratic10/equation.tex),
as are the earlier [degree816 page](candidates/one-page-scaled10/equation.pdf)
and [thirteen-positive degree51 page](candidates/one-page-ordinary13/equation.pdf)
with their standalone sources. The13-positive page uses fewer operations
and lower degree, with three more unknowns; no global optimum is claimed.

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
[tight main folding](research/nine-folded-saturation-tight/README.md) nine-positive
409/1,191,572 and compact54 417/1,316,548 forms, plus a lower-degree
[position-zero](candidates/position-zero-norm-sharing/README.md)1,056/997,810 choice. The earlier953/999,518 remains a different cost option.
The [quadratic ten-positive equation](candidates/ten-positive-quadratic-projection-shared/README.md)
now reaches101/368 with a [fixed root weight and positive short projector](candidates/ten-positive-short-projection/README.md).
Its strong and auxiliary Pell equations recover the
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


The [identical integer14 simplification](candidates/constructive-integer14-shared/README.md)
reduces147 to145 live operations at unchanged degree568. Two complete
`(1+x)-1=x` substitutions preserve the entire polynomial and all six
fixed coefficients. Root reviewed the literal checker, all node maps,
normal/optimized replays and all30 sealed files. The lower-degree
148/414 and lower-cost137/792 alternatives remain useful tradeoffs.
The then-current10-positive105/408 PDF and TeX are unchanged by this minor
integer-domain simplification; Lean remains paused.


The [mixed retained-wire family](candidates/projected-radius-mixed-retained/README.md)
now gives1,580/933/788/724/710 unrestricted integer variables, all at
exact degree4. It keeps all original raw rows and coefficients, proves
A and D nonnegative from four original-row bounds, and copies107 guard
triples into the literal reviewed994 equation, with six fresh Legendre
witnesses for its two remaining guards. The full592-wire map is over
integers. All five collected quartics and complete signed inverses pass
independent and deterministic checks in both Python modes. Heights remain
427/4,750/737,653/737,653/938,261; each matched159-guard sibling loses
156 coordinates,52 rows and780 terms. The smaller706-variable, larger-height
family remains a separate tradeoff. The canonical PDF/TeX and Lean are unchanged.


The [signed main-root reduction](candidates/constructive-integer14-quadratic/README.md)
now reaches14 unrestricted integer variables,121 operations and exact
degree312. Absolute-value Pell folding recovers the missing main norm
before the signed rank bootstrap; a whole-product absolute height bound
resolves the quadratic projection for both signs of H. Explicit integer
n maps preserve zero existence in both directions. The complete proof,
all six original coefficients, universal formula binding, literal35-term
norm, exact leading form and normal/optimized replays pass independent
and root review. This improves both cost and degree over14-integer
137/792,145/568 and148/414, which remain preserved checkpoints. It has
more variables and operations than the then-current10-positive105/408 page,
so that complete PDF/TeX remains the canonical display. Lean is paused.


The [contracted mixed-bound family](candidates/projected-radius-mixed-bounds/README.md)
now reaches988/729/703/701/700 unrestricted integer variables at degree4.
All585 original body rows are unchanged. Restoring592 raw wires over
integers licenses the four actual t,n,A,D row bounds;107 copied guard
triples plus six fresh A/D witnesses give the literal reviewed994 zero.
Every projection restores the entire988 parent first. Independent and
full deterministic normal/optimized checks pass all1177 row identities,
complete coefficients/inverses and15 corruption controls. The700-variable
polynomial has10,437 terms and height2,445,790,974,704;729 retains lower
height63,905,891. Each matched994/735/709/707/706 checkpoint loses six
variables, two rows and28 terms. The710-variable retained-wire option
has much smaller height938,261. Canonical PDF/TeX and Lean are unchanged.


Two [identical prefix rewrites](candidates/constructive-integer14-quadratic-shared/README.md)
reduce the new14-integer degree312 equation from121 to119 operations.
Reusing q² and factoring ell(ell+1)k²=(ell*k)(ell*k+k) preserve the entire
polynomial over every commutative ring. Complete148-to146 node coverage,
all removed private definitions, every named register, the full35-term
norm and all six payloads pass independent root review and both complete
checker/rebuild modes. All33 packet seals pass. The signed ordinary proof
and exact nonzero leading coefficient transfer unchanged. This is a minor
saving within the new signed degree312 route; the canonical10-positive
105/408 PDF/TeX remains the separate lower-variable/operation display.
Lean remains paused.


The [thirteen-integer quadratic trace equation](candidates/integer13-quadratic-trace/README.md)
now uses135 operations at exact degree536, down from184/1072. Normalized
trace gives both CRT congruences before signs, the unscaled guard gives
four-root separation, and signed Pell folding restores the main norm.
The whole-product height proof resolves its quadratic projection, then
explicit unrestricted n maps restore the frozen trace endpoint in both
directions. Root reviewed the entire ordinary proof and independent
literal checker; all four normal/optimized checker/rebuild commands pass,
including the full495-term norm, centered425-term degree calculation,
authentic six ports and all138 original archive members. This improves
both current13-integer cost and degree. At that checkpoint, the10-positive105/408 page remained
a separate lower-variable/operation display. Lean is paused.


The [five exact original-row sign consequences](research/guard-seed-consequences/README.md)
remove two factorial-output guards, the moduli-product and CRT quotient
guards, and one endpoint quotient guard before any arithmetic semantics.
The CRT numerator uses its independently proved defining sums, avoiding
a circular quotient dependency. The [complete102-guard family](candidates/projected-radius-mixed-signs/README.md)
now gives973/714/688/686/685 integer variables, all degree4. A literal
102-triple transfer plus15 new Legendre witnesses restores the full988
parent; all integer projections are reversed first. Root reviewed both
ordinary proofs and independent checkers. Full normal/optimized checks
and rebuilds pass every original-row identity, the975-step sign ledger,
all coefficients and inverses. Each matched988/729/703/701/700 parent loses
15 variables, five rows and73 collected terms at unchanged height. The
smaller-coefficient retained710 family and canonical PDF/TeX are preserved;
Lean remains paused.


The [scalar-carrier twelve-integer equations](candidates/scalar-carrier12/README.md)
now use145 operations/degree1200 and141/1456, improving208/2400 and202/2912
with the same twelve unrestricted variables and all six original constants.
A scalar intersective quintic enforces H|K and excludes zero strong scale;
prime-order separation leaves four roots, and signed folding recovers the
missing main norm before its whole-product projection. The completeness
proof keeps one strong witness fixed while selecting the translated
intersective residue. Direct nonodd step-down is proved from the auxiliary
index polynomial. Full independent ordinary review, separate all-register
ring binding, all495 norm coefficients, exact every-gate leading induction,
whole payloads/parent inventory and final normal/optimized checks pass.
Both degrees are halved; cost falls by63 and61 operations. Canonical
10-positive105/408 PDF/TeX remains the lower-variable/operation tradeoff;
Lean stays paused.


The [nine-positive folded-saturation equations](research/nine-folded-saturation/README.md)
now reach414 operations/degree1,355,142 on the full original31 tuple and
422/1,497,238 on compact54-sharp. Saturating the strong norm with the
first Pell radicand allows a two-root equation; coprimality recovers both
squares, then main-Pell folding recovers C=psi_A(B1). Positivity is proved
before extraction, and finite matrix periods construct positive i,j,n.
Both directions retain the exact source/binomial boundary and whole fixed
tuples. Root read the full ordinary proof/checker and verified every
retained source node, every local algebraic cut, centered identity and
actual-coefficient homogeneous witness in both Python modes; both complete
rebuilds pass and all packet seals are checked. Both cost and degree improve
the matched419/427 parents. Lower-degree higher-cost alternatives remain
separate, and canonical10-positive105/408 PDF/TeX is unchanged. Lean is paused.


Two [exact private sign orbits](research/guard-sign-orbits/README.md)
now replace the U and bootstrap-witness guards. Complete raw/contracted
row identities negate U and its sixteen quotient partners together, or
reflect Zminus1 with its two private wires. The independent A>=2 row
bound excludes Z=0 before reflection; U=0 uses the identity branch.
All100 remaining guard values and all643 semantic-prefix coordinates
stay fixed. The [whole100-guard family](candidates/projected-radius-mixed-orbits/README.md)
has967/708/682/680/679 integer variables at degree4. Normalize private
values first, then six fresh witnesses give the literal973 equation;
reverse all signed projections before that step. Root reviewed the full
proofs/checkers and all normal/optimized checks/rebuilds pass. The679
polynomial has397 rows and10,335 terms at unchanged height2,445,790,974,704.
Each matched973/714/688/686/685 checkpoint loses six variables and two
rows. The retained-wire low-height family and canonical PDF/TeX remain
separate tradeoffs. Lean stays paused.

## Tightened nine-positive folding accepted

The [tightened packet](research/nine-folded-saturation-tight/README.md)
now gives409 operations / degree1,191,572 on the whole original31 tuple
and417 /1,316,548 on the separate compact54-sharp tuple. It improves the
frozen414/422-operation equations in both operation count and degree.
The strong ordinate omits J, the auxiliary quotient uses positive j
without a shift, the carrier is Jn+Q, and the first norm shares its
majorant. A new strict-gap proof forces positive margin before root
extraction; two finite matrix periods and a strict carrier bound construct
all three changed positive witnesses. No tuple or domain is weakened.
The [root review](reviews/nine-folded-tight-root-peer.md) records the full
ordinary proof audit, exact degree argument, all four normal/optimized
checks and rebuilds, and closed artifact seals. This nine-variable result
is a separate tradeoff from the maintained ten-positive one-page equation.
Lean remains paused; no new internal-ZFC endpoint is claimed.

## Direct positive J in the ten-variable equation accepted

The [free-J ten-positive equation](candidates/ten-positive-free-j/README.md)
saves two operations, reaching103 at the same exact degree408 and ten
positive unknowns. The enlarged positive J domain is sound: odd main
index recovery gives p=R before q parity, then odd q would force even J
and even R. Coprimality is used only after this contradiction recovers
even q. The J=1 case constructs fresh positive source61 witnesses and
uses its actual unrestricted-positive-J soundness statement. The whole
original tuple and separately calibrated BFS tuple remain distinguished.
The [root review](reviews/ten-positive-free-j-root-peer.md) and
[independent ordinary review](reviews/ten-positive-free-j-ordinary-peer.md)
record the proof and full literal affine-map/degree checks. All four
normal/optimized checks and deterministic rebuilds passed. This minor
two-operation saving does not trigger a new canonical PDF/TeX rendering;
its complete105-operation page remains available pending a substantial
improvement. Lean remains paused.

## Raw100-guard low-height quartics accepted

The [retained-wire100-guard packet](candidates/retained-radius-mixed-orbits/README.md)
gives complete integer quartics in1559/912/767/703/689 unknowns, at
coefficient heights427/4750/737653/737653/938261. Each saves21 unknowns
and seven quadratic rows over its corresponding frozen107-guard raw
parent, without increasing height. All original raw coefficients remain.
An exact zero-set bijection restores592 triangular monic affine wires
and copies all100 guard triples to the actual frozen967 equation before
using its sign theorem; no fresh witness or sign premise is needed for
the bridge. Each signed projection first restores the whole raw parent.
The [root review](reviews/retained-orbits-root-peer.md) records all1277
row identities, complete coefficient collections, four successful
normal/optimized checks/rebuilds and closed seals. The contracted679
quartic remains a different coefficient-height tradeoff. No new Lean
endpoint is claimed and formalization remains paused.

## Smaller signed fourteen-variable guard accepted

The [guard-reduced equation](candidates/constructive-integer14-guard-reduced/README.md)
has14 unrestricted integer unknowns,117 operations and exact degree312.
It removes the explicit v-square factor from the guard. Its new proof
excludes v=0 by rationalizing the remaining two roots and deriving an
impossible CRT divisibility, before using any weak-scale estimate. Both
integer witness maps regenerate only the four private guard coordinates;
the entire degree256 norm and six fixed coefficients are unchanged.
The full output difference has degree at most304, so the complete
nonzero degree312 leading component survives. The
[root review](reviews/integer14-guard-root-peer.md) records all node/guard/
norm identities, four successful normal/optimized checks and rebuilds,
and closed seals. The [initial research note](reviews/signed14-guard-research.md)
also records why two tempting smaller positivity gadgets fail. Lean and
the canonical ten-positive page remain unchanged.

## Ten-positive102/388 accepted

The [shifted strong equation](candidates/ten-positive-shifted-strong/README.md)
now reaches102 operations and exact degree388 in ten positive unknowns.
It uses I=(i+q²)c² and the shorter transport L=HI+b. The shift preserves
the unconditional lower bound and square-ordinate divisibility; a new
rational-rho bound licenses the smaller transport before parity recovery.
Canonical completeness keeps the strong ordinate and constructs a fresh
positive final n, including zero transport quotient. The complete norm
has a nonzero selected coefficient2^28*beta^224 in degree388. The
[root review](reviews/shifted-strong10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-shifted-strong-ordinary-peer.md)
record the full proof, exact gate/degree/whole-tuple checks, four passing
normal/optimized replays and closed seals. A new complete one-page display
is being prepared for the combined gain over105/408; its predecessor
will be preserved. Lean remains paused.

## Canonical page updated to102/388

The maintained [equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) now print the complete ten-positive102-operation,
exact-degree388 equation, including every fixed constant, on one Letter
page. This batches the direct-J, shifted-strong and shorter-transport
improvements into one update over the preserved105/408 page: three fewer
operations and degree20 lower. The complete436-character seed,62-character
alphabet,943 tiles and closed arithmetic coefficient recipe are unchanged.
The [new page packet](candidates/one-page-shifted10/README.md),
[independent root page review](reviews/shifted10-page-peer.md) and
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) bind the displayed bytes.
Both independent peer modes, renderer replays and full coefficient
reconstruction modes pass; the page was visually reviewed. The previous
[105/408 PDF](candidates/one-page-quadratic10/equation.pdf) and its TeX
remain preserved. Lean formalization remains paused.

## Twenty-one pointwise guard consequences accepted

The [main-root/modulus proof](research/main-root-and-modulus-signs/README.md)
recovers15 main-root signs and six power-modulus signs from the unchanged
raw equations with79 retained guards. Its independent semantic-prefix
proof precedes a strict A>W^W bound, signed-index recovery and negative-root
residue contradiction. Only then does a positive-base power call establish
f0>0 and the final modulus sign. All15 actual exponents are proved positive.
The [root review](reviews/main-root-signs-root-peer.md) and
[independent peer](reviews/main-root-modulus-signs-peer.md) verify the
complete original-row, constructor and21-call ledger; all six root
normal/optimized checks, rebuilds and peer runs pass. At the same body
tuple,79 existing triples and63 fresh Legendre witnesses reach the literal
frozen967 equation. Complete new quartics and signed projections are being
materialized separately; no unverified projected count is added here.
Lean and the current canonical PDF/TeX remain unchanged.

## Fixed root weight lowers ten-positive degree to368

The [weighted-root equation](candidates/ten-positive-weighted-roots/README.md)
has ten positive unknowns,102 operations and exact degree368. It replaces
the full-mu strong shift by I=i*c² and weights only the first root by3.
All signed cancellations are excluded before root extraction: two pairs
would imply mu|8, the third would equate an integer to -1/Delta, and a
zero triple would imply mu|2025, then mu|25 despite mu>=1025. Main folding
then gives the strict bound needed for weighted transport. Canonical
completeness uses the explicit positive shifts i_new=i_old+q² and
n_new=n_old+2*tau. The [root review](reviews/weighted10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-weighted-roots-ordinary-peer.md)
record the full proof and exact circuit/degree/whole-tuple checks. All four
normal/optimized checks and rebuilds pass; the unique leading component
has a positive selected coefficient2^28*beta^184. The prior102/388 packet
is preserved; a complete new page is under review. Lean remains paused.

## Complete79-guard compact quartics accepted

The [materialized compact family](candidates/projected-radius-main-root-signs/README.md)
gives full integer quartics in904/645/619/617/616 variables. The smallest
has376 quadratic rows,10,028 collected terms and coefficient height
2,445,790,974,704; the645-variable point has5,580 terms and height63,905,891.
Every profile saves63 unknowns and21 rows over its matching100-guard
parent at unchanged height. Complete signed inverses first restore all79
guards, then592 raw affine wires. The ordered21-sign theorem supplies
63 fresh witnesses at unchanged body values into the literal967 equation.
The [root review](reviews/main-root-quartics-root-peer.md) records full
coefficient collections, every100 copied/fresh guard-row identity, all
four passing normal/optimized checker/rebuild replays and closed seals.
These are checked whole equations, not estimates from deleting guards.
Lean and the ten-positive display remain separate and unchanged.

## Retained-coefficient79-guard quartics accepted

The [new raw family](candidates/retained-radius-main-root-signs/README.md)
keeps all original coefficients and gives1496/849/704/640/626 integer
variables, with exact degree4 and heights427/4750/737653/737653/938261.
The smallest has386 rows and8,904 collected terms. Each profile saves
63 variables and21 rows at unchanged height against its100-guard parent.
The [root review](reviews/main-root-raw-quartics-root-peer.md) records
the complete1256-row integer bijection into904, all592 affine inverses,
and the composed79-copied/63-fresh-witness transfer into literal967.
All100 target guard rows and every full collected polynomial are checked.
All four root normal/optimized checker/rebuild replays and closed seals
pass. The616-variable compact quartic is a separate height tradeoff;
no new Lean or native calibration endpoint is claimed.

## Comparison-base positivity guard removed existentially

The [comparison-base proof](research/comparison-base-sign/README.md) permits
negative B and then lifts it to a positive comparison base while preserving
all78 other guard values. Its complete1177-row audit accounts for62 private
coordinates,141 unit gates and every46 affected nongate constraints. The
signed-index and21-sign proofs precede the lift; q4 positivity is supplied
at the new tuple, not asserted at the old tuple. Three fresh Legendre
witnesses reach the literal904 source. The [root review](reviews/comparison-base-sign-root-peer.md)
and [independent peer](reviews/comparison-base-sign-peer.md) record full
normal/optimized author and peer replays, all passing. New compact/raw
quartics are being materialized separately; this theorem alone supplies no
new projected coefficient count. Lean remains paused.

## Positive short projector reaches101 operations at degree368

The [short-projector equation](candidates/ten-positive-short-projection/README.md)
uses ten positive unknowns and101 live operations at exact degree368.
Kpos=X(3c-2X)+2 is positive after main folding and obeys
Kpos=H*X*c-2*Kquad. Only2 is cancelled modulo odd H; P is retained in
the whole-product argument. Every old positive zero maps to a new one
by the strictly positive shift n_new=n_old+3*(Kquad/H)-X*c. The
[root review](reviews/short10-root-peer.md) and [independent ordinary peer](reviews/ten-positive-short-projection-ordinary-peer.md)
check the full unbounded proof. All four root normal/optimized checker
and rebuild replays, complete53-entry seals and full coefficient binding
pass. The entire polynomial change has degree at most360, preserving the
degree368 leading component. A complete one-page specification is being
reviewed for the next canonical PDF/TeX update. Lean remains paused.
