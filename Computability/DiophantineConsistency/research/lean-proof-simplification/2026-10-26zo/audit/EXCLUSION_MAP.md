# Exclusion map

Pinned source: `9f35798db4a63c25e435fca14d75931144657d7e`.

Exclude the same mathematical mechanism at the same target or explicitly announced consumer family, regardless of adoption/compilation status. Generic use of induction or library lemmas alone is not a duplicate. Do not count helper relocation, patch validation or profiling as new ideas.

All entries below are treated as already applied. Entry counts are bookkeeping counts; some entries overlap.

## E001

Recursor congruence via `simp` or generic `rec_congr`, replacing duplicate induction in PR realizers/optimizer

Evidence: A report, “Rewrite under primitive recursion”; `lean/RecursorCore.lean`; `patches/pr-congruence.patch`

## E002

Core `List.mem_of_getElem?`, `List.getElem?_of_mem`; Option map injectivity

Evidence: A report “Use the core list-lookup API”; E report section 6 and `checker_examples/standard_library_cleanup.patch`

## E003

Assignment naturality under `Sum.map`, evaluator renaming, transport of input/witness blocks

Evidence: A assignment-map patch; B “Witness layouts”; D “Checked refactor: assignment naturality”; H “A small assignment-transport API”

## E004

Existential witness splitting/regrouping using `Fin.addCases`, `Fin.exists_fin_add`, or `Sum.exists_sum`

Evidence: B `lean/WitnessLayout.lean`; H “Regroup witnesses with the existing sum-type theorem”

## E005

Move witness-count/projection/rename lemmas to earlier dependency layers

Evidence: B “Move existing projection lemmas to their natural home”; C “Share residual-system facts”

## E006

Generic validated-history fold with separate input/stored types, append, invariant, Produces composition and certified rule fragments

Evidence: B “One invariant-preserving history fold”; C `notes/syntax.txt` (ready_binary/ready_unary/fragment2/fragment3); H “An input row and a stored judgment need not have the same type”

## E007

Shared Nat.rec iteration, fixed/reject/done states, invariants, and `Function.iterate` bridge

Evidence: A “Share iteration laws”; B/C/D/E scanner sections; H `lean/ScanIteration.lean`

## E008

Shared encoded-list simulation with sufficient fuel, step-cons, distinct rejection/terminal encodings and arbitrary-raw-code soundness

Evidence: B “Separate recurrence from encoding”; C “Share scanner proofs at the correct semantic boundary”; G “One simulation kernel”

## E009

Dynamic-seed/input-dependent PR iterator; supplied program/`.val` preservation

Evidence: B “A better primitive-recursive iterator interface”; C “Factor the supplied PR iterator”

## E010

Exact numeric Boolean output and threshold/tag dispatch normalization on all natural tags

Evidence: A BooleanCore and “Replace acceptance equivalences”; E section 8

## E011

Shared finite sum-of-squares syntax, evaluation/zero criterion, degree and operation-count bounds

Evidence: A sections 4/7; B “One executable sum-of-squares API”; C/H compiler sections

## E012

Reuse semiring gate soundness/completeness, separate gate data from semantics; combine identical constructor proof branches

Evidence: B “The semiring theorem already subsumes the natural induction”; E section 5

## E013

Existing `run_power` exponent certificates for generated pure-power chains

Evidence: A generated-steps; B power certificates; F `report/sections/04_circuits.tex`

## E014

Circuit-specific indexed `run_node_equation` facade, selected named wrappers, on-demand proof generation

Evidence: A/B generated step proposals; F circuit C2

## E015

Generic topological run invariant for uniqueness, nonnegativity, degree/range

Evidence: A `CircuitInvariant.lean`; C “Use a common DAG invariant theorem”; H “A reusable invariant”

## E016

Generic circuit simulation and local NodeRel allowing commuted addition/multiplication

Evidence: A `NodeRelCommutative.lean`; C “Positive/natural translation is a simulation”

## E017

Generic register append topology/dependency/evaluation facts

Evidence: A `source_notes/circuits-review.md` section 7

## E018

Earlier structural/weighted degree API, weight-one specialization, shared RHS degree bounds

Evidence: A/C/D degree interfaces; H “Weighted syntax degree”

## E019

Cancellation-aware normal-form certificates before degree checking

Evidence: C “Preserve cancellation-aware degree arguments”; F circuit C4

## E020

Preserve/reuse established register semantic cuts in generators

Evidence: C “Use established register facts as proof boundaries”; split-register-cuts.patch

## E021

Common 99-node Split/Gap tail with boundary-port substitution and insertion theorem

Evidence: C “Extract the shared 99-node free-carrier tail”

## E022

Common scalar FreeCarrierPolynomial ratio tail, map/cast laws, common recipe-tail correctness

Evidence: E sections 9/11; C shared-tail section

## E023

Row-index coefficient-envelope dispatcher; conditional-bound tactic; common nonnegative monomial context

Evidence: C “Compress the coefficient-row proofs”; D “Coefficient envelopes”; G narrow envelope tactic

## E024

Finite signed-monomial majorant certificates retaining sharp dependence on K

Evidence: C “A stronger abstraction: a finite majorant certificate”; D further research

## E025

Coefficient expression syntax / single AST, generic naturality by homomorphism interpretation

Evidence: C “Do the same for coefficient naturality”; F architecture A6

## E026

Sparse quadratic row normalization tied to independently supplied residual/source data

Evidence: C “A small sparse-row normalizer”; G low-degree row certificates

## E027

Elementary row additions and surjective row reindexing preserve common zero sets

Evidence: C “Represent elementary row operations once”, `lean/checked/RowOperations.lean`

## E028

Exact scaled half-radix quotient/remainder identity instead of finite case enumeration

Evidence: A/B/C/D/G half-radix sections

## E029

Weaken modulo 2048 reflected coefficient to modulo 16 using divisibility

Evidence: A modulus-reuse.patch; B/C/G congruence sections

## E030

Conditional padding witness eliminates irrelevant dummy witnesses

Evidence: A conditional-padding.patch; A digits-review section 1

## E031

Exact digit/carry decomposition gives quotient, remainder, modular projection, zero carry

Evidence: A NormalizationArithmetic; B CarryCertificate; E equation-side carry lemmas

## E032

Derive rather than store redundant `Facts.carry_recurrence`; small named carry/window views

Evidence: A digits-review section 3; C “Improve the current-window API”; D carry records

## E033

Shared ambient cyclic modulus/field residue/offset/nonorigin support facts

Evidence: A digits-review section 5; B physical-field residues; D generic cyclic residues; G cyclic-field interface

## E034

Aligned-cell equivalence with `ZMod N`, reindexing and reuse existing Cell type

Evidence: B report lines 613-615; E section 12; J `evidence/prior_ideas.md` E29 explicitly warns that a basic AddEquiv is too close

## E035

No-borrow origin decrement word law, separate low +1/high -1 corrections

Evidence: A digits-review section 6; G “One origin-correction lemma”

## E036

Direct physical selector sum API avoids prefix-sum round trips

Evidence: A digits-review section 7

## E037

Coherent restored source/window extraction preserves the same source and N across low/high/full window

Evidence: A digits-review section 8; F architecture A3

## E038

Decode common source/Pell register equations once; semantic identities and Nat/Int rank conversion

Evidence: B “Decode source-register equations once”; C `notes/arithmetic.txt` section 6

## E039

Generic finite table chunk/tail dispatcher, balanced block assembly, finite sum chunks

Evidence: B “Keep checked finite chunks”; E section 13; WangTiles942Data and CurrentKernel2011 are explicit targets

## E040

Shared copied-field bounds, finite direction/offset/width descriptor and 34-control reindexing

Evidence: B “One copied-field bound interface”; E section 13

## E041

Optional mask-block lookup/length/bound API

Evidence: E section 13, “Optional mask-block reuse”

## E042

Definable induction transport with explicit object formula and satisfaction witness

Evidence: A “A definable-induction transport lemma”; G “Wrap internal induction”

## E043

Shared model-axiom extraction/completeness/sealing bridge retaining arbitrary models and contexts

Evidence: A/B/C/D/E/H object endpoint sections

## E044

Arity-polymorphic closed-sentence/environment transport

Evidence: B “Generalize closed-sentence transport”; C “An especially small arity-polymorphism improvement”

## E045

Generic finite-index row-family facts for internal naturals (`Fin.forall_fin_add`, `forall_fin_two`), quantified List.ofFn simplification

Evidence: C “Build on algebraic interfaces already present”; G object finite-index section; H `inputsNaturalForm_spec`

## E046

Nine-coordinate packaging equivalence with coordinate 7 left unshifted

Evidence: F architecture A1; `NineCoordinatePackaging.lean`

## E047

Parameterized sharp Split/Gap numerical degree profiles and leading-coefficient bounds

Evidence: F architecture A2

## E048

Lower CurrentCarrierBase import layer/facade avoiding thirteen-coordinate completeness dependencies

Evidence: F architecture A4

## E049

Named conjunction accessors and derived positivity projections

Evidence: F architecture A5

## E050

Local standard-algebra reductions: Carrier66 positivity/canonical zero; `run_map`; whole-disjunction cast in FirstPellCarrier

Evidence: E sections 3-5, exact algebra patches

## E051

Specialize existing half_base_bound at 31; Finset intersection for mask sums; predecessor power identity; convolution distributivity; `Nat.one_lt_two_pow`; finite-switch boundary

Evidence: F `report/sections/02_local.tex` and tactics candidates

## E052

Finite-fiber/pushforward identity for foldStencil mass, convolution and word

Evidence: D “One finite-fiber identity for folded stencils”; FinitePushforward prototype

## E053

Injective sparse placement API distinct from general colliding foldStencil; Fin-to-ZMod transport

Evidence: G “Separate arbitrary folding from injective sparse placement”; H finite-word boundary

## E054

Guarded solvability congruence/transport and composition, without unnecessary witness bijections

Evidence: E section 10 and SolutionTransport.lean; G positiveZero_congr

## E055

Shared direct/native graph enumerator builder with separate cost projections

Evidence: E section 14; exact rawStepProgram/boundedRunProgram duplicates

## E056

Parser-then-check composition, generic quotation injectivity via partial decoder

Evidence: G “Reuse parser and list infrastructure”; checker source notes

## E057

Successful Option.bind inversion to remove impossible decoder branches; combined decoder graph/fuel theorem

Evidence: H decoder-options (with axiom distinction); J/K exact decoder graph sections

## E058

Pell parity theorem reuse in NativePellStepDown

Evidence: I “Reuse the already proved Pell parity criterion”

## E059

Signed congruence up to ±1 as transitive relation; absolute value transport; half-interval equality

Evidence: I sign section; J signed congruence section and algebra_review.md

## E060

Product-equivalence inverse projection graph theorem, including pairing/Cantor extension

Evidence: I “Derive inverse graphs from a product equivalence” and further questions

## E061

Shared positive-denominator Euclidean certificate and full quotient/remainder/slack uniqueness/coherence

Evidence: E section 6; I Euclidean certificate section and further questions

## E062

Affine composition-depth/witness budget helper and removal of ordinary graph nonempty-arity premise

Evidence: I “Factor the arithmetic budget”; further questions

## E063

Certified max-plus/depth-budget summaries, local constructor adapters and expression traversal preserving let sharing

Evidence: I further question; J “Synthesize representation-depth bounds”

## E064

Internal tagged constructor/no-confusion views and combined unique-existence code induction

Evidence: J “Constructor views and one internal unique-existence induction”

## E065

Internal recursive-graph invariant/preservation/fusion, retaining exact definable predicate

Evidence: J “Preservation and fusion for internal recursive graphs”

## E066

Explicit least/greatest cyclic carry formulas, two-solution classification and budget selection

Evidence: J “An optional structural alternative: explicit cyclic carries”; algebra_review.md

## E067

Preserve chosen rational witnesses on integer descent using denominator-one integrality

Evidence: K “Preserve rational roots when descending to integers”

## E068

Decompose product units once using IsUnit.mul_iff/Int.isUnit_iff

Evidence: K “Decompose the product's units once”; E has older factor-by-factor unit simplifications

## E069

Finite invariant reflection/restricted injection surjectivity instead of periodic predecessor orbit

Evidence: K “Use finiteness to recover an invariant predecessor”

## E070

Polynomial support envelope first, then coefficient vanishing via natDegree

Evidence: K “Prove the support envelope before individual coefficients”

## E071

Rotation as convolution with a point mass, reuse word_convolution

Evidence: K “Rotation is convolution with a point mass”

## E072

Scoped fun_prop registrations for extensional Primrec composition, separate from supplied program syntax

Evidence: K “Automate extensional primitive-recursiveness composition”

## E073

Fixed raw+digit carry uniqueness via finite maximum principle; fixed-length packing injectivity

Evidence: K “Canonical normalization from a finite maximum principle”

## E074

Support-restricted evaluator congruence/frame rules, signed Expr extension of existing WitnessCompaction.eval_congr

Evidence: J `evidence/prior_ideas.md`, candidate 7, including subsequent maintained-source caveat

## E075

Normalize schema renaming chains by algebra of index maps

Evidence: J `evidence/prior_ideas.md`, candidate 8; `evidence/semantic_review.md` section 5

## E076

Cyclic packing via monoid algebra/quotient-ring homomorphism

Evidence: J `evidence/prior_ideas.md`, candidate 9; `evidence/algebra_review.md` optional direction

## E077

General profiling, simp boundaries, small checked certificates, sharding, generator/output synchronization, compatibility wrappers, explicit audit policies/import coverage

Evidence: All manuscripts; F validation and import census. These are sound practices, not new proposal mechanisms.

## E078

Future finite-state controller invariants only after actual decoder binding; SCC/ranking for cycle exclusion

Evidence: E report section 13, final paragraph. This does not specifically propose Wang step/tape decomposition, but generic finite-state-invariant language is already present.

## E079

Replace artificial trivial existential lets by `set ... with ...` in NativeHalfBinomial.upper_estimate_scaled

Evidence: H `evidence/arithmetic/findings.txt`, section 8, “Minor readability improvements in analytic estimates”

## E080

Standard natural subtraction/remainder identities; let omega handle supported Nat/Int casts; keep huge powers symbolic

Evidence: H manuscript “Natural subtraction and remainder”, “Let omega handle the cast interface”, “Keep huge powers symbolic”; `evidence/arithmetic/findings.txt` sections 4-6

## E081

Shared semantic binaryForm/unaryForm constructors and code/rename/bound laws remove repeated valid-tag branches

Evidence: H `evidence/syntax/findings.txt` section 6; applies to AnnotatedRename.binary_sound and AnnotatedBound.binary_sound

## E082

Central `zero_pair : Nat.pair 0 n = n*n` and reuse generic syntaxDegree_rename

Evidence: H `evidence/syntax/findings.txt` section 7

## E083

Dedicated natural-semiring evaluator with erasure correctness, preserving typed register costs

Evidence: H `evidence/structural/findings.txt` section 7; manuscript final paragraph before validation

## E084

Directly specialize binaryWord_prefix at South offsets 19/20, normalizing addresses under lambdas

Evidence: L `report/report.tex`, page heading 4; M `report/sections/06_south_prefix.tex`

## E085

Reuse theta of an aligned representative as the exact difference-cell reachability witness

Evidence: L `report/report.tex`, page heading 5, `CurrentCellCycle2011.reachable_from`

## E086

Make zero-base cell propagation a specialization of existing propagate_from, with declaration reorder

Evidence: L page heading 5; M `report/sections/05_finite_and_cycle.tex`, C4

## E087

Guarded symbolic North/South tile-color fibers, or color-indexed NorthView, to share exact boundary classification

Evidence: L page headings 6–7; M `report/sections/08_north_view.tex`

## E088

Characterize alternate marked assignments by their selected bits in the same original word, then transport existing marked-word correctness

Evidence: L page heading 8, `assignment_eq_iff_selector` and `facts_marked_word_of_selector`

## E089

Replace raw parent-code reconstruction by existing total table decoding, exact re-encoding and check_lists

Evidence: M `report/sections/03_parents.tex`; `annotated/REVIEW_NOTES.md`, A

## E090

Hoist existing binaryWord_congr to the definition layer and reuse it in copy-word and horizontal-word clients

Evidence: M `report/sections/07_word_congruence.tex`; `current/current_findings.txt`, C3

## E091

Replace CRT modulus tactic search by explicit congruence transport through add/multiply/add

Evidence: M `report/sections/09_supplemental.tex`, S1; `supplemental/crt-explicit-congruence.patch`

## E092

Uniform Pell fundamental-unit criterion for positive ordinate at most three, replacing firstUnit_fundamental entirely

Evidence: N `report/additional_lean_simplifications.tex`, lines 283–370; `patches/main.patch`

## E093

Consume quadratic Boolean zero-certificate equivalence before assembling conditional witnesses

Evidence: N report section “Consume the Boolean certificate before constructing a conditional”

## E094

Package physical-position injectivity as Fin.cons of zero and a positive injective strict-rank tail

Evidence: N report section “Optional: recognize the physical permutation as a positive tail”; `optional/permutation-injectivity.patch`

## E095

Replace internal omega_ind proofs whose induction hypothesis is unused by existing nat_zero_or_succ decomposition

Evidence: O report Idea 1, ObjectAdditionCancellation.addRel_zero_iff and ObjectNaturalZero.mulRel_zero_iff; further audit question

## E096

Prove simultaneous Pell-coordinate monotonicity in the base, compare indices directly, and inspect weaker base-separation obligations downstream

Evidence: O report Idea 4 and further research questions; NativePellBootstrap.main_index_gt_first

## E097

Keep nonsquare integer norm proof integral via Int.pow_dvd_pow_iff and cancellation of a nonzero square

Evidence: O report Idea 5, MinimumNorm.norm_ne_zero_of_not_isSquare

## E098

Share the general separated-norm integer-root theorem below both finalizer clients, retaining signed nonzero weights

Evidence: N report “Put the general separated theorem below both clients”; overlaps E67's exact-root descent but adds this explicit theorem-placement/generalization obligation

## E099

Parameterized Pell approximation error allowance / positive scale and lower comparison

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26p/report.tex', 'line_start': 124, 'line_end': 190}

## E100

Proof fragments for an arbitrary list of premises, exact reversed-history offsets and fragment composition

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26p/report.tex', 'line_start': 192, 'line_end': 245}

## E101

Successor-first fork correctness, separating the zero output before predecessor arithmetic

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26p/report.tex', 'line_start': 247, 'line_end': 281}

## E102

Support separation via an additive quotient homomorphism and a difference-set test

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26p/report.tex', 'line_start': 283, 'line_end': 324}

## E103

Full canonical pairing witness vector from certificate uniqueness

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26p/report.tex', 'line_start': 326, 'line_end': 363}

## E104

Negative Pell norm obstruction by squaring a negative unit, positive-unit classification and first-coordinate congruence

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26q/report/new-proof-simplifications.tex', 'line_start': 139, 'line_end': 215}

## E105

Normalize several square/norm residue obstructions to a single existing theorem

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26q/report/new-proof-simplifications.tex', 'line_start': 217, 'line_end': 266}

## E106

Finite minimum saturation converts a sum of lower bounds attained at equality into all component equalities

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26q/report/new-proof-simplifications.tex', 'line_start': 268, 'line_end': 315}

## E107

Monotone local certificate closure under empty, union and justified insertion

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26q/report/new-proof-simplifications.tex', 'line_start': 317, 'line_end': 376}

## E108

Natural perturbation identity and power sandwich, factoring error tolerance into a separate budget

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26r/report.tex', 'line_start': 256, 'line_end': 422}

## E109

Exact integer binomial quotient and discrete half-quotient rounding instead of real fractional-part restoration

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26r/report.tex', 'line_start': 424, 'line_end': 558}

## E110

Define a rule schedule syntax once, derive direct checker and PR interpretations with executable erasure

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26r/report.tex', 'line_start': 560, 'line_end': 648}

## E111

Compositional satisfaction normalization for object-formula specification theorems

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26s/report.tex', 'line_start': 177, 'line_end': 289}

## E112

Recover a discrete integer from two asymmetric approximation-error budgets

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26s/report.tex', 'line_start': 385, 'line_end': 441}

## E113

Identify the existing numeric list codec exactly with the standard library codec, then reuse length/typed parent results

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26t/report/sections/02_encoding.tex', 'line_start': 1, 'line_end': 109}

## E114

Local two-point ordered-pair coefficient fiber theorem, square and mixed-product versions, foundational selective coefficient layer

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26t/report/sections/03_coefficients.tex', 'line_start': 1, 'line_end': 116}

## E115

Use magnitude/squared magnitude of the second Pell coordinate and optional minimum-coordinate fundamentality criterion

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26t/report/sections/04_pell.tex', 'line_start': 1, 'line_end': 103}

## E116

Bounded first-exit or first-failure theorem returning the endpoint and valid prefix

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26t/report/sections/05_first_exit.tex', 'line_start': 1, 'line_end': 84}

## E117

Native rank envelope (2q-1)(q^2-1) <= rank, implying rank>=40 and rank>3q

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26u/report.tex', 'line_start': 198, 'line_end': 268}

## E118

Centered or translated integer induction for interval propagation

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26u/report.tex', 'line_start': 270, 'line_end': 318}

## E119

Build a Wang row from one shared horizontal edge function and a single bridge edge

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26u/report.tex', 'line_start': 353, 'line_end': 438}

## E120

Use le_abs' directly for absolute-value machine trace bounds

Evidence: {'path': 'Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26u/report.tex', 'line_start': 440, 'line_end': 448}

## E121

Identify the halt-last Option (Fin 215) stateNumber with finSuccEquivLast; derive injectivity by composition.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26v/report/sections/04_encoding_action.tex

## E122

Reflect actual action halting through stateNumber_injective and act_stateNumber while retaining target <216.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26v/report/sections/04_encoding_action.tex

## E123

Split color_action only at the written tape cell; leave moved-head conditional symbolic away from write support.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26v/report/sections/05_machine.tex

## E124

Represent west/east step-row edges by one bond pulse and derive horizontal matching by evaluation at one bond.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26v/report/sections/07_pulse.tex

## E125

Treat the helix as a period lattice vector; derive integer multiples and seam-time invariance through period algebra.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex

## E126

Prove RefinedPair sign-invariant polynomial identities before evaluation instead of passing through complex square roots.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex

## E127

Centralize twisted-band indexing in an exact helical coordinate equivalence, normalization and inverse laws.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex

## E128

Construct matching rows from shared horizontal and vertical edge fields, with constructor-local tile equations.

Evidence: Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26w/report.tex

## E129

Replace finite seam-wall enumeration by Fin 3 bounds and Nat.pow_le_pow_left.

Evidence: docs/incoming/Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip :: report/08-accounting.tex

## E130

Prove every actual receive tile lies at the actual moved head from spatial matching alone; derive far_pass_or_finish and zero-edge clients.

Evidence: docs/incoming/Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip :: report/06-causality.tex

## E131

Retain complete receiver tile equality and identify extraction with independently constructed stepTile on the open strip; project south_step.

Evidence: docs/incoming/Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip :: report/07-canonical.tex

## E132

Replace signed helical induction with a periodic orbit, including a reusable one-parameter orbit interface.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex §A

## E133

Derive coprime divisibility decomposition in RatioReparameterization through library divisibility cancellation, retaining degenerate cases.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex §B

## E134

Use the exact geometric-series identity to derive the PolynomialRangeBounds geometric inequality.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex §C

## E135

Read a positive quadratic margin as the exact centered interval via a square/absolute-value theorem.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex §D

## E136

Give finite signed borrow its whole-prefix quotient/remainder meaning, including negative prefixes and borrow-zero iff nonnegative sum.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex §E

## E137

Compare native ranks via the single scalar C+qF, with strict/weak/equality comparisons and exact actual-core adapters.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex §F

## E138

Prove the endpoint span cutoff before inspecting most supports in the Sidon position argument.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex §P1

## E139

Use a two-dimensional helical period group law instead of induction.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex §P2

## E140

Derive the period lower bound from initial-strip width and geometry.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex §P3

## E141

Recover the pairing branch from the output square-shell threshold so only two cases remain.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex §P4

## E142

Use the list-code constructor equation directly for the list-head bound.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex §P5

## E143

Replace two local geometric-sum inductions by matching exact library identities and derive the bound without another induction.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex §P6

## E144

Build the internal-natural LinearOrder from its existing strict total order using linearOrderOfSTO, preserving definitional compatibility.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex §P7

## E145

Use direct polarization for the Sidon argument after endpoint-sum equality.

Evidence: docs/incoming/diophantine-lean-further-deltas-2026-10-26.zip :: report/report.tex Supplement

## E146

Derive formula-code thresholds from constructor minima rather than decode or enumerate smaller codes.

Evidence: docs/incoming/diophantine-lean-proof-refinements-2026-10-26.zip :: report/lean-proof-refinements.tex §A

## E147

Establish strict internal multiplication through a nonzero additive difference before successor discreteness; obtain Boolean roots from algebra.

Evidence: docs/incoming/diophantine-lean-proof-refinements-2026-10-26.zip :: report/lean-proof-refinements.tex §B

## E148

Expose period-one functions to replace helical and seam-time inductions.

Evidence: docs/incoming/diophantine-lean-proof-refinements-2026-10-26.zip :: report/lean-proof-refinements.tex §C

## E149

Preserve an exact witness before existential erasure so two existing clients share the stronger intermediate theorem.

Evidence: docs/incoming/diophantine-lean-proof-refinements-2026-10-26.zip :: report/lean-proof-refinements.tex §D

## E150

Normalize helical orbits and seam-time invariance through the algebra of periods.

Evidence: docs/incoming/proveit-lean-structural-simplifications-2026-10-26.zip :: report.tex §P1

## E151

Replace the index-six Pell threshold with a fixed anchor, retaining monotonicity in the index and parameter rather than a new asymptotic estimate.

Evidence: docs/incoming/proveit-lean-structural-simplifications-2026-10-26.zip :: report.tex §P2

## E152

Certify signal-family masses through cardinality and four color-coordinate sums because packed weights are affine in those statistics.

Evidence: docs/incoming/proveit-lean-structural-simplifications-2026-10-26.zip :: report.tex §P3

## E153

Recognize operating rows by a canonical full-tile form, optionally using guarded three-color tile determinism.

Evidence: docs/incoming/proveit-lean-structural-simplifications-2026-10-26.zip :: report.tex §P4

## E154

Extend exact signed-prefix division to concatenation with a nonzero incoming borrow; this is already an announced direction.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex Further questions

## E155

Expose both margin endpoints if new clients justify a shared centered-interval lemma.

Evidence: docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip :: report/report.tex §D/Further questions
