# Prior-proposal exclusion ledger

Pinned source: `6f46a5e3480a2fa2e45993b8090826f256aeaa56`.

Treat every proposal in the user-specified directories as already applied, including uncompiled, pending, deferred, and design-only ideas. This is a technique exclusion ledger, not an implementation/adoption verdict.

The audit inventory covers 329 files in the two requested directories and 400 archive members in the five current incoming ZIPs. SHA-256 entries are in `prior-corpus-manifest.json`. All eleven principal manuscripts were inspected by sections, with supplementary source notes and code artifacts searched for overlap. Hash coverage is not a claim that every incidental source snapshot or binary was independently read.

References below are file-and-line references in the pinned repository; `archive!member` identifies the text inside an incoming ZIP.

## EX01 — Primitive-recursion congruence

Rewrite pointwise recursive function equality through a generic recursor congruence lemma, including data-preserving PR optimizer proofs.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 114–131.

## EX02 — List and Option library reuse

Replace duplicated lookup-to-membership/existence inductions and Option injectivity proofs with existing library facts.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 132–143.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 162–185.

## EX03 — Assignment naturality and witness layouts

Move variable/witness renaming through combined assignments, use witness sum-type equivalences, and share layout/projection transports.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex`, lines 219–283.
- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 371–427.

## EX04 — Residual squares

Centralize finite sums of squares, zero-set characterization, evaluation and syntax-level degree lemmas across compilers.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 162–189.
- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 428–505.

## EX05 — Power-label certificates and generated node facades

Replace individual power proof chains by existing run_power, share per-circuit node specialization/indexed gate interfaces, preserve public wrappers and producer output.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 190–239.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/04_circuits.tex`, lines 50–166.

## EX06 — One topological DAG invariant

Share DAG induction for uniqueness, nonnegativity and degree; do not claim the first generic semantics theorem.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 240–255.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/report.tex`, lines 676–710.

## EX07 — Circuit translation and commutative relations

Generic positive/natural translation simulation, commutative operand swaps, low-level append invariants and degree infrastructure extraction.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 256–277.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/report.tex`, lines 711–753.

## EX08 — Scanner iteration and coding simulation

Iteration fixed states, successor commutation, encoded-list scanner simulation, fuel/rejection boundaries, code-level iterator interface; closure encoding fusion is included.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex`, lines 327–379.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 186–213.
- `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip!diophantine-lean-simplification/report.tex`, lines 256–294.

## EX09 — Validated history folds

Abstract guarded lists with potentially distinct input/output history types; append and preservation proofs; parser/checker adaptation.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex`, lines 284–326.
- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 506–555.

## EX10 — Exact numeric checkers and tag dispatch

Booleanity plus acceptance iff turned into exact 0/1 output; shared threshold dispatch for current frozen numeric tags.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 296–310.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 214–233.

## EX11 — Half-radix, scaled division and residue interfaces

Exact scaled division identity instead of finite digit enumeration; transport cyclic residues through Fin/ZMod/list boundaries; stronger modulus reused for weaker.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26d/report.tex`, lines 310–374.
- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 603–647.

## EX12 — Conditional padding witness

Conditional padding existence when the count exceeds the relevant threshold instead of an overstrong unconditional premise.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 330–342.

## EX13 — Exact carry decomposition and recurrence

Package exact digit/carry equations, derive recurrence from normalized local arithmetic, share carry zero and residue consequences.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 343–354.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex`, lines 642–677.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 305–332.

## EX14 — Internal definable induction wrappers

Shared induction transport from an explicitly defining formula, not unrestricted external induction on model naturals.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex`, lines 355–364.
- `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip!diophantine-lean-simplification/report.tex`, lines 463–483.

## EX15 — Object semantic completeness/sealing and model bridges

One completeness-and-sealing wrapper, shared ZFC-model to ZF-axioms bridge, closed-sentence environment transport polymorphic in arity.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex`, lines 726–781.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/report.tex`, lines 809–868.

## EX16 — Coefficient envelopes and row naturality

Shared coefficient-row bound schema, finite majorant certificates, map/naturality simplification and computational coefficient syntax.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/report.tex`, lines 330–426.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/03_architecture.tex`, lines 214–253.

## EX17 — Register cuts and common carrier tail

Reuse named register facts, isolate identical 99-node scalar tail/recipe correctness, preserve cutpoints.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/report.tex`, lines 427–540.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 234–256.

## EX18 — Shared gate semantics and compiler syntax layers

Generic semiring soundness/completeness, extract root/count/rename facts below natural/signed realizers, retain cost distinctions.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex`, lines 397–468.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26d/report.tex`, lines 502–576.

## EX19 — Sparse-row reflection and elementary row operations

Small certified sparse arithmetic normalization; zero-set preservation by row addition and surjective row reindexing.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/report.tex`, lines 754–808.

## EX20 — Finite-fiber pushforward and sparse placement

Share finite weighted fiber identity; separate noninjective cyclic folding from injective sparse packing.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26d/report.tex`, lines 415–445.
- `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip!diophantine-lean-simplification/report.tex`, lines 427–434.

## EX21 — Native facts records and coherent window source

Named conjunction projections/Prop records, one shared source assignment and scalar window witness, layered WordFacts context.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/03_architecture.tex`, lines 68–146.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 305–332.

## EX22 — Finite certificate block assembly

Balanced coverage of checked chunks, final partial blocks, retain kernel checks rather than one huge decide.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex`, lines 678–711.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 333–355.

## EX23 — Aligned-cell and packed-direction geometry

Reuse cell equivalences including additive/cyclic geometry, direction descriptors and reindexing of 34 controls; origin and mask block distinctions.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 305–355.
- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 92–120.

## EX24 — Guarded solution transport

Abstract existence and zero-set equivalence with positivity/domain guards and witness quantifier order preserved.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 257–286.
- `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip!diophantine-lean-simplification/report.tex`, lines 240–255.

## EX25 — Direct/native graph-enumerator builder

Parameterize common graph control flow over differing combinators, preserve actual witness counts.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 356–377.

## EX26 — Nine-coordinate packaging

One evaluator-parametric positive/natural coordinate equivalence with asymmetric unrestricted j coordinate.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/03_architecture.tex`, lines 11–67.

## EX27 — Degree-profile abstraction

Share Split/Gap layer domination and upper bounds from symbolic degrees with actual leading coefficient/height and strict gap hypotheses.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/03_architecture.tex`, lines 172–213.

## EX28 — Typed circuit views and semantic block certificates

Checked circuit wrapper or Fin-earlier node view erasing to original list; block certificates bound to existing DAG and independent recipe.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/04_circuits.tex`, lines 167–233.

## EX29 — Degree-prefix consolidation

Shared ShortSystem prefix proof or degree certificate preserving cancellation-sensitive sharp bound.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/04_circuits.tex`, lines 188–210.

## EX30 — Import and audit architecture

Current base interface below completeness, thematic imports, audit manifest/gates and consolidation of pure print-axiom wrappers.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/03_architecture.tex`, lines 147–171.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/05_validation.tex`, lines 39–107.

## EX31 — Local algebraic and library edits

Carrier66 positivity/canonical_zero, add/mul branch sharing, ArithmeticDAG.run_map, FirstPellCarrier casts, integer units and residual sum cleanup.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 77–161.

## EX32 — Local finite-set and arithmetic edits

Generic half_base bound specialization, finite-set intersection, predecessor exponents, modular rewrites, convolution factorization, exact powers and finite-switch normalization.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/02_local.tex`, lines 10–245.

## EX33 — Finite sum at most one support classification

Use existing sum_le_one_iff-style finite support theorem for one-hot rather than new Finset induction.

- `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip!diophantine-lean-new-ideas-2026-10-26/report.tex`, lines 143–200.
- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 255–270.

## EX34 — Pell parity reuse

Derive duplicated Pell odd-power/parity facts from criterion already established elsewhere, with dependency correction.

- `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip!diophantine-lean-new-ideas-2026-10-26/report.tex`, lines 201–252.

## EX35 — Product-equivalence inverse graphs

Inverse coordinate graphs from product equivalence, separate tuple normalization and preserve actual program data.

- `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip!diophantine-lean-new-ideas-2026-10-26/report.tex`, lines 253–350.

## EX36 — Euclidean division certificate and uniqueness

Shared positive-denominator certificate for natural quotient/remainder across backends; uniqueness/coherence of tuple.

- `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip!diophantine-lean-new-ideas-2026-10-26/report.tex`, lines 351–414.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex`, lines 162–185.

## EX37 — Composition budgets and depth certificates

Arithmetic budget lemma, remove unnecessary nonempty premise when valid; small max-plus certificate for representation depth.

- `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip!diophantine-lean-new-ideas-2026-10-26/report.tex`, lines 415–496.
- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/report.tex`, lines 347–405.

## EX38 — Compositional congruence up to sign

Signed modular relation with transport/transitivity instead of repeated Pell four-way sign cases.

- `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip!diophantine-lean-new-ideas-2026-10-26/report.tex`, lines 497–562.
- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/report.tex`, lines 169–216.

## EX39 — Exact recursive-decoder graph

Fuse soundness/correctness and exact fuel condition into decodeFuel k n = some t iff code/fuel fact; characterize arbitrary-code rejection. Also includes parse-then-check factoring and generic quote injectivity from a partial decoder left inverse.

- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/report.tex`, lines 123–168.
- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 182–221.
- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 310–370.
- `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip!diophantine-lean-simplification/report.tex`, lines 445–454.

## EX40 — Internal constructor views and joint unique existence

Tagged-relation inversion over arbitrary model carrier, and one ∃! induction instead of separate totality/functionality in ObjectCodeBound.

- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/report.tex`, lines 217–275.

## EX41 — Internal recursive-graph preservation and fusion

ThetaG invariant proof using genuine definable induction, totality/uniqueness and successor law; formula-generation and semiconjugacy extensions included.

- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/report.tex`, lines 276–346.

## EX42 — Explicit cyclic carries and least solution

Closed cyclic carry formula from rotations; extremality/two-solution boundary, budget selection of least carry.

- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/report.tex`, lines 406–507.

## EX43 — Rational root integral descent

Denominator lemma and exact complete-tuple descent preserving rational roots rather than recovering signs later.

- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 121–158.

## EX44 — Product unit decomposition

Derive unit factors together rather than manufacture complementary products separately.

- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 159–181.

## EX45 — Finite invariant predecessor reflection

Finite/injective map gives predecessor within invariant subset, applied to offset19 cycle exclusion.

- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 222–249.

## EX46 — Univariate support envelopes

Prove degree support bound first and use it for vanishing coefficients rather than replaying individual coefficients.

- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 250–282.

## EX47 — Rotations as point-mass convolution

Derive rotation/translation formulas by convolution with a singleton impulse.

- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 283–308.

## EX48 — Extensional Primrec automation

Register Primrec closure rules for fun_prop with parameterized pairing, independent of executable PR-code construction.

- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 309–347.

## EX49 — Canonical carry normalization uniqueness

Finite maximum principle for carry uniqueness with fixed normalized digit vector; full packed word fixes digits; coherence consequence.

- `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip!diophantine-lean-additional-simplifications-2026-10-26/report.tex`, lines 348–395.

## EX50 — Origin-decrement word identity

Shared no-borrow origin decrement between current and legacy high-mask words, retaining pointwise lower bound.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/source_notes/digits-review.md`, lines 205–229.
- `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip!diophantine-lean-simplification/report.tex`, lines 414–426.

## EX51 — Direct physical selector-sum interface

Expose physical Fin-942 selector sum directly rather than convert via prefix sum and back, using existing physicalEquiv.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/source_notes/digits-review.md`, lines 230–248.

## EX52 — Pell rank Nat/Int source-facts boundary

Package natural rank, nonnegativity, cast equality and derived bounds from actual positive source rows; preserve ordered natural subtraction.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/notes/arithmetic.txt`, lines 227–252.

## EX53 — Typed proof-fragment composition

Common Produces run/append/step laws with reversed history order, used by ready_binary/ready_unary/fragment2/fragment3 completeness constructors.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/notes/syntax.txt`, lines 75–90.

## EX54 — Functional relational evaluation

Generic functional-relational evaluator for ObjectNaturalExpression.evalRel_unique preserving arbitrary inputs, and shared standard/internal row-family algebra.

- `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/notes/syntax.txt`, lines 123–135.

## EX55 — Semantic binary constructor lemmas

Share code_binaryForm/renamed_binaryForm/bound_binaryForm and typed constructor witnesses across AnnotatedRename/AnnotatedBound with valid-tag guard.

- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/evidence/syntax/findings.txt`, lines 122–133.

## EX56 — Small pairing and syntax-degree helper consolidation

Share zero_pair across CodeGraphs/SyntaxGraphs/SharedSyntax and reuse general syntax-degree renaming API.

- `docs/incoming/lean-proof-simplification-review-2026-10-26.zip!lean-proof-simplification-review/evidence/syntax/findings.txt`, lines 135–147.

## EX57 — Support-local evaluator frame rules

Agreement only on occurrences, overwrite/frame corollaries, and signed Expr extension building on existing WitnessCompaction.eval_congr.

- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/evidence/prior_ideas.md`, lines 154–167.

## EX58 — Schema index-map normalization

Certified normalization of AnnotatedSchemaMaps rsep/rf1/rf2/ri renaming composition.

- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/evidence/prior_ideas.md`, lines 168–172.

## EX59 — Cyclic word packing via monoid algebra

Additive monoid algebra on ZMod n mapped to ZMod(radix^n-1), deriving convolution/product and rotation laws; exact natural values require bounds.

- `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip!new-lean-simplification-2026-10-26/evidence/prior_ideas.md`, lines 173–180.

## EX60 — Additional provisional search directions

Do not present as untouched general ideas: functional-graph uniqueness eliminating witnesses, split-encoding reconstruction equivalences, relation algebra for zero-set feasibility, natural-difference/order-embedding APIs, and special syntax-pair induction principles. A distinct concrete residual application still needs its own comparison.

- `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip!diophantine-lean-new-ideas-2026-10-26/novelty-audit.md`, lines 67–69.
