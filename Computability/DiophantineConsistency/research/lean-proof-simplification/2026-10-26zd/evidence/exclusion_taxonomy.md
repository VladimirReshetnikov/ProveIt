# Exclusion audit for the 26 October 2026 review

## Snapshot and counting

The comparison pin is `89226e3921bce3e8949fadd12d3efb6914c7630c`. The exact tree contains **23 placed packets** (`2026-10-26a` through `2026-10-26w`), **1,286 files** under `research/lean-proof-simplification` including the index/adoption records, and **four incoming ZIPs containing 911 non-directory members**. These are repository/artifact counts, not counts of novel proposals or verified Lean modules.

The incoming README's prose is insufficient to determine the current queue: four ZIPs exist in the tree. They are:

- `Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip`
- `diophantine-lean-further-deltas-2026-10-26.zip`
- `diophantine-lean-proof-refinements-2026-10-26.zip`
- `proveit-lean-structural-simplifications-2026-10-26.zip`

`prior_corpus_inventory.json` records the paths, byte counts and SHA-256 identities. `prior_proposal_sections.tsv` records 2,028 heading occurrences from report and supplementary text, excluding selected bundled baseline/catalog copies. This heading count includes repeated discussions and metadata; it is not a manuscript or idea count.

The review used report bodies, summaries, prior exclusion ledgers, supplied notes and targeted searches. It did not execute supplied programs. Existing compilation logs are inherited evidence only. Every recorded proposal, including optional, deferred, uncompiled or unselected ideas, is treated as available for the user's non-repetition requirement. Conflicting alternative designs are assumed contracts, not a fictitious jointly compiled codebase.

## Reference convention

`a` through `w` mean `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26<letter>/`. Section titles below identify exact text; the TSV gives path and line references. `PA`, `FD`, `PR` and `SS` mean the four incoming ZIPs in the order above. ZIP references denote archive members rather than URLs to individual members.

## Excluded families and exact prior applications

| Family | Mechanisms already proposed | Primary anchors |
|---|---|---|
| Primitive recursion and scanners | Congruence under `Nat.rec`; iteration zero/successor/done; scanner semiconjugacy; dynamic-seed PR iterator; guarded/validated history folds | a `report.tex` §§Small proof replacements, Scanner proofs; b §§Checked histories; c §§Share scanner proofs |
| List and option interfaces | Seven private lookup inductions; `Option.map_injective`; exact successful-decode graph; arbitrary-code decoder correctness; quote/depth fusion; parent raw/typed decoder bridge; exact identification with standard list codec; constructor list-head bound | a lookup; i/j decoder graph; n parents/decoder sections; t `02_encoding.tex`; FD P5 |
| Boolean and tag interfaces | Exact numeric 0/1 value rather than Booleanity+iff; frozen tag dispatch; Boolean certificate consumed before conditionals; semantic constructor witnesses; formula thresholds from constructor minima | a/b/e; m §Consume Boolean certificate; PR A |
| Assignment and witness interfaces | Evaluation/renaming naturality; sum-type witness splits; witness count projections; nine-coordinate packaging; explicit coherent source/window assignment; exact witness retained before existential erasure | a/b/d/f; PR D |
| Pairing | Product-equivalence inverse graphs; existential projection of forward certificates; canonical pairing witness; output threshold recognizing square-shell branch | k; m; p E; FD P4 |
| Algebraic residual systems | Common sum of residual squares; zero-set row operations; guarded solution/existence transport; heterogeneous block minima and minimum saturation | a/b/c/e/g; q minimum-saturation section |
| Circuit/DAG proof architecture | Existing power labels; indexed node facade; generated wrappers; shared topological invariant; semantic cuts; identical 99-node tails; typed circuit views; shared semiring gate semantics; rename/root/count layers | a–h; f circuit sections |
| Degree and cost | Degree certificates/profile; ShortSystem shared prefix; sparse normalization; affine composition budgets; max-plus depth certificates; ordinary zero arity | c/f/j/k and n Fin2 helper |
| Coefficients and sparse supports | Shared envelope schema; finite majorants; naturality; univariate degree support; exact local coefficient fibre; injective sparse placement; quotient homomorphism support separation; early short-span Sidon cutoff and direct polarization | c/d/h/i; p D; t `03_coefficients.tex`; FD P1 and supplement |
| Finite data assembly | Balanced/chunked certificates; decoder-bound tables; physical selector sums; copied-field directions; affine signal-mass statistics | a/b/e/f; SS P3 |
| Cyclic arithmetic | Exact half-radix/scaled quotient identity; whole-shift division/remainder; stronger-to-weaker moduli; Fin/ZMod/list boundary; cyclic packing through monoid algebra; point-mass convolution rotations; binaryWord congruence and South prefix specializations | a–h, i, n/o |
| Carry structure | Shared exact decomposition and recurrence; full-word/fixed-digit canonical uniqueness; explicit least carry formula and ambiguity classification; origin decrement/no-borrow word identity | a/b/e/i/j and a digits notes |
| Pell elementary arithmetic | Signed congruence/divisibility composition; parity reuse; integer norm proof; small-ordinate/magnitude criterion; negative norm via positive units; residue obstruction normalization | i–m, q, t |
| Pell growth | Positive-pair recurrence and parameter monotonicity; one explicit error-factor theorem; natural perturbation kernel; positive scale/denominator normalization; integer error-budget rounding; fixed index-six anchor | l/p/r/s/u; SS P2 |
| Native rank/quotients | Stronger common rank lower envelope; exact integer quotient for half-binomial; natural/integer rank source facts; retain huge powers symbolically | c notes/h; r/u |
| Internal arithmetic/model transport | Shared model axioms; arity-polymorphic closed transport; semantic completeness/sealing; definable induction wrappers; constructor views; unique existence and recursive graph fusion; delete vacuous induction; strict-order construction; strict multiplication before successor discreteness | a–h/j/l/q; FD P7; PR B |
| Internal formula semantics | Exact formula-specification semantic fold; internal finite-row quantifier normalization; functional-relational evaluation; schema rename-chain normalization; support-local evaluator frames | c notes/g/j notes/s |
| Internal certificates | Monotone local certificate calculus; union/insertion closure of observed sets; generic relation-closure views | q/s |
| Annotated proof construction | Typed `Produces` fragment append laws; variadic premises; normalized rule schedule DSL and two interpretations | c notes/p B/r |
| Finite invariants | Injective finite map predecessor reflection; finite-set inverse invariance; sum-at-most-one support classification | i/k/l and n |
| Cell and boundary geometry | Aligned-cell equivalence; direct theta difference witness; zero-base propagation specialization; high-color north/south fibre views; selected-index coherence | e/i/n/o |
| Integer strip arguments | Centered integer induction; translated interval induction; first-exit/first-failure with valid prefix; direct wall power bounds; absolute-value trace cleanup | t/u/v and PA |
| Helical periodicity | `Function.Periodic` via lattice vector or shear; integer multiple closure; seam period-one; band/time canonical equivalence; period lower bound from strip width | w; FD P2/P3; PR C; SS P1 |
| Machine encoding | Reflect halt through equivalence; split only on write site; absolute-value state/tape view | v |
| Wang row construction/recognition | Shared edge fields; one bridge pulse; constructed row matching by representation; local tile determinism; canonical operating-row recognition; exact actual receiver location; actual tile equals independent `stepTile` | u/v/w; SS P4; PA |
| Finalizers | Witness-preserving rational-to-integral descent; product units; signed root recovery; formal `RefinedPair.core_eq` by injective polynomial exponent expansion before evaluation | i/m/w |
| Module and audit architecture | Import-layer cuts; consolidated pure axiom wrappers; trust/statement/data-preservation audits; meaningful performance measurement | a–h and later validation sections |

## Important late exclusions

1. **Periodicity is repeatedly proposed.** Giving a different one-line application of `Periodic` in another old helical/seam client is not new.
2. **Canonical row and edge-field designs already exist.** Distinguish a genuinely different mathematical contract from merely proving another matching corollary in that representation.
3. **Support algebra already includes weighted fibres.** An injective finite-image or selector-weight transfer is not new merely because the current client is a new controller module.
4. **Parameterized Pell bounds are saturated territory.** Error-factor, denominator, magnitude, rank envelope, fixed anchor and rounding improvements all occur in the corpus.
5. **Preserving witness information is an old explicit proposal.** A new exact theorem can still be useful, but the proposal must identify the new conclusion and pay its helper cost instead of claiming the old strategy as novel.
6. **Tiny current-source applications need honest positioning.** A specific new declaration may admit a new useful patch even under an old general API. State it as a new application, quote the nearest precedent and do not claim a new architecture or global tactic idea.

## Novelty standard for retained candidates

For each candidate, identify: (1) actual current declaration and proof burden; (2) closest earlier proposal; (3) exact residual contract or deletion after that earlier API is available; (4) full helper/import cost; (5) validation status. If (3) is only a renamed use of (2), discard the candidate. A claim of absence is bounded to the pinned comparison corpus, not a claim of mathematical or Lean-library priority.

## Closing refresh

A separate check through `663fb267f6142ca4c0ea5bcd2d4f607f9a4b0eda` includes one additional incoming packet, bringing coverage to 28 packets (23 placed and five incoming). All four retained deltas survive the comparison. See `freshness/FRESHNESS_SUPPLEMENT.md` and `freshness/refresh_corpus_manifest.json`; initial source measurements and hashes remain tied to `89226e3921bce3e8949fadd12d3efb6914c7630c`.
