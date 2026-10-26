# Non-repetition audit: 26 October 2026

Initial repository/comparison pin: `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.

Final effective cutoff: `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`, with 43 placed packets and no incoming ZIPs. See `final-refresh-addendum.md` for the seven new placements, relocation checks, and final candidate decisions. The original account below preserves the initial inspection scope.

## Scope and standard

The comparison set contains 36 placed packets, `2026-10-26a` through `2026-10-26zj`, and all five ZIPs physically present in `docs/incoming` at the pin. The index and adoption record, all principal report heading maps, inherited full-body exclusion ledgers, relevant proposal bodies and supporting notes, and all five current incoming reports were reviewed. Candidate-specific searches covered the textual prior artifacts, including proposed patches and prototypes; unmodified baseline copies were distinguished from recommendations. This is an overlap audit, not independent mathematical or compiler certification of the earlier packets. It does not recursively retrieve every historical link in the large incoming README.

Every earlier proposal is excluded regardless of adoption status. Optional, design-only, and deferred directions count as earlier ideas. Incompatible alternatives are treated as advertised contracts, not as a claim that all patches can be applied simultaneously. An incorrect rejected shortcut is not silently assumed as a valid mathematical lemma. Novelty below is relative to this bounded corpus, not a mathematical or Lean-library priority claim.

A different helper name, another tactic proving the same advertised abstraction, a new client of an already advertised general interface, or a new compilation check is insufficient. A retained idea must remove a distinct proof obligation after the earlier APIs are available. Complete helper/import/compatibility costs must be charged.

Reference prefixes below: `P` means `Computability/DiophantineConsistency/research/lean-proof-simplification/`; a packet letter means `P/2026-10-26<letter>/`. Incoming references name the ZIP followed by member path.

## Established families to exclude

| Family | Already proposed mechanisms | Exact representative evidence |
|---|---|---|
| Primitive recursion | Recursor congruence instead of nested induction; optimizer congruence; scoped `fun_prop` for extensional `Primrec` | a `report.tex`, Rewrite under primitive recursion; i `report.tex`, Automate extensional primitive-recursiveness composition; i `notes/checker.md`:32-58 |
| Scalar program builders | Dynamic-seed PR iterator; shared direct/native graph builders preserving actual supplied programs and costs | b `report.tex`, A better primitive-recursive iterator interface; e `report/report.tex`, shared control-flow section |
| Lists/options/decoders | Core lookup APIs; `Option.map_injective`; successful-decode exact graph; arbitrary-code correctness; quote/depth fusion; raw parent correspondence; equality with standard list codec | a lookup section; i/j decoder graph sections; n parent/decoder sections; t `report/sections/02_encoding.tex` |
| Scanners and histories | Nat.rec fixed-point/zero/done/successor laws; typed/encoded semiconjugacy; validated history folds; variadic proof fragments; a rule-schedule DSL interpreted twice | a/b/c/e scanner sections; p `report.tex` B; r `report.tex`, Define rule schedules once |
| Boolean/tag/constructor views | Exact numeric 0/1 reflection; tag dispatcher; consume Boolean certificates before conditionals; schema renaming normalization; constructor minima for formula bounds | a/b/e; m Boolean-certificate section; x `report/lean-proof-refinements.tex` A |
| Witness transport | Assignment naturality; split Fin witness blocks; early count projections; nine-coordinate packaging; coherent source/window witness; preserve exact band witness before existential erasure | a/b/d/f; x D; zi excluded H2 comparison |
| Pairing | Inverse projection from forward certificates; canonical witnesses; shell/output-threshold branch detection | k/m/p; y `report/report.tex` P4 |
| Residual systems | Common sum-of-squares and evaluation; guarded solution transport; zero-set row operations; minimum-saturation equality of all blocks | a/b/c/e/g; q minimum-saturation section |
| Circuit/DAG proofs | Existing exponent-label certificates; indexed node facade; generated wrappers; shared topological invariants; semantic cuts; shared 99-node tails; typed circuit views; generic semiring gate semantics | a-h, especially f `report/sections/04_circuits.tex` |
| Degree/cost | Syntactic/weighted degree interfaces; profile certificates; ShortSystem common prefix; affine composition budgets; max-plus depth certificates | c/f/j/k; n Fin2 helper; incoming Round5 definitional depth equality |
| Coefficient arithmetic | Common envelopes/majorants; finite catalogs; local coefficient fibres; support-before-coefficients; homomorphic coefficient evaluation; injective sparse placement | c/d/h/i/p/t |
| Composed coefficient bounds | Apply the existing linear coefficient estimate twice to bound products/squares; general power extension | zc `report.tex`, Compose the coefficient bound; zf `report.tex`, Apply the linear coefficient estimate twice |
| Sparse syntax | Monomial-list sum evaluation bridge; sparse-list coefficient expansion; polynomial identity transport into internal semiring semantics | ze monomial-list section; zg `report/sections/02_polynomial.tex`, `03-local.tex` |
| Finite data assembly | Chunked/balanced dispatch; decoder-bound tables; physical-selector direct sums; copied-field descriptors; affine signal mass/color statistics | a/b/e/f; z P3 |
| Cyclic arithmetic/support | Half-radix identity; full-modulus residue normal forms; stronger modulus implies weaker; finite-fibre pushforward including collisions; monoid-algebra packing; support quotient homomorphism; origin correction | a-h; p D |
| Carry theory | Decomposition/recurrence equivalence; named coherent Facts; fixed-word uniqueness; extremal explicit full-cycle carry; signed borrow prefix quotient/remainder | a/b/e/i/j; zb E |
| Pell algebra | Sign-relation composition; oddness reuse; magnitude minimality; negative norm via positive units; residue obstructions; positive-pair recurrence | i-m/q/r/t |
| Pell bounds | Common error-factor and positive-scale estimates; natural perturbation; exact quotient/rounding; index-six anchor; scalar exponential to quadratic threshold | l/p/r/s/u/z; zc/zf; incoming lean-proof-simplifications D |
| Native rank | Natural/integer rank bridge; common lower envelope; exact scalar affine rank; retain huge powers symbolically | c notes/h/r/u; zb F |
| Internal model transport | Model-axiom extraction; closed arity transport; completeness/sealing bridge; definable induction wrappers; constructor views; unique-existence induction; recursive graph preservation/fusion | a-h/j/l/q |
| Internal arithmetic/order | Exact formula specs and semantic folds; delete vacuous induction; strict-order construction; multiplication before discrete successor; internal successor from set membership; unit multiplication at zero | s; x B; y P7; zf first two proposals |
| Internal certificates | Monotone local certificate calculus; union/insertion closure; generic relational closure views; quantified environment restriction via surjectivity | q/s; zg P3 |
| Finite invariants | Injective finite-map predecessor reflection; invariant-set inverse closure; sum-at-most-one support | i/k/l/n |
| Wang geometry | Aligned-cell equivalence; direct theta differences; high-color fibres; selected-index coherence; translated interval induction; first-failure/exit prefix; direct wall bounds | e/i/n/o/t/u/v/za |
| Helical geometry | Vector/period-one closure; seam period-one; canonical band-time coordinates; exact quotient witness; period lower bound from strip width/divisibility | w/x/y/z/zb/zg; zi excluded comparisons |
| Wang row semantics | Shared edge representation; single bridge pulse; action encoding/halt reflection; canonical operating row; actual receiver causality; local determinism; shared halted-color witness | u/v/w/z/za; zi B2 |
| Finalizers | Witness-preserving rational-to-integer descent; product-unit decomposition; signed root recovery; algebraic RefinedPair identity before evaluation; margin interval | i/m/w; zb D |
| Controller local clients | Finite order rigidity; canonical bounded modular representatives; ZMod castHom/value normalization; coprime representative; Hs wrapper removal; prime-factor exact-order criterion | zd/zh/zj |
| Current words | Marker-only terminal product band; tail cutoff by contrapositive; bounded-color complement cancellation; source positivity from one selected positive digit | zd/zh/zj |
| Methodology | Simp policy, import cuts, profiling, trust audits, statement/data preservation, exact source accounting | already recurring throughout a-zj; not new proposals |

## All five current incoming archives

These are additional exclusions beyond the older broad ledgers. Text members and archive hashes are in `incoming_manifest.json`.

### `Lean_Proof_Simplification_Power_And_Masks_2026-10-26.zip`

Root member directory: `Lean_Proof_Simplification_Power_And_Masks/`.

- `report/03-power.tex`: fuse `PrimePowerOrder.pow_cast_eq_one_iff` into one guarded rewrite; preserve `1 <= g` for natural subtraction. Inline CRT order transport; derive auxiliary/C0 generator identities from exact order at exponent zero; delete one-use `order_transport` by rewriting `modulus_factorization`.
- `report/04-units.tex`: optional `Gamma_pos` from existing coprimality with 47, explicitly acknowledging the stronger calibration dependency.
- `report/05-masks.tex`: `CurrentWordPadding2011.bit3_clear_of_residue` through direct `testBit_mod_two_pow` simplification. Its methodology and modulo16 transport are already available.
- The report explicitly excludes predecessor-power cancellation, normalized-padding carry/reset reuse, and generic scalar witness packages.

### `ProveIt_Lean_Simplification_Round5_2026-10-26.zip`

Root: `LeanReview5/`; main report `report/proof_simplification_report.tex`.

- Lines 58-90: Sidon weight injectivity via a diagonal repeated pair instead of zero; ordered pair injectivity by discharging the swapped branch with endpoint inequalities. Earlier polarization is assumed applied.
- Lines 92-108: generator order-one endpoints at exponent zero, overlapping Power_And_Masks.
- Lines 110-120: `IterationSize.iterate_depth` by `rfl` instead of `congrArg` applied to a definitional equality.

### `diophantine-lean-new-obligations-2026-10-26.zip`

Root repeats archive stem; main report `report/report.tex`.

- A (89-121): export the five private Jones finalizer evaluation lemmas and remove the identical second implementation in ExecutableJones.
- B (123-217): one affine integer positivity lemma reused via `(m,G,y) -> (-m,-G,2-y)` for Thirteen carrier soundness/completeness.
- C (219-304): `List.Nat.antidiagonalTuple` directly enumerates homogeneous degree-four exponent vectors instead of filtering the Fin5 Cartesian product; acknowledges expression-tree/API compatibility changes.
- D (306-381): fixed-controller identities require fixed-power equations, not least orders; propagate `x^p=x` to `x^(p^n)=x`. Retain exact auxiliary prime-power order used for coordinate bijections.
- Rejected shortcut (419-425): local bound-code observations do not imply least generated formula validity; internal ZFAxioms lacks Foundation and no external well-founded induction is licensed.

### `lean-proof-simplifications-2026-10-26.zip`

Root repeats archive stem; main report `report/report.tex`.

- A (166-322): certify Gamma in the fixed modulus `47*2011*120199`; common B/K/radix residues, power fixed point, one gcd/Bezout certificate, then coprimality at all `d*p^n`. Preserve natural subtraction and independent zero exponents.
- B (324-438): arbitrary-exponent LTE divisibility spectrum `p^(k+1) | g^m-1 iff p^k | m` as foundational API; derive lift/order uniformly including `m=0,k=0`.
- C (440-572): finite carry recurrence from a seed; bounded prefix/reset/matches/locality; characterize actual per-cell carries/digits from incoming carry zero after top-field reset. Explicit seed-zero per-cell construction replacing global fixed-point is also proposed at 555-572, although deferred as possibly longer. This entire direction is excluded.
- D (574-608): `NativePellPower.sixteen_pow_bound` by `t=4^r` and one quadratic inequality, overlapping zc/zf.

### `proveit-lean-additional-certificates-2026-10-26.zip`

Root repeats archive stem; main report `report.tex`.

- A (111-179): evaluate the 941-row literal kernel once in a common residue ring; 177 separate chunk certificates become 59 plus projections. The actual kernel bridge remains required.
- B (181-230): power-map fixed point for all three controller residues; overlaps new-obligations D.
- C (232-274): `Function.update`/finite weighted sum APIs for one dummy mutation and Boolean update; explicitly retains normalized transport nonwrapping hypotheses.
- D (276-300): specialize reflected-source theorem at offset zero, eliminating previous-cell address reconstruction.
- Joint synthesis (302-327): common-modulus Gamma certificate.
- Future direction (395): multiple distinct-coordinate updates/batch API is explicitly advertised; a generic batching proposal is not new.

## Decisions for this iteration

| Candidate | Decision | Reason after assuming previous APIs |
|---|---|---|
| Derive `haltingTest_natPrimrec` from `DirectEnumerator.program` and `ScalarPRCode.primrec`, removing the separate Primrec certification layer and inverting the acyclic dependency | Retain as distinct, subject to actual API/build checks | i shortens independent extensional proofs using fun_prop; e shares actual builders. Neither deletes the second certification route by consuming the already stronger supplied realizer. Mere import splitting gets no separate credit. |
| Internal `ObjectDivision.quotient_not_lt` via disjoint ordered quotient intervals, without two slack witnesses and ring identity | Exclude as new after supplemental-note check | Incoming additional-certificates `audit/exclusion_taxonomy.txt`:245-249 explicitly raises generic ordered-semiring division uniqueness, though not endorsed. Under the strict user requirement even this exploratory suggestion counts. k external uniqueness and zf successor APIs are further nearby precedents. |
| Replace concrete global fixed-point carry construction by reset-seeded per-cell scans | Reject | Incoming lean-proof-simplifications C explicitly advertises both characterization and explicit constructor. |
| One common-modulus Horner certificate for CurrentKernelResidues2011 | Reject | Incoming additional-certificates A is exactly this change. |
| Finite batch dummy updates as such | Reject as a headline | Incoming additional-certificates future question already advertises it. A distinct aggregate safety theorem would require separate proof and actual client benefit. |
| Remove CurrentDummySafety quantitative nonwrapping estimates by zero terminal carry on old/new normalized words plus exact support of the physically interior perturbation | Provisionally retain; mathematical/source validation belongs to arithmetic review | Generic telescope and per-cell reset APIs are assumed. The residual obligation is exact ordinary-word mutation and deletion of the coarse magnitude chain; prior incoming C explicitly retains that chain. Preserve Boolean controls and actual spatial/temporal interior guards. |

These decisions are based on targeted full-text searches and reading the closest mechanisms. A compile result alone cannot upgrade a duplicate proposal to a new one.

## Supplemental-note correction

The structural reviewer found the internal-division direction in an incoming plain-text supporting note, not the main report. It was consequently withdrawn as new despite a successful compiled generic proof. Subsequent candidate searches include `.txt` notes. The Primrec dependency-inversion search still found no corresponding recommendation; the two theorem names merely appear together in packet f validation endpoint lists.
