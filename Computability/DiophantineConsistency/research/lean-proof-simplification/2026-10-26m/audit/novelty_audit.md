# Prior-proposal exclusion audit

Repository snapshot: `7fa06d530df54d4aeb2e18027409df082234c69e`.

Audited seven current incoming ZIPs (1990 members) and the placed packet explicitly referenced by the incoming README. Archive and member hashes are in the JSON artifacts. Recorded compilation statements below belong to the prior packets; this audit did not rerun them.

## Packets

- **P1** `Lean_Proof_Simplification_2026-10-26.zip`: 615 members; SHA-256 `dda8929e3e159c3f165b469dbdaacd9e180e30e4a90fb62abe3ecff69a6d58ac`.
- **P2** `ProveIt_Lean_Proof_Simplification_2026-10-26.zip`: 1015 members; SHA-256 `2a0f51271b3d327a2916f66273b999f09e8c2fbebd69489102e2558e397d3f1e`.
- **P3** `diophantine-lean-simplification-2026-10-26(1).zip`: 73 members; SHA-256 `c8d7d56a0344f141dc7d2e44c63b0ee450d552205d4ae9c8d10076cd310e1118`.
- **P4** `diophantine-lean-simplification-2026-10-26.zip`: 48 members; SHA-256 `f05ee2789f3cfbca29467377aeaaef6972211406807ce45d4590459621c86470`.
- **P5** `lean-proof-simplification-2026-10-26 (2).zip`: 51 members; SHA-256 `5035e9a719f7504dfc5c035b2675bbcdf207e9b81c5cbcc28f6112d9be1cdc56`.
- **P6** `lean-proof-simplification-2026-10-26.zip`: 64 members; SHA-256 `a7d630331b4f50b653a57de9c3b8f1958762d4b2257e65da1e1de17302182c20`.
- **P7** `lean-proof-simplification-review-2026-10-26.zip`: 124 members; SHA-256 `9d9eb709f2d454c4439d2e1f822dbe1b1bcda3cb0f3eedcf5338542b1fbe1ecb`.
- **P0** is the placed `research/lean-proof-simplification-20261026` packet. `ADOPTION.md` is referenced but absent at this commit.

## Exclusion map

### E01. Core list lookup reuse

**Targets:** AnnotatedRename; AnnotatedBound; AnnotatedProofChecker; AnnotatedAssumption; AnnotatedRuleSide.

Replace seven private membership/lookup inductions with List.mem_of_getElem? and the converse core API.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 132–143 (Use the core list-lookup API); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 222–254 (Seven list inductions have direct replacements).

**Archived status:** Generic exact types compiled in multiple packets; P7 also reports complete modified AnnotatedProofChecker replay. Full combined client migration not claimed.

### E02. Recursor congruence

**Targets:** ScalarPRCode; PRCode; ScalarPROptimizer.

Rewrite base and step correctness through Nat.rec, including lambda congruence; alternative induction helper preserves a smaller axiom footprint.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 114–131 (Rewrite under primitive recursion).

**Archived status:** P0 reports all three complete modified modules compiled, 34 physical lines saved, PR data equality checks.

### E03. Assignment naturality and witness-block splitting

**Targets:** Representation; QuarticCompiler.

Factor natAssignment composition with Sum.map, left/right finite witness blocks, conjunction/disjunction and existsBlock bookkeeping.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 144–161 (Expose assignment naturality once); P3: `diophantine-lean-simplification/report.tex`, lines 136–175 (Assignment transport and witness splitting); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 371–372 (A small assignment-transport API).

**Archived status:** Several complete modified Representation modules compiled; variants save 16, 18, or 25 lines. P3 reports full constructor equality by rfl, including data.

### E04. Generic finite residual zero criterion

**Targets:** ShortSystem; DAGQuartic; NaturalDAGQuartic; QuadraticRegisterSystem.

One nonnegative sum-of-squares zero theorem, shared syntax evaluator and finite polynomial degree bound.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 162–163 (Sums of squares:); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 428–429 (Share the finite residual and degree arguments).

**Archived status:** P7 reports a checked four-module patch, net 33 lines including a 36-line support module, eight paired axiom audits, 15 overlay commands.

### E05. Sum-type existential regrouping

**Targets:** DAGQuartic; NaturalDAGQuartic.

Use Sum.exists_sum plus one cast identity to replace manual assignment construction and extensionality.

**Evidence:** P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 467–482 (Regroup witnesses with the existing sum-type theorem).

**Archived status:** Part of P7 checked finite-residual patch, with all eight paired theorem audits matching.

### E06. Generic residual cost bound

**Targets:** DAGQuartic; QuarticCost.

Promote generic sumExpressions_cost parameter b and derive current b=5 and b=11 instances.

**Evidence:** P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 650–665 (Promote the parameterized cost bound already present); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 485–505 (Generic sum cost.).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E07. Weighted syntax-degree reuse

**Targets:** QuadraticRegisterSystem; WeightedExpressionDegree.

Identify syntaxDegree with weight-one weightedDegree and reuse degree_evalRing_le; reorganize foundational imports.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 266–271 (Move existing degree machinery); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 493–505 (Weighted syntax degree.).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E08. Generated step specialization and power certificates

**Targets:** SplitCircuitSteps59; GapCircuitSteps66.

Use existing run_power and run_node_equation through exponent labels and local helpers while preserving all public names and cutpoints.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 190–191 (The largest measured source reduction); P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 483–523 (Replace 193 power chains); P2: `LeanReview/report/sections/04_circuits.tex`, lines 50–127 (Consolidate power proofs).

**Archived status:** P0 static candidate saves 1650 lines preserving 1192 signatures, not integrated. P4 checks Split imported circuit and Gap exact-data fixture, with full Gap import failing under resource limits.

### E09. Topological circuit invariant

**Targets:** ArithmeticDAGSemantics; ArithmeticDAGNonnegative; ArithmeticDAGDegree.

Share topological induction for uniqueness, nonnegativity, degree and input independence.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 240–255 (A shared induction for topological circuit semantics); P3: `diophantine-lean-simplification/report.tex`, lines 332–341 (One topological induction principle); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 707–728 (A reusable invariant for arithmetic DAG evaluation).

**Archived status:** Generic prototypes compiled in P0/P3/P7; wholesale client migration not claimed.

### E10. Commutative node correspondence and simulation

**Targets:** SplitCircuitTranslation59; GapCircuitTranslation66.

Treat swapped add/mul parents as relation cases; abstract positive/natural translation without treating it as a ring map.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 258–265 (Treat commutative swaps in the relation); P3: `diophantine-lean-simplification/report.tex`, lines 352–369 (Factor the two translation proofs); P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 713–738 (Positive/natural translation is a simulation).

**Archived status:** P3 compiles generic commutative correspondence soundness; both full translation migrations remain proposed.

### E11. Local register append invariants

**Targets:** ArithmeticDAG register construction.

Package valid length/topology and append semantic facts as local invariants.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 272–277 (Package append invariants locally).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E12. Indexed circuit facade and typed views

**Targets:** SplitCircuitSteps59; GapCircuitSteps66; ArithmeticDAG.

Consider indexed views before removing named wrappers; optional typed valid-index circuit layer.

**Evidence:** P2: `LeanReview/report/sections/04_circuits.tex`, lines 128–166 (Offer an indexed facade); P2: `LeanReview/report/sections/04_circuits.tex`, lines 211–233 (Treat typed circuit views).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E13. Semantic circuit blocks and common 99-node tail

**Targets:** SplitCircuit59; GapCircuit66; SplitCircuitRecipe59; GapCircuitRecipe66.

Factor common semantic tail, preserve shared nodes and 22-let cutpoints, verify explicit index map for identical 99-node suffix.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 234–256 (9 Share the identical polynomial tail); P1: `Lean_Proof_Simplification/report/report.tex`, lines 287–304 (11 Preserve DAG cutpoints); P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 468–504 (Extract the shared 99-node free-carrier tail).

**Archived status:** P1 extraction uncompiled. P6 records static exact suffix equality and regeneration checks; shared-block semantic theorem remains a proposal.

### E14. Register proof cutpoints

**Targets:** SplitCircuitRegisters59.

Use established register facts in shorter simp lists, with generator and output changed together.

**Evidence:** P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 427–467 (Use established register facts as proof boundaries).

**Archived status:** P6 static checks preserve generator output; two rewrite lists 19→7 and 36→9, 844 output bytes saved; module replay not completed.

### E15. Scanner iteration laws and encoding fusion

**Targets:** AnnotatedBoundScan; AnnotatedRenameScan; AnnotatedLineScan; AnnotatedContext; AnnotatedAxiomContext; AnnotatedClosure.

Bridge unchanged Nat.rec to iteration, prove fixed-state/right-step laws and semiconjugate iteration once.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 186–213 (7 Replace scanner inductions); P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 280–295 (Share iteration laws); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 508–523 (Recursive steps and terminal states).

**Archived status:** Core generic laws compiled in several packets, some with empty axiom sets; complete scanner migrations remain separate.

### E16. Validated history fold

**Targets:** AnnotatedBound; AnnotatedRename; AnnotatedProofChecker.

Generic input type, stored judgment type, validator and output map share append, soundness and Produces fragment proofs.

**Evidence:** P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 286–326 (One invariant-preserving history fold); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 524–555 (An input row and a stored judgment).

**Archived status:** P4/P7 compile generic runners and bridges; they explicitly distinguish function equality bridges from unjustified rfl.

### E17. Numeric Boolean and tag dispatch interface

**Targets:** AnnotatedBoundLocal; AnnotatedRenameLocal; AnnotatedBoundScan; AnnotatedRenameScan.

Derive exact truth value from 0/1 range plus acceptance iff; normalize threshold tags for all natural inputs, retaining truncated subtraction behavior.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 214–233 (8 Exact checker outputs); P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 296–310 (Replace acceptance equivalences by exact numeric values); P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 380–396 (Share tag dispatch and Boolean reflection).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E18. PR iterator constructor reuse

**Targets:** Annotated scanner PR realizers.

Factor the actual code-valued primitive-recursive iterator, preserving executable expressions and witness costs.

**Evidence:** P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 362–379 (A better primitive-recursive iterator interface); P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 614–623 (Factor the supplied PR iterator).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E19. Decoder Option-map proofs and optional fusion

**Targets:** AnnotatedProofCode.

Use Option.map success/injectivity to shorten two decoder proofs; optional combined induction fuses decode/depth facts but alters axiom dependencies.

**Evidence:** P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 310–311 (Shorten decoder proofs without enlarging their axiom dependencies).

**Archived status:** P7 full-file default patch 55→43 lines with matching paired axiom sets; optional fusion checked but depth acquires Classical.choice.

### E20. Parse-then-check composition and partial-decoder injectivity

**Targets:** AnnotatedProofCode; AnnotatedParents; encoded trees/judgments/contexts/formulas.

Share parse-then-check soundness extraction; derive encoding injectivity from a partial decoder left inverse; use Option.map_injective.

**Evidence:** P3: `diophantine-lean-simplification/report.tex`, lines 445–454 (Reuse parser and list infrastructure); P1: `Lean_Proof_Simplification/report/report.tex`, lines 172–185 (The supplied \code{standard_library_cleanup.patch}).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E21. Half-radix arithmetic instead of sixteen cases

**Targets:** NativeCyclicRotation.

Prove exact scaled quotient/remainder half-radix identity and derive parity/bounds without finite digit enumeration.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 319–329 (A half-radix shift); P3: `diophantine-lean-simplification/report.tex`, lines 176–198 (Replace half-radix case enumeration); P5: `lean-proof-simplification-2026-10-26/report.tex`, lines 312–348 (An exact identity removes finite digit enumeration).

**Archived status:** Core theorem and original-signature imported adapters compiled in P3/P5.

### E22. Weak residues from divisibility

**Targets:** CurrentEarlyPadding2011; CurrentClause2011.

Derive modulus-16 residue from existing modulus-2048 theorem via Nat.ModEq.of_dvd.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 313–318 (Derive weaker moduli); P3: `diophantine-lean-simplification/report.tex`, lines 229–239 (Use a stronger congruence).

**Archived status:** P3 ReflectedResidueRefactor compiled against actual source theorem.

### E23. Cyclic-field residue and support interface

**Targets:** CurrentClause2011; CurrentMarker2011; CurrentReflectedGeometry2011.

Share add/sub residue and support exclusion lemmas at full cyclic modulus N*L, retaining whole-cell position.

**Evidence:** P3: `diophantine-lean-simplification/report.tex`, lines 398–413 (Extract cyclic-field arithmetic); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 605–618 (Share residue transport at the correct modulus).

**Archived status:** P3 generic cyclic facts and four actual low-support exclusions compiled.

### E24. Exact carry decomposition and derived recurrence

**Targets:** NativeCyclicCarry; NativeWindowCarry; CurrentPolynomialWindow2011.

Recover quotient/remainder, transition recurrence, zero carry from small total, and residue consequences from one normalized local equation.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 343–354 (Use one exact decomposition interface); P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 644–677 (Derive recurrence instead of storing it twice); P1: `Lean_Proof_Simplification/report/report.tex`, lines 320–332 (Add equation-side carry lemmas).

**Archived status:** P3/P4 checked generic arithmetic prototypes; full structure migration remains proposed.

### E25. Conditional padding witness

**Targets:** CurrentEarlyPadding2011.

Require witness only in the phase that uses it; remove unused dummy witness branch by changing producer/caller API together.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 330–342 (Make the padding witness conditional).

**Archived status:** P0 explicit API-changing patch; not checked full integration.

### E26. Coefficient envelope schema

**Targets:** NativeCoefficientBounds.

Reuse generic envelope lemma for all rows; compact branch tactics; stronger finite majorant vector certificates.

**Evidence:** P2: `LeanReview/report/sections/02_local.tex`, lines 10–54 (Specialize the generic coefficient bound); P5: `lean-proof-simplification-2026-10-26/report.tex`, lines 222–223 (Coefficient envelopes:); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 199–219 (A certificate design that could remove repeated arithmetic search).

**Archived status:** P5 and P7 complete compact modules compiled. P7 reports 679→122 lines but slower elaboration and local 4,000,000 heartbeat budget; not a speedup.

### E27. Coefficient naturality

**Targets:** NativeNinePolynomial52.

Group coefficient-map cases, reuse map_* lemmas; possible common coefficient syntax/reification avoids duplicated expressions.

**Evidence:** P2: `LeanReview/report/sections/03_architecture.tex`, lines 214–253 (Remove duplicated coefficient expressions); P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 384–406 (Do the same for coefficient naturality).

**Archived status:** P6 candidates remove 303 lines but isolated proof check timed out; not verified.

### E28. Finite-fiber pushforward for folded stencils

**Targets:** NativeSparseDigits; folded sparse stencils.

Prove weighted finite-fiber summation for arbitrary collisionful placement, then specialize injective sparse placements.

**Evidence:** P3: `diophantine-lean-simplification/report.tex`, lines 427–434 (Separate arbitrary folding); P5: `lean-proof-simplification-2026-10-26/report.tex`, lines 415–445 (One finite-fiber identity).

**Archived status:** P5 FinitePushforward helper compiled; generic rather than completed all-client migration.

### E29. Origin correction and mask blocks

**Targets:** CurrentHighDigits2011; NativeSparseDigits.

One guarded subtraction/addition-at-origin lemma and optional reusable block lookup/length/bound facts; distinguish low +1, high -1 and scalar beta shift.

**Evidence:** P3: `diophantine-lean-simplification/report.tex`, lines 414–426 (One origin-correction lemma); P1: `Lean_Proof_Simplification/report/report.tex`, lines 350–355 (Optional mask-block reuse.).

**Archived status:** P3 WordOriginRefactor imports actual packed-word definitions and compiles; all mask consumers not migrated.

### E30. Finite chunk certificate assembly

**Targets:** WangTiles942Data; kernel-checked finite tables.

Retain bounded kernel-check chunks and prove adjacent-block coverage/dispatch once; include final partial block; optionally balanced assembly.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 333–355 (13 Finite dispatch); P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 678–711 (Keep checked finite chunks).

**Archived status:** P4 NativeRefactorCore finite dispatch helper compiled; complete generated-table migration not claimed.

### E31. Direction-indexed packed layout

**Targets:** CurrentKernel2011; CurrentCellLabels2011.

Describe four west/north/east/south blocks once and reindex 34 controls, preserving tile order and summed collisions.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 338–355 (Describe the packed direction layout once.).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E32. Word, Fin, ZMod and padded-list bridge

**Targets:** NativeCyclicConvolution; NativeRadixDigits.

Compose word/ofDigits/List.ofFn and Fin/ZMod equivalence transport once while retaining NeZero and digit bounds.

**Evidence:** P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 619–634 (One boundary between).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E33. Small staged native context

**Targets:** CurrentPolynomialWindow2011; CurrentOneHot2011; CurrentCellLabels2011; CurrentDecodedWindow2011.

Project WordFacts from actual Facts, derive additional phase/count/decode stages explicitly; avoid assuming global alignment or occupancy.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 305–332 (12 Native proofs need smaller contexts); P5: `lean-proof-simplification-2026-10-26/report.tex`, lines 579–598 (Bundle carry witnesses with named fields).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E34. Aligned cell and geometric facts

**Targets:** CurrentCellTranslation2011; CurrentEarlyPadding2011; CurrentReflectedGeometry2011.

Reuse existing aligned Cell type; centralize index bounds, residues and wrap cases in proved local facts.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 331–332 (Reuse the existing aligned-cell type.); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 635–647 (Package repeated geometric facts).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E35. Current coherent source/window certificate

**Targets:** CurrentSparseDigits2011; CurrentHighDigits2011; CurrentPolynomialWindow2011.

Extract common polynomial-zero→parent→source→normalized window bridge and preserve a single coherent source witness.

**Evidence:** P2: `LeanReview/report/sections/03_architecture.tex`, lines 99–146 (Share one coherent source and scalar window certificate); P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 869–912 (Improve the current-window API).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E36. Base-layer dependency reorganization

**Targets:** CurrentCarrierArithmetic2011; ThirteenCarrierComplete.

Move current arithmetic interface below completeness and retain facades instead of importing later completeness merely for low-level facts.

**Evidence:** P2: `LeanReview/report/sections/03_architecture.tex`, lines 147–171 (Put the current base interface below completeness).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E37. Nine-coordinate packing

**Targets:** SplitSourceExistence; GapSourceExistence66.

Parameterize identical positive/natural tuple existence proof by scalar evaluator, preserving slot 7 and positivity.

**Evidence:** P2: `LeanReview/report/sections/03_architecture.tex`, lines 11–67 (Prove the nine coordinate packaging equivalence once).

**Archived status:** P2 generic and compatibility prototypes are explicitly uncompiled.

### E38. Named long-conjunction projections

**Targets:** SplitSource59; GapSource66; semantic row packages.

Add named accessors or small proposition records without changing literal row data or assuming consequences.

**Evidence:** P2: `LeanReview/report/sections/03_architecture.tex`, lines 68–98 (Give long conjunctions names).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E39. Parameterized Split/Gap degree profiles

**Targets:** SplitWordBounds; GapWordBounds66; ShortSystemDegree.

Generalize lower-layer domination and upper bounds through exact degree profile inequalities and leading coefficients; factor common ShortSystem prefix.

**Evidence:** P2: `LeanReview/report/sections/03_architecture.tex`, lines 172–213 (Abstract the degree profile); P2: `LeanReview/report/sections/04_circuits.tex`, lines 188–210 (Share the ShortSystem degree prefix).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E40. Source-register arithmetic facts and cast boundaries

**Targets:** NativePellBootstrap; NativePellPower; NativePellFirstIndex.

Decode q=1+Jβ,L=q²−1,N=q³,X=qw once; normalize rank toNat/cast identities from positive source rows.

**Evidence:** P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 617–641 (Decode source-register equations once).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E41. Guarded solvability transport

**Targets:** CurrentCarrierArithmetic2011; carrier witness maps.

Package two domain-preserving existence directions and congruence/transitivity, without requiring inverse witness bijections.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 257–286 (10 Guarded solution transport); P3: `diophantine-lean-simplification/report.tex`, lines 240–255 (Lift pointwise zero-set equivalence once).

**Archived status:** P3 PositiveZeroRefactor compiles generic congruence and both current 69↔70↔71 polynomial comparisons; P1 broader core transport uncompiled.

### E42. Elementary residual row operations

**Targets:** residual systems and polynomial shears.

One reusable row-add/negate/swap zero-set argument, e.g. r²+(s+t*r)²=0 iff r=s=0.

**Evidence:** P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 774–808 (Represent elementary row operations once).

**Archived status:** P6 RowOperations checked; concrete full-system migration remains future work.

### E43. Definable object induction transport

**Targets:** ObjectAdditionLaws; ObjectMultiplicationLaws; ObjectCodeBound.

Wrap omega induction using actual formula, environment and satisfaction equivalence; retain all internal model naturals.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 357–364 (A definable-induction transport lemma); P3: `diophantine-lean-simplification/report.tex`, lines 463–477 (Wrap internal induction while retaining definability).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E44. Object completeness and sealing bridge

**Targets:** ObjectNaturalExpression; Object* endpoints.

Share arbitrary-model validity→complete derivation→sealed statement administration, preserving definability and model quantifiers.

**Evidence:** P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 365–372 (One bridge from model validity); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 558–581 (A completeness-and-sealing helper).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E45. Object ZFC-to-ZF axiom extraction

**Targets:** ObjectArithmetic; ObjectMultiplication; CodedRank.

Reuse zfAxioms_of_zfcModel through low-layer helper rather than importing a heavy later development.

**Evidence:** P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 582–592 (Reuse the ZFC-model-to-ZF-axioms bridge).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E46. Object finite quantifier and arity normalization

**Targets:** ObjectQuadraticSystem; ObjectDivModSyntax; ObjectPredecessorSyntax; ObjectNaturalExpression; closed sentence transport.

Use Fin.forall_fin_add/two, List.forall_mem_ofFn_iff, and arity-polymorphic closed sentence transport.

**Evidence:** P3: `diophantine-lean-simplification/report.tex`, lines 455–462 (Normalize finite-index reasoning); P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 768–781 (Generalize closed-sentence transport across arity); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 593–602 (A smaller quantified-list example).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E47. DivMod certificate sharing

**Targets:** QuadraticDivMod; RegisterDivMod.

Move identical certificate_iff arithmetic into neutral layer, retaining distinct realizers and 1 versus 23 witness counts.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 174–185 (Share the quotient/remainder certificate, not its realizers.).

**Archived status:** P1 extraction prototype uncompiled.

### E48. Simple positivity and canonicality bodies

**Targets:** Carrier66.

fin_cases followed by goal-directed exact hv _ for drop_pos/restore_pos; narrow simp for canonical_zero.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 77–105 (3 Small local proofs with less repetition).

**Archived status:** P1 source-only candidates, not compiled.

### E49. Integer-unit and common constructor branch reuse

**Targets:** ShortSystem; QuarticCompiler; ArithmeticDAG; FirstPellCarrier.

Reuse integer unit classification, merge add/mul Gates.complete branches, simplify run_map, cast whole Pell conclusion.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 106–130 (4 Algebraic facts); P1: `Lean_Proof_Simplification/report/report.tex`, lines 131–161 (5 Structural induction).

**Archived status:** P1 nine algebra body candidates 123→56 nonblank lines; all uncompiled.

### E50. Finite set intersection and at-most-one sums

**Targets:** finite support sets; NativeOneHot.

Use finset intersection membership and Finset.sum_le_one_iff instead of repeated membership/one-hot reasoning.

**Evidence:** P2: `LeanReview/report/sections/02_local.tex`, lines 105–144 (Use finite set intersection); P3: `diophantine-lean-simplification/report.tex`, lines 199–208 (Use the existing sum-at-most-one API); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 255–270 (A finite sum at most one).

**Archived status:** P3 OneHotCore and P7 small arithmetic examples compiled; P2 intersection proposal uncompiled.

### E51. Predecessor exponent and power facts

**Targets:** geometric bounds; NativeRadixDigits; NativeCoefficientBounds.

Factor predecessor exponent arithmetic; use Nat.one_lt_two_pow; keep huge scale powers symbolic with pow_add and monotonicity.

**Evidence:** P2: `LeanReview/report/sections/02_local.tex`, lines 145–175 (Remove the repeated predecessor exponent); P2: `LeanReview/report/sections/02_local.tex`, lines 223–245 (Use the exact power fact.); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 301–309 (Keep huge powers symbolic).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E52. Natural remainder and cast simplification

**Targets:** CurrentCellTranslation2011; NativePellStepDown.eq_of_residues.

Use Nat.sub_add_cancel(mod_le) and divisibility remainder identities; let omega handle existing linear Nat/Int cast interface.

**Evidence:** P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 271–288 (Natural subtraction and remainder); P7: `lean-proof-simplification-review/lean-proof-simplification-review.tex`, lines 289–300 (Let \texttt{omega} handle the cast interface).

**Archived status:** P7 core arithmetic examples compiled; full Pell step-down original/replacement compiled, 248→241 lines, paired audits match.

### E53. Convolution and finite-switch local simplifications

**Targets:** NativeCyclicConvolution; ArithmeticFiniteSwitch; CurrentHighDigits2011.

Factor final distributivity via sum_mul/mul_sum/pow_add; eliminate redundant threshold split; optional two-line digit bound.

**Evidence:** P2: `LeanReview/report/sections/02_local.tex`, lines 210–245 (Smaller opportunities and a reason).

**Archived status:** P2 explicitly uncompiled; report advises retaining existing high-digit proof unless measured improvement.

### E54. Direct/native graph builder parameterization

**Targets:** DirectGraphEnumerator; NativeGraphEnumerator.

Factor common rawStepProgram/boundedRunProgram control flow over graph combinators, preserving separate 1742/6924 witness costs.

**Evidence:** P1: `Lean_Proof_Simplification/report/report.tex`, lines 356–377 (14 Share control flow without collapsing cost models).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E55. Sparse low-degree reflection certificates

**Targets:** residual rows; ArithmeticDAG translations.

Use a narrow sparse-row normalizer or low-degree certificate before attempting whole-DAG reflection.

**Evidence:** P3: `diophantine-lean-simplification/report.tex`, lines 382–389 (Use low-degree row certificates); P6: `lean-proof-simplification-2026-10-26/report.tex`, lines 754–762 (A small sparse-row normalizer).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E56. Semantic compiler specialization

**Targets:** QuarticCompilerSemiring; QuarticCompiler; NaturalDAGQuartic.

Specialize existing generic semiring gate completeness/soundness instead of maintaining a natural-only induction; share RHS degree lemmas without conflating signed and natural wires.

**Evidence:** P4: `diophantine-lean-simplification-2026-10-26/report.tex`, lines 443–468 (The semiring theorem already subsumes); P1: `Lean_Proof_Simplification/report/report.tex`, lines 299–304 (Degree accounting is a smaller companion change.).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

### E57. Audit/import/certificate engineering

**Targets:** check modules; generated code pipeline; audit scripts.

Consolidate pure audit wrappers, retain regression theorems, enforce expected axiom policy, narrow imports, profile actual bottlenecks and compare total maintained source including helpers.

**Evidence:** P2: `LeanReview/report/sections/05_validation.tex`, lines 39–71 (Turn the existing audit output); P2: `LeanReview/report/sections/05_validation.tex`, lines 72–107 (Consolidate pure audit wrappers); P0: `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex`, lines 373–374 (Automation and performance:).

**Archived status:** Proposal in prior packet; no new replay performed in this audit.

## Candidate distinctions checked

### Pell fundamental-unit minimality via least-y/nonsquare

No matching proposal located in the seven reports, accompanying proposal notes/candidates, or placed report. Nearby source-row extraction and Pell casts are excluded above.

### Inverse pairing graph transport and finite witness normalization

No matching proposal located outside original snapshots. Nearby prior work includes generic finite witness-block split, nine-coordinate packaging, Sum.exists_sum regrouping, and partial-decoder injectivity. Any new result should state this distinction explicitly.

## Scope limits

This audit supports novelty relative to the inspected proposal corpus. It does not establish mathematical novelty in the literature, certify every prior Lean candidate, or prove that no semantically similar idea could be inferred from an unrelated passage. Reports and accompanying notes/code were compared by mechanism and target, rather than filenames alone. Original bundled source snapshots were excluded from proposal keyword results; their contents do not turn every existing theorem into a prior simplification proposal.

## Additional candidate checks during implementation

### Signed rational-root descent and finalizer deduplication

No matching proposal located. Earlier NearSquareFinalizer.norm mentions only common scalar-tail extraction; earlier residual-square proposals are separate.

### Odd Pell-index theorem reuse and signed modular composition

No matching proposal located. Earlier SignedPellResidue mentions are dependency metrics; prior NativePellStepDown patch changes eq_of_residues casts only.

### Zero-head positive-tail injection for physical positions

No exact proposal located. Earlier packets praise existing structural inverse/rank arguments and reject sorting caches, but do not give this Fin.cons refactor.

### Quadratic Boolean graph specifications

No matching proposal located. Scanner numeric Boolean interface and witness-block layout are nearby prior work, not the same graph-certificate consumption.

