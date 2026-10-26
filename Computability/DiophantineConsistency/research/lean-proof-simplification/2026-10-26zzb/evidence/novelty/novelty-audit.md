# Novelty audit: residual Lean-proof simplification ideas

**CLOSING UPDATE:** Read `freshness-addendum.md` first. At closing pin `3b51c69d42ff99bc420698532af3fe1d1f9bd356`, four additional incoming packets were reviewed. The original supplied-code PR proposal below is now WITHDRAWN as an exact duplicate. The final retained directions are the whole-list accumulator evaluator and the smaller direct signed-rank residue; a checked nine-line tag-only Option-decision deletion is retained strictly after the prior incoming migration. The original sections below preserve the initial audit history, and the addendum overrides their statuses.

## Scope and decision rule

Initial source pin: `7ba7d102822df1eff376cbca913727d9d588ab4e`. Closing source and exclusion pin: `3b51c69d42ff99bc420698532af3fe1d1f9bd356`.

The research directory contains 43 placed packets, `2026-10-26a` through `2026-10-26zq`. The audit indexed 117 principal TeX inputs (including component files, not 117 independent reports), read the packet delivery READMEs, the research README and adoption record, and examined the proposed mechanisms and candidate-nearest sections. The entire current `docs/incoming/README.md` was read. All three incoming ZIP payloads present at the initial pin were extracted as data: 998 archive member entries in total. Candidate-directed searches also covered supplementary notes, Lean candidates, patches and audit ledgers, with source snapshots distinguished from proposal text. The accompanying text manifest inventories 2,209 research text files, 956 extracted incoming text files and the current intake README; this is an inventory, not a claim that every copied production source and build log was read word for word.

The user asks us to assume every preceding proposal has already been applied. Accordingly, optional ideas, uncompiled candidates, architectural suggestions, and an old mechanism proposed for a different client all count as exclusions. Adoption status does not make an old proposal new. A corollary or additional client of an assumed interface is not a new headline. This is novelty relative to this repository corpus, not a claim of originality in mathematics or Lean libraries.

## Initially incoming packets that must be excluded

The four additional closing archives and the final seven-archive inventory are documented in `freshness-addendum.md`; those exclusions are equally binding.

| Current incoming archive | Mechanisms covered |
|---|---|
| `ProveIt_Lean_Simplification_Round6_2026-10-26.zip` | Inline the existing four-block packing cast certificate in `CurrentPackingRank2011.fourBlocks_cast`; the packet itself excludes normalized rank growth because that mechanism is already earlier. |
| `diophantine-lean-proof-deltas-2026-10-26.zip` | Normalize raw binary-rotation shifts modulo the full bit window for arbitrary natural digits; derive nonwrapping from two strict summand bounds, including radix two; cancel a common quotient term and retain one division gap; prove zero-test soundness from product and reconstruction rows; expose a fixed affine controller coefficient to linear arithmetic and injection. |
| `lean-residual-guards-2026-10-26.zip` | Infer positive beta/ports and an early size bound from the first literal source rows and an existing positivity guard; arbitrary-digit rotation phase/quotient normalization; prove internal division uniqueness by interval separation rather than repeated gap witnesses. |

Archive SHA-256 values and member counts are recorded in `incoming/inventory.json`.

## Established mechanism families

References below use the suffixes of the 43 packet directories. The family descriptions include optional extensions and supporting notes; the list is a practical exclusion map, not a claim each row is disjoint.

| Family | Already assumed available | Principal anchors |
|---|---|---|
| Primitive-recursion congruence | Pointwise equations transported through `Nat.rec`, preserving supplied programs and literal constructors. | a, b, c |
| List and numeric Boolean interfaces | Core lookup theorems, exact 0/1 values, constructor/tag views, parse-then-check, decoder left inverses. | a–h, n, t, y |
| Scanner semantics | Fixed/reject/done states, encoded iteration simulation, generic history folds, absorbing failures, parameterized dynamic seeds. | b–h |
| Program construction | Common parameterized direct/native graph builder with separate costs; rule-schedule syntax with numeric and actual PR backends. | e §14; r |
| Extensional PR proofs | Scoped `fun_prop` composition and arithmetic/formula adapters for the already fixed functions. | i §7 |
| Witness layouts | Assignment naturality, projection laws near constructors, finite block split/append APIs, definitionally equal data. | a–f |
| Circuit semantics and bounds | One topological invariant for uniqueness, nonnegativity and degree; shared degree/cost folds, scope views, append invariants and commutative node relations. | a–h |
| Circuit certificates | Reuse power labels, specialize local node evaluation, shard literal certificates, share exact free-carrier recipe tails. | a–f |
| Polynomial/row algebra | Direct Sidon moment-polarization identity; sum-of-squares interfaces; sparse coefficient catalogs; sign/row schemas; factor-degree coefficient vanishing; symbolic quadratic certificates and coefficient fibers. | a–i, t, y supplement |
| Native words | Fin/list/ZMod lookup/evaluation bridges, generic word contexts, finite-fiber pushforward, support shifts, origin corrections, strict bounds and carry interfaces. | d–j, n–o |
| Word algebra | Point-mass convolution rotation, private monoid-algebra interpretation and packing homomorphism optional extension, exact quotient/remainder and half-radix decomposition. | i; j supporting algebra review; a–h |
| Carries | Finite-max uniqueness; exact cyclic least/greatest carries and all-zero/all-maximum ambiguity; first failure and reset-separated raw-prefix characterization. | i, j, u, zo |
| Support separation | Difference-set obstruction through an additive quotient; common translations cancel before natural remainder arithmetic. | p §D |
| Internal semantics | Definable induction transport, constructor views, exact relational/function formula semantics, support-local frames, environment restriction, rename-chain normalization. | c, g, j, s, zg |
| Internal arithmetic | Positive multiplication from additive gaps; remove unused induction; successor discreteness; total-order consequences; natural polynomial identity transport by coefficient cross-sums; division gap/interval simplifications. | l, x, y, zf, zg; two incoming archives |
| Model interfaces | One completeness/sealing bridge, extraction bundles, compositional formula satisfaction specifications. | a–h, s |
| Syntax certificates | Quote/depth fused decoder; variadic proof fragments; successor fork transport; max-plus graph-depth certificates; affine witness/depth composition. | i, j, k, n, p |
| Pairing | Product equivalence inverse, deterministic certificate witnesses, threshold branch view, shared Euclidean certificate. | k, m, p, y |
| Pell arithmetic | Preserve chosen rational roots, unit decomposition, composed signed congruence, coordinate monotonicity, small ordinate classification, negative norm via positive case, discriminant reuse, common error factors and scale, exact integer half-binomial quotient, fixed-index anchor and actual-sum divisibility. | i–u, z, zb |
| Finite arithmetic/order | Restricted forward-invariant injectivity gives predecessors; finite-chain rigidity; order factorization certificates; order-one API; exact cardinality congruence and cast projection. | i, zd, zh, zj, zm |
| Field/cell geometry | Aligned-cell quotient equivalence, helical band/time coordinates, exact canonical band quotient, Wang shared edge fields, receiver causality, row determinism, finite wall bounds and positive strip geometry. | early notes; v–za |
| Control updates | Last-write location view, weighted point updates, finite subset translation and affine residue coverage, one-gap subsets for every size, single selected-digit positivity. | zd, zj, zn, zp, zq |
| Exponent and residue arithmetic | Common power scalar substitution, translated thresholds, affine rank envelope, common modulus `47*2011*120199`, fixed-factor annihilating powers, all-offset reflection, prime-support coprimality, Gamma constant residue, full LTE divisibility spectrum/first lift. | zc–zq |
| Enumeration and source compression | Direct homogeneous tuple enumeration, semantically equal polynomial-expression transformations, affine reflection for the thirteen-variable carrier. | zk |

## Candidate decisions for this review

### A. Derive extensional primitive recursiveness from the existing supplied code

**WITHDRAWN at the closing pin: exact new incoming duplicate.** The candidate was distinct from the initial 43-packet/3-archive corpus, but the new `ProveIt_Proof_Simplification_Review_2026-10-26.zip` now proposes the same dependency reversal. See its main report lines 90–159 and `patches/01-certificate-dependency.patch`: split semantic definitions into `EnumeratorSemantics`, build the actual program above them, derive `haltingTest_natPrimrec` from `Realizes`, and remove 32 private PR proofs. This work must not be presented as a new recommendation even if our checks are stronger. The historical receipt `pr_reversal_screen.json` records only the initial cutoff and is superseded for this decision.

### B. Verified accumulator evaluation after the common-modulus refactor

**Retain, with the narrow closing novelty and accounting qualification below.** After assuming zn's common modulus already available, replace the remaining power-and-length recursive evaluator by an accumulator with a proved invariant such as `run xs z = z * r^xs.length + evaluate r xs`. Use the exact unchanged literal list and common modulus to certify the whole list once instead of keeping 59 numeric chunk facts and their length/append assembly.

The exact nearest exclusion is `2026-10-26zn`: it already replaces three copies of the 59-block proof by one common-modulus proof. Its copied candidate and arithmetic README call those blocks "Horner", but the existing recursive definition still uses tail length and powers. Corpus searches found no proposal for the accumulator evaluator or eliminating the final chunk certificate assembly. Generic history/scanner fusion addresses different data and proof obligations. Count any improvement against zn's one-modulus baseline, and include the accumulator correctness theorem and literal-data connection. Whole-list kernel checking must be demonstrated before claiming it is practical. At the closing pin the 426-line maintained module is byte-identical to zn's candidate. New Shape/Windows/Growth supporting notes explicitly discuss/reject affine-monoid chunk assembly; that assembly mechanism is now also assumed available. The retained novelty is the executable whole-list accumulator and elimination of the remaining 59 numeric chunk certificates. Do not claim chunk-monoid packaging or an exact all-prior-adjusted 243-line saving. See the closing addendum for exact references.

### C. Common modulus for the three fixed kernel residues

**Exclude.** Exact prior proposal zn, including `patches/01-common-modulus.patch` and its checked certificate. This is not new even though the current production file still has three modular copies.

### D. Shared representation algebra for scalar/direct/native enumerators

**Exclude.** `2026-10-26e/report/report.tex` §14, lines 359–363, proposes a common builder parameterized by composition, branching, pairing/unpairing and state/formula constructors with separate native/direct realizers and costs. A scalar backend is an additional instance of that mechanism. Packet r's numeric/PR rule-schedule interpretation is also adjacent.

### E. One unsaturated digit for a strict Mersenne-word bound

**Exclude.** The exact one-strict-digit proof already appears in maintained `CurrentCarryConstruction2011.lean`, theorem `Facts.word_lt` (lines 74–86 at the pin). Packet j covers exact zero/all-maximum ambiguity; packet i covers fixed-word uniqueness. Complement identities, radix-parameter generalization and iff corollaries are routine continuations rather than a new headline.

### F. Positivity of source masks from one nonzero digit

**Exclude as a headline.** The current maintained `word_pos_of_digit` theorem supplies the mechanism, and zj explicitly proposes source positivity from a selected digit. Using it in `CurrentMasks2011.highPort_pos/lowPort_pos` is a useful client cleanup with a lighter dependency on population calculations, but not a distinct idea under this user's criterion.

### G. Split/Gap cross-exclusion through an integer difference set

**Exclude the generic mechanism.** `2026-10-26p/report.tex` lines 283–324 defines `S-S`, excludes the projected shift, cancels common translations in an additive group, and explicitly seeks additional support-separation clients to amortize its helper. Applying it to SplitGeometry59/GapGeometry66 is an additional client. A concrete faster sorted finite-certificate algorithm could be separately assessed only if it adds more than this already assumed interface.

### H. Option-Kleisli iteration fusion / absorbing failure

**Exclude absent a clearly different mathematical obligation.** Encoded semiconjugacy, generic iteration laws, fixed/reject states and absorbing-failure arguments are already proposed throughout b–h. Merely phrasing them as Kleisli fusion does not supply novelty.

### I. Joint value/degree/cost abstract interpretation

**Exclude.** Generic topological invariants and shared degree/cost folds are already explicitly proposed in a–h.

### J. Grothendieck-ring embedding for internal natural-number arithmetic

**Not cleared.** zg's natural polynomial identity transport explicitly avoids embedding the carrier into a ring, so an actual embedding is not literally that same construction. However, it must eliminate an obligation not already discharged by the assumed cancellative-semiring identity transport or the x/zf/internal-division improvements, and it may increase infrastructure. No independent remaining simplification has yet been demonstrated.

### K. Direct Sidon moment polarization

**Exclude: exact earlier proposal.** The proposed identity `2(a-c)(a-d) = (a²+b²-c²-d²) + (a-b-c-d)(a+b-c-d)` after casting to the integers is already the supplementary proposal in `2026-10-26y/report/report.tex` lines 524–538. Its `arithmetic/patches/sidon-moment.patch` and complete checked `SidonPositions.lean` overlay implement the same `zify`/`linear_combination` route. Packet zm explicitly composes its later endpoint simplifications after that patch. This is stronger evidence than a generic cast-normalization resemblance.

### L. Direct low-mask rank residue with weaker hypotheses

**Retain as a smaller interface strengthening after the closing 50-package screen.** No exact prior window-rank residue proposal was found. Packet o's excluded reflected-parity projection concerns an equation for normalized carry digits; it is not this rank formula. However, maintained `CurrentPackingParity2011.fourBlocks_mod_four` already proves that a full low mask forces `(C-1)%4=0`. Reusing that fact at the ring-valued `windowRank` to obtain `-1` modulo `2^k` removes the need for a natural four-block equality and its range/balance hypotheses. The producing agent has checked a generic theorem with arbitrary signed F and MF and a negative-rank boundary example. A full client migration and net source reduction are not claimed. The bitmask lemma and elementary modular projection themselves are not new.

### M. Tag-only Option decision after the prior PR migration

**Retain the checked nine-line post-prior delta.** The new incoming PR proposal deliberately retains `stateEquiv` and private `Primcodable St`/`DecidableEq St` instances. The cleaned semantic module removes only these three declarations, uses the narrower `Mathlib.Logic.Encodable.Basic` import and keeps the actual test definition. The complete module is 85→76 physical lines. The cleaned module, exact incoming-baseline comparison by `rfl`, actual endpoint axiom audit and patch applicability check pass. The generic constructor-only decision needs no payload instance. This is a reduction in unnecessary state structure, not credit for the excluded PR dependency reversal or its 32-private-proof deletion. See the closing addendum and `analysis/source/tag_only/validation.json`; a whole-repository build is not claimed.

## Scope cautions for the final report

- Do not quote current-versus-proposed raw deletion counts as incremental savings if a prior assumed refactor already removes those lines.
- A distinct proof can still be a duplicate idea when it establishes the same previously proposed interface.
- Existing compilation receipts in prior packets are evidence about those packet versions, not evidence that a new composition has compiled.
- This audit supplies source-based novelty screening; it does not certify mathematical correctness or Lean elaboration of retained candidates.
