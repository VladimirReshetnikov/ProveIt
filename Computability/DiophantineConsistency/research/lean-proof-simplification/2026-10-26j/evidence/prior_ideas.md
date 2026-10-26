# Prior-proposal audit for the 26 October 2026 Lean review

## Scope and provenance

Reviewed repository snapshot: `8e8b5dcb954969621c484588f0b902be1cfea7b3`.

The current `docs/incoming/` contains one README and two ZIP archives. Both
archives were extracted as inert data, with absolute-path, traversal, and
per-member size checks. No supplied script was executed. Their inventories
and per-member SHA-256 hashes are in `archive_inventory.json`.

| Label | Source | Members | SHA-256 of original ZIP |
| --- | --- | ---: | --- |
| A | `docs/incoming/diophantine-lean-simplification-2026-10-26.zip` | 48 | `f05ee2789f3cfbca29467377aeaaef6972211406807ce45d4590459621c86470` |
| B | `docs/incoming/lean-proof-simplification-2026-10-26.zip` | 64 | `a7d630331b4f50b653a57de9c3b8f1958762d4b2257e65da1e1de17302182c20` |
| C | `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/` | placed tree | Incoming README lines 15–19 links this retired packet, originally `diophantine-lean-proof-simplification-2026-10-26.zip`, arrival `151a732b91`. |

A and B each have one top directory whose name matches the ZIP stem. Their
`report.tex` files were read, including their substantive proposal sections.
The associated design notes, patch topics, Lean declaration families, and
proposals were inspected or searched to detect recommendations omitted from
the main articles. C's report, README, placement record, source-note files,
and the inventories of its Lean/proposal/patch directories were retrieved
at the pinned snapshot. Its complete report and three source notes are
preserved locally as `placed_report.tex` and `placed_notes/`.

The reports themselves review the older source pin
`60e9c5d620c6c387d932876cfa2d9376f64ea56c`, Lean 4.32.0, Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`. Their checks are historical
claims; this audit did not replay their compiler receipts. C's placement
record points to `ADOPTION.md`, but that file is absent from its directory
at the reviewed snapshot, so no adoption inference is made from that link.

The incoming README also indexes many older Diophantine-equation and K215
proof reports. Its relevant proof-simplification references were inspected
for routing and scope, but this audit does **not** claim a semantic reading
of every historical manuscript transitively linked from the entire intake
index. Use the wording “not found in the audited proof-simplification
packets,” not “never previously proposed.” The present exclusion set covers
the two current ZIPs and the directly linked retired DiophantineConsistency
proof-simplification packet, including its detailed source notes.

## Exclusion matrix

Locations below are internal paths and section names, or source line ranges
within the corresponding packet's `report.tex`. Different packets often
repeat the same suggestion; one sufficiently explicit occurrence is enough
to exclude it from the new report's claimed contributions.

| ID | Prior idea to exclude as a new proposal | Evidence |
| --- | --- | --- |
| E01 | Replace seven optional-lookup/membership inductions with `List.mem_of_getElem?` and `List.getElem?_of_mem`. | A, “Immediate proof-only improvement,” lines 173–217; B, lines 202–235; C, “Use the core list-lookup API.” |
| E02 | Replace congruence-through-`Nat.rec` inductions in `ScalarPRCode`, `PRCode`, and `ScalarPROptimizer` with simplifier transport or one `rec_congr`. | C, “Rewrite under primitive recursion,” lines 114–130; `source_notes/checker-review.md` §2. |
| E03 | Prove `natAssignment` naturality under `Sum.map`, move renaming outside expression evaluation, then specialize left/right witness blocks. | A, “Witness layouts,” lines 219–267; B, “Move renaming out of expression evaluation,” lines 237–276; C assignment patch. |
| E04 | Split or merge existential `Fin (m+n)` witnesses with `Fin.addCases` and projections, preserving literal expression data. | A, “The repeated argument” / “Preserve the executable data,” lines 241–267; `lean/WitnessLayout.lean`. |
| E05 | Move simple witness-count/projection laws from `RepresentationSize` next to the constructors so earlier clients need not unfold whole records. | A, “Move existing projection lemmas to their natural home,” lines 269–282. |
| E06 | Generic validated history fold, invariant, `run_append`, `Produces.append`, `Produces.step`, and certified rule-fragment composition. | A, “One invariant-preserving history fold,” lines 286–325; B, “Share typed execution and proof fragments,” lines 601–612; B `notes/syntax.txt` §3 explicitly includes `ready_binary`, `ready_unary`, `fragment2`, `fragment3`. |
| E07 | Common iterator zero/fixed-point/successor/invariant laws for numeric scanners, retaining their executable definitions. | A, lines 327–348; B, lines 541–583; C, lines 278–294. |
| E08 | Generic encoded-list simulation with rejection, completed states, `step_cons`, enough fuel, and separate all-raw-code soundness. | A, lines 350–360; B, “Share scanner proofs at the correct semantic boundary,” lines 541–599; `ScannerCore.Encoding`. |
| E09 | `iterateFrom` / `iterateProgram` accepting supplied seed/fuel/step programs and preserving `.val` and node counts. | A, lines 362–378; B, lines 614–622; B `notes/syntax.txt` §4. |
| E10 | Factor threshold tag dispatch for tags 0–7, and replace acceptance iff + Boolean range by exact numeric `truth valid` equality. | A, “Share tag dispatch and Boolean reflection,” lines 380–395; C, lines 296–309. |
| E11 | Shared finite sum-of-squares evaluation/zero criterion, degree bound, and syntax constructor across DAG and register compilers. | A, lines 397–441; B, lines 624–648; C, lines 162–188. |
| E12 | Use the ordered-ring finite-squares theorem for the five residuals of `ShortSystem`. | C, “The five-residual theorem,” lines 164–174. |
| E13 | Generalize and move the existing sum-expression operation-count bound; share `degree_add`/`degree_sub` helpers. | A, lines 419–436; B, “Promote the parameterized cost bound,” lines 650–664 and `notes/circuits.txt` §5. |
| E14 | Split compiler gate data from semantics, then obtain natural gate correctness as an instance of existing semiring theorems. | A, “The semiring theorem already subsumes the natural induction,” lines 443–458; `proposals/SemiringSpecialization.lean`. |
| E15 | Move structural degree machinery earlier, specialize weighted degree at weight one, and retain cancellation-sensitive identities. | A, lines 460–467; B, lines 763–772; C, lines 266–270. |
| E16 | Replace generated power rewrite/ring chains with existing `run_power` exponent certificates on the unchanged circuit. | A, lines 483–522; C, lines 192–209; associated power-label prototypes. |
| E17 | Factor circuit-specific `run_node_equation` specialization, emit fewer low-level wrappers, or lazily generate them. | A, lines 524–544; B, lines 739–752; C, lines 211–238. |
| E18 | Generic topological `run_invariant` for uniqueness, degree, nonnegativity, range, and related per-node properties. | B, lines 676–709; C, lines 240–254. |
| E19 | Reuse previously established semantic register cuts in the generator instead of expanding source/high/rank subcircuits again. | B, “Use established register facts as proof boundaries,” lines 427–466, exact two-theorem patch. |
| E20 | Factor the identical 99-node free-carrier tail as a reusable boundary-port arithmetic block. | B, “Extract the shared 99-node free-carrier tail,” lines 468–539; `notes/circuits.txt` §2. |
| E21 | Generalize positive/natural circuit simulation and make `NodeRel` accept commuted add/mul operands. | B, lines 711–737; C, lines 258–264. |
| E22 | Package old/new-index append invariants for `NaturalRegisterProgram` and common append evaluation lemmas. | C, “Package append invariants locally,” lines 272–276; C `source_notes/circuits-review.md` §7. |
| E23 | Finite-row dispatcher replacing 22 coefficient-envelope lemmas; shared homomorphism naturality for coefficient rows. | B, “Compress the coefficient-row proofs,” lines 330–405; candidate whole-file replacements. |
| E24 | Symbolic nonnegative-monomial majorant with finite small-integer coefficient certificates. | B, “A stronger abstraction: a finite majorant certificate,” lines 407–425; `notes/arithmetic.txt` §7. |
| E25 | Sparse quadratic row normalizer / checker, bound to the independently specified source residual. | B, “A small sparse-row normalizer,” lines 754–761. |
| E26 | Elementary row-addition and surjective reindexing API preserving simultaneous zero sets. | B, “Represent elementary row operations once,” lines 774–807; `lean/checked/RowOperations.lean`. |
| E27 | Exact half-radix formula `(s*a)%(2*s)+(s*b)/(2*s)=s*(a%2)+b/2`, with bound/parity consequences. | A, lines 548–580; B, lines 278–328; C, lines 319–328. |
| E28 | Share physical-field residue, arbitrary temporal-shift/wraparound, off-origin high-mask, and convolution support calculations. | A, lines 582–615; C `source_notes/digits-review.md` §5. |
| E29 | Identify aligned cells with `ZMod N` to simplify reindexing. | A, report lines 613–615 explicitly suggests this later equivalence. A basic `AddEquiv` proposal is too close without substantially different content. |
| E30 | Derive the modulo-16 reflected coefficient fact from the modulo-2048 fact using divisibility; retain strongest congruences. | A, lines 607–611; B, lines 903–911; C, lines 313–317. |
| E31 | Decode common Pell/source-register arithmetic identities once and share Nat/Int rank conversion facts. | A, “Decode source-register equations once,” lines 617–640; B `notes/arithmetic.txt` §6. This does not mention signed-congruence algebra. |
| E32 | Derive carry recurrence/remainder from exact decomposition plus strict digit bound; expose carry reset/modulus projections. | A, lines 644–676; C, lines 343–353 and `source_notes/digits-review.md` §3. |
| E33 | Replace redundant `Facts.carry_recurrence` storage by a derived method, and expose small proved views of existing window facts. | B, lines 869–901; C `source_notes/digits-review.md` §3. |
| E34 | Generic finite-chunk table dispatcher and checked block-sum assembly, preserving manageable checked leaves. | A, lines 678–710; B `notes/arithmetic.txt` §8; C certificate-sharding discussion. |
| E35 | Shared copied-field bounds and finite field descriptors preserving actual field order. | A, “One copied-field bound interface,” lines 712–724. |
| E36 | Make the padding witness conditional on the middle phase, removing dummy outer witnesses. | C, lines 330–341; C `source_notes/digits-review.md` §1. |
| E37 | Generic no-borrow origin-decrement word lemma `word_sub_origin`. | C `source_notes/digits-review.md` §6; this additional recommendation is not prominent in the main report. |
| E38 | Expose the direct physical selector sum identity to avoid prefix-sum round trips. | C `source_notes/digits-review.md` §7. |
| E39 | Share canonical restored source/window extraction while preserving one coherent witness across low/high masks. | C, report lines 353; C `source_notes/digits-review.md` §8. |
| E40 | Shared completeness/model-extraction/sealed-validity-to-provability bridge, plus arity-polymorphic closed-sentence transport. | A, lines 726–780; B, lines 809–849; C, lines 365–371. |
| E41 | Definable induction transport `omega_ind_of_spec`, keeping an actual formula witness and all internal naturals. | C, lines 357–363; C `source_notes/checker-review.md` §6. |
| E42 | Share model-independent finite-index/row-family facts between existing internal-natural algebra and host-natural systems. | B, lines 851–867; B `notes/syntax.txt` §6. |
| E43 | General profiling, stable simp boundaries, preserving semantic cuts, matching generator/output, small kernel certificates, and compatibility wrappers. | All three reports' automation/adoption sections. These remain good validation practices but cannot be presented as newly discovered simplifications. |

## Promising candidates not found in this audit

These are overlap judgments, not proof or implementation claims. The source
analysis agents must still establish the mathematics and concrete payoff.

1. **Fuse tree-decoder correctness into one graph theorem.** In
   `AnnotatedProofCode.Tree`, prove `decode fuel code = some t` iff
   `t.quote = code ∧ t.depth ≤ fuel`, reusing one recursive analysis for
   quoted-code recovery and depth. Neither the three manuscripts nor their
   source notes discuss `decoded_depth_le` / `quote_of_decode` fusion.
   Generic scanner simulation is different: this candidate concerns the
   recursive syntax decoder and its exact image, not iterative execution.
2. **Internal code-constructor views and inversion.** Give object-level
   encoded constructors a typed disjoint view/no-confusion interface, then
   replace repeated eight-way eliminations in `ObjectCodeBound.*_inv`.
   Earlier tag dispatch concerns raw numeric checker branching; it does
   not supply object-model constructor injectivity or disjointness.
   A related concrete strengthening is to prove
   `∀ c, IsFormCodeSem H c → ∃! b, BoundCodeRel H c b` in one internal
   code induction, then project `boundCodeRel_total` and
   `boundCodeRel_unique`. No such combined induction occurs in the
   audited manuscripts, notes, or prototypes. The actual source currently
   duplicates eight constructor branches in `boundCodeRel_total` and
   `boundCodeRel_unique` (`ObjectCodeBound.lean:324–348,367–405`).
   The candidate defining formula
   `fEx (fAnd (boundCodeForm 0 1) (fAll (fImp (boundCodeForm 0 2) (fEq 0 1))))`
   has the right de Bruijn coordinates: initially `c` is at 0; under the
   existential, the chosen bound is at 0 and `c` at 1; under the inner
   universal, a competing bound is at 0, chosen bound at 1, and `c` at 2.
   The old mentions of totality/uniqueness concern preserving the more
   general `ObjectNaturalExpression.evalRel_unique` assumptions, not
   fusing these bound-code inductions. This strengthening belongs with
   constructor views as one design direction rather than inflating the
   proposal count.
3. **Internal recursive-graph invariants/fusion.** A `ThetaG` preservation
   theorem or a definable recursive-algebra fold for internal formula codes
   can subsume repeated proofs of naturalness/closure. This goes beyond
   transporting `omega_ind` through a satisfaction equivalence, provided
   the new theorem actually abstracts recursive graph equations and has
   concrete clients. All formula/definability requirements must remain.
4. **Signed congruence modulo ±1 for Pell transport.** The older Pell
   recommendation packages source equations and casts. It does not model
   `(a ≡ b mod m) ∨ (a ≡ -b mod m)` as one transitive, negation-invariant
   relation or postpone sign decisions until half-interval injectivity.
5. **Closed-form least cyclic carries.** The prior packet explicitly says
   the existing bounded-box monotone fixed-point proof is already short;
   it does not give a rotated weighted-sum formula for least carries.
   A global algebraic characterization would be distinct, but its new
   infrastructure must earn its cost in downstream exactness/uniqueness
   clients. Unconditional uniqueness is false (e.g. constant raw digit
   `radix-1` admits carries zero and one).
6. **Compositional max-plus depth certificates.** A bound-synthesis tactic
   or small certificate language specifically for `BoundedForallDepth`
   (`factorial_depth`, `product_depth_le`, `finiteRep_depth_le`) is not in
   the audited packets. Distinguish it from prior polynomial-degree and
   witness-count projection recommendations. Its claimed benefit should
   be replacing manual `h1`…`hN` monotonicity plumbing while preserving
   exact supplied programs and sharp bounds.
7. **Support-restricted evaluator congruence and frame rules.** A theorem
   requiring assignment equality only on variables actually used by an
   expression, with overwrite/frame corollaries, is absent. Prior
   assignment naturality proves equality of entire coordinate functions;
   this candidate uses semantic locality. Establish enough actual clients
   to justify a new support interface rather than merely adding a lemma.
   **Subsequent maintained-source check:**
   `WitnessCompaction.lean:93–102` already proves exactly
   `eval_congr` for `NatExpr`, requiring agreement on `e.occurrences`.
   Therefore a claim that semantic locality is absent from the project
   would be false. An extension to signed `Expr` and proved overwrite
   frame rules could still serve new clients, but should explicitly build
   on the existing interface and should not be advertised as a major new
   abstraction merely by changing the expression type.
8. **Normalize schema renaming chains by algebra of index maps.** No
   explicit proposal for `AnnotatedSchemaMaps.rsep/rf1/rf2/ri` composition
   was found. There is a broad prior suggestion to share finite-index and
   renaming facts; the new contribution needs a precise certified
   normalization mechanism and source-level payoff to be distinct.
9. **Cyclic word packing as an algebra homomorphism.** Evaluation from
   the additive monoid algebra on `ZMod n` into `ZMod (radix^n-1)` can
   derive convolution/product and rotation/monomial laws through one
   universal property. Nothing resembling this construction appears in
   the audited manuscripts, notes, or prototypes. Prior convolution
   proposals concern support/field residues and copied-field bounds.
   Exact natural-word equalities still need range hypotheses; quotient
   algebra equalities alone establish congruence.

## Suggested report language

“I excluded the proposals in both current incoming ZIPs and in the retired
DiophantineConsistency proof-simplification packet linked by the intake
README. The archive includes a comparison matrix. The ideas below target
proof patterns not found in those audited materials. This is a scoped
nonduplication result, not a claim of novelty across all Lean literature
or every historical report linked from the intake index.”

Do not count an implementation of an old suggestion as a new idea merely
because it now compiles. That is valuable integration work, but it should
be described as validation/adoption of prior work and kept out of the new
proposal count.
