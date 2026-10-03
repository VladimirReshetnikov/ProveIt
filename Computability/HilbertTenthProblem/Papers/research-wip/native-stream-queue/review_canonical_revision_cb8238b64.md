# Independent integration review of canonical-certificate revision cb8238b64

**PASS with one minor editorial finding.** The new Part XVI correctly integrates the already reviewed cubic sandpile manuscript. I found no new mathematical or arithmetic-source defect. This is an integration review of `cb8238b64` against its parent, with a targeted audit of the immediately preceding Part XV integration `ebea5a2e8`; it is not a new review of all sixteen Parts or a proof-assistant verification. A subsequent root integration applied the editorial correction and rebuilt the PDF, as recorded below.

The reviewed file is [article.tex](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex). In the pinned revision at **line266**, its organization paragraph says “fifteen Parts”, and the adjacent table ends with XV at **line287**, omitting XVI. The maintained source now corrects the count and adds the cubic sandpile Part, manuscript16. The abstract, actual PartXVI and provenance already describe sixteen manuscripts correctly. This is a P3 navigation/editorial issue, not a theorem defect.

## Evidence and reproducibility

The companion portable checker [review_canonical_revision_cb8238b64.py](review_canonical_revision_cb8238b64.py) reads pinned Git objects, opens immutable arrival ZIPs in memory, compares mapped shipped bytes and audits retained formulas/labels. It neither executes archive code nor modifies the repository. Replay:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_canonical_revision_cb8238b64.py --root . --output /tmp/canonical-review-replay.json
cmp /tmp/canonical-review-replay.json Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_canonical_revision_cb8238b64.json
```

`cb8238b64` article SHA256 is `5520ff74da3c9eefbd0bf87b5793ff6c7d87b01083dd20575f93cfe3312581bd`; README SHA256 is `f418887966f7b75c6561276d259746c94664cd268273a91373f1d0721b8de827`. The receipt records original/member and shipped hashes for **50 byte-identical mapped files**:9 ExactWiring,12 Topology,10 NoGhost and19 Sandpile. These include every delivered Python source, coefficient export and replay receipt listed by the integration. All **35 original sandpile named equation/align displays** survive the explicitly documented macro and namespace renamings. All **68 original sandpile labels** survive. The full integrated document has no duplicate labels after excluding literal source examples, and all **537 integration references** in the new manuscript namespaces resolve.

Pinned original archives at arrival `1977e6ea6`:

| Archive | SHA256 |
|---|---|
| Exact_Wiring_Diophantine_Report.zip | `5115e76cf01577b7348cc7b987260d4ec166ba61b746dc7601625adad00fcf08` |
| Topology_Is_Not_Free_Interaction_Nets.zip | `d0d7405ec4e572f1542b8a618815f5de99498cc385ccd9cdcdbd5d8080ebd5b8` |
| no_ghost_wires.zip | `5df354ceed72357e5b61233535052e424e56a5646f8afafcdc26c981a902419a` |
| sandpile_diophantine_research.zip | `2022a5d4986621045e2d9e25ac7edb79d90d8a13c3112e24fa6ee3f4ddffb14e` |

The prior complete source/proof reviews and author executions are preserved in the maintained [incoming_substrate_review_1977e6ea6 packet](incoming_substrate_review_1977e6ea6.md) and its linked checkers, receipts, and patches. Since code and exports are unchanged, this bounded integration audit does not repeat those expensive suites or claim new replay counts.

## New mathematics and scope

I read the new PartXVI proof text and editorial links, checking support burning, local canonical ranks, the complementary-selector cubic gadget, compact zero-set maps, the collar and unique radius, the Dirichlet height bound, exact eventual periods and the uniform single-fold boundary. The integrated content preserves the reviewed hypotheses: loopless undirected finite graphs, every internal component reaching a sink, natural coordinates, and a stable periodic background outside a finite defect box. The compact maps are inverse on complete natural zeros; off-zero polynomial equality is explicitly disclaimed. The baseline13n+6m and compact10n+3m witness counts use ordered-adjacency m=2E, independently of edge multiplicity. Their structured-summand counts are not operation ledgers.

The new connection to PartXI is sound. Every displayed sandpile summand is nonnegative on the **joint real nonnegative orthant** of input and certificate coordinates; sums such as f+k are nonnegative weights as well. Each fixed polynomial has degree at most3. The classification theorem therefore applies to its full natural zeros and their projections: they are effectively semilinear. Consequently a universal fixed-arity compression preserving this nonnegative-cubic format is impossible. This does not exclude sign-changing cubics or degree4, and does not itself settle single-fold MRDP.

The spatial certificate treats the radius as a compiler parameter and changes its arity with that radius. The all-input universality application imports Cairns's effective periodic-plus-finite global-halting reduction; no implemented ordinary-input loader or fixed-arity operation saving is asserted. Finite total topplings are distinguished from local finiteness. The original primary-source check of [Cairns, Sections5–6 and Theorem3](https://arxiv.org/html/1508.00161v2) remains applicable. The single-fold equivalence uses the two-parameter universal relation and literal program specialization, avoiding an unproved unique Diophantine loader for arbitrary many-one reductions.

The new defect disclosure correctly records all three delivered-constructor defects, their tested immutable-input/direct-instance patch, and the fact that the patch is **not applied** to the preserved delivered programs. The README copying recipe restores original sibling import names in a scratch directory; it warns against running the prefixed build script in place. No additional reproducibility issue was found.

## PartXV spot checks

The revised memory comparison keeps17L−4 capped, zero-initialized memory separate from PartV's uncapped relation. The three previously derived source reductions are quoted accurately: orbit169→147 rows with126 witnesses; local matching23→15 rows and17→15 helpers; sorted memory144→134 rows with167 witnesses. Their natural-domain/sign qualifications and unchanged shipped exports are explicit. Full six-rule universality, finite fixed schedules, a selected-delta component, and an operation-counted fixed universal polynomial remain distinct. These transfer candidates are useful finite kernels, but the integration supplies no new arithmetic-operation record.

The applied narrow repair is [canonical_sixteen_parts_organization.patch](canonical_sixteen_parts_organization.patch) (SHA256 `410005b355ebd61aa2a64fead3e10458fa4cd978666b3ad46896dd2088ac6c3f`), tested by application in a private temporary tree. It changes only fifteen→sixteen and inserts the XVI table row pointing to the existing `cdc:part:sandpile` label. The report README prescribes `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` in a scratch copy; this environment has pdflatex and kpsewhich but no latexmk. The independent reviewer did not build the PDF. Root subsequently ran three pdfLaTeX passes in a private scratch directory; the final pass has no errors, LaTeX warnings, unresolved references, duplicate destinations or overfull boxes. The single pre-existing underfull line remains. The rebuilt PDF has 452 pages, and the corrected organization table was visually inspected. The source diff only changes the Part count and inserts the missing row; no mathematical text or delivered source code was changed. The historical receipt continues to audit the pinned integration commit and therefore retains its original editorial finding.
