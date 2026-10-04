# Bounded review of the Parts XI–XII Polish-arithmetic publication

No integration defect was found in the checks below. The selected interfaces supply no concrete improvement to a finite paid integer compiler. This is a publication/interface review, with some bounded proof checks; it does not certify the complete manuscripts or their external dependencies.

## Immutable scope

Arrival is merge `4f03443e018a4c882d288b950928943b7d92892a`. The actual three-file Polish publication is its first parent, `dd26f917ccde006c648bf1d0a84ddf7b8daf7b90`, against publication base `5c32fda02a1ec5b40b455d3d31ac7b394d051d34`. All three published blobs equal their arrival blobs. Comparing only arrival against its first parent would instead review unrelated arithmetic changes.

Repository prefix:
`Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/`.

| File | Arrival blob | SHA256 |
|---|---|---|
| README.md | `23c390ddd63b9581a2736c8849b8700b4303f509` | `103bd64abfd63347ea2b0c221daffc46bb19854afef2430b416af57963d20ed7` |
| article.tex | `76f3a90c2d34794fc7dcec6a5b5025defdc69695` | `7ad5f687b80f6faf6ea7837da6e11da99dffc280ccbe089d1ad300b1cf69440f` |
| article.pdf | `26c4906731be04c779fdc19083b30b4b46cc4c29` | `511accf3c9c51f7ba6c736a13ebe3485ea9fe9d84f21498cf6c34b15b82f85d9` |

Companion manifest: `review_polish_publication_4f03443e0.json`, SHA256 `5cf8c76bcdbfa8ed9a87465f9f086c6af7e4209890e340c236250d00d12045d1`. It records before/after blobs, exact byte hashes of every read span, full archive/member hashes and label mappings. Line spans preserve original bytes including line endings. Applicable `Algebra/SurrealNumbers/AGENTS.md` was read fully and is pinned there.

The entire README publication diff was read: 34,340 bytes, SHA256 `1e8930ed42de6ccc9595fa9699eb9cd5520a191bd8050e71dd9070e45deb3c31`. This is not a claim to have read the entire final README.

## Integration checks

Fresh static checks found 923 unique TeX labels, up from 784. Every old label remains, in its previous relative order. All 2,500 internal-reference occurrences resolve to defined labels; all parsed citation keys resolve to the 122 bibliography keys. These are source-token checks, not a build or verification of rendered counters or external literature.

The original source archives at immutable arrival `a162e4386` were opened as inert ZIP bytes. All 14 members across `local_geometric_codes_research.zip` and `glazer_proveit_topology_research.zip` are inventoried and hashed. All 39 source-17 labels occur with prefix `pma:lgc:`, and all 62 source-18 labels occur with prefix `pma:gcm:`. Added labels comprise 13 local-code labels, 15 completion labels, two part labels and eight labels on earlier questions: exactly 139 additions. This authenticates label integration, not word-for-word preservation of all manuscript prose.

Raw section counts confirm 138 main sections before Part XI, twelve in Part XI and sixteen in Part XII: the advertised Sections 139–150 and 151–166. There are 28 appendix sections. The read appendix text explicitly supplies the AA/AB numbering transition after Z.

All six placed support files match their source archive members byte for byte: source-17 proof status, source audit, diagnostic program and JSON; source-18 proof audit and build script. Their exact mappings are in the manifest. The original delivery TeX targets are intentionally absent at the placed command paths. The merged report discloses this at article lines 30331–30336 and in the README diff; the source-18 build script still targets its original delivery filename. It is an archived reproduction artifact, not a working builder for the merged article.

`pdfinfo` reports 450 pages and 3,539,123 bytes. No PDF page was rendered or read, and no TeX/PDF equivalence or clean-build claim is made.

## Mathematical and compiler routing

**Part XI: fixed local codes, not a new paid compiler.** At lines 23538 onward and 24451–24458 the code uses a fixed remainder evaluator
`E(i) = rem(u, 1 + (i+1)v)` together with `E(0)=1` and the requirement `E(i+1)=q E(i)` for every internal `i<C`. The fixed tuple is finite, but the internally bounded interval can be externally uncountable. The recurrence is not replaced by a fixed ordinary-input existential integer polynomial.

The unique analytic-evaluation argument at 23447–23490 correctly needs totality on a Borel domain. The selected local-law and inverse-decoder proofs keep all evaluations inside the certified interval. They give Borel regularity and bounded-induction facts; they do not supply an effective arithmetic operation count. The code-domain/Borel-certificate deductions at 24449–24550 are conditional on the local obstruction and the countable-core theorem. In particular the proof of Borelness uses countability of the valid index intervals, not bounded syntax alone. I found no issue in these limited arguments, without re-auditing their main theorem dependencies.

The usual partial-exponentiation domain remains distinct: lines 25027–25079 state an open recoding question and a conditional sufficient criterion, not a completed recoder. No successor/addition/multiplication closure of the coded-length domain follows merely from the local product law.

The local ATR₀ claim at 24771–24848 remains explicitly “as claimed,” with a coding sketch and Glazer's uniform perfect-set Optimization as an unreviewed input. The publication separately keeps the global Harrington–Marker–Shelah/countable-core conclusions in ordinary ZFC. This review does not upgrade either the inherited Part VIII claim or the new local ATR₀ claim to a certified theorem. The source's 14,953 finite assertions are a reported diagnostic result, not something rerun here or evidence for the infinite/nonstandard argument.

**Part XII: a topological extension criterion.** I read the complete criterion proof, its Polish and locally compact upgrades, and the two-local-tests proof, lines 25726–25964. For a Hausdorff, commutative cancellative monoid with continuous addition and linear natural order, continuity of partial subtraction gives the topology on formal differences with neighborhoods `U−U`. The two topology comparisons explicitly use the permitted ordered pairs, and uniqueness and the Polish upgrade use `G=M∪(−M)`. The latter proof uses the two completely metrizable cone subspaces as a finite union of Gδ sets in the metric completion. No gap was found in this bounded proof read, conditional on the stated classical metrization/subspace inputs.

“Criterion,” “local tests” and “recognition” here refer to continuity in a topological structure, including arbitrary convergent sequences. They do not give a terminating finite integer decision algorithm or a fixed-arity polynomial certificate. Partial subtraction is also explicitly distinguished from total truncated subtraction.

The two merge deductions at 26271–26317 fit their stated interfaces: discontinuity on uncountable discretely ordered ring cones uses the inherited Baire-rigidity result; the locally compact carrier deduction uses the inherited cone classification. Those earlier results were not re-proved in this review. The new class-manifold results are presented only under specified coding/exhaustion/neighborhood hypotheses; the unrestricted Global Choice problem remains open. Their full proofs were not read here.

## Exact read and non-read boundary

In addition to the full README diff, the following article spans were read in full, totaling 2,013 lines. Their individual byte hashes are in the manifest:

| Article lines | Scope |
|---|---|
| 23108–23419 | Part XI integration, main interfaces and conventions |
| 23445–23497 | Unique Borel evaluation and elementary decoders |
| 23533–23681 | Code definitions, local laws and inverse evaluator |
| 24449–24552 | Code domains, certificates and coding boundaries |
| 24741–25018 | ATR₀/coded-presentation claims, formalization and complexity interfaces |
| 25027–25080 | Open ordinary-exponentiation recoding criterion |
| 25305–25461 | Diagnostic/status boundaries |
| 25463–25810; 25811–25964 | Part XII integration, exact completion criterion and upgrades |
| 26271–26344 | Two merge deductions and completion scope |
| 27213–27264 | Claimed outcomes and unresolved manifold boundary |
| 27461–27575 | Verification/scope; also the first 29 lines of the following old appendix |
| 30260–30422 | New dependency/reproduction/terminology appendices and bibliography opening |

Also read fully: `17-local-codes-PROOF_STATUS.txt` lines 1–126, `18-polish-completions-PROOF_AUDIT.txt` lines 1–155 and the inert build script lines 1–13. Their descriptions of prior reviews are source claims, not additional reviews performed here.

The whole TeX was scanned for headings, relevant keywords, labels, references and bibliography keys. Unlisted proof text was not thereby read. In particular, the Part XI infinite fusion/category proof and polynomial-cut construction, the Part XII class-sethood/manifold proof chain and most examples, external literature, earlier Parts and formal-source interfaces remain outside this review. No archived/frozen program was executed or imported, no build was run, and no repository file was changed. Only fresh metadata/static-text scripts and PDF metadata inspection were used.
