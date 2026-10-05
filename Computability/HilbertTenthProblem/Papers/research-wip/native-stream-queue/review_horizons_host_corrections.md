# Independent review of the horizons host corrections

**PASS within the changed-text scope.** The reviewed Part XVI empty-case repairs and Part XVII arithmetic-summary corrections are mathematically consistent with their printed definitions and theorem statements. The adjacent Note XVI.5.32 omission identified during this review is now repaired. No further actionable finding remains in the reviewed diff.

This is an independent proof-only review by the exotic-reports agent, requested by root on 4 October 2026. Root authored and applied the host changes. I made no repository or Git mutation and ran no supplied, archived, predecessor or frozen helper, source array, import, TeX build or PDF inspection. Only fresh read-only metadata commands were used.

## Exact text and inherited evidence

Host: `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/`. The baseline is HEAD `70af24030afae144d7c6e38038ccef39796ffc1d`. I read the complete final uncommitted textual diffs: 94 lines for the guide and 222 lines for the article, including context and Git headers.

| File | Baseline Git blob | Reviewed working-file SHA-256 | Exact per-file diff SHA-256 |
|---|---|---|---|
| README.md | `54ab5a57c1c49633756820d9c1252770ffc93d14` | `17052f827980198a8ccb9da7aec6c017e4558542aa0b064b54a4d7e044d0293b` | `e2f13de0328e7bb71fb3f1c31909aaea785cb7e1f0bf37f287ff535fc0342c43` |
| article.tex | `fd29c0d9f4df3a2a46424b25abcfba8ceca4aefe` | `26892670444fb6e82297d872ff5c99e14abfcc5de71fa5bc65cff841a5463aa2` | `bcb5ddecf02d7cae131d841c2666a4d0ce4209ff2783465397f6f90f29461507` |

Both evidence notes were read completely as frozen text:

* `review_horizons_xvi_corrections_a21a42d8c.md`, SHA-256 `7060ea9d136a3623ae431083f84f07b844b4073b8774c14c4b173f8946d2d4ca`.
* `review_horizons_write_a21a42d8c.md`, SHA-256 `023370dec45b5ffb6275e55143081b80601caa11c564a1d4654e6592ea90edea`.

I additionally read the actual neighboring canonical-history definition and its nonempty carrier/schedule conventions; exact-tower definition and tower/history remark; finite-digit theorem and its proof; revised digit and converse remarks and the conditional-converse proof; the adjacent exhaustion Note; the complete set-likeness and set-base statements/proofs; and the normal-form addition and multiplication statements/proofs. Their stable source locators are respectively `swo:bo:hist:definition`, `swo:dh:def:tower`, `swo:xvi:rem:towers`, `swo:dh:thm:digits`, `swo:xvi:rem:digits`, `swo:dh:prop:converse`, `swo:xvi:rem:converse`, `swo:dh:prop:exhaust`, and `swo:hn:ar:{setlike,setbase,addition,multiplication}`. The changed frontmatter, review-status paragraphs and H4 dependency note were read with their surrounding text. This is not a rereview of the whole manuscript, the entire GB dependency chain or the unreviewed spectrum/truth results.

## Part XVI: domain repairs

1. **Empty exponent schedule.** The tower definition requires nonempty W but permits empty Gamma. When Gamma is empty, its one-stage tower has equality as its final relation; exhaustion therefore forces W to be a singleton. Its digit map to P(Gamma)=1 is the unique isomorphism. The revised digit remark treats this case before invoking a canonical history, whose printed definition requires both W and Gamma nonempty. Its initial-image conclusion is preserved.

2. **Empty carrier.** The source conditional-converse proposition now explicitly assumes nonempty W, matching the exact-tower definition. The broader embedding/initial-embedding equivalence separately treats W empty, then nonempty W with empty Gamma, and only then invokes the tower/history machinery. The terminating-history equivalence remains restricted to both nonempty. These cases are exhaustive, with no silently extended tower or history convention.

3. **Adjacent propagation, found and repaired during this review.** Note XVI.5.32 formerly identified existence of exhausting towers for “all class well-orders” with CTH. W=0 lies outside the printed tower definition, whereas CTH quantifies nonempty W. The current Note says “all nonempty class well-orders” and retains the former phrase and its empty-carrier counterexample within the existing numbered Note. Its equivalence with CTH and CWO then has the intended domain.

The original W=1, Gamma=0 and W=0, Gamma=1 counterexamples remain explicit in the existing numbered digit/converse remarks. Review remark H5 qualifies the earlier unshipped working-note report and frozen review passes, instead of erasing or silently upgrading them. The added frontmatter and guide follow-ups distinguish the historical intake assessment from the later bounded publication reviews. H4 gives the retained choice-dependency correction an explicit numbered locator; its explanation correctly separates the Tm/T typo from the already supplied replacement of the cited GBC equivalence in item (4). This review does not independently recertify every premise of the completion theorem.

## Part XVII: the three corrected summaries

1. **H1, multiplication scope.** Both operations are stated on the hereditary order; only addition is extended to every fixed finite-support power Omega^[B]. This matches the actual two arithmetic theorems. At B=2, the point-cut Omega multiplied by itself is the whole order Omega^2, which cannot be a proper initial point-cut of itself. The old overextension is retained and refuted in H1, and all three identified summary occurrences—the guide, notation table and Part introduction—are corrected.

2. **H2, set-likeness assumptions.** The guide now includes A having at least two elements and B nonempty. With A=1, B=Ord+1, the power is the set-like singleton but neither stated alternative holds; with A=Ord, B=0, the same happens independently. Both counterexamples are retained. The qualified printed theorem and proof are unchanged.

3. **H3, set-base collapse.** The guide now assumes a is a set ordinal at least two. The retained example a=1, B=1 refutes the old unrestricted summary by forcing 1 isomorphic to Ord. The printed corollary and proof are unchanged.

The new review-status text accurately attributes the frozen publication review's selected scope and exclusions. Its coverage and provenance numbers are inherited from that pinned review, not independently recomputed in this host-diff check. It does not turn finite ordinal-relative syntax into an ordinary-integer evaluator, a fixed-arity Diophantine compiler or a paid operation-count improvement.

## Retention, locators and links

The H1–H5 headings explicitly number the retained review remarks. The mathematical empty-case counterexamples remain inside existing numbered remarks/Notes. The edits neither add nor remove a theorem environment or literal label: a fresh source-only comparison, accounting for optional label arguments, finds the same 2,293-label multiset and the same begin-environment multiset before and after. All 1,889 targets recognized by the simple literal ref/cref/eqref/pageref scan resolve. These are source checks, not a TeX expansion or rendered-counter audit.

The two new guide links each climb five directory levels and resolve to the intended `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` review filenames. At the time of this review, their frozen copies exist in `/tmp` and root plans to install them; the repository targets were not yet present. Their path depth and spelling are correct, and the landing must include those two companions for the links to resolve. This is a recorded landing dependency, not a mathematical defect.

The pins above describe the exact text reviewed. A later guide build-status paragraph, installed review companions and the rebuilt PDF are outside this proof-only approval unless separately checked. No claim about PDF correspondence, page count, external literature, Lean/Rocq verification, historical priority or the entire Parts XVI–XVII is made.
