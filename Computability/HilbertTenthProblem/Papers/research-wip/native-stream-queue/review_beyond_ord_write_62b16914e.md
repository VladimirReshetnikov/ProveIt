# Bounded Beyond-Ord publication review at 62b16914e

**Result: byte/label checks pass; three editorial metadata corrections are needed.** The selected effective interfaces preserve the distinction between class-order constructions, finite syntax relative to supplied coefficient orders, and ordinary integer computation. No paid fixed-arity Diophantine compiler is provided by these interfaces. A separately pinned independent review passes the selected GB history and completion arguments. Neither review certifies the entire new Part XVI.

Reviewed commit: `62b16914ebf724b672badca7d4851f90b2ba6f2b`; parent: `d18416ec7e187a0948248cb3077e37d7b089a8f9`. Host: `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/`. This review records the immutable publication before any subsequent correction. Root alone owns repository edits.

## Three retained findings

1. **R1 — manuscript-read coverage is overstated.** README line 1513 and article lines 58499–58500 describe the old intake as reading “2,468 selected lines of the four manuscripts.” The earlier receipt instead records **1,665 TeX manuscript lines plus 803 other archive-member lines**, totaling 2,468. Its additional 446 context lines are separate. The four manuscript counts are 392, 318, 584 and 371. A precise replacement is “2,468 archive-member lines, including 1,665 manuscript lines.” This is a coverage/provenance error, not a new mathematical counterexample. The surrounding publication correctly describes the intake as bounded and names omitted proof dependencies; the wrong noun should not silently expand that scope.

2. **R2 — the reported Mathlib pin is wrong.** README lines 976–977 and article lines 57615–57620 say that this repository pins `v4.31.0`. Both immutable root and `Algebra/SurrealNumbers/lake-manifest.json` instead pin **`v4.32.0`**, revision `81a5d257c8e410db227a6665ed08f64fea08e997`. The root manifest at source 32's cited repository pin `8f7d4a5c8` already has that version. This finding concerns the repository dependency claim; it does not refute what a separately consulted v4.31.0 documentation page says. The cited local `Sep_form`, `Repl_form`, `ZFax`, `ZFprov` and `FirstOrder.Calculus` import exist in the inspected Lean source. I did not audit Mathlib's external declaration/deprecation history or run Lean. A correction should distinguish any consulted documentation version from the actual dependency pin rather than treat an uninspected API claim as freshly verified.

3. **R3 — one guide output-location sentence contradicts the shipped script.** README lines 465–467 say source 35 writes `artifacts/finite_notation_results.json` relative to its working directory. The actual placed script, `code/35-completion-finite_notation_checks.py:161`, uses `Path(__file__).with_name("finite_notation_results.json")`: its output goes **beside the script**. The later guide/article copying instructions already use the beside-script convention. This is established by an inert read of the script's last 55 lines, not by executing it. The archive's delivery filename remains a valid provenance name; only the claimed runtime path is incorrect.

These original clauses and their explicit corrections are retained here under the incoming-report retention rule. No unproved theorem is deleted or silently promoted, and no repository file was changed by this review.

## Byte, placement and label authentication

The fresh companion collector reads immutable Git and ZIP bytes only. Its receipt binds all three changed paths, their six before/after blobs, and exact raw diffs. Current postimages are:

| File | Git blob | SHA-256 |
|---|---|---|
| README.md | `83706ca489926fc5f9020a9c3901373a63c1cdb0` | `1dd56eb923da9bc2b14007bfe5810191081102dcd7ef7505f5c8c734f28f3a08` |
| article.tex | `a4c1c5a049e864b44c25cefe0fdaee218451b013` | `31d10373d5fe12073c40ad1113d8fe6b0c6ef9138fa6ac233c73641f32425300` |
| article.pdf | `cd34960bb7f0f882cdb1b7e5ae34ff8453c785d4` | `ee44c06c5b846f12d0c19f420dd97e9699779d7ba0e2dd802c2149037ca76c0a` |

The PDF is hash-only: no rendering, extraction, pagination or source/PDF equivalence check occurred.

At arrival `e3839ad2c6be32ac5c6fdc422507da07f85f4fb6`, all four archives and **27 regular members** match the earlier intake pins. All **16 delivered checksum entries** match their actual member bytes. The **13 ancillary files** placed by `111c380120cb27a886eb8be5df1920d31e3d111c` equal their original archive members both at first placement and at this publication. Earlier selected archive/context span hashes were independently reauthenticated; that operation does not count as a new human read of their contents.

All **227 original literal source labels** have unique prefixed locators in the new host: source 32 has 55 under `swo:dc:`, source 33 has 62 under `swo:dh:`, source 34 has 53 under `swo:bo:`, and source 35 has 57 under `swo:fc:`. The host label census changes from **1,876 to 2,188**, with 312 additions, no duplicate literal labels and no lost old label. All **193 literal reference occurrences** in this review's selected current article spans resolve. This is a source-level locator census, not TeX expansion, full crosswalk verification, theorem-body equivalence or certification of the normalized merge. The new publication now contains Part XVI; the earlier placement review had deliberately established only ancillary placement.

## Exact new read scope

The whole **545-line raw README diff** was read. For the 10,478-line raw article diff, only **lines 1–520** were read as a diff, covering frontmatter/editorial changes and the beginning of the new part. Separate current article reads comprise the following **891-line union**:

| Article lines | Scope |
|---|---|
| 54888–55186 | Complete new choice-free completion proof; finite notation, worked comparisons and four effective-interface levels |
| 55360–55458 | Supplied well-ordered-index diagonal theorem, GBC catalogue corollary and start of the truth discussion |
| 57498–57625 | Model/universe and formalization interfaces, coefficient representation and current Lean-status claims |
| 57745–57830 | ETR/universe/formalization qualifications and surrounding source handoff |
| 58403–58523 | New answers/status and prior-review provenance |
| 64268–64384 | Delivery/check instructions and surrounding retained reproducibility text |
| 66870–66910 | Beginning of the source 34 statement crosswalk |

The receipt additionally pins README postimage reads 440–477, 958–995 and 1492–1532; the full applicable 182-line `Algebra/SurrealNumbers/AGENTS.md`; incoming retention lines 426–440; both complete earlier intake/placement review notes; the full two-type effectivity note; the exact Lean/manifest spans; and the last 55 lines of the source 35 script. These are 22 current context spans totaling 1,583 lines, separate from raw-diff reads. Overlap between a diff and a postimage read is not additional proof coverage. Span hashes use UTF-8 lines joined with LF and one final LF, as stated by the fresh collector.

The earlier intake JSON is pinned at `183d06eaad58bc4f23defca1151dacedc7b77bebfdaeb496095b1d5beb7ad228`; the earlier placement JSON at `119e10dc4d6250ec7c4adc0fe5591c30feb315b15db9783effde98452a4859b0`. Their programs were never run or imported. Their recorded scopes remain immutable; no new body coverage is inherited from member hashes or label routes.

## Mathematical and computational interfaces

The new completion argument explicitly addresses the old uniformity gap. Finite nested codes make the stages and connecting maps uniform in internal n. The induction predicate uses only set quantifiers after replacing class well-foundedness by the set-subset minimum criterion. Thus ordinary GB induction with the supplied class parameters applies; it is not merely an external proof at every standard finite stage. Initial connecting embeddings make the least-stage colimit argument work. This is not an algorithm taking arbitrary program descriptions of class relations as input.

The independent `review_beyond_ord_gb_62b16914e.md` supplies a broader, separately documented **2,011-line** proof challenge. It passes the set-subset/power lemmas, supplied-history termination, floors, finite changes, normal-form initiality, anchored restriction, GB equivalence, hereditary construction, source 33's digit-map strengthening, and source 35's completion with the new choice-free replacement. Its MD SHA-256 is `f79d9caf8a3d51c9b7850d8833b04650ea7f6d60dca26bf847bfa3f019c027e6`; JSON SHA-256 is `aa2759996a6fd225ece66ea39edee693b71c07cf0839d486c44b8e06b0df604a`. I read that review in full. Its spans overlap mine and must not be added as disjoint coverage. It found no additional mathematical correction within that chain. The publication's statement that the new theorem had not yet been reviewed was accurate at its immutable snapshot; this new evidence is a later event.

The diagonal theorem is over **GB with a supplied well-ordered index class**. The arbitrary-index catalogue corollary explicitly uses GBC to obtain that index order. The difference is preserved in the selected source, so an external list of definitions cannot be substituted for its uniform interpreted class relation. The opening truth paragraph does not constitute a review of the later truth-presentation proof. Truth classes, external model spectra and unavailable class recursions retain their stated hypotheses and their unreviewed status here.

The selected notation interface also makes the essential representation boundary explicit. A finite tree can contain arbitrary set ordinal coefficients; comparison then relies on that supplied coefficient order. Restricting to recursively presented notation systems is a different, effective interface. Finite proof syntax for constructor closure does not turn proper-class orders, initial maps, or internal histories into a fixed tuple of ordinary integer witnesses. No source in the read spans supplies a finite natural-number evaluator for arbitrary class definitions, a paid arithmetic DAG, a gate count, or a universal positive-integer decoder.

The pinned `ordinal_two_type_effectivity_boundary.md` strengthens this distinction for program-index semantics. Its orders are uniformly decidable and always well-orders, promised to have type omega or omega+1. Type omega+1 is nonhalting, so a uniform effective isomorphism-invariant comparison with omega, or an effectively enumerable finite existential integer certificate for that upper type, is impossible. This does not prohibit constructor syntax, oracle-relative comparison or explicitly restricted valid notation systems, and it refutes no claim in the selected publication passages.

## Validation and remaining limits

Executed Python was confined to fresh standard-library metadata reads, this packet's new collector and its replays. No archived, supplied, committed, frozen or predecessor program—including copies—was executed or imported. No build, repository mutation, external-source lookup or kernel verification occurred. The whole 10,228-line TeX change, all truth/spectrum proofs, external cited results, full statement/body reconciliation and PDF were not certified. Unreviewed source questions remain questions.

Fresh normal and `python -O` exact receipt replays from `/` both pass. Collector SHA-256: `b77050534c72b03af9615d6c2f6df254221969e894f8aed46c75ae07a048cfaa`. Receipt SHA-256: `73df09930370852a63ba4ac2f7038e7cfa24498e5614b8f95051fa667a12f81f`. These replays validate the byte/census/read-span assertions, not the unreviewed mathematics.
