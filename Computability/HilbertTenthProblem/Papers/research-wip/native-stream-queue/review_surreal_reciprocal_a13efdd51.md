# Reciprocal surreal notes at a13efdd51: bounded independent review

**PASS; no new correction requested.** This review covers only the twelve README/TeX/PDF changes in commit `a13efdd513da7d0adf7cb1b1a74b2ca7fc4206af`, against its parent `acb0041e13eb423320c0a598fe9626093de0a222`. It is a preservation and editorial-reference audit, not a new proof of the original theorems or a claim of Lean verification. No unchanged author program, TeX build, or historical test suite was run. The applicable `Algebra/SurrealNumbers/AGENTS.md` was read and is pinned in the receipt. All outputs and PDF checks use private temporary files; repository contents are only read.

The cited `surreal-well-orders/article.tex` at this boundary is byte-identical to the previously reviewed synthesis at `0be9b913487fa2cc0e16cea6545c55f33b4446d8`: SHA256 `728573d68da543e25ee8d0f7d37f9d75410695ce5196702336e71e4a7928b503`. This relies on the completed original-source review and the separate `review_surreal_transfer_0be9b9134` and `review_surreal_synthesis_0be9b9134` audits. Their previously identified “coherent” wording and non-PDF maximum qualification are separate findings on the cited synthesis, not new changes in this commit. The new reciprocal prose does not repeat those overstatements.

The executable audit authenticates all 24 before/after publication blobs, the cited synthesis's article/README/PDF, and AGENTS. It checks that the commit changes exactly the declared twelve files. Each original article is preserved as an ordered sequence of exact lines: all six changes are insertion-only, totalling 91 added TeX lines. In addition it compares every declared theorem-like environment, proof, display, label sequence, preamble, and structural counter event. Nothing is normalized algebraically or matched as an unordered set; duplicates remain separate occurrences. Every theorem environment declared by these four preambles must be covered by the parser. The single pre-existing README line replaced merely expands its “62 pages” build-history qualification; the remaining README changes are insertions.

| Report | Exact formal blocks | Exact proofs | Exact displays | Labels | Unchanged companions | PDF pages before/after |
|---|---:|---:|---:|---:|---:|---:|
| birthday-cutoffs-and-hereditary-sets | 117 | 75 | 87 | 156 | 17 | 62 / 62 |
| foundations | 56 | 22 | 61 | 265 | 8 | 95 / 95 |
| real-vector-space-structure | 187 | 78 | 227 | 249 | 4 | 88 / 88 |
| lexicographic-well-orderings-of-reals | 101 | 76 | 82 | 150 | 10 | 54 / 54 |
| **Total** | **461** | **251** | **457** | **820** | **39** | |

All PDF files have valid PDF headers/end markers, are accepted by `pdfinfo`, and are unencrypted. This checks the delivered files and their page counts; it does not reproduce their TeX builds or independently establish the author’s “no build warnings” claim. Byte pins and ordered source-line maps for every formal/proof/display occurrence are saved in the JSON. Unchanged preambles, labels and structural events support the unchanged-numbering claim; no `.aux` file was assumed.

## Reading the added claims

- **Birthday cutoffs, article 2552–2568 and 2684–2696, plus README.** The first note correctly distinguishes the order interpolation property from pure-field saturation. For regular infinite κ, including ω, regularity bounds the birthdays of fewer than κ endpoints. The original birthday inequality places a separator below κ; placing the forbidden points already inside the interval on the lower side supplies the avoidance clause. Neither real-closedness nor uncountability is needed. Cardinality κ, and hence the quoted permutation-order application, additionally uses `2^{<κ}=κ`. The surrounding regular-κ hypothesis remains in force. The second note correctly reports the GB-without-set-choice equivalence of Global Choice, an arbitrary class well-order of `No`, a set-like one, and an `Ord`-bijection. Its successor-stage subset coding uses the unique enumeration of the already constructed set well-order; it does not assert that successive rank orders extend one another. The separate birthday-coding theorem and its two open problems are expressly left unchanged.

- **Foundations, article 1260–1276, plus README.** The summary matches all four source foundational sections and the reviewed class-choice proof. The recursive value is a set, and the history through each set ordinal is a set; fixed class parameters are permitted. Local set recursions agree by uniqueness and assemble through elementary class comprehension. The note does not infer unrestricted ETR, does not claim a recursion producing class-valued stages is covered, and explicitly leaves iterated residual decompositions open. Its citation to the local-recursion proposition preserves that proposition’s dependency and uniqueness hypotheses. Source subsection numbers 5.3, 5.4.4, 5.5.3 and 5.6.2 are independently counted and checked.

- **Real vector spaces, article 4241–4257, plus README.** Source 52 really uses a set-like well-order of the surreal class in the second proof of the basis-extension proposition. The cited class-choice theorem identifies this hypothesis with Global Choice over GB, even without prior set Choice. The new note carefully does not infer a class well-order from a Hamel basis, so it does not purport to settle the weaker-principle question. It also does not turn the basis construction into an algorithm or a canonical coordinate map.

- **Lexicographic well-orderings, article 3005–3009 and 3446–3467, plus README.** For an infinite cardinal cutoff θ, the alphabet is the sign order `S_{<θ}`, with cardinality λ=`2^{<θ}`. The cited dichotomy gives binary coding length λ in the nonexceptional cases and ordinal length `θ·θ`, not cardinal multiplication, at singular strong-limit θ. The example θ=`beth_ω` requires no extra cardinal-arithmetic hypothesis. This genuinely addresses the displayed classification at the minimal stratum `n=0`. The remaining-question language is read as the general classification and weakest-hypotheses problem, not as claiming that every individual case with `n>0` is unknown: for example, the θ=ω alphabet is already a subset-of-the-reals case. The note neither proves nor claims a uniform new theorem for those longer strata. All thirteen general-alphabet pointers resolve and their printed numbers agree. The finite-block pointer is to the factorial-block description reprinted in the surreal synthesis, not an extension of the real report’s endpoint-dependent topology conclusions to arbitrary alphabets.

The executable verifies the eight cited `swo:` theorem/question numbers against the actual section/shared-theorem counter stream, the thirteen `lwo:` numbers, the four foundations subsection numbers, and each new local/external label reference. The new README relative links resolve to the cited synthesis README at the pinned commit. The original source of each new statement is identified explicitly; these are supported cross-report summaries and references, not new formal assertions or independently verified computational results. There are no new displayed-equation blocks, theorem environments, labels, macros or computational files.

## Reproduction

Use Python 3 with its standard library, Git, and `pdfinfo` on PATH. No SymPy, author-script dependency, network access, or current checkout state is needed. All publication content is retrieved from immutable Git blobs, including when the working tree has since changed.

```sh
python3 /path/to/review_surreal_reciprocal_a13efdd51.py \
  --repo /path/to/Proofs \
  --expect /path/to/review_surreal_reciprocal_a13efdd51.json
```

`--write /path/to/new.json` produces a receipt; it is mutually exclusive with `--expect`. Receipt comparison is recursive and type-sensitive. The final saved receipt was reproduced from `/`, with all the counts above unchanged. The source and receipt hashes are recorded below; the receipt also records the source hash and all authenticated publication hashes.

- review_surreal_reciprocal_a13efdd51.py: `fcecc1b4b3840180edc77f9caf9e8496cc0241ea22ee5dad923a9cc30211bdf4`.

- review_surreal_reciprocal_a13efdd51.json: `915f17aa87ce01a26affe784d6a7635dd995882df4574f018378375d3a929659`.
