# Bounded reciprocal-note review: batch 92

Reviewed immutable commit `9bffd43d5dbf10d2b8712650aabc26d1a4b98efb` against parent `f300069cfc840fc3d178f0ba31bcb3596a35d7a3`. The result is two scope clarifications in the new summaries, with no additional defect found in the selected source interfaces. This is a review of reciprocal notes, not certification of all mathematical proofs or of the cited external literature.

## Read and authentication scope

I read every changed README/article source diff: **16 complete text diffs, 390 raw diff lines, across ten report directories**. The commit changes 24 files; the other eight files are PDFs, authenticated as bytes only. The attached JSON pins all 48 before/after Git blobs, byte sizes and SHA256 values, all raw diffs, their complete text-read spans, and their old/new source hunk spans. A raw diff line can be a long TeX paragraph; the line count is not a word or proof count.

I also read the 37 selected source spans recorded individually in `source_reads` (1,619 lines counting overlap). They include the relevant PMA hypotheses and embedding, summability, integer-part and exponent-cone statements/proofs; the affected reports' local strongness/valuation interfaces; and the MBG normal-form, minimax, budget and finite-equality interfaces. No claim of full manuscript coverage is made. Each span hash uses exact immutable Git bytes, inclusive 1-based lines and retained line endings.

The full applicable `Algebra/SurrealNumbers/AGENTS.md` and incoming retention-rule context at `docs/incoming/README.md:420–445` were read and pinned. The latter requires credited open questions for unproved assertions and retention of demonstrably wrong assertions with explicit failure/counterexample. The findings below preserve the original wording rather than silently discarding it.

All eight modified articles preserve their literal TeX label sequences and bibliography-item sequences. Their respective literal label counts are: CSF 70; large-cardinal embeddings 323; entire functions 493; hidden-negative directions 89; surcomplex automorphisms 229; discrete initial subgroups 313; omnific-preserving automorphisms 729; surreal self-embeddings 468. This counts source `\label` commands, including optional theorem-type syntax, not generated `.aux` entries or cleveref companions.

All 47 explicit label references in the added lines resolve to one source definition (26 distinct labels), and all three newly introduced relative Markdown links resolve at the immutable commit. Resolution establishes existence, not proof validity. The PMA article is byte-identical to its cited publication at `4af6f191d876089a536dcdb65658e211ec2a52ea`; the MBG article is byte-identical to its cited publication at `721cf81969897cecd69d9fe2ae757ad12dffd511`. This is a two-article publication-snapshot check, not a reauthentication of every earlier archive or ancillary placement.

## Findings

### R92-1: retain the rational-vector-space hypothesis in the CSF summary

At `Algebra/SurrealNumbers/docs/foundations-and-computation/cantor-families-of-surreal-subfields/article.tex:604`, the new note describes exponent groups

> `0\ne\Gamma,\Delta\le\R`

and says the field embeddings are classified by triples `(lambda,c,u)` via `pma:rk:thm:parameters`. The source convention at PMA lines 31362–31370 and parameter theorem at 31689–31704 assume **nonzero rational vector subspaces** of the real numbers. The positive leading-coefficient character is part of this parametrization.

The unqualified additive-subgroup reading is too broad for that conclusion. With `Gamma=Delta=Z`, the left-finite field over the real algebraic numbers is the ordinary Laurent-series field. Its field automorphism `t -> -t` has leading character `c(1)=-1`; it is therefore not among the cited triples with positive character. This example refutes the unrestricted positive-character parametrization, not every possible scaling theorem for other exponent groups.

**Minimal correction:** write `0\ne\Gamma,\Delta\le_\Q\R`, or explicitly say “nonzero rational vector subspaces of the real numbers.” The same convention should be explicit wherever the guide compresses this family to the notation `L^Gamma`.

### R92-2: retain countability in the SSE guide's Cantor-family clause

At `Algebra/SurrealNumbers/docs/surreal/surreal-self-embeddings/README.md:334–342`, the new guide says

> “with a Cantor family of proper closed immediate self-copies in infinite rank (`pma:rk:thm:family`).”

PMA lines 32001–32066 impose **countable** `Gamma` of infinite rational rank for the stated Polish/Effros Cantor-family result. The corresponding new SSE article note, line 1509, correctly says “for countable `Gamma`.”

**Minimal correction:** say “for countable `Gamma` of infinite rational rank” in the guide, retaining the rational-vector-space setup. This is an omitted hypothesis of the cited theorem. I do not claim a separately formulated uncountable extension is false.

## Selected mathematical and interface checks

**Forward summability versus automorphisms.** The new KS-related notes correctly identify the needed distinction. For `K=k(t)` and the character `u(n)=(1+t)^n`, substitution induces `f(t) -> f(t+t^2)`. A Laurent expansion of a rational function is bounded below; after substitution the term indexed by `n` still has least exponent `n`, so only finitely many indices contribute to any output coefficient, and the sum is again rational. Nevertheless the image is proper: `rho(t)=-1-t` fixes `t+t^2` but not `t`, since `rho(t)-t=-1-2t` is nonzero over any field. Thus forward summability alone does not establish surjectivity or a summable inverse. PMA records the alleged external lemma and counterexample rather than erasing them. I checked this algebra and the repository's quoted interface; I did not retrieve or certify the external preprint's versioned text.

The local OPA factorization proof starts with an already strongly additive automorphism, and its character construction therefore does not require the rejected converse. The selected automatic-strongness and convex-support arguments were also read. The Saut definition expressly requires strongness for both the automorphism and its inverse. These local checks support the notes' distinction, but do not constitute an exhaustive dependency audit proving that no remote theorem anywhere uses the external lemma.

**Left-finite fields and integer parts.** The source setup is a complete left-finite field with real algebraic coefficients and a rational-vector-space value group; it is not a full Hahn field or the proper class `No`. The scaling proof uses real-closedness/order and integer comparisons, then continuity and density. The parametrization extends a finite group-algebra map to the completion. Finite rational rank gives surjectivity; the bounded-exponent shift produces a proper closed immediate copy in infinite rank. The countable Cantor-family result is a separate topological statement.

The new ISG/OPA notes preserve the distinction between the canonical finite-negative integer part and arbitrary transported integer parts. The `L^Q` example is larger than the Puiseux field used in the older construction, while retaining the displayed canonical floor ring. Although its field self-embeddings are onto, the substitution `t -> t+t^2` need not preserve that integer part: the image of `t^-1` has a nonzero positive-exponent tail. The cited integer-pair classification remains an open question. The exponent-cone notes concern real-coefficient rings with `Gamma <= Q`: order-bounded division and the root condition `Gamma=k Gamma` are not claims of a well-founded Euclidean norm or arbitrary Hahn/class-field transfer.

**Measurable membership games.** The two new SetTheory guide notes are consistent with the selected MBG source interfaces. The full-Borel/universal sharp minimax statements use an invariant conull good set and should not be transferred to a Baire-property-only setting. The Baire-property clause remains open; the displayed comeagre-null example explains why category does not replace measure in that argument. For fair independent hats and deterministic strategies, the expected-query threshold is the minimax quantity `sup_i E(Q_i)=2`; an individual coordinate can have expectation below two, and free randomization changes the problem. The bounded common-depth divergence result is stated in the null/meagre sense. The finite extremizer classification is the stated equality case for the specified parameter pairs and minimum depth, not a classification of arbitrary finite teams at arbitrary budgets.

None of these reciprocal notes supplies a paid fixed-arity universal Diophantine compiler or improves the current arithmetic operation ledger. Recognition, field-embedding, category and finite-game results retain their separate scopes.

## Execution and proof limits

Only fresh read-only metadata code, Git object reads and text inspection were executed. No report script, supplied/archive program, frozen helper, copied predecessor, TeX/Lean builder or PDF renderer was run; no repository file or Git state was changed. PDF build outcomes asserted by the publisher were not independently reproduced. The external references, complete proofs, and unselected manuscript sections remain outside this review.

Metadata collector: `/tmp/collect_reciprocal_9bffd43d5.py`, SHA256 `7f9e50536e01a636c88e8d1002bb4ec34a5a5531806a054a6b6bdc8547f658c1`.

Receipt: `/tmp/review_reciprocal_9bffd43d5.json`, SHA256 `3ef8053e5e0e05dd1df6fc044ed3fefea44f645aa0c5823f400c3d310eeabdd8`.
