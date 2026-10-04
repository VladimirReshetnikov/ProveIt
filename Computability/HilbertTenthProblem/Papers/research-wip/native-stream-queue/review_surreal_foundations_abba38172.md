# Scoped publication review: surreal foundations, Part IX

Two corrections are needed in the immutable publication: a missing effectiveness premise in the general extension lemma, and incorrect counts of the delivered manuscripts' labels. Neither finding invalidates the stated finite-language ZFC application. The selected interpretation and class-boundary arguments otherwise preserve their essential hypotheses. This review does not certify all proofs or the external foundations they import, and yields no ordinary-integer compiler or arithmetic-cost improvement.

The reviewed commit is `abba381729f85fd28f997ab2a7eefa1b8d1bf242`, parent `b8bc36acc1f94bdc081b21a4d79b429b4f3acc27`. Its host is `Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/`. All line numbers below refer to those immutable bytes. Later corrections by the root agent are outside this receipt.

The companion JSON has SHA-256 `3885ce42fd750f8cf5557349653ba089e7eb3a6d5425d9e42361a9ce83502c98`. It contains the before/after Git blob identifiers, byte lengths and SHA-256 hashes, all three diffs, exact read-span hashes, the complete two-archive member inventories, placements, and literal label/reference inventories.

## Coverage and authentication

The entire 392-line README diff was read. Selected article coverage is precisely lines **7633–8575, 8729–9417, and 9467–11844**, totaling **4,010 lines**. This includes the Part IX introduction and correspondence claims; logical conventions; imported sign facts and block storage; graph validity, collapse and Choice boundary; numerical round trips and axiom recipes; definability, quotient birthdays and the canonical reduct criterion; the NBG and class-domain obstructions; both class round trips and variants; computation/formalization limits, questions, status and provenance. The gaps include the detailed pairing/tuple codec and part of the axiom-status discussion. Earlier parts, other changed TeX spans, the full article diff, and external proof bodies are not newly certified.

The two complete delivered guides and source14's complete source/status note were read from the arrival archives. The earlier `review_new_foundations_f300069cf.md` was read in full as inert context; its receipt pin was authenticated. That earlier intake explicitly left the complete round-trip/class-lift arguments unread. The present selected reading adds those checks but does not retroactively broaden the intake. Applicable `Algebra/SurrealNumbers/AGENTS.md` and the incoming standing retention rule were read; original incorrect clauses are retained below.

Metadata checks succeeded for all three changed paths and six before/after blobs; two arrival archives and all twelve regular members; all eight supplied checksum entries; and all five source14 ancillary placements, byte-identical at both placement and publication. The archives are:

| Source | Arrival archive | Bytes | SHA-256 |
|---|---|---:|---|
| 13 | `surreal_omnific_foundations.zip` | 566,548 | `db8e989962143836b5c6c9520167d258c1d922cb69295bc14b65e9824ca1013c` |
| 14 | `Surreal_Only_Foundations_and_NBG.zip` | 381,702 | `22ef255d65a2dfa9b92f717cadb0f2412cd1455853da30cee9ce991f317f11c7` |

Both arrive at `ec91f8c7c5dbe1e34aef03214e441a1c0154f410`; the five files are placed at `350b9a954d302554e04d510f5ee9f220042ed75c`. Source13 ships no executable or data. The original source, placement and publication hashes are recorded separately. The declared baseline commits and arrival/placement commits are ancestors of this publication.

All **372** parent labels survive, and exactly **151** new `hset:sf:` labels give **523** total, with no duplicates. All **1,100** literal local reference occurrences resolve. The receipt records subject/prefix destination locators for all **113** literal source labels: 96 direct prefix routes and 17 manually specified subject routes. These are label locations, not a claim that the merged text is a verbatim reproduction or that every merged proof is equivalent. The two delivered TeX files have the claimed 2,765/1,836 lines and 12/11 question environments. PDFs were only hashed; page counts, typography, builds and historical test execution were not checked.

## Review Remark 1: effectiveness of translated extensions

The new general lemma `hset:sf:lem:persist`, article **9522–9541**, correctly states persistence of bi-interpretability under translated extensions, but ends its statement with the original clause:

> “if $\Sigma$ is recursive, so is the second theory.”

No premise in that lemma or the Part IX logical conventions requires either starting theory to be effectively axiomatized. For a counterexample, take `S=T=Th(N)` in the finite language of arithmetic, identity interpretations and comparisons, and `Σ=∅`. All the interpretation and extension premises hold, while the resulting complete true arithmetic theory is not computably axiomatizable. If it were computably enumerable, completeness would let parallel proof searches decide every arithmetical sentence, contradicting arithmetic undecidability.

The corrected final clause can be:

> If `T` has a computably enumerable axiom set, `Σ` is computably enumerable, and the translation `σ ↦ σ^I` is computable, then `T ∪ {σ^I : σ ∈ Σ}` is computably axiomatizable.

Dovetail the two axiom enumerations, applying the computable translation to the second. In the intended finite-language, fixed-formula interpretations the translation condition is automatic. The earlier recipes explicitly assume recursive axiomatizability, and the actual ZFC/GBc/GBC/KM applications retain effective presentations. Thus the general lemma needs this qualifier; the claimed concrete constructions are unaffected. The bi-interpretation persistence argument itself remains valid for arbitrary sets of additional sentences without any effectiveness claim.

The root agent has been given this exact correction and counterexample, with a request to retain the original clause in a numbered correction remark rather than delete its history.

## Review Remark 2: delivered-label counts

The original README **61** says “the delivered labels, 76 and 70”; README **225–227** and article **11777–11781** also describe source13 as having “76 labels” and source14 as having “70 labels.” These are the incorrect original numerals, preserved here.

The immutable archive TeX has **59** source13 and **54** source14 literal `\label` declarations. Both a whitespace/optional-argument-aware parser and the raw occurrence count of `\label` give these numbers. Every declaration and its source line are in the receipt. Replace those particular delivered-source counts with **59 and 54**; do not change the correct host count `372+151=523`, the earlier batch90 count76, or theorem/section numbers containing76 or70. This is a provenance-count correction, not a lost-label or proof defect. The root agent has the exact locations and replacement recommendation.

## Mathematical and computational boundaries checked

The native block construction uses the imported omnific sign criterion and initiality. Conditional on these facts, the prefix, storage and graph interfaces read consistently: all bounded subsets are represented; validity includes well-foundedness, extensionality and root access; membership uses an edge-reflecting, predecessor-closed embedding; the collapse range is exactly `HWO` without Choice and all sets with set Choice. The numerical round trip compares the full sign function of every original number, not merely specially formatted graph codes. Source14's second route distinguishes raw numerical equality from equality of interpreted set codes.

The new quotient-birthday reduction is a useful semantic result. Native fraction-birthday comparison identifies the unique ordinal of birthday `birthday(a/b)`; a negative denominator is normalized and a zero denominator is assigned zero. Its conclusion is first-order definability on the actual omnific birthday structure, conditional on the graph/round-trip infrastructure and imported sign facts. It is not a low-cost arithmetic formula on ordinary integers. Likewise, the new reduct criterion requires set-definable primitives and a canonical comparison sending an original number to codes of that very sign-function set. It does not settle a one-way interpretation or an arbitrary noncanonical reconstruction in a weaker language.

The pure-omnific canonical no-go argument uses a parameter-fixing automorphism and transports it through a set-definable comparison to an automorphism of the well-founded set universe. Its rigidity contradiction is correctly restricted to this canonical setting. The Hahn lifting theorem used to obtain the automorphism is an imported dependency, not freshly established here. The reflection obstruction keeps `Con(ZFC)`, a uniform provable interpretation and a finitely axiomatized target. The separate cardinality obstruction keeps `Con(GBC)` and a forward domain consisting of finite tuples/quotients of the original sets. Its class-forcing extension premise is imported. The elementary diagonal argument is not overstated to arbitrary class-quantified predicates in GB; KM's stronger comprehension is handled separately.

The saturated-class maps and the second numerical-class round trip preserve the particular available class realization rather than replacing it with all external subclasses. They avoid selecting global graph representatives. GBc, Global Choice, KM and ETR are distinguished, and the GB-without-set-Choice codec problem remains open. The stronger variant proof uses translated principles, not unproved short native axioms. The larger-inaccessible-universe example explicitly changes the universe; it is not a same-universe numerical elimination of classes.

No finite ordinary-integer evaluator is obtained. Even the native block code for a positive finite length `n` has birthday `ω(n+1)`. The graph-validity formulas quantify over all numerically coded subsets of an ordinal; a fixed finite formula or tuple dimension does not bound integer witnesses or replace those quantifiers by charged ring gates. Formula-by-formula syntactic translation is distinguished from a universal truth evaluator, and a recursively enumerable axiom presentation is distinguished from a decision procedure. A usable Diophantine bridge would still require finite integer representations, paid evaluation of birthday/sign/coding primitives, and a proved positive-integer converse. None is supplied by this publication.

The new status passages retain the CHY attribution and unchecked intrinsic-axiom question; the external omnific sign, Hahn lifting, class-forcing, reflection/incompleteness and class-theory foundations remain attributed. No external source was fetched or certified in this review. The claim that only the fraction-field ingredient has relevant Lean support remains an attributed ledger claim; no proof-assistant audit or build was performed. The full-source textual-merger claim and all worldwide novelty claims are outside scope.

## Execution and disposition

Only the fresh standalone metadata collector `/tmp/review_surreal_foundations_abba38172_metadata.py` ran. Its exact receipt was reproduced from `/` under normal Python and `python -O`. No supplied, archived, committed/frozen or copied predecessor program was executed or imported; no build, PDF render, mathematical suite, repository write or Git mutation occurred.

This is a bounded publication/interface review with two concrete corrections, not a blanket pass for the manuscript. Apart from the generic effectiveness clause and delivered-label counts, no further defect was found in the selected arguments. The existing arithmetic operation and witness bounds are unchanged.
