# Independent bounded GB/completion review at 62b16914e

**Result: PASS within the proof scope below.** The selected choice-free history argument, supplied-tower digit-map strengthening, and the write's Theorem XVI.6.21 (`swo:xvi:thm:choicefree`) survive this independent challenge. I found no missing choice or class-recursion assumption in those proofs. This is not certification of all Part XVI, its external literature, truth/spectrum arguments, formalization, or publication integration. Pascal owns the full guide-diff and metadata audit; root alone edits the repository.

## Immutable evidence and coverage

Reviewed commit: `62b16914ebf724b672badca7d4851f90b2ba6f2b`; parent `d18416ec7e187a0948248cb3077e37d7b089a8f9`.

Source: `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/article.tex`, Git blob `a4c1c5a049e864b44c25cefe0fdaee218451b013`, 3,820,844 bytes, SHA-256 `31d10373d5fe12073c40ad1113d8fe6b0c6ef9138fa6ac233c73641f32425300`.

The companion `review_beyond_ord_gb_62b16914e.json` pins every inclusive read span with original line terminators, ten exact label locators, instructions and prior-review evidence. Receipt SHA-256: `aa2759996a6fd225ece66ea39edee693b71c07cf0839d486c44b8e06b0df604a`.

| Article lines | Actual scope |
|---|---|
| 51275–51384 | GB conventions, set-subset criterion, definability and recursion distinctions |
| 51799–51849 | One-step block decomposition |
| 52156–52244 | Choice-free finite-support power and minimization |
| 52690–52735 | Original bounded-specialization lemma |
| 52922–53254 | Full selected history chain: termination, floors, finite changes, capped decoding, anchored restriction, comparison equivalence and uniqueness |
| 53730–53997 | Exact tower definition, tower/history identification, source 33 digit theorem, its initial-image strengthening and conditional converse |
| 54018–54294 | Hereditary terms, bounded interpretation, GB well-ordering, height cuts, fixed point and leastness |
| 54632–55035 | Finite-support preservation, full fixed-point completion, local/global criteria, successor extension and the new choice-free proof |
| 55096–55254 | Finite syntax, relative/effective notation, constructor certificates and general-base interfaces |
| 55361–55445 | Uniform-family diagonal and its GB/GBC index-order hypotheses |
| 58403–58523 | Status and prior-review claims |
| 62719–62756, 62819–62848 | Retained digit-map and choice-free-completion questions |

This is a union of 2,011 article lines. Searches provided locators only. I read the full applicable `Algebra/SurrealNumbers/AGENTS.md` and immutable `docs/incoming/README.md` 426–439, including retention of wrong or unproved statements. Only fresh inline metadata code ran; it read Git bytes and computed hashes/counts. No supplied, archived, frozen or predecessor program was executed or imported, including copies. No build, PDF examination, external-source lookup or repository mutation occurred.

The earlier `review_beyond_ord_e3839ad2c.md` was read in full as an inherited scope record, not treated as a certificate for omitted proofs. At the current immutable commit its SHA-256 is `04cd0623189d2273958c469e2fc6e1a93c4e92c3293c108043da9d8e4e1d43d6`; its JSON is `183d06eaad58bc4f23defca1151dacedc7b77bebfdaeb496095b1d5beb7ad228`. That review checked the power/set-subset arguments but explicitly left the full history dependencies and completion open for review. The present reads add the specific proof challenge recorded here. They do not repeat the old four-archive audit.

## GB strength and supplied-history termination

The set-subset criterion is the key choice-free step. If an admitted subclass C of a linear order had no least point, below each current x choose the least rank slice meeting C below x, and then the order-minimum of that **set** slice. The assumed set-subset property supplies a unique minimum. Recursion with uniquely specified set values and Class Replacement gives a descending set sequence, contradicting the same set-subset property. This is not the invalid blanket inference that absence of a descending sequence proves class well-foundedness in arbitrary choiceless settings.

The finite-support power proof likewise selects unique minima of already well-ordered exponent and digit classes. A nonterminating prefix construction would yield decreasing selected exponents. No arbitrary predecessor choice is introduced. The one-step block construction uses ordinal ranks of set intervals; a nonfinal set-sized block would merge with the next point, so a nonfinal block has type Ord.

For a **supplied** canonical history on W+1, the successor induction deletes the next possible nonminimal point and the limit intersection removes every previously excluded point. This proves termination on that schedule. It does not construct the history. Floors exist by successor block minima and, at a limit, by the least earlier floor value, which is attained and then constant. Infinitely many changes would give a descending sequence through uniquely selected change stages. Thus each point has finitely many nonzero digits internally.

The initial-image argument was checked beyond injectivity. Below a genuine code, decode the common higher digits and decrease its first differing digit. The next rank in that block gives a fixed upper point a'. Every subsequent lower-digit insertion lies in a nonfinal block bounded above by a', hence has every ordinal rank available. This reconstructs every smaller polynomial and proves initiality. The anchor in convex restriction is necessary and is present: replacing the global floor of the local minimum by that minimum preserves precisely the relevant set-interval tests.

These ingredients support the stated GB equivalence. One history for R+S restricts to both orders on a common schedule, giving comparable initial polynomial ranges. Conversely comparison with P(W+1), together with the successor obstruction, forces the embedding of W to lie below the final monomial, hence inside P(W). The explicit polynomial history then pulls back. No simultaneous selection of histories for a proper collection is used. The result is an equivalence of principles; it does not assert that GB proves every history exists, nor establish comparison ⇒ ETR.

## Source 33's digit map

The write's strengthening of Remark 5.5 is valid. An exact tower has convex equivalences, successor set-interval condensation and **union** at limits. Taking class minima turns it into the nested history H; at limits, being least in a union-equivalence class is exactly remaining least at every earlier stage, so the history uses **intersection**. Conversely equality of history floors recovers the equivalences; stabilization supplies the union limit clause.

The ordinal r_a(x) in source 33 is then exactly the order type of the H_a representatives between p_(a+)(x) and p_a(x), which is source 34's c_a(x). Hence the digit map is the already reviewed normal form, with initial image, over GB from the supplied tower. It requires no additional comparison principle. Remark 5.5's original wording makes a nonclaim about this stronger conclusion; it is not a false theorem. Keeping that wording and its question while adding the supplied proof is an appropriate retained strengthening. The separate converse from an arbitrary embedding explicitly retains its ETR assumption to obtain a tower; it does not assert that an arbitrary embedding becomes initial in bare GB.

## Theorem XVI.6.21: completion without choice

The new proof resolves the stated internal-uniformity issue rather than merely iterating an external assertion at each standard n. Finite nested polynomial codes and finite map-evaluation traces define all A_n=P^n(A) and j_n=P^n(j) by one elementary formula with the supplied A,j as class parameters. The induction predicate says that A_n is linear, each nonempty **set** subset has a minimum, and j_n is an initial embedding. All its quantifiers range over sets. GB separation/induction therefore applies internally on omega. The set-subset criterion and choice-free power theorem establish the step. This includes internally finite stages of a nonstandard model; no metatheoretic standard-n restriction is being substituted.

I checked the rest of the completion proof with that replacement in place. Least-stage representatives avoid making proper equivalence classes into elements. Comparing in a common finite stage is elementary. Initiality of each connecting map makes every predecessor of a point appear in its own stage, so a minimum in an intersected stage is a minimum in the colimit. Every polynomial has finite support and hence one common finite stage; decoding that support defines the fixed-point isomorphism, independently of the chosen stage. Proper seed embeddings have uniquely defined least omitted elements d_n; Class Replacement collects their increasing cofinal omega-sequence. This is compatible with a non-set-like proper class order.

The universal maps into another supplied fixed point are finite evaluations. Their initiality is elementary and inductive; two initial embeddings of the same class well-order agree by least disagreement, so the evaluations commute with the connecting maps. No arbitrary class-valued recursion or choice of class witnesses is needed. The bounded-specialization improvement uses the same set-subset criterion: bound the labels in one set of terms, choose one larger admissible ordinal interpretation, and take its least image. The hereditary fixed-point statement separately has a valid choice-free bounded-cardinal interpretation and root-removal inverse. The local criterion, global FPE equivalence and successor extension then use the supplied maps and the previously checked GB history equivalence. Empty inputs cause no exceptional choice requirement.

The essential input remains an **initial** embedding j:A→P(A), or the corresponding principle that supplies one. A countable display of stages alone would not justify this argument. Here it is the explicit uniform finite coding plus set-quantifier induction that does so. This is a proof-level review, not a kernel-checked formalization or an external priority claim.

## Effective and ordinary-integer boundaries

“Finite” has several scopes in these passages. A term has finite tree shape but may carry arbitrary set ordinal labels. A history is one uniform class relation with possibly proper-class slices and schedule. Termination on W+1 is not a finite natural-number time bound. A set-coded cofinal omega-sequence in a non-set-like class order is not a finite certificate. Elementary definability with supplied class parameters is not effective evaluation from a natural-number index for arbitrary definitions.

The explicit four-way distinction at 55153–55179 is sound: mathematical class presentations, relative comparison using a coefficient-order procedure, a restricted recursively presented notation language, and proof-carrying constructors. A proof of a constructor's semantic preservation can be finite syntax, but its encoded objects and supplied initial maps are not thereby a fixed tuple of ordinary integer witnesses. The selected code-demo claim is only finite trees with nonnegative integer coefficients; I did not run it and infer no general decision procedure from it.

The diagonal theorem at 55385–55417 works in GB **with a supplied well-ordered index class**. The following arbitrary-index catalogue corollary is expressly in GBC, where the global order supplies that index order. I found no loss of that premise in the theorem/proof. An external list of formulas is not the uniform semantic class relation the diagonal requires. No new ordinary-integer evaluator, fixed arithmetic budget, positive-domain decoder or universal Diophantine compiler follows from the reviewed interfaces.

## Retained limits and coordination

Pascal separately found an editorial review-coverage error at article 58499ff and in the guide: the old 2,468 count was called “manuscript” lines. I independently recomputed the inert old receipt: **1,665 TeX lines + 803 other archive-member lines = 2,468**, with old context reads separate. The original wording and correction belong in Pascal's publication audit; this note does not silently inherit inflated manuscript coverage. No additional concrete mathematical defect was found in the selected chain.

The unreviewed truth, external-spectrum, inaccessible/beta-model, full-source reconciliation and bibliography claims retain their source status. No external assertion concerning published reverse-mathematical results or the current status of an open problem is certified here. Source questions outside the two explicitly proved strengthenings remain credited questions. This review supplies bounded independent proof evidence and exact locators, not a replacement for the whole publication audit.
