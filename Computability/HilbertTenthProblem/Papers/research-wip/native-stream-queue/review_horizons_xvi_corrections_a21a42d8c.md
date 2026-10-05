# Bounded review of the four Part XVI corrections at a21a42d8c

**Result: the intended nonempty-domain results and the GB completion theorem remain sound, but two empty-case proof steps still need clarification.** The new text correctly identifies the old notation/dependency and domain issues. It does not yet fully propagate the nonempty hypotheses through the digit-map and converse arguments. This note qualifies the earlier bounded review; it does not retract the GB completion theorem or certify the whole Part XVI or XVII.

Immutable commit: `a21a42d8c27f62ac3443393f88adfeb3d5f6f265`; parent: `5a69916e8d753a2cbfab5afa9fa9c22cda0971bd`. Article: `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/article.tex`. The parent is the same article blob reviewed at62b16914e.

## 1. Theorem XVI.6.21: notation and the dependency summary

The bounded-specialization lemma at current53008–53025 calls its term class **T**. The old proof's two occurrences of `Tm` pointed unambiguously at that lemma but used an undeclared different name. Replacing them with T is a typographical correction, not a changed hypothesis or theorem.

The first sentence's old “source35's proofs use global choice only” summary was overbroad as a statement about its cited dependencies: the FPE corollary imports the GBC history/comparison equivalence. However, **item(4) of the old proof already replaced that cited equivalence by its GB version**. The new opening sentence accurately acknowledges this replacement. There is no missing global-choice elimination in the theorem's actual argument and no new mathematical counterexample to its conclusion.

I reread the whole corrected statement/proof and the bounded-specialization and FPE interfaces. The class of nonempty set subsets having minima is elementary in the supplied order; the uniform finite-code stage predicate has only set quantifiers, so internal induction is available. The added explanation that the finite-trace definitions agree with P at successive stages is consistent with the construction; it does not introduce an external standard-n induction or an unprovided class recursion. The fixed-point completion still requires its supplied initial seed embedding. These conclusions retain the earlier proof review's scope rather than recertifying all its dependencies afresh.

The dated paragraph at55330–55340 retains both old defects and the exact dependency counterevidence. Its **content** satisfies retention. It is not, however, a numbered remark: it is an unnumbered merge paragraph after the theorem/proof. If the standing rule's numbered-remark format is applied literally to the false dependency summary, give this retained explanation an explicit review-remark number or locator without changing the theorem numbering. The mere Tm typo does not require inventing a mathematical counterexample.

## 2. Remark XVI.5.24: a real domain omission, now corrected

The exact-tower definition at54045ff requires **W nonempty**, but permits an empty exponent schedule Gamma. The canonical-history definition at53258–53286 requires **both W and Gamma nonempty**, and its first slice is indexed by `min Gamma`.

The old universal passage from an exact tower to a canonical history therefore exceeded the definition's domain. Take **Gamma empty and W a singleton**. The only stage is infinity; its equality relation is also universal, so it is an exhausting exact tower. But no canonical history on Gamma+1 is defined by the stated nonempty-Gamma convention. This is not merely a spelling error, nor a refutation of the nonempty theorem. It is a concrete failure of the old unconditional domain claim.

The new nonempty-Gamma hypothesis repairs that statement. The added explanation inside the already numbered Remark XVI.5.24 explicitly gives the empty-schedule example and preserves the old omission on record. That is an adequate mathematical and retention correction.

For nonempty schedules, the proof still works: convex class minima give floors; successor condensation agrees with D_W; union of equivalences at a limit becomes intersection of representative classes; and stabilized floors give the converse. No additional class-choice principle is introduced.

## 3. Remark XVI.5.29: a correct distinction, but an empty branch is missing

The source question at66321–66327 distinguishes the initiality of the **supplied tower's** canonical Phi from a potentially different compression with a weaker axiom bound. The old response answered only the conditional Phi interpretation while presenting it as an answer to the whole second question. Calling that an ambiguity or an incomplete response is more accurate than calling the initiality theorem false.

The new separation is sound. Given a tower on the valid nonempty history domain, identifying its digits with the normal form proves initiality over GB. Requiring an appropriate initial map for **every input order**, rather than merely using a supplied tower, is the CWO-equivalent existence principle at53477–53535. The coefficient-one monomials give ordinary embeddings into P(W) without that principle. The “cost” here is axiomatic strength, not a paid ordinary-integer gate count. The old answer is quoted and its scope corrected within the numbered remark, so this distinction is retained appropriately.

There is nevertheless a remaining proof-domain issue at54238–54240. The new remark still starts with an **arbitrary supplied exhausting exact tower** and immediately obtains H from XVI.5.24. Such a tower allows Gamma empty, while the newly corrected XVI.5.24 now excludes it. The final claim about Phi is true in that case, but this intermediate H is undefined.

The repair is short: if Gamma is empty, exhaustion of equality forces W to be a singleton, `P(empty)=1`, and Phi is the unique isomorphism to that singleton, hence initial. Then assume Gamma nonempty before invoking the history. This proves the endpoint for every supplied exhausting tower without silently extending the definition of canonical history.

## 4. Remark XVI.5.31: the last clause is fixed, but the first tower step also has a domain

The newly restricted last clause correctly says that the embedding/initial-image equivalence becomes a terminating-history equivalence **for nonempty W and Gamma**. These are exactly the hypotheses of the cited fixed-schedule criterion. The old clause had the same empty-schedule counterexample as XVI.5.24: `W=1, Gamma=empty` has an initial embedding into `P(empty)=1`, but no canonical history under the printed definition. Empty W is outside that history definition as well.

The first part of the remark, however, still quantifies over “a class well-order W” and says that its exact tower exists. At **W empty**, an order embedding into P(Gamma) exists and its image is initial, but the printed exact-tower definition applies only to nonempty W. The inherited conditional-converse proposition immediately before the remark has the same literal domain issue. This is an undefined intermediary under the present convention, not a counterexample to the endpoint `W embeds into P(Gamma) iff W initially embeds`.

A precise repair is to handle empty W first by its empty initial embedding, then handle empty Gamma with W nonempty by `P(empty)=1`, forcing W to be a singleton. Only after those cases should the proof invoke the exact tower and the nonempty history correspondence. When quoting the inherited proposition, its tower assertion should be understood or restated on its defined nonempty-W domain, with that clarification retained. An alternative is an explicit extension of the tower convention to empty carriers, but no such extension should be assumed silently.

The current dated sentence in XVI.5.31 acknowledges the missing hypotheses, but gives no explicit counterexample there and does not resolve the first tower step. The singleton/empty-schedule example above, or a precise cross-reference to the retained counterexample in XVI.5.24 together with the empty-W case, would complete the numbered retention record. These are small domain repairs; they do not add choice or ETR to the substantive nonempty proof.

## 5. Qualification of the earlier review and current status claims

The frozen `review_beyond_ord_gb_62b16914e.md` (SHA-256 `f79d9caf8a3d51c9b7850d8833b04650ea7f6d60dca26bf847bfa3f019c027e6`) said that taking minima of an exact tower gives the history and passed the digit-map/converse chain without recording these empty-domain qualifications. My publication review `review_beyond_ord_write_62b16914e.md` (SHA-256 `0c584cb04115c93ca476b1dc8f93a6f5551b23412597960105e34cdb6d21861c`) reported that pass. **Those statements need this explicit scope qualification.** The frozen notes should remain unchanged as historical evidence of what was checked and what was missed.

The GB completion result, the nonempty tower/history equivalence and the digit-map endpoint survive. The earlier statement that empty input orders create no exceptional **choice requirement in the completion construction** is not refuted by an empty schedule falling outside a different definition. Nor did either earlier note certify all Part XVI. This follow-up should therefore record the overlooked domain details, not turn a local correction into a claim that the main theorem or whole report is false.

The current status paragraph at58875–58892 attributes a separate unshipped working-note check to the batch97 write. I cannot authenticate that note. Its intended nonempty conclusions agree with this review, but a blanket claim that all remark proofs are now fully repaired should be qualified until the two residual empty-case steps above are addressed.

## 6. Exact evidence scope and limits

The companion JSON pins the immutable article before and after, the raw article diff, and every inclusive span listed here. After-image blob: `94dc646dac6942c82eb0f12f7a8ee75b8c8a011a`, SHA-256 `a5108202c9094a511f2e628318f8c5f54da9b3b116fe9e8c804fa0c16577d9c5`. Before-image blob: `a4c1c5a049e864b44c25cefe0fdaee218451b013`, SHA-256 `31d10373d5fe12073c40ad1113d8fe6b0c6ef9138fa6ac233c73641f32425300`.

Current article reads:53000–53055,53245–53292,53465–53582,53955–54348,55085–55170,55212–55358,58865–58916,66312–66347: **937 lines**. Parent reads:53735–53836,53903–54003,54888–55000: **316 lines**. The focused unified-eight-context diff read is lines515–696: **182 lines**. The initial oversized diff output was truncated and is not counted as a full read. The raw diff hash is `a7ec4959a8a578f173c7806260209238e7061de214c46c14711fcae068f9b2b3`.

Incoming instructions414–444, including the retention rule, were read; the applicable182-line AGENTS file was previously read in full and verified unchanged. Relevant earlier-review passages were reread and pinned separately. The new PartXVII material, whole guide diff and its arithmetic publication review belong to Aristotle's separate packet. I do not import its unread proof coverage.

Only inert Git/text extraction and hashing utilities were used. No supplied, archived, frozen, predecessor or new mathematical helper was executed or imported; no replay, build, external-source audit, repository edit or Git mutation occurred. The JSON is a scope/pin record, not an executable proof receipt. No fixed-arity integer compiler or new arithmetic-operation bound follows from these corrections.
