# A279551/A279556: bounded publication review and an all-length support boundary

This review is pinned to content commit `80adcb9101de0af8792ff52023fd1710217bf5c0`, whose parent is `ed4d0a12f6c1bbd9723ac2b801472af50dd84760`. It concerns the directory `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279551-inversion-log-deficit/`. The commit rewrites the README and article TeX and adds the PDF. This is a bounded interface review, with one elementary support theorem and one conditional check of a short refutation. It is not a full asymptotic proof audit or a claim that the report advertises Turing universality.

## 1. Exact result and its scope

The report joins the logarithmic-deficit work of Reports 126, 127 and 129. Its weighted enumeration and asymptotic claims concern two nontrivial counting sequences. However, the particular unweighted question “is there a terminal path of length n?” has answer yes for every integer n >= 0, for both displayed commitment trees. Consequently, choosing the length alone as the input and testing this terminal support supplies no nontrivial acceptance predicate. No new fixed-program universal substrate or paid fixed-arity Diophantine compiler is obtained from that support interface.

The statements below do not exclude using exact counts, extra constraints, different initial or terminal conditions, an enriched machine, or another encoding. Such a construction would need its own proof and arithmetic accounting. No complete compiler count or improvement is asserted here.

## 2. An explicit path for each length, in both classes

Article lines 292–335 specify a root `(0,0)`, a unit ordinary edge `(p,c) -> (p+1,c)`, and boundary edges

`(p,0) -> (p-ell,b)`, where `0 <= ell <= p-1`,

of multiplicities `M_759(ell,b) = C_b binom(ell,b)` and `M_247(ell,b) = C_b binom(b+1,ell-b)`. Here `C_b` is the Catalan number, and out-of-range binomials are zero. The source separately explains the `b=0` suffix rule: `M_759(ell,0)=1` for `ell>=0`, and `M_247(ell,0)=1` for `ell=0,1`. In particular, `ell=b=0` gives a unit self-loop at every `(p,0)` with `p>=1`. This self-loop is already explicit in the report; the consequence for the proposed support interface is the present review's deduction.

The terminal sets are `T_759 = {(p,0): p>=0}` and `T_247 = {(p,0): 0<=p<=2}`. At `n=0`, the empty path ends at the terminal root in both classes. At any `n>=1`, take one ordinary edge `(0,0)->(1,0)` and then exactly `n-1` copies of the boundary self-loop at `(1,0)`. Each boundary edge satisfies `0<=ell=0<=p-1=0`, has multiplicity one, and preserves `(1,0)`, which belongs to both terminal sets. Thus this is a legal terminal path of exactly n edges and total multiplicity one in each class. The terminal restriction for class 247 is respected at every step; the argument does not count its nonterminal long all-zero access paths.

There is also a direct witness in the original definitions (article lines 202–211), independent of the full tree/counting correspondence: use `e_i=i-1` for `1<=i<=n`, or the empty sequence at zero. These entries satisfy `0<=e_i<i`. For any `i<j<k`, one has `e_i<e_k`, so the prohibited conjunction containing `e_i>=e_k` fails. This sequence belongs to both avoidance classes. Hence both counts are at least one at every length, without invoking the report's all-size decorated-history bijection or analytic estimates.

**Review boundary 1 (support versus weighted information).** The inference “non-D-finiteness or a nontrivial deficit supplies an undecidable nonzero-count predicate in n” would be false for these two classes: their nonzero support is all nonnegative integers. This is a boundary on an attempted substrate interpretation, not a claim made by the report. The displayed paths do not determine the full counts, their growth, or any differential-equation property. At each fixed n the original definition also gives a finite exact enumeration over `0<=e_i<i`; this is a decidability observation, not a bounded-operation or fixed-arity arithmetic compiler.

## 3. Conditional check of the retained external asymptotic refutation

The new Remark 1.2 (article lines 256–271) retains the external numerical proposals, credits Britt and Beaton's stated non-rigorous status, and distinguishes them from their exact trees and finite enumerations. The external paper has not been independently checked in this review. The following is a check of the implication printed in the new report, conditional on its Theorem 1.1.

Let `psi(n)=n^(1/3)(log n)^(2/3)`. Assume the asserted eventual two-sided bound `c psi(n) <= D_j(n) <= C psi(n)`, with positive c,C. An equivalent

`a_j(n) ~ A n^g mu_j^n exp(-b n^beta)`, with `A>0` and real g,b,beta,

would give `D_j(n)=b n^beta-g log n-log A+o(1)`. Since `log n=o(psi(n))`, all cases contradict the assumed bounds. If `b<=0` or `beta<=0`, the first term is bounded above and the deficit has an `O(log n)` upper bound. If `b>0` and `0<beta<=1/3`, then `n^beta=o(psi(n))`. Both cases contradict the lower bound. If `b>0` and `beta>1/3`, then `n^beta/psi(n)->infinity`, contradicting the upper bound. These cases exhaust the stated parameter range. In particular, `beta=3/8,b>0` would give `D_j(n)/n^(3/8)->b`, whereas the upper bound gives a quantity at most `C n^(-1/24)(log n)^(2/3)->0`.

**Retained claim 2 (external pure-power equivalent).** The report's retained `n^(3/8)` proposals and its broader pure-power family are therefore refuted as full equivalents if Theorem 1.1 holds. This narrow implication passes by hand. It does not independently validate that theorem, disprove the usefulness of finite fits, or challenge the imported exact combinatorics. The larger publication statement that no wrong claim was found in any manuscript is not promoted here to an independently established fact. No new report error was found in the selected material.

## 4. Computational connection and missing bridges

The full guide and three companion guides distinguish mathematical arguments from bounded checks. The article's verification sections make the same distinction; Part III explicitly says that finite checks do not certify asymptotic uniformity, martingale convergence or infinite tails (lines 3743–3745). Section 39 labels the new residual table as a hint and says it proves nothing (lines 3762–3776). All execution, count, floating-point, build and rendering claims are reported source claims only in this review.

The selected interface provides exact local transition multiplicities and terminal extraction. It does not in these spans provide a fixed program alphabet with an ordinary-input map for arbitrary computation, a finite-arity unbounded-history arithmetic encoding, or a paid whole-source operation ledger. Non-D-finiteness is a statement about the generating function, not such an interface. The useful next-action boundary is therefore to avoid pursuing bare terminal support as the acceptance mechanism.

**Open question 3 (a different arithmetic interface).** Could exact weighted-count information or an explicitly enriched commitment system admit a useful native coefficient relation, fixed-arity history certificate, and operational universality proof? This is a question posed by the review, not an unresolved theorem asserted by the authors. The present positive-support theorem supplies none of these missing bridges and rules out none of them in another formulation.

## 5. Immutable binding and actual read scope

All sources were read through `git show` at the content commit above. The whole main README and its complete parent-to-content textual diff were read. The article was read only in the selected spans below; its complete diff and remaining analytic proofs were not read. Commit message, changed-path list and diff navigation were also inspected. The companion guides were fully read. These semantic reads comprise 1,064 guide lines plus 525 article lines, or 1,589 source lines in total, excluding diff rereads. No guide is mislabeled as a full article audit.

| Relative file | Whole bytes / lines | Git blob | Whole SHA256 | Semantic read |
|---|---:|---|---|---|
| `README.md` | 28634 / 497 | `7c498e8a54a169c3930dca3a93d57a2d606322f8` | `7d596edc47bc439b7d0af8cc6467601587f63c661ddb5f8362e1da860b17a1b1` | Full 1–497; full README diff |
| `article.tex` | 213789 / 3823 | `07dbf0e7ce08b90f1fbeaf8555acfbbc4cf4a64a` | `5f67900ec89287daf9fa8f6de94be1520d8d8d56eff25f38e2ead8dab4766108` | 55–165; 201–427; 1155–1200; 2568–2609; 3725–3823 |
| `126-scale-checks-README.md` | 11486 / 190 | `24a5a9baf266a61e0cc9376cac24bbec2923c289` | `362cabe16cb2d7215dddd0c8e7555874a7bda8c5a5d731e9e0d0d61c45436583` | Full 1–190 |
| `127-sharp-checks-README.md` | 11601 / 190 | `6f8466e5d8daccc45fa031d2a2170abd28dfc546` | `3acaf71ad6d047e1ea4bc5a9af3b3f33dad65083ae8f3a446244840f18a20aa0` | Full 1–190 |
| `129-loglog-checks-README.md` | 11368 / 187 | `2dcb2747cce4d96757fb08a63b7713d6bee48f1a` | `91fefc04ec06ba57f387a9b092feb7abeae38c39594bc61c9da1ed1e7358783c` | Full 1–187 |

The accompanying JSON records exact span bytes and hashes and the README diff binding. The new PDF was authenticated as bytes only: 905640 bytes, Git blob `3646a9d0237404d4ffa7caa78ed6d6f64cf1cdfa`, SHA256 `289d0b4f899bd9957f9b9882059235685e59e848f7a09d18df8411d2b289aad2`; it was not read, rendered or rebuilt. No source/helper execution, imports, saved-array evaluation, coefficient computation, numerical experiment or build occurred. Fresh standard-library byte/span/hash metadata and read-only Git commands were used. No repository or Git mutation occurred.

Frozen after root's independent full 59-line draft challenge, PASS with no correction. Root separately checked the definitions at article 201–211, the exact tree/terminal/suffix loop at 292–335, the direct increasing avoider, and the conditional all-parameter refutation at 256–271. This corroborates only the bounded claims above, not a complete asymptotic theorem audit. Final changes were provenance only.
