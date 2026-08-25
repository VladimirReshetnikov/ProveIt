# Submission notes for the Fabius function Wikipedia draft

Companion to `Fabius_function (Wikipedia draft).txt`. This is a decision document, not a
recommendation to publish or withhold.

## 1. Current state of the draft

The draft is a full rewrite of [Fabius function](https://en.wikipedia.org/wiki/Fabius_function),
roughly 31 KB of wikitext against the live article's 6.7 KB. Everything the live article contained
is now present, including material an earlier version of the draft had dropped (the two OEIS
citations on the dyadic values, the Alkauskas Thue–Morse preprint, the Dimitrov thesis full-text
link, the `Volodymyr Rvachov` and `Delay differential equation` wikilinks, the `s2cid` and
`doi-access` parameters, and the recursive characterization `F(x + 2^r) = -F(x)` of the signed
extension). Factual and MoS errors identified in review have been corrected, the notation
conventions have moved out of the lead into a short `== Notation ==` section, the lead is three
paragraphs, and the asymptotics material has been tightened from about 30% to about 25% of the
article body without dropping any result. Attribution to V. Reshetnikov for the integrality
question and for the Rvachev evaluation algorithm has been added and cited to the published
Arias de Reyna paper. Six blocks that are sourced only to the author's own unpublished GitHub
repository are now each preceded by a visible HTML comment reading
`<!-- REVIEW NOTE: unsourced-to-published-literature. See submission notes. -->`; the content of
those blocks is unchanged and no decision has been made about it.

## 2. Conflict of interest

Stated factually:

- The draft's author is Vladimir Reshetnikov. The source paper, Juan Arias de Reyna,
  "Arithmetic of the Fabius function", *Integers* **18** (2018), #A51, contains a section titled
  "Reshetnikov's Question" and a numbered statement "Question 1 (V. Reshetnikov)" for exactly the
  integer sequence the draft calls `R_n`. The paper cites the author's MathOverflow question 261649
  (7 February 2017) as reference [11], and cites Mathematica Stack Exchange question 120331 as
  reference [3], crediting the author's answer there with bringing the Rvachev evaluation algorithm
  to the paper's attention.
- The same author wrote the live article's existing `== Asymptotic ==` section, in edits dated 2021
  and 2025. That section carries no citation on the live article.
- The draft cites the author's own GitHub repository (`VladimirReshetnikov/ProveIt`) 12 times
  across 11 lines: 10 to `ASYMPTOTIC_COMPLETION_AUDIT.md` and 2 to the `Analysis/FabiusFunction`
  Lean 4 sources.

Wikipedia's conflict-of-interest guidance ([WP:COI](https://en.wikipedia.org/wiki/Wikipedia:Conflict_of_interest),
and [WP:SELFCITE](https://en.wikipedia.org/wiki/Wikipedia:Conflict_of_interest#Citing_yourself) for
citing one's own work) asks an editor in this position not to edit the affected article directly,
but to post the proposed text on the article's talk page as an edit request (`{{edit COI|answered=no}}`)
with a disclosure, and to let an uninvolved editor decide whether to apply it. The relevant sourcing
policies are [WP:SPS](https://en.wikipedia.org/wiki/Wikipedia:Verifiability#Self-published_sources)
(a GitHub repository is a self-published source) and
[WP:NOR](https://en.wikipedia.org/wiki/Wikipedia:No_original_research).

Directly replacing a 6.7 KB article with a 31 KB rewrite that cites the editor's own unpublished
repository a dozen times, without disclosure, is the highest-risk possible route: it combines a
large unreviewed change, a self-citation to a self-published source, and an undisclosed COI. The
most likely outcome is a wholesale revert, which would also lose the well-sourced expansion.

## 3. Claims sourced only to the author's GitHub repository

| # | Claim | Location in the draft |
|---|---|---|
| 1 | Sharp decay near zero is governed by the lower Lambert branch plus a non-vanishing periodic correction of amplitude about two parts in a million | Lead, third paragraph |
| 2 | Closed formula for the Fourier–Legendre coefficients `a_n` in terms of `F(2^{-2k-1})`; absolute and uniform convergence including at the endpoints | `=== Fourier–Legendre expansion ===` |
| 3 | "A sharp description requires both the Lambert W function and a logarithmically periodic correction" | `== Asymptotic behaviour near zero ==`, opening paragraph |
| 4 | Definition of the sharp main term `M(x)` (with constants `C_0`, `7L/12`, `-½log(πx)`) and the estimate `log F(x) = M(x) + O(1/(-log x))` | `=== Sharp Lambert-W form ===` |
| 5 | Existence, smoothness, one-periodicity and mean-zero normalization of `Ψ` | `=== The periodic correction ===` |
| 6 | The gamma–zeta Fourier series for `Ψ` and its absolute convergence | `=== The periodic correction ===` |
| 7 | Every Fourier coefficient of index `k ≠ 0` is nonzero; `Ψ` is nonconstant; amplitude ≈ 2.1 × 10⁻⁶ | `=== The periodic correction ===` |
| 8 | Expanded elementary asymptotic in `ℓ, a, b` **including the `Ψ(λ(x))` term** | `=== Expanded elementary form ===` |
| 9 | Dyadic expansion of `log F(2^{-n})` **including the `Ψ(λ_n)` term** | `=== Expanded elementary form ===` |
| 10 | Exact dyadic-scale decomposition of `log D(-s)` with one-periodic `R` and the bound `|E(s)| ≤ e^{-s}/(1-e^{-s})²` | `=== Origin of the logarithmic oscillation ===` |
| 11 | Full saddle-point expansion with one-periodic coefficients `P_j`, and the explicit formula for `P_1` | `=== Full saddle-point expansion ===` |
| 12 | Scope of the Lean 4 formalization (what is verified, and the `F` / `𝓕` separation) | `== Formal verification ==` |

Notes on this table:

- Rows 8 and 9 are the two displays that already appear in the live article's `== Asymptotic ==`
  section, where they carry no citation at all. The draft adds the `Ψ` term to both and attaches a
  citation. The bare displays are therefore not new to Wikipedia; the `Ψ` term is.
- Row 3 is a framing sentence rather than a mathematical result; it could be rewritten to cite only
  Arias de Reyna if the surrounding subsections were deferred.
- Row 12 describes the repository itself. Even if kept, `WP:SPS` allows a self-published source only
  for uncontroversial claims about itself, and notability of the formalization is not established by
  the repository.
- Rows 1–11 have no published-literature source known to this review.

## 4. Two-stage submission plan

**Stage 1 — the well-sourced expansion, via a talk-page edit request.**

Submit everything that is cited to Arias de Reyna (1982/2017 and 2018), Jessen–Wintner (1935),
Fabius (1966), Rvachev (1990), Haugland (2016), the OEIS sequences and the Alkauskas preprint:

- `== Notation ==`
- `== Definition and elementary properties ==`
- `== Probabilistic and convolution constructions ==`
- `== Rvachev's up function ==`, including the Fourier transform, the partition-of-unity and cosine
  series subsections, and the general (non-explicit) part of the Fourier–Legendre subsection
- `== Signed global extension and non-analyticity ==` (the Thue–Morse extension)
- `== Moments and generating functions ==`
- `== Dyadic values and exact computation ==` and `=== Arithmetic of reciprocal-power values ===`
- `== History ==`
- the corresponding lead paragraphs, See also, References, Further reading and External links

Post this on [Talk:Fabius function](https://en.wikipedia.org/wiki/Talk:Fabius_function) as
`{{edit COI|answered=no}}` with a `{{connected contributor}}` disclosure naming the two connections
(named in the source paper; author of the live Asymptotic section). Keep the live article's
`== Asymptotic ==` section unchanged in this stage, so the request is purely additive and reviewers
are not asked to evaluate unsourced material at the same time as a large expansion. Mention in the
request that the OEIS, Alkauskas, Dimitrov and Rvachov links from the current article are all
preserved.

**Stage 2 — the asymptotics, deferred.**

Hold rows 1–11 of the table above until the results appear in a peer-reviewed venue (a journal
paper, or a refereed conference), then propose them in a separate, much smaller edit request citing
that publication. An arXiv preprint alone does not resolve `WP:SPS`, though it is a substantial
improvement over a repository link. Until then, the material stays in this repository, and the
review-note comments in the draft mark exactly which blocks are affected. If the live
`== Asymptotic ==` section is to be touched at all before then, the minimal, lowest-risk change is
to tag it `{{citation needed}}` or `{{unreferenced section}}` rather than to extend it.

## 5. Note on presentation weight

The periodic correction `Ψ` has amplitude about 2.1 × 10⁻⁶ in `log F`, i.e. it changes `F` by
roughly two parts in a million. Its mathematical interest is that it does not tend to zero, so no
asymptotic formula omitting it is exact — not that it is numerically large. The presentation weight
given to it should be proportional to that: one clear statement of the fact, not a section
structure that makes the oscillation look like the article's main subject. This is also the
practical answer to a `WP:UNDUE` objection.

## 6. Edits applied by this pass

Restorations of live-article content the draft had dropped:

1. `{{cite OEIS|A272755}}` and `{{cite OEIS|A272757}}` on the table of exact dyadic values.
2. The Alkauskas (2001) Thue–Morse preprint, with its `web.archive.org` link, cited in the signed
   global extension section.
3. The Dimitrov thesis full-text URL (`rave.ohiolink.edu`), keeping the added `institution` field.
4. The `[[Volodymyr Rvachov]]` wikilink (lead and Further reading) and `[[Delay differential equation]]`.
5. `s2cid=122126180` on Fabius (1966) and `doi-access=free` on Jessen–Wintner (1935).
6. The recursive characterization `𝓕(x + 2^r) = -𝓕(x)` for `0 ≤ x ≤ 2^r`, restored alongside the
   Thue–Morse sum, and the word "unique" in the statement that the extension exists.
7. Additionally restored: the OEIS A288163 citation on the up function.

Corrections:

8. The tautology "Every nonzero Fourier coefficient in this series is nonzero" replaced by a
   statement that the coefficient of index `k` is nonzero for every `k ≠ 0`, because the gamma
   function has no zeros and the zeta function has no zeros on the line `Re s = 1`, on which
   `1 - χ_k` lies.
9. "the nonzero zeros of `û` are precisely the nonzero integers" → "the zeros of `û` are precisely
   the nonzero integers", with `û(0) = 1` stated explicitly just above.
10. `(n ≥ 1)` added to the 2-adic valuation formula, which fails at `n = 0`.
11. Lead and body made consistent: `F : ℝ → [0,1]` in both.
12. The normalization for the up function's uniqueness made explicit: unique up to a constant
    factor, with `∫ u = 1` fixing the factor.
13. The 1971 attribution rephrased to match the cited source, which credits V. A. Rvachev in its
    numbered history while listing both Rvachevs on the 1979 monograph.
14. Three `<ref name="..."/>` tags that began a line immediately after a `</math>` block (which
    MediaWiki renders as a stray floating superscript paragraph) moved onto the preceding sentence.

Manual of Style and `WP:NOTTEXTBOOK`:

15. `\boxed{}` removed from both formulas. The main asymptotic term is now named `M(x)` where it is
    first stated, and later sections refer to it by name rather than to "the boxed" term.
16. Derivation-chain phrasing trimmed to statements of results ("It follows that…", "Conversely,
    this integral equation … determines F", "This gives a direct proof that…", "This gives exact
    rational arithmetic rather than numerical quadrature", and the errata-style note about
    truncating the phase).
17. Notation conventions moved from the lead into a short `== Notation ==` section; the lead cut to
    three paragraphs; the oscillation sentence rewritten in plain language, with "order-one error"
    replaced by an explicit statement of the amplitude and of the fact that it does not tend to zero.
18. `[[Infinite convolution]]` removed from See also (no such page).
19. Short description shortened to "Smooth nowhere-analytic function" (32 characters).
20. `{{Use British English}}` added, so `{{Use dmy dates}}` and "behaviour" are now consistent.
21. Arias 1982 converted from `{{cite arXiv}}` to `{{cite journal}}` with `|arxiv=1702.05442`,
    *Rev. Real Acad. Ciencias* (Madrid) **76** (1982), 21–38; the unsupported "no. 1" dropped.
    Haugland's year corrected from 2020 to 2016 (reference renamed accordingly).
22. Citations added to previously uncited blocks: the moments and convolution paragraphs, the
    Fourier inversion and rapid-decay paragraph, and the cosine series paragraph.

Attribution:

23. The integrality of `R_n` is now stated as answering a question of V. Reshetnikov, cited to
    Arias de Reyna (2018) and to the MathOverflow question the paper itself cites
    (`mathoverflow.net/questions/261649`, 7 February 2017). The History section notes the same.
24. The recursive evaluator is now credited to V. A. Rvachev, reached via V. Reshetnikov's answer on
    Mathematica Stack Exchange, cited to the question the paper cites
    (`mathematica.stackexchange.com/questions/120331`, asked by Pierrot Bolnez, 9 July 2016).
    The paper cites the question, not the answer permalink; no answer id appears in the paper.

Unsourced-material handling:

25. `<!-- REVIEW NOTE: unsourced-to-published-literature. See submission notes. -->` inserted
    immediately before: `=== Sharp Lambert-W form ===`, `=== The periodic correction ===` (the
    gamma–zeta Fourier series, now its own subsection so the note has a clear scope),
    `=== Origin of the logarithmic oscillation ===`, `=== Full saddle-point expansion ===`,
    `== Formal verification ==`, and the explicit Fourier–Legendre coefficient formula. No
    mathematics was deleted.
26. Asymptotics tightened from about 30% to about 25% of the article body: the exponentiated
    restatement `F(x) ~ 2^{-7/12}/√(πx) · exp(…)` (a pure restatement of the `log F` formula) and
    the redundant `N = 2` special case of the saddle-point expansion were removed, and the
    proof-sketch paragraphs in "Origin of the logarithmic oscillation" and "Full saddle-point
    expansion" were compressed into statements. Every result in the section is retained.
</content>
