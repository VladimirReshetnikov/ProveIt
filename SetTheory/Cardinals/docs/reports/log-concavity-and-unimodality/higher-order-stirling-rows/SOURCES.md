# Sources and status check

Access dates: 19 September 2026 (first source draft) and 20 September 2026
(second source draft). Both drafts performed the check independently and
reached the same conclusion; the merged report records both.

## Originating statement

Bishal Deb and Alan D. Sokal, *Higher-order Stirling cycle and subset
triangles: Total positivity, continued fractions and real-rootedness*,
arXiv:2507.18959v1, submitted 25 July 2025.

```text
https://arxiv.org/abs/2507.18959
https://arxiv.org/html/2507.18959v1
https://arxiv.org/pdf/2507.18959
```

Definitions: equations (1.3)–(1.4), printed page 6.
Recurrences: Lemma 1.1, equations (1.13)–(1.14), printed page 7.
Selected statement: **only the log-concavity assertion** in Conjecture
1.4(c), printed page 10. This includes all rows for orders r=1,...,5.
Additional statement: the row-log-concavity assertion in Conjecture 1.3(c).
The present article proves its cases r=1,...,4, not r=5.
The source's finite verification reports are Appendix C, Tables 1 and 2,
printed page 51; they report testing log-concavity through n=1000.

The relevant PDF pages were visually inspected to check formulas and the
tables against the parsed HTML/text. The arXiv abstract page displayed
only v1 in its submission history at the time of access.

## BCC30 problem statement

Peter Cameron (editor), *Problems from BCC30*, arXiv:2409.07216v1, 2024.
Problem 30.9, presented by Bishal Deb, states the **cycle** conjecture for
r=3,4,5. It is not a separate source for the subset conjecture.

```text
https://arxiv.org/abs/2409.07216
https://arxiv.org/html/2409.07216v1
```

## Recurrence-criterion background

Bruce E. Sagan, *Inductive and injective proofs of log concavity results*,
Discrete Mathematics 68 (1988), 281–292. Theorem 1 on printed page 282
assumes nonnegative pure and mixed contributions in the recurrence proof.
That page was inspected as an image because the scanned text is garbled.

```text
https://doi.org/10.1016/0012-365X(88)90120-3
https://users.math.msu.edu/users/bsagan/Papers/Old/iip-pub.pdf
```

Umesh Shankar, *Log-concavity of rows of triangular arrays satisfying a
certain super-recurrence*, arXiv:2508.12467v1, 2025. The introduction and
Theorems 1.2–1.4 were inspected to distinguish its results and parameter
families from this article. The present proof is self-contained and does
not invoke those theorems. Theorem 1.2 there records the same
coefficient-sign criterion (P, Q, M >= 0 in its letters; A, B, H >= 0 in
ours) that Sagan's Theorem 1 gives; the merged article cites both, since
they are independent sources for the condition that the present criterion
relaxes. Section 1 of that paper also defines a *different* family of
generalized Stirling numbers, the r-Stirling numbers, which require certain
distinguished elements to lie in distinct blocks. They must not be
conflated with the shifted associated subset triangle treated here.

```text
https://arxiv.org/abs/2508.12467
https://arxiv.org/html/2508.12467v1
```

## OEIS connection

OEIS A134991 records the Ward triangle: the nonzero columns of the
second-order subset triangle in the article's indexing.

```text
https://oeis.org/A134991
```

No claim is made that the higher-order row-sum sequences in the data
are absent from OEIS or are newly discovered sequences.

## Attribution and scope

The underlying combinatorial objects, their recurrences, and the target
conjecture are from the cited literature. What this report offers as its own
contribution is the fifth-order certificate in its several forms, the
induction, the quantitative bound, the sharpness argument, the cycle
extensions and the cycle obstruction, the interpolating family, the
asymptotic explanation of the cutoff, and the accompanying checks. No
exhaustive novelty claim is made for the general two-variable preservation
lemma, for the elementary identities, or for the small counterexamples.

## Search and priority limitation

The status check used the exact source identifier; exact-phrase searches
for higher-order Stirling with log-concavity; and arXiv searches for
higher-order Stirling, Stirling log-concavity, and Deb/Sokal author terms.
The returned relevant sources continued to present the selected statement
as a conjecture. No later resolution was located in those searches.
This is not an exhaustive bibliographic review and does not establish
priority. It also does not imply that every generic lemma or elementary
identity in the article is new.

The original source PDFs are not redistributed. The archive contains the
new report, its own proofs, executable checks, and generated data.
