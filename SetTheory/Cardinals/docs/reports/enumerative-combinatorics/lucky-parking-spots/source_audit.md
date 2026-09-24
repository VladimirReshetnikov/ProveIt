# Source and status audit

Consulted on 19 September 2026.

## Primary target

Steve Butler, Kimberly Hadaway, Victoria Lenius, Preston Martens, Marshall
Moats, *Lucky Cars and Lucky Spots in Parking Functions*, Journal of Integer
Sequences 29 (2026), Article 26.1.1.

https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.pdf
https://cs.uwaterloo.ca/journals/JIS/VOL29/Hadaway/had3.html

The PDF has 18 pages. Its printed page 10 was inspected as a rendered image,
not merely as extracted text. It contains the formulas for columns 3–5,
Conjecture 13 (polynomial degree j-2, rational coefficients, and an unspecified
rational limiting coefficient), and Observation 14 on the last column.
Printed page 11 contains Question 15 about the next-to-last and other fixed
right-distance columns. The target does not include the trivial j=1 case in
its degree assertion; our theorem explicitly separates it.

The associated preprint is arXiv:2412.07873v1, submitted 10 December 2024:
https://arxiv.org/abs/2412.07873
https://arxiv.org/html/2412.07873v1

The preprint numbers the target Conjecture 3.1; this report consistently uses
the journal numbering, Conjecture 13. The journal volume year is 2026; no
claim is made here about the exact day its files first became publicly
available.

## OEIS entries

https://oeis.org/A374756
https://oeis.org/A374533

A374756 has a headline referring to a lucky car, but its comment and examples
refer to a lucky spot. The data in its displayed later rows give only the
first six columns. We compare the published coordinate-wise prefixes,
including all entries through n=6 and the first six entries for n=7..10.
We do not mistake the truncated display for a complete flattened triangle.

A374533 has offset n=2, and its nine displayed terms are
3, 11, 74, 708, 8733, 131632, 2342820, 48068672, 1116809255.
All nine are checked. The entry consulted contained no general formula for
these counts. Our local extension includes n=2..100 and is not submitted to
OEIS automatically.

## Related literature and novelty boundary

Pamela E. Harris and Lucy Martinez, *Parking functions with a fixed set of
lucky cars*, arXiv:2410.08057v1 (2024):
https://arxiv.org/html/2410.08057v1

In particular, its Theorem 2.6 describes counting through outcome permutations
and local preference factors when lucky cars are specified. Our local weight
lemma is related standard machinery and is reproved in full, not claimed
as a novel technique. Specifying a spot while summing over its occupant is a
different marginal statistic.

A related vector-parking paper was also checked:
https://arxiv.org/html/2508.13917v1
Its treatment of outcomes with specified lucky spots is not by itself a
proof of the one-spot marginal formula in this manuscript. It is not used
as a dependency of the proof.

Targeted searches included the exact source title together with "proof" or
"conjecture", "lucky spots" with "formula", "binomial", "reflection", and
"Poisson", and the exact OEIS identifiers. These searches did not locate a
published solution of Conjecture 13. Some queries returned irrelevant
results. A potentially related May 2026 thesis URL surfaced in search but
could not be opened through the available web retrieval; it was not used as
evidence for or against priority. These are limited search results, not a
certificate of exhaustive novelty.

## What is established by this package

The article proves its displayed identities from the parking process using
formal generating functions and Lagrange inversion. The computed checks are
exact finite checks. Neither a journal peer review nor a Lean/other proof-
assistant verification has occurred. No claimed theorem depends on an
unproved empirical pattern, a fit, a floating-point test, or an inaccessible
source.

No cited paper, web page, or font file is redistributed in this package.
