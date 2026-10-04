# Sources and research provenance

Consultation date: October 3, 2026. Dates appearing in the manuscript are
research dates, not inferred modification dates of external pages.

## Primary OEIS sources

1. https://oeis.org/A182220
   Definition of the maximum number of sources; displayed sequence;
   conjectural logarithmic formula attributed to Antti Karttunen (2013).
   A formula from August 2026 also appears in the consulted entry.
   The footer's site-wide modification time is not treated as the entry's
   revision date.
2. https://oeis.org/A182162
   Labeled source triangle. Johnston's Maple source sieve (2012) is existing
   mathematics, not a new result of this article. First 25 displayed terms
   are used as exact test fixtures.
3. https://oeis.org/A001192
   Full/transitive finite sets and displayed recurrence; first 17 terms used
   as test fixtures. Bibliographic pointer to Peddicord (1962).
4. https://oeis.org/A182161
   Total labeled extensional acyclic digraphs; n! times A001192.

## Research literature

5. Alexandru Ioan Tomescu, *Sets as Graphs*, PhD thesis, Udine, December 2011.
   https://www.cs.helsinki.fi/u/tomescu/PhDThesis-AT.pdf
   Parsed text consulted in the relevant parts of Chapter 2:
   printed pp. 26-29 (PDF indices 35-38), including:
   - marked-source inclusion-exclusion and total recurrence;
   - rigidity (Lemma 2.1.3);
   - source deletion recurrence (Corollary 2.1.7);
   - explicit bound s <= n-ceil(log2(n)) on printed p. 29.
   The web renderer did not return requested screenshots of these pages.
   The mathematical statements were read from parsed text, not guessed
   from figures; inequalities were reconciled with their equivalent formulas.
6. Alberto Policriti and Alexandru I. Tomescu, *Counting extensional acyclic
   digraphs*, Information Processing Letters 111(16) (2011), 787-791.
   https://doi.org/10.1016/j.ipl.2011.05.014
   Publisher abstract and metadata consulted. Detailed related proofs are
   available in the thesis above; no claim of full independent journal-PDF
   review is made.
7. Stephan Wagner, *Asymptotic enumeration of extensional acyclic digraphs*,
   ANALCO 2012, pp. 1-8.
   https://doi.org/10.1137/1.9781611973020.1
   Publisher abstract and metadata consulted. The author-hosted PDF at
   https://math.sun.ac.za/swagner/DigraphsFull.pdf timed out; the publisher
   PDF route returned an abstract/access page. The article does not rely on
   an unchecked theorem from this source.
8. Richard Peddicord, *The number of full sets with n elements*, Proc. AMS
   13 (1962), 825-828. Bibliographic information verified through OEIS and
   Tomescu's thesis. Original article not independently read.

## Repository

https://github.com/VladimirReshetnikov/ProveIt
Snapshot: 6bf7f30d0352f7596e70928b3d4f304914075907

The repository tree, README, OEIS report directory, and focused code searches
were inspected through the GitHub connector. Searching for A182220 yielded
no matching repository result. This is a limited search, not a complete
semantic duplication audit. No theorem from the repository is assumed.

A promising alternative, growing powers of Mahonian coefficients, was
rejected after finding an existing matching repository report. It is not
presented as new work here.

## Novelty boundary

The upper bound, finite-set correspondence, rigidity, source sieve, total
recurrence, and source-deletion recurrence are classical or explicitly
recorded in prior sources. Exact boundary formulas follow quickly from the
classical sieve, and the article says so.

The fixed-defect entropy profiles, their full growth-rate intervals, the
exponential-jump non-P-recursiveness proof, and the quantitative conditioned
arc law are developed and proved in this manuscript. Searches did not
establish historical priority. No claim is made that these are the first
proofs in the literature or that a major long-standing conjecture has been
settled.
