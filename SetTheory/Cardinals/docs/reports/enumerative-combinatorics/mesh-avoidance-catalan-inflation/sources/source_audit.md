# Source audit

Consultation date: September 20, 2026.

## 1. The selected conjecture

**OEIS A289587:** https://oeis.org/A289587

The consulted entry defines the sequence using simultaneous avoidance of
classical 321 and the mesh pattern (12,174), with the inverse pattern (12,234)
giving the same counting sequence. Its displayed initial values run from n=0
through n=16. It labels the radical generating function proved in the article
as conjectural and attributes it to Thomas Scheuerle, December 23, 2025.
The original sequence entry is attributed to N. J. A. Sloane, July 8, 2017,
and the visible offset is 0. The 17 published values used as an external
comparison are

    1, 1, 1, 3, 6, 18, 47, 139, 405, 1225, 3740, 11602,
    36357, 115049, 366969, 1178791, 3809802.

The entry's b-file is at https://oeis.org/A289587/b289587.txt . This archive
does not contain a wholesale copy of the OEIS page or of that b-file.

These are the provenance facts used in the article. The coefficient extensions
through n=200 and through n=1000 are calculated by the included programs and
are not represented as OEIS-provided files.

## 2. Literal meaning of the numerical mesh identifiers

**SeqFan, “RFE Dec 2025: Mesh patterns avoiding 321”:**
https://groups.google.com/g/seqfan/c/9jqIgQGj8Gg

The thread was opened by Sean A. Irvine. Christian Sievers gives the bit
encoding: bit 3*I+J specifies the square (I,J), with each coordinate in {0,1,2}.
He also identifies the pair 174 and 234 among the patterns for this sequence.
The source records independent enumeration, including a(11)=11602,
a(12)=36357, and a(13)=115049.

This encoding gives

    R174 = {(0,1),(0,2),(1,0),(1,2),(2,1)},
    R234 = {(0,1),(1,0),(1,2),(2,0),(2,1)}.

The article and both verifiers use these explicit sets, not an opaque identifier.
I did not locate a proof of the displayed radical in the entry or this thread.

## 3. Standard background, not claimed as new

**Petter Brändén and Anders Claesson, "Mesh patterns and the expansion of
permutation statistics as sums of permutation patterns" (2011):**
https://doi.org/10.37236/2001 , preprint https://arxiv.org/abs/1102.4226

The foundational source for the general mesh-pattern framework. It is not a
source for the specific argument in the article, which needs only the
length-two specialization defined explicitly there.

**Philippe Flajolet and Robert Sedgewick, "Analytic Combinatorics" (2009):**
https://ac.cs.princeton.edu/home/

Referenced for formal Lagrange inversion and for the transfer of square-root
singular expansions. The article derives its own functional equations and its
own local expansion, and checks the dominant-singularity hypotheses itself.

**Astrid Reifegerste, “The excedances and descents of bi-increasing
permutations” (2002):**
https://arxiv.org/abs/math/0212247

The paper studies the increasing excedance/nonexcedance decomposition of
321-avoiders, fixed-point separation, and the Narayana distribution; see
especially Corollary 3.7 for the latter. The article supplies its own proofs of
the background facts it uses. The mesh-occurrence classification and the
run-contraction argument are presented explicitly rather than attributed to
this background paper.

## 4. Scope and limitations

The OEIS entry also links a 2016 thesis by Murray Tannock. Direct access to
that linked PDF was blocked in this session, and it is not treated as a read
source. The original discussion describes how the relevant patterns arise in
its tables; our proof does not depend on those tables or the thesis.

The mathematical claim is that the exact formula marked conjectural in the
consulted entry follows from the proof provided. The status check is not an
exhaustive literature or priority certification. Nothing has been posted to
OEIS or sent to the source authors.

## 5. Provenance of this archive

This package is the merger of two independently produced archives,
`mesh-avoidance-catalan-inflation` (the base) and
`mesh-pattern-algebraic-generating-function` (folded in and not kept
separately). Both consulted the same two primary sources on the same date,
September 20, 2026, and both recorded the entry as still labelled
conjectural; the statement above is the single surviving version of that
observation, not one of two. The Brändén-Claesson and Flajolet-Sedgewick
entries came in with the second archive. Neither archive claimed an
exhaustive priority search, and neither used the linked Tannock thesis; the
merged article makes the same two disclaimers, once each.
