# Source audit

Consultation date: September 20, 2026.

## 1. The selected conjecture

**OEIS A289587:** https://oeis.org/A289587

The consulted entry defines the sequence using simultaneous avoidance of
classical 321 and the mesh pattern (12,174), with the inverse pattern (12,234)
giving the same counting sequence. Its displayed initial values run from n=0
through n=16. It labels the radical generating function proved in the article
as conjectural and attributes it to Thomas Scheuerle, December 23, 2025.
The original sequence entry is attributed to N. J. A. Sloane, July 8, 2017.

These are the provenance facts used in the article. The coefficient extension
through n=200 is calculated by the included program and is not represented as
an OEIS-provided file.

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

The article and verifier use these explicit sets, not an opaque identifier.
I did not locate a proof of the displayed radical in the entry or this thread.

## 3. Standard background, not claimed as new

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
