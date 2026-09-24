# Literature status and exact sources

Checked 19 September 2026. This is a record of the sources actually used, not
an assertion that every relevant publication has been indexed or inspected.

## Documented open research direction

Isa Vialard, *Measuring well quasi-orders and complexity of verification*,
PhD thesis, Université Paris-Saclay, 2024, NNT 2024UPASG037:

https://isavialard.github.io/home/mwqo.pdf

The conclusion, printed page 109 (PDF page index 108), asks whether the
friendly order type can be computed compositionally. Chapter 5, Section 5.4,
studies its calculation. The relevant pages were checked both in parsed text
and in rendered PDF screenshots. The current author's publication page was
also inspected:

https://isavialard.github.io/home/

The finite equality in this manuscript is a precise subproblem extracted
from that research direction. It is not described here as a separately
published conjecture. Searches for the exact term, incomparability components,
finite cases, disjoint sums, and the older “safe order type” terminology did
not locate a matching component-and-core result. These searches are limited
and do not establish novelty.

## Published 2023 source

Isa Vialard, *Ordinal Measures of the Set of Finite Multisets*, MFCS 2023,
LIPIcs 272, 87:1–87:15.

https://doi.org/10.4230/LIPIcs.MFCS.2023.87

https://drops.dagstuhl.de/storage/00lipics/lipics-vol272-mfcs2023/LIPIcs.MFCS.2023.87/LIPIcs.MFCS.2023.87.pdf

Specific dependencies:

- Definition 3.3: friendly/open-ended bad-sequence tree.
- Theorem 3.4: multiset-order width equals omega to the friendly rank.
- Theorem 4.5: lower bound giving the limit-floor lemma used here.
- Proposition 4.1(1): binary ordinal-sum additivity; the manuscript gives an
  independent proof extending it to ordinal-indexed families.

## A substantive version distinction

Proposition 4.1(2), printed page 87:9 (PDF page index 8), gives the unrestricted
identity

    f(A disjoint B) = 1 + (o(A) - 1) natural-sum (o(B) - 1).

The actual types A = omega disjoint omega and B = 1 give a counterexample:
the true value is omega*2 + 1, whereas that expression gives omega*2. The
manuscript derives the true value directly from the residual recurrence.
The printed formula and its surrounding proof were inspected as an image,
not inferred only from potentially garbled text extraction.

The 2024 thesis does NOT repeat this unrestricted formula. Instead, its
Theorem 5.4.8(2), printed page 75, gives equality with maximal order type when
both summands' maximal order types are limits. The new counterexample does
not contradict that conditional statement. No conclusion is drawn about
whether the author had already recognized the earlier formula's limitation.
No communication with the author took place in preparing this archive.

## Background references

The 1977 de Jongh–Parikh paper and the 2020 Džamonja–Schmitz–Schnoebelen chapter
are cited for standard maximal-order-type theory. Their bibliographic details
and the facts used are consistent with the above primary sources; this work
is not a fresh audit of all proofs in those background references.

## Scope of the claimed outcome

The manuscript supplies proofs of a finite formula, a connected transfinite
classification using the established limit-floor lemma, exact disjoint-sum
laws with an additional core predicate, and explicit failures of a printed
identity and of four-invariant compositionality. It does not claim a uniform
algorithm for arbitrary infinite presentations or independently verified
priority for these results.
