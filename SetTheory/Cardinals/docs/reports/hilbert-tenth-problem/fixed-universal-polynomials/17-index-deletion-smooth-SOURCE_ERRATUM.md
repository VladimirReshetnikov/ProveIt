# Narrow endpoint clarification for the frozen preliminary note

The frozen factorial packet is intentionally unchanged. Its preliminary
PROOF.md, Section3, states the strict Pell upper bound

    psi_A(p)<(2A)^(p-1) for p>=2.

At p=2 there is equality: psi_A(2)=2A. The strict range should be
p>=3, or the bound should be non-strict at p=2. The Report41 writer
caught this while checking the article's general lemma; root confirmed
the correction and requested that the original bytes remain preserved.

No conclusion or witness construction is affected. The preliminary
small-index contradiction applies that strict bound only at p=4 or5.
The full positive counterfamily uses p>=55 and first index n>=40.
The smooth-radix addendum changes neither range. The article can state
the corrected general lemma while citing this explicit source erratum.

This is separate from the already documented p4-to-p5 correction for
2p/2^p<1/2 in FINAL_RELEASE_REVIEW.md. Neither correction is evidence
of a failed full candidate or a restored integer h.
