# Independent review of the positive carrier translations

All six candidate definitions in positive/SHIFTED12_PROOF.md were reviewed.
The cheaper Kr^2 gate is an exact identity. The five nontrivial carriers
change the polynomial, but do not alter the separating norm's hypotheses:
q,X,Y,E,k,c,A,G,D,Q,d,M remain unchanged, apart from the permitted doubling
of M in the last two variants. Every added correction is positive on the
weak unit locus, so W remains positive and W=b0 modulo H still holds.

For completeness, the important condition is not merely that the carrier
is translated: the new positive t must exist. The proof establishes this.
Since c<2kY, ell/c>E/2>2, hence
(a+2)c-ell<ac<sqrt(G). The half-corrected delta is smaller still.
The inherited bound M0 sqrt(A)>2(v sqrt(D)+b) then pays for the b term.
For the last variant, M=2M0 and (a+2)I<2sqrt(D) pay for the added
v(a+2)I term. The positive canonical gamma and auxiliary root complete
the strict t>0 estimate. No new Pell-period or coefficient promise is used.

The field-conjugation proof uses actual automorphisms only; the eight
formal sign factors are used for polynomial identities. The modulus4
unit argument, nonzero F(0), rational auxiliary Pell saturation and
main-root gamma recovery are unaffected by the translations.

The exact degree proof by weighted Laurent expansions was checked
independently. The special half-auxiliary branch cancels degree119 at
one sign, but its next degree118 term is nonzero:
2*dbar*Hbar^2*bbar*Mbar*cbar/(2*Ebar).
All other terms in that factor have smaller degree. Thus the stated
product degrees1081,1041,1033,1025,1023,1022 follow from the factor
lists and the additional degree9 of Nk Nt. These are exact polynomial
degrees for the authentic fixed tuple, not just sampled degree estimates.

The separate checker check_positive_independent.py evaluates the
homogeneous inner norm in a two-dimensional quadratic algebra and takes
its final quadratic norm. It does not use the generator's trace reduction
or the author's eight-dimensional factor-multiplication checker. Across
240 signed/zero/degenerate assignments per candidate it agrees with the
actual delivered DAG. Receipt: POSITIVE_INDEPENDENT_CHECKS.json.
Finite checks are supplementary; this review does not compile a formal
certificate or verify an unbounded machine run.
