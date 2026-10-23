# Additional independent source review

Reviewed `packing/mask_popcount/section.tex` and the frozen calibrated-mask
convention. No gap was found in the three new source-layer arguments:

1. The extraction condition compares each used monomial with every possible
quadratic expansion monomial. Full Sidon separation is unnecessary. It
also implies injectivity of reversed source positions, which is required
to retain the unmultiplied coefficient bound.
2. Before decoding, integer g<2bB^t implies 1+g<=2bB^t. The bound
D(B)<A B^(q+1)/(B-1) gives the stated estimate on 2(1+g)^2D. The actual
source beta>64A suffices for the quarter-block estimate; beta>4096A
separately supplies the signed coefficient bound after decoding. The
strict S+T<N argument includes both g and the low mask, not just the
high blocks. No binary-base assumption is used before the reverse bridge.
3. Sparse target padding uses borrow states -1 and 0. It does not silently
assume all residual coefficients nonnegative. The popcount formula uses
N=B^5741, not the earlier provisional 4B^5741; consequently the multiplier
is 2^(kappa-21), and the delivered exponent 2134919 is correct.

The fixed source is the original package31 transport convention. Package45
has a related shifted transport row, so equality of its label support alone
would not authenticate numerical source coefficients. The delivered
independent source reconstruction is essential and was retained.

This review covers source adaptation and composition hypotheses, not an
independent proof of Sun's imported number-theoretic theorem or the native
compiler calibration. The root finite controls exhaust 43,945 small binary
triples and 9,088 whole signed-padding examples, with separate overflow and
missing-padding counterexamples. They supplement the universal proofs and
are not substitutes for them.
