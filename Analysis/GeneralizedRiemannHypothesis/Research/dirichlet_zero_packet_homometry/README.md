# What zero differences forget about Dirichlet characters

The paper is in zero_packets.pdf. Its complete LaTeX source is zero_packets.tex.

## Results

Theorem 1 classifies the balanced Fourier measurements of pooled Dirichlet zero ordinates by rotations of finite histograms at unramified primes. Corollary 2 identifies a coprimality condition under which the rotations come from a common character twist. For quadratic twists the entire classification reduces to a multiset of pairwise character quotients.

Theorem 3 gives an exact 28-class ambiguity at conductor 32045 together with a linear lower bound on unmatched zero occurrences. Theorem 4 proves agreement of the balanced measurements uniformly in a growing frequency band. Theorem 5 recovers an odd-prime-order local histogram from one complex cubic and its mass.

## Reproduce the finite checks

Use Python 3.10 or newer. Both scripts use only the standard library.

    python3 verify_packets.py
    python3 verify_cubic.py

packet_checks.txt and cubic_checks.txt contain the recorded outputs. The first script uses the least positive primitive root at each of 5, 13, 17, and 29 and maps each generator to i. The complex traces in the output use this convention. The absolute gap is independent of those choices.

The finite checks enumerate exact character and histogram data. The analytic limits and the lower bound on zero discrepancies follow from the proofs in the paper. The general results are human-readable mathematical proofs. The upstream Lean theorem is cited along with published independent verification.

## Rebuild the PDF

With a standard TeX Live installation, run the following twice in this directory to resolve cross-references.

    pdflatex -halt-on-error zero_packets.tex
