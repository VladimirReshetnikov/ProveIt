# Source notes

Consulted September 20, 2026 (America/Los_Angeles date).

## OEIS A289587

https://oeis.org/A289587

The entry defines the sequence using avoidance of 321 together with mesh
(12,174), or equivalently for its listed sequence mesh (12,234). The formula is
explicitly labeled conjectural and attributed to Thomas Scheuerle, December
23, 2025. The visible offset is 0. The 17 published values used as an external
comparison are:

    1, 1, 1, 3, 6, 18, 47, 139, 405, 1225, 3740, 11602,
    36357, 115049, 366969, 1178791, 3809802.

The b-file source is https://oeis.org/A289587/b289587.txt .
The archive does not contain a wholesale copy of the OEIS page.

## SeqFan: RFE Dec 2025: Mesh patterns avoiding 321

https://groups.google.com/g/seqfan/c/9jqIgQGj8Gg

Christian Sievers's December 4, 2025 message specifies cell (I,J) as the bit at
position 3*I+J. The December 5 table associates labels 174 and 234 with the
initial sequence used here. These facts fix the exact mesh convention; the
article defines the actual shaded cells and proves inverse equivalence.
The public discussion, rather than any private connected account, was used.

## Brändén and Claesson: Mesh patterns

https://arxiv.org/abs/1102.4226
https://www.combinatorics.org/ojs/index.php/eljc/article/view/v18i2p5
https://doi.org/10.37236/2001

Petter Brändén and Anders Claesson, Mesh patterns and the expansion of
permutation statistics as sums of permutation patterns, Electronic Journal of
Combinatorics 18(2) (2011), P5. This is the foundational source for the general
mesh-pattern framework, not a source for the specific proof in this article.

## Flajolet and Sedgewick: Analytic Combinatorics

https://ac.cs.princeton.edu/home/

Philippe Flajolet and Robert Sedgewick, Analytic Combinatorics, Cambridge
University Press, 2009. Referenced for formal inversion and singularity
transfer. The article explicitly derives its functional equations and local
square-root expansion, and checks the needed dominant-singularity hypotheses.

## Scope

The independent combinatorial proof and its extensions are developed in
article.tex. Current conjectural wording in OEIS does not, by itself, establish
that no proof has appeared elsewhere. The article makes no exhaustive priority
claim. It does not rely on the thesis linked from OEIS, whose full text was not
used in this work. No third-party full text is redistributed in the archive.
