# Primary sources and attribution

Checked 2 October 2026. This is a bounded source check, not a universal novelty certification.

## Exact counting model and established results

Thomas Browning, *Counting Parabolic Double Cosets in Symmetric Groups*, Electronic Journal of Combinatorics 28(3) (2021), P3.40.

- DOI: https://doi.org/10.37236/9988
- Primary preprint: https://arxiv.org/abs/2010.13256
- Readable full text: https://arxiv.org/html/2010.13256
- Journal PDF: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v28i3p40/pdf/

The exact p/q transform is attributed to arXiv Theorem 3.18; the ordered even-block interpretation is Proposition 3.19; the generalized-Fubini generating function is in Section 4.1. The higher-order conjecture is arXiv Conjecture 5.1 and journal Conjecture 41, Section 5.1. The leading equivalent and its constant are already Browning's theorem. The programs in this package are original implementations of the cited identities, not copies of his repository code.

## Sequence data

OEIS Foundation Inc., A260700: https://oeis.org/A260700

Numerical reference file: https://oeis.org/A260700/b260700.txt

The included `data/b260700.txt` was retrieved on 2 October 2026 and has SHA-256:

2a22bf909a7a4b2245fd6dd2bd9a641343e877f23a6965de7005f363a1e4e091

The file is numerical reference data, separately attributed to OEIS and the contributors named by the entry. The article does not reproduce the entry's prose. OEIS usage information: https://oeis.org/wiki/License_Agreements

The separate `data/exact-values.json` contains locally computed values from the integer recurrence implementation. The full validation compares all n=1,…,400 with the reference b-file. Coefficient data and inverse results were computed locally.

## Nearby problems checked

- A120733, arbitrary nonnegative tables without zero rows or columns: https://oeis.org/A120733. This is not distinct parabolic coset subsets; at n=2 it has value 5 instead of 3.
- Václav Kotěšovec, *Asymptotics of the sequence A120733* (2015): https://oeis.org/A120733/a120733.pdf. Relevant neighboring asymptotic and Stirling-transform methods, not the distinct-subset correction theorem.
- Emanuele Munarini, Maddalena Poneti and Simone Rinaldi, *Matrix Compositions*, Journal of Integer Sequences 12 (2009), Article 09.4.8: https://cs.uwaterloo.ca/journals/JIS/VOL12/Rinaldi/rinaldi.html. Fixed-row matrix-composition regimes differ from the present problem.
- Persi Diaconis and Mackenzie Simper, *Statistical Enumeration of Groups by Double Cosets*, Journal of Algebra 607 (2022), 214–246: https://doi.org/10.1016/j.jalgebra.2021.05.010. Specified subgroup pairs and prescribed table margins.
- Paul Renteln, *Counting Sylow Double Cosets in the Symmetric Group*, Discrete Mathematics 347(10) (2024), 114109: https://doi.org/10.1016/j.disc.2024.114109. Sylow subgroup quotients, a different family.
- Ludovic Schwob, *On the Enumeration of Double Cosets and Self-Inverse Double Cosets*, Advances in Applied Mathematics (2026), article 102982: https://doi.org/10.1016/j.aam.2025.102982 and https://arxiv.org/abs/2506.04007. Section 4.3 treats prescribed parabolic pairs and aggregate sequences A321652 and A178718, not A260700.
- Browning's mathematical writings page: https://math.berkeley.edu/~tb65536/math.html. It listed the counting paper without a separate correction paper when checked; this is only negative search evidence.

Searches included the exact sequence identifier, paper title, correction and higher-order terms, the conjecture number, and later double-coset publications. No later primary solution to the precise correction conjecture was located. The article's defensible contribution is its explicit correction and uniform all-fixed-order proof from Browning's exact model, together with qualified inverse consequences.

No full third-party papers are redistributed in the package.
