# Sources and attribution

## Bounded OEIS integer fixtures

The only third-party data distributed in this package is a total of 72
integer values: 24 initial terms for each of the following sequences.
The snapshot is recorded for the report dated 4 October 2026.

- OEIS A098131, https://oeis.org/A098131, indices 0 through 23
- OEIS A098132, https://oeis.org/A098132, indices 1 through 24
- OEIS A098133, https://oeis.org/A098133, indices 1 through 24

Attribution: OEIS Foundation Inc.; these entries were contributed by
Vladeta Jovovic, with additional terms by Emeric Deutsch. The entry pages
provide the complete contribution history and references. Consult the
OEIS terms at https://oeis.org/wiki/The_OEIS_End-User_License_Agreement
for use of OEIS material. This package does not assert a new license over
OEIS content or reproduce complete records, comments, programs, b-files,
or page text.

The fixture JSON retains only identifier, offset, bounded integer terms,
a source URL, and attribution. Its schema is checked, and the terms are
compared with independently computed exact counts. No OEIS query or other
network access occurs during checking or building.

## Normalization

For every integer s>=0, a_s(0)=1 includes the empty composition and
b_s(0)=a_s(0)-a_{s+1}(0)=0. For n>0, a_s(n) counts ordered compositions
with k parts, each part at least k+s; b_s(n) counts those with minimum
exactly k+s. Hence A098131=a_0, A098132=a_1 on its published n>=1 offset,
and A098133=b_0 on n>=1. The zero term of a_1 is a convention of this
family, not an extra published fixture term for A098132.

## Prior mathematical sources

The manuscript contains the mathematical bibliography and the precise
scope of each source. In particular, the minimum-versus-length counting
model and generating functions are established material, also related to
the more general minimum>k^p family in Hùng Việt Chu, Nurettin Irmak,
Steven J. Miller, László Szalay, and Sindy Xin Zhang, “Schreier Multisets
and the s-step Fibonacci Sequences,” arXiv:2304.05409 (2023), published
in Integers 24A (2024), A7:

- https://arxiv.org/abs/2304.05409
- https://math.colgate.edu/~integers/a7Proc23/a7Proc23.pdf

The binomial formulas, Gaussian Poisson identity, and classical saddle
coefficient manipulations are not presented as newly invented methods.
No source paper, downloaded web page, full database record, or source
research cache is redistributed. The report's detailed claims and
limitations, rather than finite experimental agreement, define its
mathematical scope.

## Authored and generated content

All supplied Python modules, build/replay/verification scripts,
documentation, and the manuscript are authored package content. The
release builder generates the PDF, exact-check and guard JSON summaries,
fixed build metadata, and closed hash manifest. The optional mpmath and
SymPy results are not mandatory build inputs and are not inserted into
the release archive.
