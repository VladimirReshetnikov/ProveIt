# Public sources and attribution

This note identifies the public sources behind the article's context and
methods. It is not an independent novelty certificate. The article's bibliography
and theorem statements give the precise scope of each use. Links below were
checked on 2026-10-05. No third-party paper PDF is redistributed in this package.

## Counting sequence

The OEIS Foundation, [A110058](https://oeis.org/A110058), records the count of
square nonnegative integer matrices with every row and column margin equal to
the matrix dimension. The entry attributes the sequence to Brendan McKay and
includes the n=0 empty-table term. The [associated b-file](https://oeis.org/A110058/b110058.txt)
contains the displayed finite values.

The package independently recomputes n=0,...,5 by exact dynamic programming and
checks n=0,...,3 with a second labelled recursion. It does not derive the
asymptotic coefficients by fitting OEIS data. It includes only the short
numerical fixture needed for these checks.

## Constant-margin asymptotics

E. Rodney Canfield and Brendan D. McKay,
[Asymptotic enumeration of integer matrices with constant row and column sums](https://arxiv.org/abs/math/0703600v2),
arXiv:math/0703600v2, revised 12 June 2009.

This is a source for the existing constant-margin asymptotic enumeration
framework. The present article must identify any needed localization or
comparison result precisely; the leading asymptotic framework is prior work.
The public code in this package does not independently prove a cited analytic
localization theorem.

## General smooth-margin context

Alexander Barvinok and J. A. Hartigan,
[An asymptotic formula for the number of non-negative integer matrices with prescribed row and column sums](https://arxiv.org/abs/0910.2477v2),
arXiv:0910.2477v2, revised 5 April 2010.

This is relevant prior work on asymptotic enumeration of contingency tables
with smooth prescribed margins. Any comparison in the article is limited to
stated hypotheses and precision; a title or abstract alone does not establish
that another work lacks a particular higher-order coefficient.

## Complex cumulant truncation

Mikhail Isaev,
[A tail bound for cumulant series for complex functions of independent random variables](https://arxiv.org/abs/2508.16952v2),
arXiv:2508.16952v2, revised 28 August 2025.

This provides bounds on truncating complex cumulant series using mixed
differences for functions of independent random variables. The article applies
the cited theorem only after checking its hypotheses. Formal connected-diagram
calculations alone are not a replacement for that analytic step.

## Computational scope

The included connected-Wick evaluator, independent formal-factorization
verifier, direct small-Gaussian checks, finite table counters and formal inverse
check implement the equations described in `COMPUTATION.md`. The finite
receipts certify agreement of those stated arithmetic calculations only.
The package contains neither private review reports nor private source paths.

## Sparse antecedent and the Canfield--McKay comparison

Catherine Greenhill and Brendan D. McKay,
[Asymptotic enumeration of sparse nonnegative integer matrices with specified row and column sums](https://web.maths.unsw.edu.au/~csg/papers/GMinteger-update.pdf),
corrected author version of the paper in *Advances in Applied Mathematics* 41
(2008), 459--481. Its 2011 note describes corrections that leave the result
statements unchanged.

This is an important sparse antecedent. In particular, it identifies a sparse
range in which the Canfield--McKay conjecture on the comparison parameter is
already established eventually. It must not be represented as a dense-regime
result, or omitted from a discussion of that conjecture's prior status.

## Connected-cumulant and enumeration toolkit

Mikhail Isaev and Brendan D. McKay,
[Asymptotic enumeration of graph factors by cumulant expansion](https://arxiv.org/abs/2508.18731v1),
arXiv:2508.18731v1, 26 August 2025.

Mikhail Isaev, Brendan D. McKay and Rui-Ray Zhang,
[Cumulant expansion for counting Eulerian orientations](https://arxiv.org/abs/2309.15473v2),
arXiv:2309.15473v2, revised 20 December 2024.

These are related prior cumulant-expansion enumeration works. The general
connected-diagram and cumulant toolkit is not claimed as a new invention of
this article. Their graph and orientation counting settings are distinct from
the geometric contingency-table specialization here.
