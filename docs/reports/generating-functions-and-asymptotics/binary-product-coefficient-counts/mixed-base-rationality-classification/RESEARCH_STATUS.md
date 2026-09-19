# Source attribution and research status

Date of this report: September 19, 2026.

## The specific question

Richard Stanley, **A conjectured rational generating function**, MathOverflow
question 431075, September 23, 2022:

https://mathoverflow.net/questions/431075/a-conjectured-rational-generating-function

The question asks whether positive integer exponents tending to infinity and
having a rational ordinary generating function necessarily give rational
ordinary generating functions for fixed coefficient-multiplicity counts in
finite products. It permits factors `1+x^G` and, more generally, a fixed digit
range. It does not require monotone exponents.

The page displayed the question and two comments, but no posted answer, when
inspected on the report date. Targeted searches for the question's exact title,
its numerical identifier, and combinations of Stanley, coefficient counts,
rational generating functions, mixed bases, and counterexamples did not reveal
an existing resolution. These searches are not exhaustive and do not establish
priority. An unindexed or differently described earlier result may exist.

## Related primary sources

Richard P. Stanley, **Theorems and Conjectures on Some Rational Generating
Functions**, arXiv:2101.02131, version 3, September 30, 2021:

https://arxiv.org/abs/2101.02131

This paper provides context about coefficient moments in related products.
The present target is the later fixed-multiplicity question, not all of the
paper's conjectures.

Richard P. Stanley, **Differentiably Finite Power Series**, European Journal
of Combinatorics 1 (1980), 175–188:

https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf

This is the source for standard D-finite terminology. The report explains the
finite-singularity obstruction and the implication from polynomial-coefficient
recurrences directly. No third-party paper or copyrighted source PDF is included
in this archive.

## What is proved in the article

1. An explicit admissible exponent sequence gives a nonrational coefficient-one
   counting generating function, refuting universal rationality.
2. The rectangular count, the even-subsequence floor formula, and the exact
   even/odd relation are proved, including the exceptional initial indices.
3. The particular binary/ternary generating functions have natural boundaries,
   so they are non-D-finite, transcendental as functions, and their coefficient
   sequences are not P-recursive.
4. Within the defined two-base digit family, rationality is equivalent to
   multiplicative dependence of the bases. An eventual recurrence is proved
   in the dependent case.

The report supplies proofs in conventional mathematics. Exact finite checks
support the combinatorial identities and indexing, but are not the logical
basis for the infinite assertions. No proof-assistant certification or
independent refereeing has been performed. Mathematical correctness and
historical priority are separate questions.

## Not claimed

There is no claimed resolution for monotone exponent sequences, for every
coefficient value k > 1, or for all constant-coefficient-recurrent exponent
sequences. No OEIS accession number is claimed. The growth constant
`2^(1-log_3(2))` is not asserted to be algebraic or transcendental; neither
property is needed. The radial boundary blowups are not described as isolated
poles. The problem's author is not represented as endorsing this report.

No material has been posted to MathOverflow, OEIS, arXiv, or any other external
service as part of this work.
