# Source attribution and research status

Date of this report: September 19, 2026.

This report merges two independently produced research reports on the same
question, originally distributed as the directories
`mixed-base-rationality-classification` and `mixed-base-natural-boundary`.
Both reached the same enumerative core by the same argument; that core is
proved once in the merged article. Where the two diverged — the algebraic
obstruction and the natural-boundary proof — both arguments are preserved and
labelled. Section 1.2 of the article states the provenance in full. The
status statements below are the union of the two originals, resolved in
favour of the more cautious wording wherever they differed.

## The specific question

Richard Stanley, **A conjectured rational generating function**, MathOverflow
question 431075, September 23, 2022:

https://mathoverflow.net/questions/431075/a-conjectured-rational-generating-function

The question asks whether positive integer exponents tending to infinity and
having a rational ordinary generating function necessarily give rational
ordinary generating functions for fixed coefficient-multiplicity counts in
finite products. It permits factors `1+x^G` and, more generally, a fixed digit
range. It does not require monotone exponents. The construction in the article
uses `r = k = 1` in the general formulation.

The page displayed the question and two comments, but no posted answer, when
inspected on the report date. Targeted searches for the question's exact title,
its numerical identifier, and combinations of Stanley, coefficient counts,
rational generating functions, mixed bases, and counterexamples did not reveal
an existing resolution. These searches are not exhaustive, and a page with no
posted answer does not prove that a question has no solution elsewhere. They do
not establish priority. An unindexed or differently described earlier result may
exist.

## Related primary sources inspected

Richard Stanley, **Number of coefficients equal to k in certain "Fibonacci
polynomials"**, MathOverflow question 430741, September 19, 2022, *with posted
solutions and indexing corrections*:

https://mathoverflow.net/questions/430741/

This is a different exponent sequence. Unlike the target question, it has
posted answers, which establish eventual linearity of its fixed-coefficient
counts. Nothing in this report contradicts them.

Richard P. Stanley, **Theorems and conjectures on some rational generating
functions**, European Journal of Combinatorics 119 (2024), article 103814,
https://doi.org/10.1016/j.ejc.2023.103814; preprint arXiv:2101.02131,
version 3, September 30, 2021:

https://arxiv.org/abs/2101.02131

This paper provides context about coefficient moments in related products.
The present target is the later fixed-multiplicity question, not all of the
paper's conjectures. A theorem about sums of powers of coefficients does not
by itself settle the number of coefficients equal to a particular integer.

Richard P. Stanley, **Some linear recurrences motivated by Stern's diatomic
array**, American Mathematical Monthly 127 (2020), 99–111; preprint
arXiv:1901.04647:

https://arxiv.org/abs/1901.04647

Background on linear recurrences arising from digital products.

Richard P. Stanley, **Differentiably finite power series**, European Journal
of Combinatorics 1 (1980), 175–188:

https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf

This is the source for standard D-finite terminology, and for the equivalence
between D-finite series and P-recursive coefficient sequences (Theorem 1.5
there, cited by number in the article). The report also explains the
finite-singularity obstruction and the implication from polynomial-coefficient
recurrences directly, so that no step depends on an unstated import.

The author's publication list, https://math.mit.edu/~rstan/pubs/, was consulted
only to check bibliographic metadata.

No third-party paper or copyrighted source PDF is included in this archive.

## What is proved in the article

1. An explicit admissible exponent sequence gives a nonrational coefficient-one
   counting generating function, refuting universal rationality.
2. The rectangular count, the even-subsequence floor formula, the ruler form of
   the carry-gap distribution, and the exact even/odd relation are proved,
   including the exceptional initial indices.
3. Two independent algebraic obstructions are proved: reduction modulo a prime
   (elementary; gives nonrationality) and a finite-quotient rigidity theorem
   (gives non-P-recursiveness, hence non-D-finiteness). A decimation lemma
   transfers both from the even section to the full sequence.
4. The binary/ternary generating functions have natural boundaries, proved
   twice — directly, and via a general theorem covering every irrational-floor
   series — so they are non-D-finite, transcendental as functions, and their
   coefficient sequences are not P-recursive.
5. The exact limiting distribution of the normalized fluctuations is computed,
   not merely their limit set and mean.
6. Within the defined two-base digit family, rationality, D-finiteness of the
   even section, and D-finiteness of the full series are all equivalent to
   multiplicative dependence of the bases. An eventual recurrence is proved in
   the dependent case.

The report supplies proofs in conventional mathematics. Exact finite checks
support the combinatorial identities and indexing, but are not the logical
basis for the infinite assertions. No proof-assistant certification or
independent refereeing has been performed. Mathematical correctness and
historical priority are separate questions.

## Not claimed

There is no claimed resolution for monotone exponent sequences, for every
coefficient value k > 1, for a version restricted to a single simple dominant
characteristic root or to exponent recurrences with prescribed positive
coefficients, or for all constant-coefficient-recurrent exponent sequences.

No OEIS accession number is claimed. The growth constant `2^(1-log_3(2))` is
not asserted to be algebraic or transcendental; neither property is needed.
The radial boundary blowups are not described as isolated poles. The article
does not claim an explicit list of exceptional parity indices for digit sets
larger than {0,1}; it proves the set is finite and computes it case by case.
The problem's author is not represented as endorsing this report.

The package does not claim to refute a Fibonacci-specific theorem, a
moment-of-coefficients theorem, or a monotone-exponent variant. Standard
ingredients — interval counting, finite-state recurrence arguments, reduction
modulo a prime, and irrational rotation averages — are not claimed as new; the
intended contribution is their explicit combination into the counterexample,
the exact enumeration, the two independent algebraic obstructions, the natural
boundary, and the base-family classification.

No third-party source text, font binaries, or third-party PDF papers are
redistributed. No material has been posted to MathOverflow, OEIS, arXiv, or any
other external service as part of this work.
