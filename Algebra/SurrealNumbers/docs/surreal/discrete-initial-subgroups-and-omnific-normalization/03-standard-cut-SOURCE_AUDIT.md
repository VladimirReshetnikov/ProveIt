# Source and proof audit

## Selection and source pin

The topic connects Elliot Glazer's *A Topological Tennenbaum Theorem*
(arXiv:2311.13699) with ProveIt's actual omnific constant-term and residue
construction. The article makes an algebraic no-map claim under bounded
induction, not a purported strengthening of Glazer's theorem about arbitrary
Polish presentations.

Repository snapshot inspected:
`883e0b3b22263bd9d92fdbbf10376ca4b652b862`.

Concrete source read:
`Algebra/SurrealNumbers/Surreal/Foundations/OmnificResidues.lean`.
Blob: `aacd3cac89e9f55ef6b74710cdbffbfd0f2664eb`.

Relevant declarations include `omnific_int_dvd_iff`,
`omnific_prime_pow_dvd_iff`, `omnific_dvd_all_pos_int_iff`, and
`iInf_omnific_int_multiples`. No blanket validation of the repository's
other research claims is implied. No repository modification was made.

## Prior results credited

Emil Jeřábek's 2011 MathOverflow answer explicitly states that omnific
integers satisfy open induction but fail stronger induction.

Enayat, Łełyk, and Visser, *Completions of Restricted Complexity I, Weak
Arithmetical Theories*, arXiv:2508.14758v2, provide bounded standard-cut
definitions in Section 2.5 and discuss the Shepherdson model later. The
broad phenomenon of bounded standard-cut definability is not claimed here
as a discovery. Their PDF version, not an inconsistent internal date in an
HTML rendering, is used for the version-specific correction.

Phillips's 1972 article is used only for the historical context visible in
the publisher's extract; no unread theorem is invoked. Raffer (2010)
provides the accessible account of the classical Shepherdson–Puiseux
construction. The original Shepherdson paper is listed as the classical
source, not represented as freshly inspected in full.

## Exact correction

Pages 11–12 of arXiv:2508.14758v2 were inspected in the rendered PDF.
Their Lemma 2.7 asserts uniqueness of an ideal J with R/J isomorphic to Z
under their definition of a Dorroh ring.

Counterexample: R = Z[X]. Evaluation at any integer a is a surjective
unital map onto Z with kernel (X-a). The ideals (X) and (X-1) differ.
The leading-coefficient order with X infinite also satisfies the paper's
additional ordered condition for both ideals.

The repaired proposition in this article assumes division by 2. Iteration
gives residue agreement modulo every power of 2, forcing equality of
integer-valued normalized characters. No order preservation of these
characters is used.

This correction does not by itself refute any main completion theorem.
Theorem 2.9's standard-cut argument needs a chosen retraction, not uniqueness.
A complete dependency audit of the paper has not been performed. No claim
that the error has not previously been noticed is made.

## Proof boundaries

The main dyadic result uses only discreteness, ordinary division by 2 and
3, and a normalized additive map into the actual ordinary integers. Its
sharpness examples concern this formula, not every possible definition.

The additive-character classification needs division by all ordinary
positive integers to normalize arbitrary nonzero characters. The no-map
theorem needs a unit-preserving map; arbitrary additive maps may land in
the target character's kernel.

The compiler has a separate formula for each input sentence, not a single
uniform truth predicate taking syntax codes as inputs. A positive infinite
bound is essential. Effective presentations are required for the upper
computability reductions, but an effective character is not required.

Universal proofs are in the article. Python tests are finite exact checks
and syntactic audits. No Lean/Rocq compilation was performed for the new
results and no formal-verification claim is made.

## Proposed novelty

The exact dyadic detector under the two-small-divisor hypotheses, its
additive-map consequences, the single-bound quadratic compiler, and the
local uniqueness correction are the concrete outputs of this investigation.
Priority for the whole assembled package or its individual consequences
has not been established. None is advertised as a certified breakthrough
or a resolution of a named major open conjecture.
