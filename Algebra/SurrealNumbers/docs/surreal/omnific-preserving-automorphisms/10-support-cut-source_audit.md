# Source, proof, and novelty audit

Date: 23 September 2026.

## Claim boundary

The proposed contribution is the integer-part support-cut characterization,
the associated rank boundary and support blocks, the specialized fixed-field
and displacement formulas, and explicit arbitrary-parameter surreal witnesses
with their nondefinability and definable-closure consequences. The manuscript
contains complete written proofs of these statements.

This is not a claim to have solved a named published longstanding conjecture.
No peer review, Lean verification, general classification of all non-strong
automorphisms, or historical priority certification is asserted.

## Repository actually inspected

Repository: https://github.com/VladimirReshetnikov/Surreal

Snapshot: `58cd8e1c8259a3b9626e009bb994b153fec9a417`.

Access was through the connected GitHub tool. The top-level and documentation
trees supplied navigation. The following guides supplied the relevant scope:

- `docs/README.md` (opening 220 lines).
- `docs/surcomplex/surcomplex-field-automorphisms/README.md`.
- `docs/surreal/omnific-diophantine-geometry/README.md`.
- `docs/surreal/omnific-diophantine-geometry/06-definability-reconstruction-SOURCE_AUDIT.md`.
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`.
- `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/README.md`.

Several long guides were returned as truncated previews. The scope comparison
uses their returned claims and introductions, not an assertion that all their
unseen material was inspected. The reconstruction audit was returned in full.
An empty connector code-search result was not used as proof of absence. A
container clone failed because network name resolution was unavailable; no
claim of a successful clone or local repository build is made.

The report guides and reconstruction audit do not state the exact support-cut
criterion or the complete package developed here. This targeted comparison is
not exhaustive: the repository explicitly identifies supplementary manuscripts
awaiting integration, and not every line of those manuscripts was retrieved.

### Repository material expressly credited

The automorphism guide already contains strong character/monomial maps,
leading-term kernels, a valued decomposition, phase twists, and exponential
rigidity material. None of those general assertions is presented as new.

The omnific-Diophantine guide already records `Frac(Oz) = No`, the constant
coefficient quotient and ideal, and definitions of ordinary arithmetic.

The supplementary reconstruction audit explicitly records the multiplier-ring
identity and real-coefficient rigidity for all automorphisms of Oz. During
proof development an elementary derivation of those facts was found, then
checked against that audit. They were consequently labeled prior repository
results in Section 9.4, not included among the new contributions. Independent
proofs are retained for self-containment and to show that coefficient fixation
is automatic for a full-surreal omnific stabilizer.

That same audit records Gaussian phase twists preserving Oz[i] while moving
the real axis. The present Gaussian result is different: its witnesses fix the
real axis setwise, commute with conjugation, and nevertheless move the Conway
monomial class within the real axis.

The quotient guide contains universal set-sized quotient and homological
results; this manuscript does not reprove or claim them. The holonomic guide
was investigated as an alternative direction, but no new theorem about its
remaining higher-order order-unit case is claimed.

## Primary public sources consulted

1. Salma Kuhlmann and Michele Serra, *The automorphism group of a valued field
   of generalised formal power series*, arXiv:2107.03362v3 (2022).
   https://arxiv.org/html/2107.03362v3

   Section 4 supplies the established strong Hahn-automorphism framework,
   principal-unit characters, and crossed composition law. The article does
   not claim that framework as new. Its explicit construction proves support
   admissibility and a two-sided inverse instead of relying on a bare abstract
   character formula.

2. Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra, *Decomposing the
   automorphism group of the surreal numbers*, arXiv:2509.22374v3, accessed
   23 September 2026.
   https://arxiv.org/html/2509.22374v3

   The class-size conventions and Sections 4–5 were relevant. Proposition 5.1
   supplies the established simplicity/order rigidity; Proposition 5.2 uses
   exponential displacement; Proposition 5.5 concerns omega-map rigidity.
   Our witnesses are not omega-map or exponential automorphisms. They therefore
   do not solve the paper's questions about automorphisms preserving those maps.

   Searches within the fetched HTML found no occurrence of "omnific" or
   "integer part". This is a limited text observation, not an exhaustive
   literature or priority proof.

3. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for
   generalised power series and omnific integers*, arXiv:1710.07304v5 (2024).
   https://arxiv.org/html/1710.07304v5

   Its opening normal-form and omnific support descriptions are the standard
   algebraic background. Its factorization and primality results are not new
   claims of the present work.

4. Philip Ehrlich and Elliot Kaplan, *Number systems with simplicity
   hierarchies: a generalization of Conway's theory of surreal numbers II*,
   arXiv:1512.04001v1 (2015).
   https://arxiv.org/html/1512.04001v1

   The introductory account of initial subdomains and the canonical integer
   part was used to distinguish that topic from automorphism stabilization.

Targeted web queries included combinations of "Hahn", "integer part",
"automorphism", "preserve", "omnific", "monomials", "definable",
"stabilizer", and "fixed field". No identical theorem package was located.
Other surfaced results were not substituted for primary mathematical sources.

## Critical proof checks

1. **Signs:** normal supports are reverse well ordered; positive exponents
   are the purely infinite part; valuation is minus the greatest exponent.
2. **First forbidden shift:** the set of positive shifts is well ordered.
   Its least shift outside the infinitesimal convex subgroup cannot be the
   sum of earlier shifts. Hence its rational-power coefficient is exactly
   `q*b_h`, and choosing `0 < q*g < h` exposes a negative exponent.
3. **Characteristic zero and divisibility:** the former makes that coefficient
   nonzero and gives unique leading-one roots; the latter supplies all rational
   exponent roots. An ordinary Laurent translation shows why divisibility
   cannot simply be removed.
4. **Sufficiency is genuinely two-sided:** strongness preserves the three sign
   components. Injectivity prevents a nonzero negative component from
   vanishing, and surjectivity then proves equality of the integer-part rings.
5. **Uniform shift:** `S - N*h` is reverse well ordered, and a coefficient has
   finitely many possible source/degree pairs. The program does not prove this
   lemma; the written argument does.
6. **Inverse:** the twisting functional kills `h`, so the monomial `X^(-h)`
   is fixed. This makes the inverse the negative functional. Killing the whole
   principal convex subgroup is the extra integer-part condition.
7. **Fixed field:** a uniform first nonzero degree of `F-1` gives a greatest
   nonzero correction at the greatest support exponent outside the kernel.
   Smaller source exponents cannot cancel it.
8. **Class parameters:** two unions of set-sized supports are sets. A positive
   ordinal beyond the inner support gives a coefficient functional annihilating
   all parameter exponents. No sum over a proper class occurs.
9. **Index versus element:** fixing the monomial `omega^(-h)` does not imply
   fixing the surreal element `h`. The text explicitly distinguishes these.
10. **Nondefinability:** the chosen automorphism preserves each named predicate,
    coefficient, and projection but not the target relation. Exponential failure
    is witnessed by a positive infinite displacement and a valuation mismatch.
11. **Gaussian extension:** the map is complex linear and commutes with
    conjugation; there is no claimed ordering of the full complex field.
12. **Prior reconstruction:** the multiplier and coefficient-field proof is
    included with explicit credit, not presented as an independent novelty.

## Computational and artifact verification

`verify.py` ran under Python 3.13.5 with exact `fractions.Fraction` arithmetic.
The recorded run passed 28,668 assertions. The comparison of formal-power
algorithms uses both a binomial expansion and the independent recurrence
`F*A' = a*F'*A`. Finite rank-two tests cover composition, inverses,
multiplicativity, signed projections, and exact first displacement. Rational
samples check the displayed noncommutative substitution formulas.

These are finite checks only. They do not constitute Lean verification or
verify arbitrary Hahn support, the proper-class arguments, or definability.

The source was compiled with pdfLaTeX; cross-references and citations were
resolved. The PDF was rendered for visual review, with Poppler additionally
used for the title page. The final build report contains actual integrity
checks and hashes. No font files or repository source files are redistributed.
