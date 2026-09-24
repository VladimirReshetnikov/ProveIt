# Proof and source audit

## 1. Scope and comparison point

The article was prepared on 23 September 2026 (Pacific time). The repository
comparison is pinned to commit
`51c1cc70240d208f88704b0bb0b95855701be702` of
`VladimirReshetnikov/Surreal`. The commit metadata reports
`2026-09-24T00:23:53Z`, which is 23 September in Pacific time.

The report examined was
`docs/surreal/set-sized-quotients-of-omnific-integers/`.
Its README at the pin, lines 610–635, explicitly retains conditional treatment
of nonarithmetic class primes and does not claim their existence, referring
to Question 18.4. The present article answers the **existence aspect in GBC**;
it does not purport to settle every clause of that numbered question.

The repository's main guide, document catalogue, relevant large-quotient
extracts, report README, and the stated limitation were inspected. This was
not a complete line-by-line audit of the whole repository or every companion
manuscript. In particular, absence from the selected excerpts is not treated
as proof of absence from the entire repository.

Relevant pinned blob metadata returned by GitHub:

- report README: `6d60a1a32867f7467781b9fdc1c4c3dac9678e6c`;
- report TeX: `ef7aef1d92813d54dc5a074be2eb40eb3f6b2c4c`.

No repository source files are redistributed in this package.

## 2. Attribution and novelty boundaries

### Credited background, not claimed new

- Conway normal forms; the omnific support description; real closedness of
  No and algebraic closedness of No[i].
- The equivalence between global choice and a set-like global well ordering.
- The ordinary greedy maximal-ideal construction and classical Krull/choice
  arguments.
- The monomial compatibility method in Hodges, Erne, and the corrected v3
  exposition by Entin. The article's lemma is an adaptation of this method,
  with the class-coding details and the global-choice application supplied.
- Hahn-field algebraic closure for algebraically closed characteristic-zero
  coefficient fields and divisible set-sized value groups.
- The repository's field-reservoir and dyadic finite-product/Cantor mechanisms.
- The elementary zero Jacobson radical consequence from the nonunit
  `1 - omega*x`; the standard exponent-rescaling automorphism.
- The usual universality/back-and-forth method for algebraically closed
  fields, extended with explicit set-valued stages to class fields.

### The proposed extension of the selected report

- Actual maximal class extensions under a stated foundational hypothesis,
  instead of leaving the nonarithmetic-prime statements conditional.
- Exact zero-or-unit monomial behavior throughout every proper binomial
  quotient, including explicit inverses and a separated-scale Bezout identity.
- Whole-tail truncation above the principal convex exponent subgroup.
- Lifting every binary idempotent branch to an actual maximal class ideal,
  and combining this with an ordinal family of separated scales.
- Characteristic-zero maximal separation of every nonzero omnific element,
  together with surcomplex realization of each maximal kernel.
- The explicit Hahn-summability obstruction and the support-closed-prime
  boundary theorem.

The generic class maximal-ideal/global-choice equivalence might be familiar
folklore; no claim of historical first publication is made. The monomial and
support-prime statements may also have antecedents in generalized-series or
ordered-monoid literature. The article claims a proved package with a
repository-specific application, not a certified breakthrough in a named
classical conjecture.

## 3. Sources actually used

The full URLs and bibliographic data appear in the article. The following
notes distinguish evidence read from references supplied as background.

- Hamkins, *The global choice principle in Godel–Bernays set theory*: the
  equivalences and the set-like enumeration argument were read from the
  author's exposition.
- Entin, arXiv:2404.18351 **v3**, 27 June 2025: the corrected HTML proof,
  especially the monomial step of the maximal-small-ideal argument, was
  consulted. The v3 correction was explicitly checked in the version record.
- Erne, *A primrose path from Krull to Zorn*: bibliographic and author-archived
  abstract material was checked. The finite compatibility mechanism was
  checked against Entin v3, not asserted to have been independently checked
  against every line of Erne's original paper.
- Hodges, *Krull implies Zorn*: cited as a historical antecedent through the
  verified exposition; no claim to have reread the complete original paper.
- Gitman–Hamkins–Holy–Schlicht–Williams, arXiv:1707.03700: consulted for the
  distinction between GBC and stronger class-valued recursion principles.
  The present proofs invoke only set-valued recursions with class parameters.
- Knight–Lange, *Lengths of Roots of Polynomials in a Hahn Field*: publisher
  text explicitly states the characteristic-zero Hahn algebraic-closure
  theorem and its attribution to Mac Lane. Mac Lane's original paper is
  referenced, not claimed to have been fully inspected in this session.
- Gonshor: publisher metadata, title, series, year, and DOI were verified.
  Gonshor and Conway are standard foundational references; no claim is made
  that the full books were retrieved or audited in this session.
- Blechschmidt–Schuster, arXiv:2207.03873: read as a recursive finite/set-sized
  algebra antecedent, not used as a source for any proper-class theorem.
- The Wikipedia link supplied in the request was used for orientation, not
  as a primary source for the technical proofs.

Targeted searches did not establish historical priority. No exhaustive
literature search, peer-review certification, or theorem-database search is
claimed.

## 4. Critical mathematical hypotheses

1. GB means no choice; GBC means GB plus global choice. The unrestricted
   class maximal ideal principle is not the restricted omnific principle.
2. Class-ring elements are sets. Quotient cosets are represented by least
   elements of a set-like global well order, or by Scott codes in the reverse
   implication over GB.
3. A recursion stage stores a SET of accepted generators, or a SET partial
   field embedding. It does not store a proper-class ideal as a stage value.
4. Ideal membership and rejection witnesses use only finite sums. This is
   what ensures properness at every set limit and in the final class union.
5. Every individual Hahn series has set support, reverse well ordered. The
   coefficientwise geometric cancellation is justified by this summability,
   not by ordinary analytic convergence.
6. In the monomial-killing direction, `b > n*a` must hold for EVERY ordinary
   positive integer n. Merely `b > a` is insufficient; bounded b gives a unit.
7. The Hahn-field closure results on a class exponent subgroup are proved
   by reducing EACH polynomial to a set-sized divisible support group.
8. A field core inside a maximal residue field is not a proof that the whole
   residue field is algebraically closed.
9. The support-prime classification assumes BOTH term-closure and strong
   sum-closure. It is not a classification of all prime ideals.
10. The homomorphisms to No[i] need not preserve order, strong summability,
    arbitrary infinite sums, exponentiation, or an analytic structure.
11. Uniform families of class ideals are relations on parameters and ring
    elements. The proof never treats all proper class ideals as elements of
    one ordinary class, or forms a proper-class-indexed product of fields.

## 5. Verification performed and not performed

- The mathematical arguments received internal proof review for the listed
  support, finite-witness, quotient-coding, and class-recursion issues.
  This is NOT independent peer review.
- `code/verify.py` passed 133,770 deterministic finite assertions under
  Python 3.13.5. The exact groups and counts are recorded in `data/`.
- These finite checks cover finite cyclic rings, finite Boolean product
  rings, finite geometric remainders, dyadic polynomial/idempotent algebra
  over F_257, finite branch filters, and lexicographic exponent examples.
- The checks do NOT certify global choice, proper classes, infinite Hahn
  sums, arbitrary surreal supports, or historical novelty.
- No Lean, other proof assistant, or Wolfram verification of the main
  theorems was performed. No such verification is claimed.
- The PDF was built with pdfLaTeX, rendered to images, inspected visually,
  and checked programmatically for page-boundary overflow. Details are in
  `data/build_report.json`.

## 6. Unresolved questions retained in the article

The article leaves open the restricted choice strength, parameter-definable
maximal ideals, algebraic closedness of binomial residue fields, extensions
over the embedded Hahn core, larger same-fibre branching, nilradical and
idempotent structure of the full binomial quotient, removal of one support
closure hypothesis, and complete formal verification in explicit foundations.
