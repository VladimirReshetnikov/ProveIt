# Source and proof audit

Date of research manuscript: 23 September 2026.
Repository: VladimirReshetnikov/Surreal.
Pinned snapshot: `e93a06de3d0da021022b574b498324bb041a0fe8`.

## 1. Actual retrieval and review scope

Repository content was retrieved with the connected GitHub reader. The
recursive tree supplied the snapshot above. The root README and research
catalogue were read, followed by the guides for these relevant reports:

- `docs/surreal/omnific-preserving-automorphisms/README.md`
- `docs/surreal/independent-surreal-copies/README.md`
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`
- `docs/surcomplex/surcomplex-field-automorphisms/README.md`
- `docs/surcomplex/differential-equations/README.md`

The first 100 lines of the omnific Diophantine article were also fetched,
but that preamble was not substantive proof evidence. Some long guide
responses were truncated. The work does not claim to have read all source
manuscripts, every line of the large guides, or all other repository
reports. No independent repository build or Lean audit was performed.

The omnific-preserving guide attributes the monomial lifting,
arithmetic-preservation, and strongness developments to earlier reports.
The independent-copies guide makes the set-support and class-cut boundary
explicit. The surcomplex guide's Theorem 2.2 already gives the
real-form centralizer factorization. Those ingredients are credited in
the article and not claimed as new. The differential-equations report
concerns derivations, a different operator setting.

## 2. External primary sources

1. Elliot Kaplan, Lothar Sebastian Krapp, Michele Serra,
   *Decomposing the automorphism group of the surreal numbers*,
   arXiv:2509.22374v3.
   https://arxiv.org/abs/2509.22374v3
   HTML and PDF were inspected; PDF pages 1 and 6 were rendered through
   the web PDF screenshot tool. Definitions 2.5 and 2.8 and Proposition
   3.9 identify the established two-stage lifting mechanism. Section 2
   distinguishes class automorphisms from a set or class of all of them.
   Section 5 is a boundary, not an open-problem solution claimed here.
   The HTML and PDF displayed different manuscript-date strings; the
   bibliography therefore cites the version and year, not those strings.
2. Salma Kuhlmann, Michele Serra,
   *Automorphisms of valued Hahn groups*, arXiv:2302.06290v4.
   https://arxiv.org/abs/2302.06290v4
   The current HTML was consulted for the Hahn-group context.
3. Andrés Navas,
   *On the dynamics of (left) orderable groups*, Annales de l'Institut
   Fourier 60 (2010), no. 5, 1685–1740.
   https://aif.centre-mersenne.org/articles/10.5802/aif.2570/
   The primary journal publication page was used for bibliographic and
   ordered-group context. The manuscript proves its needed ordered-action
   lemmas directly; it does not purport to review the entire Navas paper.
4. Conway's *On Numbers and Games* (1976) and Gonshor's *An Introduction
   to the Theory of Surreal Numbers* (1986) are the classical background
   references for normal forms and arithmetic. Bibliographic/theorem
   pointers were cross-checked through the Kaplan–Krapp–Serra references;
   no newly supplied full copies of these books were read.

The user-supplied Wikipedia page was an orientation source, not a formal
proof dependency. Other broad search results were not used as mathematical
premises. Searches included combinations of surreal numbers,
left-orderable groups, Hahn automorphisms, and difference equations;
they did not establish a complete priority history.

## 3. The proposed contribution and the inherited components

Inherited and re-proved for precision:

- inner ordered Hahn lift and outer field lift;
- constant-term and leading-coefficient arithmetic;
- the invariant-support argument;
- real-closed positivity and the real-form centralizer factorization.

Developed as a connected theorem package in this manuscript:

- free equivariant cut completion with a regular group orbit at every cut;
- universality on the actual pair `(No, Oz)`, minimal fixed field for
  every nonidentity element, and an independent regular orbit;
- universality after fixing arbitrary set parameters, with an explicit
  common two-level fixed field;
- a general downward-orbit summability lemma and weighted Green inverse;
- exact additive and multiplicative obstruction maps, including the
  relative multiplicative retraction;
- the scalar constant-coefficient and first-order variable-coefficient
  classifications;
- central cocycle normal forms and the free-group boundary;
- group-embedding classification with named conjugation.

This division records the manuscript's contribution claim, not a certified
priority judgment. The package makes no claim to solve a named published
problem about exponential or omega-map-preserving automorphisms.

## 4. Proof obligations checked in the manuscript review

**Class foundations.** A group action is one joint class map with a set
of group indices. At each cut-completion stage, the current order, its
cut family, and the inserted copies are sets. Each partial back-and-forth
map is a set. Set supports have set images and countable orbit unions.
The centralizer group-classification proof uses actual set subgroups
and kernels of the acting group, not sets of proper-class functions.

**Freeness.** Adding one point at a stabilized cut would fail. Adding a
copy of the left-ordered regular group makes every nonidentity element
move every newly inserted point, including at stabilized cuts.

**Two levels.** The inner lift is an ordered additive map, not in general
a field map and not necessarily unital. The outer lift is multiplicative
because its exponent map is additive. Exact monomial preservation is
not commutation with the named omega-map.

**Fixed fields.** An invariant reverse-well-ordered support contains no
nontrivial ordered orbit: forward or backward iteration would produce
an increasing sequence. Apply this separately at both normal-form levels.

**Summability.** The downward-orbit proof establishes both reverse-well-
ordering of the union and finite incidence of every exponent. The proof
uses no Archimedean assumption, orbit cofinality, or ordinary convergence.
The weighted Green residuals are exact finite identities before the
coefficientwise limiting argument. On a general ordered index set the
proof compares `q(a)>a` or `q(a)<a`; it does not assume subtraction exists.

**Arithmetic.** Both forward and backward exponent iterates preserve the
sign of the exponent. Consequently normalized additive inverses preserve
purely infinite and infinitesimal support separately. Constant extraction
is not used as a ring homomorphism on the whole field.

**Relative multiplicative retraction.** The inner projection `Q_F` acts
on an exponent's normal form. The outer projection `P_H` acts on a field
element. The retraction acts independently on the leading coefficient,
leading monomial, and formal logarithm of the normalized infinitesimal
unit. Its restriction to the fixed field is the identity. Both normalized
Green inverses are required for surjectivity on its kernel. The retraction
is not asserted to be additive or to preserve the omnific ring.

**Variable coefficients.** The identity after substituting `x=u*y` is
`sigma(u*y)-a*u*y = sigma(u)*(sigma(y)-c*y)` with `c=lc(a)`.
The resonant obstruction is the constant coefficient of `b/sigma(u)`,
not of `b`. The current weighted scalar formula uses ordinary coefficients
in R or C, not arbitrary elements of a larger relative fixed field.

**Cocycles.** Centrality is explicitly used in the compatibility equation.
For a free group, generator values supply independent normalized residual
parameters, so a universal cohomology-vanishing assertion is not made.

**Surcomplex boundary.** The centralizer and group-classification result
requires standard conjugation as a named operation. It does not classify
all pure-field or Gaussian-ring-preserving actions.

## 5. Finite verification

`verify.py` is a deterministic standard-library Python program using exact
`fractions.Fraction` arithmetic. The delivered run passed 5,555 assertions
in 29 groups. `verification.json` contains the group counts and scope.

The program checks finite inner and outer Hahn operations, a rational
localized index action, finite Green residuals, finite exponent-separation
tests, the monomial part of the relative retraction, gauge and cocycle
identities, and truncated formal logarithm/exponential identities.
It does not verify the full relative logarithmic projection theorem on
arbitrary infinite supports, the class constructions, or any theorem in
a proof assistant. A second run reproduced the recorded output.

## 6. Remaining assurance limits

No independent referee, Lean checker, or exhaustive literature review has
certified the new theorem package. The mathematical justification is the
written proofs. No repository files have been altered. The delivered PDF
was compiled and visually reviewed; its build diagnostics are recorded
separately in `BUILD_REPORT.json`.
