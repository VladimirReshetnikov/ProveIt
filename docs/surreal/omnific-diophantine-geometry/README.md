# Omnific Integers and Omnific–Diophantine Geometry

**Retractions, rigidity, definability, and infinite families**
Merged research report, from three manuscripts written independently on
22 September 2026 (batch items 01, 02 and 05 of the batch placed in
`be06fc8`). Prepared for Vladimir Reshetnikov.

```
article.tex                        the report, standalone LaTeX with an internal bibliography
article.pdf                        the compiled report, 59 pages
README.md                          this guide
02-diophantine-PROVENANCE.md       source 02's provenance and verification-boundary note, as delivered
05-diophantine-rigidity-BUILD.md   source 05's build and check instructions, as delivered
code/
  01-diophantine-geometry-verification.py   source 01 checks (writes a JSON report; see below)
  01-diophantine-geometry-build.sh, .ps1    source 01's build scripts (they compile source 01's
                                            own file name and do not build this report)
  02-diophantine-verify_examples.py         source 02 checks
  05-diophantine-rigidity-verify_examples.py  source 05 checks
data/
  01-diophantine-geometry-verification_report.json   source 01's recorded run
  02-diophantine-verification.txt                    source 02's recorded run
  05-diophantine-rigidity-verification.txt           source 05's recorded run
  01-, 02-, 05-...-requirements.txt                  each pins sympy==1.14.0
```

The report uses the `odg:` label prefix. The source-01 base already appeared
in the ledger before the three-source assembly in `bbdd536`; the parallel
elementary review also added four results. This merge retains that review's
support and size clarifications, and preserves nine renamed or combined
labels as aliases (159 labels in total). See
[RECONCILIATION.md](RECONCILIATION.md) for the elementary claim correspondence,
the subsequent proof reviews through Section 11, and the remaining
source-reconciliation boundary. The [ledger](../../FORMALIZATION.md) indexes the current
67 standard results; it does not claim Lean coverage for this report.

Two further manuscripts, locally numbered 06 and 07 and placed in `cf350b1`,
are supplementary files only: their definability and reconstruction results
have not yet been integrated. The three-source assembly described below does
not include them. Their scripts and delivery audit files are retained under
`06-definability-reconstruction-` and `07-defining-arithmetic-` prefixes.

## Three sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **01** | *Omnific Integers and Omnific–Diophantine Geometry* | `2cb9c02` | The base text and structure; the exhaustive quadratic-level dichotomy including degenerate forms (Theorem 8.1); the five-auxiliary three-square guard (Theorem 10.3); rational directions (Theorem 11.5); no real point at infinity (Theorem 9.6); symmetric matrices (Corollary 9.5); the elementary uniqueness of `ct` (Proposition 3.5). Files prefixed `01-diophantine-geometry-`. |
| **02** | *Omnific Integers and Diophantine Geometry* | `2cb9c02` | Exact decomposable fibers (Theorem 6.2(a)); bounded semialgebraic rigidity (Theorem 9.2); decidable homogeneous existence with sign conditions (Theorem 11.2(b)); the square-discriminant criterion (Theorem 12.1); the general pair without a gcd (Theorem 4.10); the explicit Lorentz matrix and the unipotent subgroup (Corollary 8.4); nilpotent tests and mixed gcds. Files prefixed `02-diophantine-`. |
| **05** | *Omnific Integers and Diophantine Rigidity* | `2cb9c02` | Binary rigidity over `C` (Theorem 6.3); Euler derivations (Section 7); separated powers (Theorem 7.4) and unimodular Fermat (Theorem 7.9); the four-square definition of `Z` (Theorem 10.4); a failed existential induction (Theorem 10.9); failed lifting (Proposition 12.4, Example 12.5); finite-support specialization (Theorem 11.7). Also the universal set-sized quotient theorem, which is **printed in the sibling report** and only quoted here (Cited theorem 3.6). Files prefixed `05-diophantine-rigidity-`. |

The source manuscripts are not shipped; their code, data, source 02's
provenance note and source 05's build note are. The pin `2cb9c02` is 107
commits before `be06fc8`. Source 01's checksum manifest is not shipped
because it lists the delivered file names.

**Why one report.** All three prove the same spine: normal forms, the rings
`B_R ⊃ Oz = Z ⊕ Π`, degree and units, the floor, the retraction `ct` and its
congruences, the full-class common divisor and clearing, non-atomicity,
transfer and Hilbert's tenth problem, the Smith criterion, the unit lemma with
binary and Pell rigidity, homogeneous scaling, polynomial arcs, and the
unimodular Pythagorean family. It is printed once (Sections 2–6), naming the
sources of each statement. None of the three contradicts another. Source 01 is
the base because it has the weakest hypotheses on most shared statements.
Where another source is more general, its statement is printed and the others
are recorded as special cases: 02's exact fibers (01's rank-`n` theorem is
case (b) of Theorem 6.2), and 05's complex binary theorem.

**Kept twice, as different proofs.** Uniqueness of `ct`: 01's divisibility
proof (Proposition 3.5) and 05's route through the set-sized quotient theorem.
Homogeneous systems: 01's leading-coefficient proof, which needs no quantifier
elimination, and 02's Tarski proof, which handles sign conditions and
decidability (Theorem 11.2). The pair `(√2ω, ω)` without a gcd: 02's general
proof (Theorem 4.10) and 01's degree proof, which works in any divisible
workspace (Remark 4.11). Quartic definitions of `Z`: 01's (five auxiliary
variables, three squares) and 05's (six auxiliary variables, four squares).

**Added in the merge**, each tagged `[merge]` with a complete proof: an
explicit identity giving the divisibility step of the separated-power proof
without the quotient ring (Remark 7.5; checked symbolically for general
`a, b` and `2 ≤ m, n ≤ 7`), and the failure of existential induction in the
pure ring language, via `Std` (Remark 10.10).

**Notation.** The purely infinite ideal is `Π`, the letter used by the
foundations report (`found:eq:omnific`); the sources wrote `𝒥` (01) and `𝓘`
(02, 05). Exponents follow the Conway normal-form convention: `ω^γ` is infinite
for `γ > 0`, so `Π` consists of the normal forms supported on **positive**
exponents. The trigonometry report writes the same class with **negative**
`t`-exponents (`t = ω^(-1)`, at `trigonometry:eq:split`); Section 1.4 prints the
translation. Other renamings resolve collisions: the Lorentz Gram matrix is
`G` (02's `J`, which also named an index set and an ideal), the guard
polynomial is `Ψ_n` (01's `G_n`), the Euler derivation is `∂_λ` (05's `D_λ`,
which clashed with the Pell `D`), the Fermat exponent is `n` (05's `p`), and a
set-sized target ring is `S` (05's `A`, which was also 01's name for `Oz`). The
full per-source table is Table 1 in Appendix A.

## What the report claims

Numbers refer to the built `article.pdf`.

1. **Rings and integer part (Section 2).** `Oz`, `B_R = R ⊕ Π` and
   `B_C = B_R[i]` are domains; `ct` is a ring retraction onto `Z`, `R`, `C`
   (Proposition 2.2); units are `±1`, `R^×`, `C^×`, and bounded omnific
   integers are integers (Proposition 2.5); the exact floor, with the
   correction at a negative infinitesimal displacement (Theorem 2.7).
2. **Residues (Section 3).** `nOz = Π + nZ`, `n | x ⇔ n | ct(x)`,
   `∩ nOz = ∩ p^k Oz = Π` (Theorem 3.1); finite quotients are `Z/n`
   (Corollary 3.4); `ct` is the unique homomorphism to `Z` and endomorphisms
   preserve it (Proposition 3.5). The universal set-sized quotient theorem of
   source 05 is quoted as Cited theorem 3.6; Remark 3.7 notes that the Hartogs
   ordinal replaces 05's use of global choice.
3. **Full-class support (Section 4).** One monomial divides a whole set of
   purely infinite elements (Theorem 4.2); `Π² = Π`, `Π` is not generated by
   any set, `Oz` is not atomic (Corollary 4.3); `Frac(Oz) = No` (Theorem 4.6);
   `(t, rt)` has no gcd for `0 ≠ t ∈ Π`, irrational `r` (Theorem 4.10); the ring
   is not integrally closed (Proposition 4.12). These are full-class results.
4. **Transfer (Section 5).** An integer system has an omnific solution iff it
   has an integer one (Theorem 5.1); Hilbert's tenth problem over `Oz` is the
   ordinary one (Corollary 5.2); nonzero, positive and nonnegative are not
   positive-existentially definable (Proposition 5.3); linear systems are
   solved completely (Theorem 5.4, Theorem 5.5).
5. **Constant products (Section 6).** Exact fibers of decomposable equations
   at a nonzero level (Theorem 6.2); binary forms with two distinct projective
   factors over `C` at a level in `C^×` have only constant points in `B_C`
   (Theorem 6.3); Pell rigidity for every `D ≠ 0` (Corollary 6.5), the full
   class for `x² − 2y² = 1` (Example 6.6), central conics (Corollary 6.8), norm
   forms for any `Q`-basis (Theorem 6.10).
6. **Separated powers and Fermat (Section 7).** For complex `a, b, c ≠ 0` and
   `m, n ≥ 2`, every `B_C`-solution of `ax^m + by^n = c` is constant (Theorem
   7.4; extending source 05’s real case), so `y² = x³ + k` (`k ≠ 0`) and
   `x^m − y^n = c ≠ 0` have only ordinary omnific solutions (Corollary 7.6).
   For `n ≥ 3` a Fermat triple in `B_C`, with all three coordinates nonzero
   and generating the unit ideal, is constant (Theorem 7.9); with Wiles and
   Taylor–Wiles there is no such unimodular omnific triple (Corollary 7.10). The threshold is sharp at `n = 2`.
7. **Quadratic levels (Section 8).** For integral `q` and `c ≠ 0`: ordinary
   points only in the nondegenerate definite case and in dimension at most
   two; injective linear families for degenerate `q`; injective quadratic
   families through every integer point for nondegenerate indefinite `q` in
   at least three variables (Theorem 8.1). The quadratic matrix orbits preserve
   the coordinate ideal, hence carry primitive integer points to unimodular
   omnific points. `(Π, +)` embeds in
   `ker(SO(q, Oz) → SO(q, Z))` (Corollary 8.4).
8. **Bounded geometry (Section 9).** Bounded semialgebraic sets (Theorem 9.2),
   definite levels (Corollary 9.3), `O_n(Oz)` = signed permutations
   (Corollary 9.4), symmetric matrices with constant `tr(M²)` (Corollary 9.5),
   no real point at infinity (Theorem 9.6). The set-sized transfer argument
   includes quantified ordered-ring formulas. Any definite real form has a
   finite integer isometry group, while the signed-permutation description
   is specific to standard Euclidean coordinates.
9. **Defining `Z` (Section 10).** Theorem 10.3 (five auxiliaries, defines
   `Z^n`) and Theorem 10.4 (six auxiliaries, defines `Z`); `ct` and `Π` are
   first-order definable (Corollary 10.6); an explicit `Σ₁` induction instance
   fails (Theorem 10.9) while open induction holds. The workspace argument
   and the nonnegative domain of induction are explicit; an order-free
   semiring formula also defines exactly the ordinary naturals.
10. **Families and primitivity (Section 11).** Polynomial lifting (Proposition
    11.1); homogeneous cone criterion and its decidability (Theorem 11.2);
    unimodular Pythagorean triples (Proposition 11.4); a real direction has a
    primitive omnific representative iff it is rational (Theorem 11.5);
    every primitive representative of a real direction is an ordinary coprime
    integer tuple. Finite-support solutions specialize to polynomial arcs
    over real coefficients (Theorem 11.7, extending source 05's integer
    case); supplied finite-support Bézout witnesses specialize with them.
11. **Omnific coefficients (Section 12).** The square-discriminant criterion
    (Theorem 12.1), initial forms (Proposition 12.3), two-term roots
    (Proposition 12.4) and a simple residue root that does not lift (Example
    12.5).

**Questions (Section 14).** Two source questions are recorded as settled by
source 05 (Section 14.1): source 01's `Y² = X³ + 1` and coprime exponents, and
the unimodular half of the Fermat questions of sources 01 and 02. Still open:
affine varieties and curves, including `Y² = X³ + aX + b` with `a ≠ 0`
(Question 14.1); primitive, non-unimodular Fermat triples (Question 14.2);
primitive homogeneous solutions (Question 14.3); an existential definition of
`Π` (Question 14.4); the guard's complexity (Question 14.5); roots with
omnific coefficients (Question 14.6); the size boundary (Question 14.7);
finite-support search (Question 14.8). No source claims that these are open in
the literature.

## Corrections made in the merge

- Source 02 stated Pell rigidity for `D > 0`; its proof needs only `D ≠ 0`.
- Source 01's abstract said "nondegenerate binary forms"; its theorem needs
  only two distinct projective linear factors (weaker in degree ≥ 3, e.g.
  `X²Y`).
- Matiyasevich, *Soviet Math. Dokl.* 11 (1970): source 02 gave pages 354–358,
  source 05 354–357. The report uses 354–357, the range given with MR 258744
  in Bhatt and Poonen's notes *Diophantine sets* and in the title of the
  *Journal of Symbolic Logic* review.
- Source 05's set-sized quotient proof uses global choice where the Hartogs
  ordinal suffices (Remark 3.7).
- Source 01's isotropic-vector lemma assumed `q(a) ≠ 0` where `a ≠ 0` suffices
  (Lemma 8.3).
- Source 02 credits MathOverflow comments by Jeřábek (2018) and Chow (2021)
  for the observation that nonzero Fermat solutions exist in `Oz`. The site
  could not be reached; the attribution is printed as source 02's and marked
  unverified (after Example 11.3).
- The assembly reported no mathematical error in its main proofs. The later
  Sections 5–7 review corrected the added divisibility identity: it requires
  the derivation to kill `a` and `b`, and its use at level `c` also requires
  `∂c = 0`. The Euler derivations satisfy these hypotheses. The review also
  extends one-variable and separated-power rigidity to complex coefficients,
  explains the support-ring witnesses in Fermat rigidity, and distinguishes
  these local Euler derivations from the normalized surreal derivation.
- The Sections 8–9 review makes polarization and the isotropic complement
  explicit, proves preservation of coordinate ideals along the quadratic
  orbits, and fills in transfer of quantified formulas from `No` to a
  set-sized real closed field. It includes empty definite levels and shows
  why symmetry and the chosen polynomial generators matter in the two
  matrix/leading-form criteria. The exact review boundary is in the
  reconciliation record.
- The Section 10 review expands the finite bounds and divisibility test,
  specifies the induction domain, and gives nonnegative witnesses for the
  order-free arithmetic formula. The open-induction argument explicitly
  transfers quantifier-free truth to a set-sized Hahn workspace.
- The Section 11 review strengthens the description of primitive real
  directions, expands the finite ordered specialization argument, and
  extends the arc theorem to real coefficients. Finite-support Bézout
  witnesses and the positive-parameter sign condition are explicit.

**Stale repository statements.** Source 01 said the repository's
trigonometry material used the omnific integer part; at the pin the
foundations report already defined `Oz = Π ⊕ Z` (`found:eq:omnific`). All
three correctly found no omnific report and no omnific Lean at the pin; the
collection now has this report and its sibling, and still no Lean.
Descriptions of `docs/NORMAL_FORM_BRIDGE.md` and the `Surreal/Foundations/`
workspace modules remain accurate.

## What the report does not claim

No non-claim of any source was dropped. Appendix B lists them per source (01:
24 items, 02: 22, 05: 26, plus the caveats common to all three). The main
ones:

- **Status.** AI-assisted; not refereed; nothing formalized in Lean; the finite
  scripts check identities and examples, not theorems. The repository was
  inspected through the GitHub connector at the pin, not checked out or built.
- **Priority.** None is claimed. Source 01 names the quadratic classification
  and the guard, source 02 the exact decomposable fibers and uniform quadratic
  lifting, and source 05 the separated-power, unimodular Fermat and set-sized
  quotient proofs as their most distinctive contributions. None is certified
  new.
- **Rigidity is not finiteness.** No Thue or Baker finiteness, no bounds and no
  algorithm for the ordinary integer solutions; a finite search does not
  certify a complete solution list.
- **Transfer is about existence.** It says nothing about fiber sizes;
  nonvanishing and order do not transfer; omnific coefficients are not
  covered by the Hilbert's-tenth-problem statement.
- **Quadratic levels.** Only the presence of infinite points on represented
  nonzero levels is classified; not every point lies on the constructed
  orbits; source 02's version excludes degenerate forms and the zero level.
- **Definability.** The guards are not claimed optimal; the definitions of
  `Π` and `ct` are first-order, not existential.
- **Fermat.** Scaling solutions are not primitive; Theorem 7.9 says nothing
  about triples that merely lack a common nonunit divisor.
- **Elliptic curves.** `y² = x³ + ax + b` with `a ≠ 0` is outside the method.
- **Full class versus workspace.** Common divisors, clearing, `Frac(Oz) = No`,
  non-generation of `Π`, the general no-gcd pair and the set-sized quotient
  theorem are not asserted for fixed Hahn workspaces; the quotient theorem
  does not apply to class-sized targets.
- **Refinement.** The 18 September 2026 announcement of a Lean proof of
  Conway's refinement conjecture is recorded, not audited and not used; no
  result assumes refinement, GCD or UFD properties.
- **Formalization.** The proposed Lean modules (Section 13.2) are proposals.
  At the repository's Mathlib pin (`81a5d257`) `Nat.sum_four_squares` exists and
  no three-square theorem does, so only source 05's quartic definition rests
  on a theorem in Mathlib.

## Relation to neighbouring reports

- [`foundations`](../../foundations-and-computation/foundations/) defines
  `Oz = Π ⊕ Z` (`found:eq:omnific`, subsection `found:sub:omnific`); this report
  develops its arithmetic with the same letter `Π`.
- [`trigonometry`](../../surcomplex/trigonometry/) uses the opposite
  (`t`-exponent) sign for `Π` (`trigonometry:eq:split`); its integer-part
  construction agrees with Theorem 2.7, and `2πOz = Π + 2πZ`
  (`trigonometry:eq:periodclass`) rests on the same fact as Theorem 3.1.
- [`gamma-and-zeta-functions`](../../surcomplex/gamma-and-zeta-functions/):
  the parity statements of `gz:cor:canonical-zeros` are instances of Theorem
  3.1.
- [`transcendence-over-bounded-support`](../transcendence-over-bounded-support/):
  its GCD hypothesis (`bst:hyp:gcd`) is about a different ring, whose units are
  the monomials; Theorem 4.10 concerns `Oz`, whose units are `±1`. No conflict.
- [`set-sized-quotients-of-omnific-integers`](../set-sized-quotients-of-omnific-integers/)
  contains a more general coefficient-ring form of the universal set-sized
  quotient theorem in its installed base; companion-source integration remains pending; its
  preliminaries overlap Sections 2–4 here.
- [`euclidean-three-space`](../euclidean-three-space/):
  `e3:cut:thm:smallquotient` is the analogous size phenomenon for `SO(3, No)`;
  by Corollary 9.4, `SO(3, Oz)` is finite.

## Build and reproduce

The report uses standard TeX Live or MiKTeX packages (`lmodern`, AMS
packages, `mathtools`, `aliascnt`, `booktabs`, `longtable`, `enumitem`,
`xcolor`, `fancyhdr`, `xurl`, `hyperref`, `cleveref`). No bibliography
processor is needed:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build gives 55 pages with no errors, warnings, undefined references or
overfull boxes. Source 01's `code/01-diophantine-geometry-build.sh` and `.ps1`
compile source 01's delivered file name (`omnific_integers.tex`), which is not
shipped; they do not build this report. Source 05's build note names its
delivered file names (`article.tex`, `verify_examples.py`,
`requirements.txt`); here they are this report's `article.tex`,
`code/05-diophantine-rigidity-verify_examples.py` and
`data/05-diophantine-rigidity-requirements.txt`.

The checks need Python 3.9 or later and SymPy (tested with 1.14.0). From this
directory:

```text
python -m pip install -r data/01-diophantine-geometry-requirements.txt
python code/01-diophantine-geometry-verification.py --output <scratch>/verification_report.json
python code/02-diophantine-verify_examples.py
python code/05-diophantine-rigidity-verify_examples.py
python code/05-diophantine-rigidity-verify_examples.py --standard-radius 200
```

Source 01's script **writes** a JSON report, by default
`verification_report.json` in the working directory; pass `--output` with a
path outside this directory (as above) or run it on a copy, so that the shipped
`data/01-diophantine-geometry-verification_report.json` stays the delivered
record. The other two print to the terminal only.

When this report was assembled all three passed with Python 3.14.4 and SymPy
1.14.0: source 01's checks cover scalar identities, 20 quadratic-isometry cases
(dimensions 3–7), 31 Pell pairs and 256 guard witnesses; source 02's 13
identity checks and 49 finite-support products; source 05's nine groups,
including quartic certificates for `|t| ≤ 40` (and `≤ 200` with the option).
The outputs of sources 01 and 02 differ from the shipped records only in the
recorded Python version (3.13.5 there); source 05's output is identical to its
record.
