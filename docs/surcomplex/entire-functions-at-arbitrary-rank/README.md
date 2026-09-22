# Cofinality, Factorization and Scalar Extension for Entire Hahn Functions at Arbitrary Rank

**A merged research report, 88 pages, from five manuscripts.** Everything in
this directory other than `article.tex`, `article.pdf` and this README is
preserved source material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled 88-page report
README.md     this guide
07-scale-moderate-interpolation-SOURCE_AUDIT.md   source 4: provenance, scope and novelty audit
code/         the five source verification programs, unmodified, and two delivered build helpers
data/         the recorded verification runs, the sources' build reports, source 4's
              package manifest and source 5's research audit
```

Every label in `article.tex` carries the prefix `ent:`. Material added from
the fourth source carries `ent:sm:`, and from the fifth `ent:mv:`. File names
keep the local numbers they were placed under: `06` is the first source,
`03` the second, `01` the third, `07` the fourth and `08` the fifth.

| file prefix | source | pinned commit | contribution |
|---|---|---|---|
| `06-cofinality-bezout-trichotomy` | 1 | `4896a28` | trichotomy, non-Bézout pair |
| `03-cofinality-and-scalar-extension` | 2 | `aa84627` | scalar-extension package |
| `01-exact-jet-image` | 3 | `a3124af` | exact image of the infinite jet map |
| `07-scale-moderate-interpolation` | 4 | `0097304` | second proof of the image; ideal theory above the product |
| `08-multivariate-extension` | 5 | `4cf691c` | several variables: exact extension domains |

## What the report is

Two independently written manuscripts, both dated 21 September 2026, each
written against its own pinned snapshot of this repository, studied the same
object: ordinary power series `sum a_n Z^n` over a **fixed** Hahn field
`K_Gamma = C((t^Gamma))` with `Gamma` a set-sized divisible ordered abelian
group of arbitrary valuation rank, where *entire* means strongly
Hahn-summable at every point of that one field. Both explicitly disclaim all
of `No[i]`. This report is their **union**, not a selection. They proved the
same engine — coefficient criterion, cofinality dichotomy, support-controlled
preparation, root counts, genus-zero canonical product, factorization by
zeros, change-of-workspace criterion — and each is printed **once**; their two
payloads, a ring-theoretic trichotomy and a scalar-extension package, are both
kept in full.

A **third manuscript** (22 September 2026, pinned at `a3124af`) was written
against the merged report and answered the question it had recorded as open
under the heading *The missing image of the infinite jet map*, now Question
15.1, marked answered. Its contribution is Theorem 1.6, proved in Section 8.
Its `rho_n` was a value-group radius and its `a_(n,j)` a field point, the
reverse of this report; everything taken from it was rewritten.

A **fourth manuscript** (22 September 2026, pinned at `0097304`) set out to
answer the same question. At its pin the question was open, so its claim to
resolve it was accurate there; it is **stale now**, because the third source
had been merged at `de84d8b`, about an hour after that pin. It is recorded as
an **independent second proof** of Theorems 8.6, 8.7 and 8.26 under the same
hypotheses, not as their source. Its sufficiency construction, by cardinal
corrections with an explicit truncation bound, is kept as a marked second
route (Section 8.5). Its genuinely new results are the finite-generator and
membership criteria, the exact threshold for paired zeros, and the complete
list of maximal ideals above a one-node-per-shell product, with its topology,
residue-field type and boundary coordinate (Sections 8.7 and 8.9). Two of its
letters are **swapped** with this report's: its `C_n` is our convex subgroup
`H_n`, and its `H_n` is a correction, our `C_n`. Several more shift. The
conversion tables are in Section 2.5.

A **fifth manuscript** (22 September 2026, pinned at `4cf691c`, after the
third source was merged) answers the scalar-extension clause of Question 15.5
(`ent:q:several`), and only that clause. It is the new Section 11, which also
absorbs the finite-variable criteria formerly in Appendix B; their labels
`ent:app:multivariate`, `ent:thm:multi-criterion` and `ent:thm:multi-unit`
are kept, and the appendices after it moved up one letter (checks are now
Appendix B, the source ledger Appendix C).

## What the report claims

Write `cf(Gamma)` for the cofinality of the value group as an ordered set,
and call `delta > 0` an **order unit** when its positive integer multiples
are cofinal in `Gamma`.

**1. The trichotomy (Theorem 1.5).** For `Gamma != 0`, the entire ring
`E_Gamma` is a GCD domain with units exactly `K_Gamma^times`, and exactly one
of:

| Value group | Entire series | Ideal structure |
|---|---|---|
| `cf(Gamma) > aleph_0` | only polynomials | PID |
| an order unit exists | nonpolynomial series exist | Bézout, non-Noetherian, full Hermite interpolation |
| `cf(Gamma) = aleph_0`, no order unit | nonpolynomial series exist | GCD but **not** Bézout |

For `Gamma = 0`, strong Hahn summability gives `E_0 = C[Z]`.

In the third case, with `gamma_(n+1)` exceeding every finite multiple of
`gamma_n` and cofinal, the canonical products with roots
`rho_n = t^(-gamma_n)` and `sigma_n = t^(-gamma_n) + t^(gamma_(n+1))` have
**disjoint simple zero sets and gcd 1, yet generate a proper ideal**
(Theorem 8.29). Section 4 makes the middle case **sharp**: a nonconstant
valuation-restricted series is invertible in `T_Gamma` if and only if its
least coefficient gap is a positive order unit (Theorem 4.1).

**2. The exact image of the infinite jet map (Theorem 1.6).** Group the nodes
of an infinite radially finite divisor `D` into valuation shells of radii
`gamma_1 < gamma_2 < ...`, let `R_n` be the finite Hermite polynomial of shell
`n` in the normalized coordinate, and let `V_n` be the valuation ring that
kills the Archimedean scale of `gamma_n`. An entire function realizing all
the prescribed jets exists **if and only if** `R_n` has coefficients in `V_n`
for all sufficiently large `n` (Theorem 8.6), with no bound on nodes per
shell, jet orders or scale exponents. So `E_Gamma / (P_D)` is an algebraic
restricted product of finite shell algebras (Theorem 8.7), and
`A P_D + B F = 1` is solvable exactly when `F` is nonzero at every node with
eventually `V_n`-bounded values (Theorem 8.26). Two independent sufficiency
proofs are printed: the sequential one of the third source and the cardinal
one of the fourth (Lemmas 8.17–8.19, truncation bound Corollary 8.20).
Without an order unit the restriction never disappears (Corollary 8.16). The
restricted product is an algebraic union, **not** a topological or adelic
object.

**3. Ideals and maximal ideals above a canonical product (fourth source).**
- `(P_D, G_1, ..., G_s) = E` exactly when at every node some `G_l` is
  nonzero and, on late shells, some `G_l` has value valuation in `H_n`,
  equivalently a gcd condition over the residue field, residue collisions
  allowed (Theorem 8.27). For one simple node per shell, membership of an
  arbitrary `F` in `(P_D, G)` is decided by the ratios `F/G` at the nodes
  (Corollary 8.28).
- For the paired products with `sigma_n = rho_n + t^(theta_n)`, and no
  Archimedean domination assumed, the pair generates the unit ideal **iff**
  `theta_n` lies in `H_n` eventually (Theorem 8.30); Theorem 8.29 is the
  case `theta_n = gamma_(n+1)`.
- For one node per shell, **any multiplicities**, the maximal ideals
  containing `P_D` are exactly the evaluation ideals and one ideal
  `M_U` per nonprincipal ultrafilter, with residue field
  `prod_U C((t^(H_n)))` (Theorem 8.36; Theorem 8.33 is the simple-node
  construction). The maximal spectrum of `E/(P_D)` is homeomorphic to
  `beta N` (Theorem 8.37). For the paired example the maximal ideals
  containing both functions are exactly the `M_U` with
  `{n : theta_n not in H_n}` in `U` (Corollary 8.38). The residue fields are
  algebraically closed (real closed over `R`) (Corollary 8.39), and `Z`
  maps to a transcendental coordinate (Proposition 8.40, a Henriksen
  Theorem 5 analogue, not claimed as a new phenomenon).
- All of Section 8's image, quotient, Bézout and ideal statements also hold
  over `R((t^Gamma))`, without algebraic closedness (Proposition 8.42,
  Remark 8.43).

**4. The scalar-extension package (Theorem 1.7).** For any ordered-group
extension of nonzero divisible groups `Gamma` inside `Delta`, *every* nonpolynomial entire series over
`K_Gamma` has the **same** exact strong evaluation domain in `K_Delta`: the
valuation ring `D_(Gamma,Delta)` of `v_Delta` coarsened by the convex hull
`H` of `Gamma`, with residue field `C((t^H))`. Entireness survives exactly
for cofinal extensions; no new zeros appear; on a noncofinal extension no
alternative entire series agrees with the old one even on `C`; and `Gamma`,
the slopes `v(a_n)/n` for `n >= 1` with `a_n != 0` and the negated
valuations of nonzero zeros generate the same
convex subgroup.

**5. Several ordinary variables (Section 11, fifth source).** Here **no
divisibility** is assumed and the coefficient field is any trivially valued
field. For a whole-family entire `F = sum a_alpha X^alpha` and a point `z`
with nonzero coordinates in the larger field, the family `(a_alpha z^alpha)`
is strongly summable **iff** the weight set
`{ sum_j alpha_j (v(z_j) + H) : a_alpha != 0 }` is well ordered in
`Delta/H` (Theorem 11.8). Infinite fibres are allowed; within the entire
category higher Hahn tails do not matter (Corollary 11.9), which corrects the
guess in Question 15.5. The one-variable domain is recovered without
divisibility (Corollary 11.10); semilinear supports give finitely many weak
inequalities (Theorem 11.15); the domain can be a nonclosed cone
(Theorem 11.17). For the separate **homogeneous-block** convention, which is
never called entire: along old-field rays the domain is `K_Delta` or
`D_(Gamma,Delta)` according as the line restriction is a polynomial
(Theorem 11.23); the polynomial-direction locus is a countable union of
projective algebraic sets with dense complement (Theorem 11.27), every proper
such union is realized when `cf(Gamma) = aleph_0` (Theorem 11.28), and in two
variables the loci are exactly the at most countable subsets of `P^1(C)`
(Corollary 11.29). The finite-variable coefficient criterion is now stated
division-free under these weaker hypotheses (Theorem 11.3); the unit criterion
(Theorem 11.5) keeps the report's standing hypotheses.

## Three things to read before using a theorem from here

**The two extension statements are one statement (Remarks 1.8 and 10.6).**
One source states the noncofinal case negatively — the series is *not
entire* over `K_Delta`, and `E_Delta ∩ K_Gamma[[Z]] = K_Gamma[Z]` — while the
other proves the same series stays strongly summable on exactly
`D_(Gamma,Delta)` and keeps all its zeros there. They are the coarse and the
exact form of one fact; Section 13.3 exhibits the concrete pair.

**One name for the order invariant (Remark 1.4).** *Order unit* and
*cofinal-cyclic element* are the same condition; the report keeps **order
unit**. It is **not** `cf(Gamma)`: an order unit forces countable cofinality
but not conversely, and that gap is exactly the third case of the trichotomy.

**Ring discipline and summation discipline (Convention 1.2, Section 11).**
Every statement names its coefficient ring:
`K_Gamma[Z] ⊆ E_Gamma ⊆ T_Gamma ⊆ A_Gamma ⊆ K_Gamma[[Z]]`, all with Hahn
series over `C` as coefficients, never `O(U)((t^Gamma))` or
`C{z}((t^Gamma))`. In several variables, *entire* means summability of the
whole monomial family; homogeneous-block evaluation is a different convention
and is never called entire.

## Explicit examples

`Gamma_infinity = ⊕_{j>=0} Q*omega^j` has countable cofinality and no order
unit. In it the Bézout counterexample has roots `omega^(omega^n)` and
`omega^(omega^n) + omega^(-omega^(n+1))`; the maximal ideals containing the
pair are exactly the `M_U`, `U` nonprincipal, with residue fields built on
`⊕_{0<=j<=n} Q e_j` (the fourth source's own group omits `e_0`); the values
`omega^(n! omega^n)` at `omega^(omega^n)` are interpolated by an explicit
cardinal series (Remark 8.21) while `omega^(omega^(n+1))` are not. The
product `prod_{j>=0} (1 - t^(e_j) Z)` has the simple positive surreal zeros
`omega^(omega^j)`. `Q^d` lexicographic and `Q e_1 + Q e_2` have order units
and are Bézout; `Gamma_(omega_1)` has uncountable cofinality and admits only
polynomials — **rank is not the driver**. Section 13.2 has the rank-two
hidden-tail pair and Section 13.6 the separation table. In several variables
(Section 11): `sum t^(n^2) (XY)^n` is evaluable at `X = omega^omega`,
`Y = omega^(-omega)`; `sum t^(n^4) X^n Y^(n^2)` has a nonclosed domain; and
`1 + sum t^(n^2) prod_(j<=n) (Y - c_j X)` has polynomial directions exactly
`[1 : c_m]`.

## What the report does not claim

- No named published conjecture is solved. Priority is **not** certified by
  any source; literature checks were targeted, and searches returning nothing
  were not treated as evidence of absence. None of the five manuscripts was
  refereed or machine-checked; **no Lean verification is claimed**.
- Classical inputs are credited, not claimed: rank-one factorization, Newton
  polygons and canonical products, the Hahn–Neumann support lemmas, algebraic
  closedness of Hahn fields, the rank-two distinction between positive
  valuation and topological nilpotence, the ultrafilter method for maximal
  ideals (Henriksen, Bruno), the finite-word well-quasi-order theorem, the
  Hilbert basis theorem, Conway normal forms, and the Ma–Neelon realization of
  algebraic unions as convergence sets (which are **not** polynomial-direction
  loci).
- Outside Section 11, `Gamma` must be divisible and algebraic closedness is
  used essentially in the factorization theory. Section 11 works under weaker
  hypotheses, and none of the divisible-group results — in particular zero
  conservation — is transferred to it.
- The maximal-ideal classification is for **one node per shell** only;
  several nodes per shell, prime ideals, and maximal ideals of `E_Gamma`
  containing no such product are not treated (Question 15.4 stays open,
  re-scoped). The unit-ideal criteria are **not** a corona theorem. The
  ultrafilter characters are ring homomorphisms and are not asserted to
  preserve strong sums; `Phi_U(P_D)` must not be computed termwise.
- In several variables only the scalar-extension clause is answered:
  preparation, interpolation, divisors, ideals and GCD/Bézout remain open
  (Question 15.5), as do the block domain at arbitrary new-field tuples
  (Question 15.6) and effective support classes (Question 15.7). The number
  of variables is finite; all fields are full Hahn fields.
- All supports and index sets are sets; the extension theorems keep the
  coefficient field fixed; the hidden-tail table covers monomial arguments
  only; strong summability, intrinsic valuation convergence and the fine
  surreal topology are never identified. "Entire" always has fixed-field
  scope, and nothing here argues against all-scale polynomial rigidity, which
  the report re-derives and credits.
- The constructions are finite-step only relative to exact field operations
  and valuation certificates; they are not algorithms for arbitrary Hahn
  input. Section 15.3 preserves every limitation recorded by any source.

## Open questions, re-scoped

- Question 15.1 (the image): answered by the third source, independently by
  the fourth.
- Question 15.3 (finitely generated ideals): answered for one generator a
  canonical product; now also for finitely many generators, and membership of
  arbitrary elements for one simple node per shell. Open: shells with several
  nodes or multiplicities, and the ideal beyond membership tests.
- Question 15.4 (maximal spectrum): answered above a one-node-per-shell
  product. Open: several nodes per shell, whether every non-evaluation maximal
  ideal contains such a product, primes, relations between divisors.
- Question 15.5 (several variables): the "In particular" clause answered by
  the fifth source; the rest open. Questions 15.6 and 15.7 are new.

## Stale statements corrected

- The fourth source presents itself as resolving "the repository's explicitly
  unidentified infinite jet image". True at its pin `0097304`; stale now, since
  the third source answered the question first in this tree. Recorded as an
  independent second proof (Section 1.4, Appendix C).
- Its phrase "a previously known disjoint-zero counterexample" is Theorem 8.29,
  and the "nonconstructive assertion that some non-evaluation maximal ideal
  contains a proper two-generated ideal" is Corollary 8.32; both hold.
- The fifth source's "Appendix `ent:app:multivariate`" is now Section 11.2.
  Its pinned blob `f034bdb` differs from the base of this merge only in the
  two appendices updated for the third source.
- The earlier text said that `m_gamma(FG) = m_gamma(F) + m_gamma(G)` "is never
  needed"; the cardinal route needs it, and Section 2.5 says so. Scope
  paragraphs that posed the several-variable replacement as open, and the
  non-claims attached to Theorem 8.33, now state what the new sources proved
  and what remains open.

## Relation to the rest of the collection

- **`surcomplex/rank-one-berkovich` — this report extends it.** Rank one is
  `cf(R) = aleph_0` with `1` an order unit, so it lands in the **Bézout**
  case. Its `prop:rankobstruction` is why Lemma 9.1 builds a *coarsening*,
  not an embedding. Its ring chain resembles ours and is not the same chain.
- **`surcomplex/analysis` and `foundations-and-computation/foundations`.** The
  whole-class rigidity corollaries (Corollary 10.12 and Proposition 11.32) are
  re-derivations in their whole-family forms; the foundations localization
  principle is consumed, and Lemma 11.30 gives the fifth source's short proof
  of it with credit.
- **`surcomplex/global-divisors` — a different ring.** Its support-restricted
  Chinese remainder theorem restricts something else, for other reasons, in
  `O(U)((t^Gamma))`; Section 14 states the difference, which covers the fourth
  source's restricted product too.
- **`surcomplex/analytic-geometry`** calls an ideal *free* when it has no
  common zero, and its "boundary" is that of a fixed disk. The fourth source's
  *free ultrafilter* and *boundary ideal* are written "nonprincipal" and
  "non-evaluation" here. Different rings; nothing transfers.
- **`surcomplex/holonomic-rigidity-for-entire-hahn-functions`** uses the same
  whole-family convention in several variables. The covering step of Theorem
  11.27 is the countable-field device of its `hol:lem:generic`. No shared
  theorem.
- **`surcomplex/nonabelian-support`** uses `Pol` for a normalized polar
  factor; the polynomial-direction locus is written `Pdir` here.

## What was run

- All five suites, from copies outside the repository, on Python 3.14.4:
  `06-…-verify-examples.py` 831 of 831, identical to the delivered record
  except its recorded Python version; `03-…-verify.py` 664;
  `01-exact-jet-image-verify.py` 1958; `07-scale-moderate-interpolation-verify.py`
  1876 in 12 categories; `08-multivariate-extension-verify_examples.py` 1072 in
  10 categories. The last four outputs are identical to the delivered records
  up to line endings.
- The SHA-256 hashes in `data/07-…-package_manifest.json` match the three
  source-4 files shipped here (the script, the record and the source audit);
  the manifest also lists that manuscript's own `article.tex`, `article.pdf`
  and `README.md`, which are not shipped. `data/08-…-build.json` likewise
  hashes the fifth manuscript's own source and PDF, not shipped.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`: 88
  pages, 0 errors, 0 undefined references or citations, 0 multiply defined
  labels, 0 duplicate PDF destinations, no overfull or underfull boxes, no
  LaTeX or package warnings. 139 numbered statements: 34 theorems, 23 lemmas,
  14 propositions, 29 corollaries, 11 definitions, 1 convention, 7 examples,
  8 questions, 12 remarks.

The checks prove no infinite theorem. In particular the **finite truncations
of the counterexample pair are coprime polynomials and do satisfy polynomial
Bézout identities**, so no finite computation can witness the main negative
result. Appendix B states what each suite checks and cannot check.

## Build and reproduce

A normal TeX Live or MiKTeX installation with the packages named in
`article.tex` and `latexmk` is sufficient. The bibliography is embedded: no
BibTeX file, external graphics, shell escape or repository checkout is needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

**Run the programs on a copy, or with an output path outside this
directory.** All use only the Python standard library.

- `06-cofinality-bezout-trichotomy-verify-examples.py` requires `--output`
  and exits nonzero without one; it cannot overwrite the delivered record by
  accident.
- `03-cofinality-and-scalar-extension-verify.py` takes no arguments and writes
  `verification.json` and `verification.txt` into the `data/` directory next
  to its own `code/` directory. Copy it into a scratch `code/` folder first.
- `01-exact-jet-image-verify.py` requires an output path and refuses to
  overwrite an existing file.
- `07-scale-moderate-interpolation-verify.py` and
  `08-multivariate-extension-verify_examples.py` take an optional `--output`
  and otherwise only print. Their documented commands write
  `data/verification.json`; name a scratch path instead.

```sh
mkdir -p /tmp/ent/code /tmp/ent/data
cp code/*.py /tmp/ent/code/
python /tmp/ent/code/06-cofinality-bezout-trichotomy-verify-examples.py --output /tmp/ent/A.json
python /tmp/ent/code/03-cofinality-and-scalar-extension-verify.py        # writes /tmp/ent/data/
python /tmp/ent/code/01-exact-jet-image-verify.py --output /tmp/ent/C.json
python /tmp/ent/code/07-scale-moderate-interpolation-verify.py --output /tmp/ent/D.json
python /tmp/ent/code/08-multivariate-extension-verify_examples.py --output /tmp/ent/E.json
```

`code/03-cofinality-and-scalar-extension-Makefile` and
`code/06-cofinality-bezout-trichotomy-build.sh` build their source manuscripts
in their original layouts and do not build this report; they are kept only as
delivered.

## Maintained review scope

The maintained proof review read the first two manuscripts and their former
finite-variable appendix before the three later manuscripts were incorporated.
The expanded portions have not received that review. It clarified the fixed-element order-unit
equivalence, the nonzero-group convention and the nonzero indices in the
extension summary; strengthened the growth barrier to require a sequence
that tends cofinally to infinity (with a counterexample to mere cofinality
of its range); supplied direct linear-division and multivariable
coefficient-criterion arguments; and separated the preparation-based finite
zero bound from algebraic closedness. The conclusion now states the
universal Bézout property separately from identities for individual pairs.
The imported Hahn-field scope was checked against Poonen, Section 3 and
Corollary 4; the positive-valuation versus topological-nilpotence distinction
against Conrad, Section 6.2; and the complete real-valued setting of the
classical entire-function results against Cherry's lectures. These checks
do not establish priority or independent peer review.

The review reran the first two unmodified programs on temporary copies:
**831/831** and **664/664** checks passed. This does not verify the later suites
or the infinite mathematical statements.
