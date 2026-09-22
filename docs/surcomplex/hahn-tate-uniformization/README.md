# Hahn–Tate Uniformization at Arbitrary Valuation Rank

**Exact summability domains, integral node charts, surcomplex elliptic curves, torsion ramification, and multiscale theta series**
Merged research report, 22 September 2026, from three manuscripts written
independently on the same day. Prepared for Vladimir Reshetnikov.

```
article.tex      the report, standalone LaTeX with an internal bibliography
article.pdf      the compiled report, 62 pages
README.md        this guide
PROOF_AUDIT.md   claims, inputs, dependency map and verification boundaries
03-tate-uniformization-PROOF_STATUS.md   source 03's own proof-status file, as delivered
code/            check_identities.py                        (source 01)
                 02-multiscale-theta-verify.py              (source 02)
                 02-multiscale-theta-build.sh               (source 02, see "Build")
                 03-tate-uniformization-verify.py           (source 03)
                 03-tate-uniformization-build.sh, .ps1      (source 03, see "Build")
data/            verification.json, verification.log,
                 requirements.txt, build_validation.json    (source 01)
                 02-multiscale-theta-verification.json,
                 02-multiscale-theta-verification.txt       (source 02)
                 03-tate-uniformization-verification.json   (source 03)
```

Every label in `article.tex` carries the prefix `tate:`. Material from source
03 carries the sub-prefix `tate:node:` (five of its labels would otherwise have
collided with existing ones, among them `tate:thm:main`), and material from
source 02 carries `tate:theta:`. **No pre-existing label was renamed or
removed**: the report had 92 labels before this merge and has 223 after it,
and all 92 original labels are still present. `docs/FORMALIZATION.md` cites no
`tate:` label.

## Three sources, one report

| | Manuscript | Repository pin | Contributes |
|---|---|---|---|
| **01** | *Hahn–Tate Uniformization at Arbitrary Valuation Rank* | `a3124af` | The base text of Part I (Sections 1–7 and 10–13) and the first proof of Theorem 1.2. Unprefixed files. |
| **02** | *Finite Positive Generation and Multiscale Theta Series over the Surreals* | `a3124af` | Part II (Sections 14–21). Files prefixed `02-multiscale-theta-`. |
| **03** | *Tate Uniformization over Surcomplex Numbers: Sharp Hahn domains, support-controlled coordinates, and exact valuation geometry at arbitrary rank* | `0097304` | Lemma 2.2; the second proof (Section 8); Section 9; Section 10.3; Corollary 13.2; Example 13.4; three open directions of Section 23; the Molcho–Wise precedent. Files prefixed `03-tate-uniformization-`. |

The source manuscripts themselves are not shipped; their code, data and
source 03's proof-status file are, under the prefixes above. Source numbers are
local to this directory (source 02 arrived as batch item 03, source 03 as
batch item 08).

**Why one report.** Sources 01 and 03 prove the same main theorem, the exact
Hahn domain `U_q` and `U_q/q^Z ≅ E_q(K)` at arbitrary rank. Source 03 was
written at pin `0097304`, before source 01 entered the repository, so it is an
independent re-derivation by a different route. Source 01 is the base because
it is wider in scope (theta, `j`-recovery, classification, nondivisible
torsion, scalar extension, the coarse reduction diagram). Source 03 is wider in
one direction, the coefficient field, and that generality is carried in, but
confined to Theorem 1.2 and the new sections. Source 02 supplies the
multivariable theta half of the open question on higher-dimensional
degenerations that sources 01 and 03 both state.

**Printed once.** The domain half of the main theorem, with its
decreasing-exponent witnesses, is Theorem 4.1 (both 01 and 03 prove it with
identical witnesses). The value sequence is Theorem 10.3 (both). The good
coarse reduction is Section 7.2 (both). The `q = ω^(-1)` example against
`u = ω^(-ω)` and `u = 1 + ω^(-ω)` is Example 13.3 (both). Source 03's
positive-input specialization lemma is Lemma 2.1 (both). Source 03's torsion
consistency check (for `C` and divisible `Γ`) is subsumed by Theorem 12.2 and
is not repeated. Source 02's strong-summability definition and Hahn support
facts are Section 2's. The `q`-expansion coefficients `(104)–(105)` appear in
sources 01 and 03 identically.

**Kept twice, as different proofs.** Surjectivity and the group law: the
first route (Sections 5–7, via Tate's complete rank-one theorem in `K_{H_α}`
and coarse lifting) and the second route (Section 8, via the integral node
chart, a smooth-residue chart, a chart at infinity, Tate's universal cleared
secant identities and Tate's generic-pair lemma).

**Renamed to avoid collisions** (always in the new material, never in source
01's text). From source 03: `δ, ν, D_q, φ_q, τ` became `α, v, U_q, Φ_q,
trop_q`; its vector valuation `ρ` became `𝐯`; its second parameter `w`
became `u'`; its `w = −1/y` became source 01's `r`; the linear part `L` became
`𝐋`; its unit `A(Q,x,y)` became `𝒜`; and its fine filtration `E_0 ⊇ E_1`
became `E^v_0 ⊇ E^v_1`, because source 01's `E_1(K)` is the kernel of the
**coarse** reduction and is a proper subgroup of `E^v_1`. From source 02: the
exponent matrix `Q`, quadratic form `q(n)` and theta series `Θ_Q` became `Π`,
`π(n)` and `ϑ_Π` (so that neither the Tate parameter `q` nor `Θ_q` is
reused); the real space `H`, form `B` and energy `F` became `𝓗`, `𝓑`, `𝓔`; the
minimum `δ_β` became `μ_β`; and "admissible" in the Amini–Nicolussi sense is
always written **AN-admissible**, since "admissible" in Part I refers to the
Hahn-admissible domain `U_q`.

## What the report claims

Numbers refer to the built `article.pdf`.

**Part I, one period.** Let `K = C((t^Γ))` for a set-sized ordered abelian
group `Γ`, with no restriction on rank or divisibility, and let `q` have
valuation `α > 0`. Let `H_α` be the principal convex subgroup generated by
`α` (values bounded by some *ordinary* integer multiple of `α`) and
`U_q = {u ∈ K^× : v(u) ∈ H_α}`.

1. **Exact domain and uniformization, Theorem 1.2.** The bilateral theta
   family is strongly Hahn-summable exactly on `U_q` (Theorem 3.1); for `u`
   outside `q^Z` each Tate coordinate family is strongly summable exactly on
   `U_q` (Theorem 4.1). Failure outside `U_q` is proved from strictly
   decreasing leading exponents, so no cancellation can repair it.
   `Φ_q : U_q → E_q(K)` is a surjective homomorphism with kernel `q^Z`.
2. **Two proofs.** The first route is Sections 5–7. The second route,
   Section 8 (source 03), uses no rank-one completion and no classical analytic
   theorem: Theorem 8.3 gives an integral formal node chart `T = (𝒳, 𝒴)` with
   integral inverse and the factorization `𝓕(Q,x,y) = (Q − 𝒬(x,y))·unit`;
   Theorem 8.5 inverts at nodal points, Proposition 8.7 at smooth-residue
   points, Proposition 8.9 at infinity; Theorem 8.10 is surjectivity and
   Theorem 8.12 the group law and kernel. **Theorem 8.13 states Theorem 1.2
   over any coefficient field `k` of characteristic zero.**
3. **Support monoids and valuation geometry (Section 9).** Equality of the
   generated positive support monoids in the two coordinate systems (Theorem
   9.1) and exact monoidal descent (Corollary 9.2); a valuation-isometry lemma
   for formal charts with invertible linear part (Lemma 9.3, Corollary 9.4);
   an exact two-period comparison (Theorem 9.5), the fixed-period distance and
   coordinate size (Corollary 9.6), and exact period sensitivity
   `v(q − q') − v(u)` (Corollary 9.7). No noncancellation hypothesis.
4. Scalar extension (Theorem 10.1); the value sequence
   `1 → O_v^× → E_q(K) → H_α/Zα → 0` (Theorem 10.3); the fine residue sequence
   (Proposition 10.4); and the **extension obstruction** (Theorem 10.5): if
   `H_α ≠ Γ`, no homomorphism `K^× → E_q(K)` extending `Φ_q` has kernel
   `q^Z`, and any extension `Ψ` has `ker Ψ / q^Z ≅ Γ/H_α`.
5. Support-preserving recovery of `q` from `j` when `v(j) < 0` (Theorem
   11.1); if `Γ` is divisible, every elliptic curve over `K` with `v(j) < 0` is
   isomorphic to some `E_q` (Corollary 11.2). The torsion field
   `K(E_q[n]) = K(q^(1/n)) = K_(Γ + Zα/n)`, of degree the order of `α` in
   `Γ/nΓ`, generated by the single point `Φ_q(q^(1/n))` (Lemma 12.1, Theorem
   12.2, Corollary 12.3; Theorem 1.3). These need `C`.
6. Transport to `No[i]` (Corollary 1.4, Theorem 13.1), and, through the second
   route, to the **real** field `No` for real `q`, with the inverse charts,
   support and valuation formulas and kernel obstruction transferred
   (Corollary 13.2). Examples 13.3 and 13.4.

**Part II, several periods (source 02).** Coefficients in `C`, `Γ` divisible
where halves are used, and **monomial** periods given by a symmetric exponent
matrix `Π`; `ϑ_Π(z) = Σ_{n ∈ Z^g} t^{π(n)} z^n`, `π(n) = ½ nᵀΠn`.

7. **Theorem 15.2, finite positive generation.** Every admissible lattice in a
   finite-dimensional higher-rank inner-product space has a finite positively
   generating set. This is a constructive affirmative answer to **Question
   11.14 of O. Amini and N. Nicolussi, *Higher rank inner products, Voronoi
   tilings and metric degenerations of tori*, Annales Henri Lebesgue 8 (2025),
   1109–1188, doi:10.5802/ahl.257**, as printed there (Section 11.5.3,
   page 1181; positive generation is their Definition 11.10, page 1179). The
   citation was checked against the published article when this report was
   assembled. The answer is pure higher-rank lattice geometry; non-full
   lattices are covered (Remark 15.6).
8. **Theorem 16.3, exact flag criterion.** A quadratic lattice family
   `(c_n t^{𝓔(n)})` is strongly summable if and only if the form is
   AN-admissible and the linear terms vanish on the radicals; the exact linear
   domain, and minimum attainment, in Corollary 16.4.
9. **Theorem 17.2**: the exponent support has order type exactly `ω^s`, `s` the
   number of strict radical drops; at positive monomial points this is the
   Conway normal-form support length, not the birthday (Corollary 17.3).
10. **Theorem 18.1**: the exact theta domain, independent of units; no repair
    by units or ordered scalar extension (Corollary 18.2); for `g = 1` the
    domain is `H_α`, for diagonal `Π` it is `∏ H_{α_j}` (Corollary 18.3).
11. **Finite certificates.** A global minimum is certified by finitely many
    inequalities over one positively generating set (Theorem 19.1), giving
    finite higher-rank Voronoi inequalities (Corollary 19.2, which supplies the
    generating set that Amini–Nicolussi's Lemma 11.11 assumes); at most `2^g`
    minimizers and a zero-cost move graph of diameter at most `g` (Theorem
    19.3, Corollary 19.4).
12. **Theorem 20.2**: smooth initial zeros lift to genuine Hahn and surcomplex
    zeros with an explicit support monoid (via Lemma 20.1).
13. Corollary 21.5: no nontrivial theta family is summable at every monomial
    point of `(No[i]^×)^g`.

**Dictionary with Part I (Section 14).** For `g = 1`, `Π = (α)`, a monomial
`q = t^α` and divisible `Γ`: `Θ_{t^α}(u) = ϑ_(α)(−t^(−α/2) u)`, and Corollary
18.3 recovers the domain half of Theorem 3.1 in that case. Theorem 3.1 is
stronger in two directions Part II does not reach (an arbitrary `q` with a
Hahn tail, and no divisibility); Part II is stronger in the number of
variables. The two are not merged.

## What the report does not claim

No non-claim of any source was dropped. The article carries each one at its
point of use and again in Sections 13, 22, 23 and Appendix A; `PROOF_AUDIT.md`
lists them.

**Across the report.** The proofs have **not** been independently refereed and
have **not** been formalized in Lean; no Lean source is supplied. The finite
computations check finite identities and examples only. Priority is **not**
certified by any of the three targeted literature searches.

**Source 01 (Part I base).**
- Part I is a new-theorems report, not a claimed solution of a named published
  open problem. Tate's rank-one theorem, the classical theta and modular
  identities, algebraic closedness of a divisible Hahn field over `C`, and the
  Kummer origin of Tate torsion are **credited as inputs**.
- Maximality concerns the **specified bilateral families under strong Hahn
  summability**; no claim that no other summation rule could assign values
  outside `U_q`.
- Hahn partial sums are **not** claimed to converge in the full surreal
  topology; the finite-tail bound is a statement in the value group.
- The negative-`j` regime is covered; **no theorem for `v(j) ≥ 0`**.
- For nondivisible `Γ`, a curve with the same `j` can be a nontrivial twist;
  twists are not silently identified with the split Tate curve.
- The value-circle sequence is algebraic and circularly ordered; **no
  real-metric Berkovich skeleton theorem at higher rank**.
- Differentiation is in an external variable, **not** the Berarducci–Mantova
  derivation.
- The repository audit was targeted; a negative keyword search is a
  navigation aid, not proof of absence.

**Source 03 (second route and refinements).**
- **The bounded-period quotient is not new**: Molcho–Wise's bounded monodromy
  and their logarithmic Tate curve (arXiv:1807.11364 v5, Definition 2.1.3.1,
  Definitions 3.5.5 and 3.6.1, Section 5.1 and (5.1.3)–(5.1.4)) are a
  precedent. Only the Hahn-summability, inverse-chart, support and valuation
  refinements are candidates; the extension obstruction is a consequence, not
  a deep discovery. **No functorial comparison with logarithmic uniformization
  is proved**; it is the principal remaining priority check.
- The obstruction does not exclude every noncanonical extension; it excludes
  one keeping both the canonical values on `U_q` and the kernel `q^Z`.
- The value quotient is not identified with a real circle without extra
  hypotheses.
- "Uniformization" means an explicit group parametrization by Hahn sums and
  formal charts: **no** complex-analytic covering space, lifted contours,
  fine-topology convergence of partial sums, global surcomplex logarithm, or
  exponential at infinite imaginary arguments.
- It does not classify elliptic curves over `No[i]`; it treats `E_q` and
  curves given with an isomorphism to one (source 01 adds `v(j) < 0`).
- No algorithm on all surreals: membership `|γ| ≤ Nα` is only semidecidable
  without a convex-subgroup oracle; degree truncation need not reach a
  requested cutoff at higher rank.
- The node-chart distances depend on the chosen Weierstrass model; calling
  them canonical would be an unsupported strengthening.
- The characteristic-0 generality applies to Theorem 1.2 and Sections 8–9 and
  10.3 only. **Torsion, `j`-recovery and the classification need `C`**, and
  Corollary 11.2 also needs divisibility.

**Source 02 (Part II).**
- The Question 11.14 answer is pinned to the **published formulation**; no
  claim that nobody answered it since.
- Credited, not claimed: the higher-rank inner products, admissibility,
  Definition 11.10, Lemma 11.11 and the rank-one acute-cone argument
  (Amini–Nicolussi); rank-one theta functions and their tropicalization
  (Foster–Rabinoff–Shokrieh–Soto); convergent higher-rank Hahn subrings
  (Joswig–Smith); the midpoint/Delaunay parity argument; initial forms and the
  formal implicit theorem.
- The size bound `|S| ≤ |S_0| + |𝒯|(M+1)^{|S_0|}` is an existence bound only;
  there is no uniform bound on descent steps; the observed descent length 35
  is experimental; there is no algorithm for arbitrary real constants.
- **No abelian-variety uniformization**, no global surcomplex exponential, no
  class-sized convergence, no fine-topological holomorphy.
- Singular initial zeros are not treated.
- Corollary 21.5 accords with, but does not reprove or strengthen, the
  collection's all-scale entire-function restrictions.

## Open questions, re-scoped

The paragraph "Higher-dimensional totally degenerate abelian varieties"
(Section 23) **stays open**. Part II supplies its theta-summability half for
monomial periods and divisible `Γ` (the exact ordered-group condition for all
lattice directions, replacing `H_α` by radical-flag conditions). Not proved:
periods with Hahn tails in several variables, nondivisible `Γ`, coordinate
maps and a group structure, surjectivity onto points of an abelian variety,
singular zero lifting, theta line bundles. The paragraph "Functions outside
the literal Hahn domain" now states what is proved (Theorem 10.5) and what is
not. New open items: comparison with logarithmic uniformization; intrinsic,
model-independent versions of the Section 9 invariants; size bounds for
positively generating sets and bit complexity of theta minimization.

## Stale statements corrected

- Source 01's novelty framing (status box, Section 1.2, commentary on Theorem
  10.3) presented the exact-domain quotient as potentially new without citing
  Molcho–Wise. The precedent is now credited in all of these, in this README
  and in `PROOF_AUDIT.md`.
- Source 03 described global elliptic uniformization as a direction the
  repository did not take. True at its pin `0097304`; false now, since the
  repository contains source 01.
- Source 02 found "no theta-lattice treatment" at its pin `a3124af`. The
  collection now has the one-variable bilateral theta domain (Theorem 3.1),
  the partial-theta domain `hol:thm:thetadomain` and the unilateral example
  `found:ex:internal`; there is still no multivariable or lattice theta series
  outside Part II.
- The previous README called this directory "one manuscript, not a merge".

## Relation to the neighbouring reports

**[rank-one-berkovich](../rank-one-berkovich/).** That report fixes the
rank-one base `C((t^R))`. Its `prop:rankobstruction` proves that `Q + Q*omega`
admits no order-preserving injective additive map to `R`, so a higher-rank
valuation cannot be silently scalarized. The first route here applies a
real-valued coarsening only inside `K_{H_α}`, where `α` is an order unit; the
second route applies none. *A Tate algebra is not a Tate elliptic curve.* That
report's reciprocal pointer describes the first route and remains true.

**[entire-functions-at-arbitrary-rank](../entire-functions-at-arbitrary-rank/).**
The first route cites its `ent:lem:coarsening` for the rank-one coarsening at
an order unit. That report assumes a divisible exponent group, which this report
never assumes; the direct completeness proof is kept in Lemma 5.3. Since the
second route proves Theorem 1.2 without the coarsening, that citation and its
divisibility caveat are no longer load-bearing for the main theorem.

**[holonomic-rigidity-for-entire-hahn-functions](../holonomic-rigidity-for-entire-hahn-functions/)**
has the exact domain of the *partial* theta series (`hol:thm:thetadomain`);
the bilateral series here is a different family. The foundations report has
the unilateral `Σ t^(n²) z^n` over `C((t^Q))`, which Corollary 21.5 does not
contradict.

**[global-divisors](../global-divisors/)** also cites Molcho–Wise, as a
different category; its "valuation monodromy" is not their bounded monodromy,
and the two are not identified here.

**[wick-summability-certificates](../wick-summability-certificates/)** is Part
II's closest relative: both give finite-certificate characterizations of
strong summability of monomial families (a quadratic energy with radical flags
here, a linear weight with a Hilbert basis there), both show that unit tails
cannot repair a failure, and both assume divisible `Γ`. Neither uses a theorem
of the other. **[markov-generators-at-every-scale](../../surreal/markov-generators-at-every-scale/)**
uses "flag" for a chain of idempotents, unrelated to the radical flags here.

**[differential-equations](../differential-equations/)**, Part VI, treats
constant (good-reduction) abelian varieties over `No[i]` by formal groups
(`diff:aut:prop:abeliansplit`, `diff:aut:thm:abelianimage`), including their
logarithmic-derivative image for every normalized derivation. That is the
regime this report sets aside under "Beyond negative valuation of `j`"; it does
not cover Hahn fields with a coarse valuation.

## What was run

- `code/check_identities.py` (source 01), on Python 3.14.4 with SymPy 1.14.0,
  on a copy: reproduced `data/verification.json` except its `python` field,
  which records the delivered run's 3.13.5. `data/verification.log` is the
  delivered console record of that run and has the same content. Both are the
  delivered bytes; an earlier in-place rerun had overwritten them and has been
  undone. Checks the Weierstrass
  equation, `u X' = X + 2Y` and inversion through `q^5`, the discriminant
  product through `q^9`, `j` through `q^5`, the inverse modular series through
  `J^6`, the local-parameter sign, theta shifts, decreasing-exponent witnesses
  in a rank-two group, and sample torsion degrees.
- `code/03-tate-uniformization-verify.py --degree 12` (source 03), standard
  library only, on a copy: all 8 identities pass, 91 monomials each, **728**
  exact coefficient equalities; output identical to
  `data/03-tate-uniformization-verification.json` except the informational
  `seconds` field.
- `code/02-multiscale-theta-verify.py` (source 02), standard library only, on
  a copy: output identical to `data/02-multiscale-theta-verification.json`,
  status `ALL CHECKS PASSED`: 5,555 allocation cases, 1,681 irrational-shear
  decompositions, 441 linear-term cases against an independent exact
  minimizer, 12 Pell witnesses, and the zero-row expansion through degree 8.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`: 62
  pages, no errors, no undefined or multiply defined references, no duplicate
  PDF destinations, no overfull or underfull boxes, no LaTeX or package
  warnings. `data/build_validation.json` is source 01's own record (26 pages,
  before it joined the collection) and is kept unchanged.

A clean compile and passing finite checks prove nothing about the infinite
arguments.

## Build and reproduce

TeX Live or MiKTeX with newtx, amsmath/amsthm, mathtools, aliascnt, tikz-cd,
tcolorbox, hyperref and cleveref. No external figures or bibliography file.

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

**Run the programs on a copy, never in this directory.**
`check_identities.py` and `02-multiscale-theta-verify.py` both write
`data/verification.json` next to their own `code/` directory, so run in place
the second would overwrite source 01's record. `03-tate-uniformization-verify.py`
writes the file named by `--output` (default `verification.json` in the working
directory). For example:

```
mkdir -p /tmp/t/code /tmp/t/data
cp code/check_identities.py /tmp/t/code/ && python /tmp/t/code/check_identities.py      # needs SymPy (data/requirements.txt)
#   compare /tmp/t/data/verification.json with data/verification.json
rm /tmp/t/data/verification.json
cp code/02-multiscale-theta-verify.py /tmp/t/code/ && python /tmp/t/code/02-multiscale-theta-verify.py
#   compare /tmp/t/data/verification.json with data/02-multiscale-theta-verification.json
python code/03-tate-uniformization-verify.py --degree 12 --output /tmp/t/node.json
#   compare with data/03-tate-uniformization-verification.json (except "seconds")
```

`data/02-multiscale-theta-verification.txt` is a byte-identical copy of the
JSON record delivered with source 02; the program does not regenerate it.
The delivered build scripts `code/02-multiscale-theta-build.sh` and
`code/03-tate-uniformization-build.sh`/`.ps1` build their source manuscripts
in their original layouts and do not build this report; they are kept only as
delivered.

## Repository audits recorded by the sources

- Sources 01 and 02: `a3124af79f66b8b9c196d76b4cbc5ac3938907c4`.
- Source 03: `0097304c7ae9d5de46d2ea342e2494f8fc126303`, which predates the
  placement of source 01.

All three audits were targeted. None modified the repository, and none treats
the repository's unrefereed manuscripts as established foundations.
