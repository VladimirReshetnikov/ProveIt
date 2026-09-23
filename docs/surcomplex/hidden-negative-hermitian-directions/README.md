# Hidden Negative Directions in Surcomplex Linear Algebra

**Prime-denominator approximation barriers and a two-scale matrix-measure criterion**
Single-source research report, 22 September 2026. It is built from one
manuscript, manuscript 06 of batch 19 (archive `hidden_negative_directions`),
pinned to repository commit `048b72c`, and placed in commit `52c7ab6`.
Prepared for Vladimir Reshetnikov.

This directory holds one manuscript. It is not a merge: there was no second
source, and nothing was selected out of a larger body of work. Every result,
proof, example, question and limitation of the manuscript is printed.

```
article.tex        the report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 33 pages (title, two contents pages, 30 numbered pages)
README.md          this guide
source_audit.md    the source's own repository and literature audit, as delivered
code/              verify.py (exact finite checks), build.sh (the source's build script)
data/              verification.json, verification.txt (the source's recorded run),
                   build_report.json (the source's summary of its own PDF build),
                   requirements.txt
```

Every label in `article.tex` carries the prefix `hnd:`. The source's 80 labels
are kept, unchanged after the prefix, and nine were added (`hnd:sec:conventions`,
`hnd:sec:position`, `hnd:sec:nonclaims`, `hnd:app:provenance`, `hnd:app:pinned`,
`hnd:app:files`, `hnd:app:reproduce`, `hnd:rem:degreescope`, `hnd:q:morescales`).
`code/`, `data/` and `source_audit.md` are byte-identical to the delivery.
`data/build_report.json` describes the delivered PDF, not this one.

## One meaning of "positive"

A Hermitian matrix is **positive semidefinite** (`A ⪰ 0`) only when
`z*Az ≥ 0` for every vector `z` over the whole field `K_Γ = C((t^Γ))`, as in
the spectral-theory report's `prop:positive`. When only some test vectors are
allowed, the statement names them: "`z*Az > 0` for every nonzero `z` in `E^n`",
called *E-probe positivity* and never shortened to "positive". A Hahn-valued
matrix measure is positive when every event matrix is positive semidefinite.
"Positive" never means entrywise positive, as it does in the Markov-generator
and matrix-scaling reports. "Hidden" is always relative to a named probe
field, and is unrelated to the "hidden negative mass" of the measures report
(Section 1.5).

## What the report claims

Let `Γ` be a nonzero divisible ordered abelian group, `K_Γ = C((t^Γ))`, and
let `P_Γ` be the field of Hahn series whose support lies in some finitely
generated subgroup of `Γ` (Definition 2.1). "Finite-lattice support" means
exactly this; it is neither finite support nor a discrete lattice. `P_Γ` is
algebraically closed and contains every monomial (Proposition 3.4); for
`Γ = Q` it is the complex Puiseux field (Example 2.2). Its valuation closure is
written `P̄_Γ` (the source wrote `C_Γ`, which clashes with the Hahn–Herglotz
report). Fix `δ > 0` and put `q_p = 1 − 1/p` for primes `p`.

- **Approximation barrier (Theorem 4.2).** For `h_δ = Σ_p t^{q_p δ}`, every
  `a ∈ P_Γ` satisfies `v(h_δ − a) < δ`.
- **Primorial law (Theorem 4.3, Corollary 4.4).** Among elements algebraic over
  `C(t^δ)` with `v(h_δ − a) > q_{p_N} δ`, the least degree is exactly
  `P_N = p_1 ⋯ p_N`, attained by the partial sum. No sequence of elements
  algebraic over the monomial field converges to `h_δ`. The tool is a
  support-index bound from diagonal character automorphisms (Lemma 3.2).
- **Separation and independence (Theorems 5.1, 5.2; Corollary 5.3).** For
  pairwise almost-disjoint infinite prime sets `A_j` and tails
  `h_j = Σ_{p∈A_j} t^{q_p δ}`, every combination `a_0 + Σ h_j a_j` with
  `a_i ∈ P_Γ`, `(a_1,…,a_r) ≠ 0`, has valuation `< δ + min_j v(a_j)`. An
  explicit binary-prefix family of `2^ℵ₀` tails is algebraically independent
  over `P_Γ`, and `trdeg(C((t^Q))/P_Q) = 2^ℵ₀`.
- **Maximal hidden negative inertia (Theorem 1.1, Theorem 6.1,
  Corollary 6.2).** `A_r = [[1, hᵀ], [h, hhᵀ − ε²I_r]]`, `ε = t^δ`, satisfies
  `z*A_r z > 0` for every nonzero `z ∈ P_Γ^{r+1}`, yet has inertia `(1, r, 0)`
  and determinant `(−ε²)^r` over `K_Γ`; the vectors `(−h_j, e_j)` have value
  `−ε²`. Size two is minimal and `r` negative directions are the most
  compatible with the one positive probe `e_0` (Section 6.1).
- **Closure (Theorem 7.1, Proposition 7.3, Corollary 7.4).** The same holds for
  vectors over `P̄_Γ`; for `Γ = Q`, `P̄_Q` is the complex Levi-Civita field.
- **Density and surreal transport (Proposition 8.1, Theorem 8.2).** Quadratic
  testing over a subfield `E ⊆ F` detects all negativity iff `E` is order
  dense (an elementary, credited fact). With `t = ω⁻¹`,
  `h = ω^{-1/2} + ω^{-2/3} + ω^{-4/5} + ⋯` is an actual surreal number, and the
  probe positivity holds for every finite surcomplex vector whose coordinates
  have Conway support in some finitely generated subgroup of `No`.
- **Two-scale matrix positivity (Lemma 9.1, Theorem 9.2, Examples 9.3–9.5).**
  For ordinary Hermitian `P`, `Q` and `ε = t^η`, `P + εQ ⪰ 0` iff `P ⪰ 0`,
  the compression `C_N` of `Q` to `N = ker P` is `⪰ 0`, and `Q` annihilates
  `ker C_N`; kernel and rank formulas follow. Any nonzero ordered `Γ`.
- **Two-scale matrix null ideals (Theorem 10.1, Corollaries 10.2, 10.3,
  Examples 10.4–10.6).** For finite Hermitian matrix measures `M_0`, `M_1` on
  any measurable space, `M_0 + εM_1` is positive iff `M_0` is positive and,
  for every ordinary `u`, `ν_u⁻ ≪ μ_u` and `|σ_u| ≪ μ_u + ν_u⁺`, where
  `μ_u = u*M_0u`, `ν_u = u*M_1u`, `σ_u = M_1u`. The vector condition is
  genuinely matrix-valued (Example 10.4); for `d = 1` it disappears and the
  scalar criterion of the Herglotz report returns (Corollary 10.3).
- **Questions 11.1–11.3** (more than two measure scales; probe classes under
  support closure; relative precision costs) are left open.

## What the report does not claim

Section 11.4 keeps the source's non-claims in place and collects them in a
ledger of 27 items: 24 from the source and 3 added when the report joined the
collection. In brief:

- Not refereed. No theorem here is Lean-verified, and no Lean source
  accompanies the report. No named published conjecture is claimed settled.
  Priority is not certified: the source's repository and literature comparison
  was pinned and targeted, and its negative searches are not evidence of
  absence.
- "Hidden" means hidden from vector probes over the named field only.
  Determinants and principal minors detect `A_r` at once; the construction is
  not an obstruction to exact positivity algorithms over the field generated
  by the entries. No undecidability claim.
- The primorial law is a field degree over `C(t^δ)` at the stated strict
  precision: not expression length, running time, or a cost over an enlarged
  ground field.
- Background, not contribution: the support-family field, character
  automorphisms, finite Hermitian spectral algebra, Hahn closedness, Schur
  complements, the density equivalence, the cardinality count.
- The independence is ordinary algebraic independence, not differential
  independence for the Berarducci–Mantova derivation. Sharpness concerns
  dimension and inertia, not support order types. The Levi-Civita corollary
  does not concern matrices defined over the Levi-Civita field.
- The measure theorem uses coefficientwise countable additivity and exactly
  two scales; the arbitrary-support matrix-measure problem is open. Its kernel
  corollary is eventwise. No spectral measure, no Hilbert completion, no
  integration on the proper-class plane, no new spectral theorem.
- Closures use the valuation topology of one set-sized workspace, not the fine
  topology of `No[i]`; surreal statements use normal-form transport.
- The finite checks are diagnostics and prove no infinite statement.
- Added: Theorem 10.1 answers no question posed in the Herglotz report (the
  sentence it addresses is a non-claim there); Theorem 5.2 neither implies nor
  follows from the tail-spans or bounded-support independence theorems; the
  scalar Lean proof in `FORMALIZATION.md` covers no statement of this report.

## Relation to the neighbouring reports

**[spectral-theory](../spectral-theory/)** — everything used about a single
Hermitian matrix is there: the order `⪰` and invariance of inertia
(`prop:positive`), and `spec:thm:hermitian`, which diagonalizes any Hermitian
matrix over `K_Γ` with all exponents in the group generated by the entries'
exponents. For `A_r` that group is not finitely generated (it contains
`q_p δ` for infinitely many `p`), and Theorem 7.1 shows the negative
eigenvectors cannot be replaced by vectors over `P̄_Γ`. Lemma 3.2 is the
rational-function-field counterpart of `spec:lem:finiteindex`; Remark 4.5
records the degree drop of `spec:warn:degreedrop`. Nothing there is extended
or contradicted.

**[hahn-herglotz-positivity](../hahn-herglotz-positivity/)** — its Section 8.3
says: "A matrix-valued version of the scalar null-ideal criterion would have
to track kernel directions of coefficient measures as well as their scalar
null sets; it is not supplied here", and its non-claims list "No
matrix-valued null-ideal criterion is supplied." Theorem 10.1 is the
two-exponent case, and its vector condition is exactly that tracking of
kernel directions. The settings differ: there, real scalar coefficientwise
measures with regular Borel coefficients on a compact Hausdorff space and
arbitrary well-ordered support; here, complex Hermitian matrix coefficients
on any measurable space and two exponents. Corollary 10.3 is
`herg:cor:twoscale`; the transfinite scalar criterion is proved once, as
`meas:thm:nullideal` of
**[hahn-valued-measures-and-probability](../../surreal/hahn-valued-measures-and-probability/)**,
and `FORMALIZATION.md` records a Lean proof of the scalar two-scale case.

**[tail-spans-and-differential-transcendence](../../surreal/tail-spans-and-differential-transcendence/)**
— the same binary-prefix almost-disjoint device (`tail:eq:Aalpha`, with
private indices), but a different mechanism and an incomparable base. Its
tails `ξ_A = Σ √p_n t^n` have square-root coefficients and integer exponents
and are independent (even differentially) over `Q((t^Q))`; here the tails
have coefficient one and prime-denominator exponents and are independent over
`P_Γ`. For `Γ = Q` each base contains the other's witnesses: `h_A ∈ Q((t^Q))`
and `ξ_A ∈ P_Q`. So square-root tails cannot hide a direction from `P_Γ`
probes. Its `tail:thm:closure` (Σ √p_n t^n is a limit of algebraic
truncations) and Corollary 4.4 here use different meanings of "algebraic".
Its warning `tail:rem:indexfamily` applies: the family of all `h_A` is not
independent.

**[transcendence-over-bounded-support](../../surreal/transcendence-over-bounded-support/)**,
placed in the same commit, works over the fraction field of series with
support bounded above. For `Γ = Q` the two bases are incomparable: every `h_A` lies in the
bounded-support ring but outside `P_Q`, while `√(1+t) ∈ P_Q` lies outside
the bounded-support fraction field. The article proves the latter by
projecting a putative fraction to one integer-exponent coset and using
that `1+t` is not a rational square. Unbounded support alone does not
suffice: `Σ_{n≥1} t^n = t/(1−t)` already belongs to the fraction field.
For a group with no order unit, every finitely generated subgroup is
bounded above, so `P_Γ` is contained in the bounded-support ring. The two
independence theorems have different bases and witnesses. Background inputs
are `found:sub:positivesupport` (foundations) and `polynomial:prop:workspace`
(polynomial-algebra).

## Main-text proof review

Sections 1–11 have received a mathematical proof review. It expands character
extension, support-index finiteness, the primorial lower and upper bounds,
closure and density, and the workspace containing an algebraic surreal root.
The finite matrix proof now displays its Schur congruence and explains why
positive pivots suffice over nondivisible Hahn groups. The measure proof
spells out vector-variation finiteness and the null-set argument.

The bounded-support comparison above corrects an invalid geometric-series
witness and restricts incomparability to the stated exponent group. The
spectral comparison distinguishes congruence from unitary diagonalization.
The 24 numbered result statements retain their mathematical content; two
wording clarifications name the intrinsic valuation topology and define the
compression even before positivity of `P` is known. All 89 labels and result
numbers are retained. Remaining imported-result checks, literature priority
and original-source reconciliation are separate from this main-text review;
see [the review record](../../REVIEW.md). No Lean mapping was added.

## Stale statements corrected

The source audited the collection at `048b72c`; `source_audit.md` keeps that
audit as delivered, and Appendix A.3 of the article corrects it. At the pin
the reader map did describe 36 reports; commit `52c7ab6` has since added four,
this one among them. The source's search for "finite-lattice" reported no
matches, but at the pin the phrase already occurs in an unrelated sense
(`tate:cor:lattice`, "A finite-lattice degree formula", listed in
`FORMALIZATION.md`), so its conclusion stands while the search was
incomplete. The source did not mention the measures report's proof of the
scalar criterion or its Lean proof, and cited the reader map generically for
Hahn closedness and the tail-span constructions; the article now points to
the specific results. The neighbouring reports compared here changed in no
relevant way between the pin and the placement.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python -m pip install -r data/requirements.txt
python code/verify.py
python code/verify.py --json
```

The recorded build has no errors, no undefined or multiply-defined
references, no duplicate PDF destinations and no overfull or underfull
boxes. A clean compile proves nothing about the proofs.

`code/verify.py` needs Python 3.10 or later and SymPy (pinned 1.14.0). It uses
exact integer, rational and symbolic arithmetic with a formal `ε`, prints to
standard output only, and **never rewrites** the files in `data/`, which hold
the source's captured run under Python 3.13.5. It checks the congruence,
determinant and negative vectors of `A_r` for `r ≤ 4`; trivial character
stabilizers, hence orbits of size `P_N`, for `N ≤ 6`; 35,100 exact
fresh-prime coset comparisons (`m ≤ 60`, primes ≤ 97); Theorem 9.2 against
all principal minors for all 5,946 pairs of a diagonal 0–1 matrix `P` and a
real symmetric `Q` with entries in {−1, 0, 1} in dimensions 1–3 (1,823
positive semidefinite); and the determinants of Examples 9.3–9.5. Rerun for
this report on a copy of the directory under Python 3.14.4 and SymPy 1.14.0,
it printed the same five `PASS` lines and counts, and its JSON output matched
`data/verification.json`; only the Python version differs.

`code/build.sh` is the source's script. It changes to its own directory and
runs `latexmk` (or `pdflatex` three times) on `article.tex`, overwriting
`article.pdf`. As placed under `code/` it does not find `article.tex`; to use
it, copy this directory and put the script beside `article.tex` in the copy.

During the main-text review, the delivered verifier was rerun with Python
3.13.14 and SymPy 1.14.0. All five checks passed; its JSON agrees with the
historical output except for the Python version. An additional scratch
check compared the criterion with principal-minor signs for 390,625
Hermitian 2×2 pairs with integer real and imaginary components in
`{−2,−1,0,1,2}`; all agreed, and the 18,145 positive cases also matched
the rank formula. These finite diagnostics do not prove the general theorem.
The current 33-page PDF was rebuilt with three clean `pdflatex` passes.
