# Shifted Catalan Hankel Polynomials

**Exact coefficients, sharp recurrences, and a denominator conjecture; with root collisions and sharp recurrences for arbitrary polynomial multipliers, and cyclotomic resonances of one repeated root**

This is a research report in three parts. Part I is the original report of
19 September 2026, on the shifted linear multiplier `x^m (a + b x)`. Part II
was added on 28 September 2026 in batch 39 of ProveIt's incoming-report
intake, from a later manuscript that takes up the extension Part I named and
left open (its Section 11): "multiple distinct linear factors in the
multiplier lead to more exponential sectors and new collision patterns".
Part III was added on 29 September 2026 in batch 42, from a manuscript that
answers Part II's first research question, "Closed classification of
cyclotomic resonances" (Section 24.1), for one repeated root, and shows that
the question's proposed parameters do not suffice. All three were prepared
with OpenAI ChatGPT for Vladimir Reshetnikov and are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 (*Shifted Catalan Hankel Polynomials: Exact coefficients, sharp recurrences, and a denominator conjecture*) | `catalan_hankel_conjecture_solution.zip` | (none) | unpacked `a3fe9660e`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–11 (pp. 6–21) and Appendices A–B (pp. 75–76) |
| 02 | batch 39, manuscript 03 (*Root Collisions and Sharp Recurrences for Polynomially Weighted Catalan Hankel Determinants*, 28 Sep 2026, 23-page PDF as delivered) | `ProveIt_Catalan_Root_Collisions.zip` (inner `ProveIt_Catalan_Root_Collisions/`, main file `article.tex`) | `fbba58593` | `e2b1f016a` (prefix `02-root-collisions-`) | Part II: Sections 12–27 (pp. 22–47) |
| 03 | batch 42, manuscript 01 (*A One-Defect Law for Cyclotomic Catalan Hankel Recurrences: Complete single-root classification, a necessary sign parameter, and the central exception*, 29 Sep 2026, 22-page A4 PDF as delivered) | `ProveIt_Cyclotomic_Catalan_Recurrences.zip` (inner `cyclotomic_catalan/`, main file `article.tex`) | `9754e8360` (and blob `b29ea42f` of this `article.tex`) | `3609d0473` (prefix `03-cyclotomic-`) | Part III: Sections 28–43 (pp. 48–74) |

The pin `fbba58593` is ProveIt commit
`fbba58593dc0622aa914972896150d4848f935b5`; the manuscript read Part I's
`article.tex` and `README.md` there, and Part I's files are unchanged between
the pin and the placement commit, so Part II's statements about "the
repository report" refer to the Part I printed here. The archive arrived in
`74f7f5bdb`. Its manuscript, PDF and delivery README are not shipped; they
survive in the arrival commit. Its provenance notes are shipped verbatim as
`02-root-collisions-provenance.md`. Part II prints every result, proof,
example, remark, limitation and question of the manuscript; Section 12
records the provenance, the notation, and where the merge had to choose.

The pin `9754e8360` is ProveIt commit
`9754e83603e223811b7515eb892f22c847144593` (the batch-41 arrival); the
batch-42 manuscript read this report's combined `article.tex` there (blob
`b29ea42fc5bba69d23c3b036bee25357e202f356`, which it records), its provenance
notes and the directory listing, and, by its source notes, the standalone
Part II manuscript. The report is unchanged between the pin and the placement
commit (same blob), so Part III's "repository report" is Parts I–II as
printed here. The archive arrived in `8315d24e3`. Its manuscript, PDF and
delivery README are not shipped; they survive in the arrival commit. Its
source and comparison notes are shipped verbatim as
`03-cyclotomic-SOURCES.md`. Part III prints every result, proof, example,
remark, limitation and question of the manuscript; Section 28 records the
provenance, the notation, what Part III answers, and where the merge had to
choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. All three
parts give written all-parameter proofs; their exact-arithmetic suites are
finite audits and debugging checks, not substitutes for those proofs.

## Results

Write `C_n = binomial(2n, n)/(n + 1)` and let `N` be the determinant size
(not the last index), with the empty determinant equal to 1.

**Part I** (unchanged apart from dated pointers in the abstract and
Sections 10.3, 11 (two) and Appendix B, two title-page lines and a title-page
top space reduced by 3 mm (so that the page still fits), contents entries for
the three parts, two bibliography entries used only by Part II and one used
only by Part III, and the closing note on source dates). For

    D_N^(m)(a,b) = det(a*C_(i+j+m) + b*C_(i+j+m+1))_(0 <= i,j < N),

1. It proves the denominator-exponent assertion on page 4 of Paul Barry's
   arXiv:2011.10827v1: the generating function is
   `P_m(t) / (1 - (a+2b) t + b^2 t^2)^(binom(m,2)+1)` (Theorem 2.2). Barry's
   separately printed Conjecture 2 needs an explicit one-unit shift
   correction, proved in Appendix A.
2. For `b != 0` and `a (a + 4b) != 0` the **minimal** characteristic
   polynomial is `(X^2 - (a+2b) X + b^2)^(m(m-1)/2 + 1)`, so the minimal
   order is `m(m-1) + 2`; every exceptional reduced denominator is determined
   (Theorem 2.3).
3. An explicit positive-integer coefficient formula (Theorem 2.1), numerator
   degree `(m-1)^2` and reciprocal symmetry, and a finite two-exponential
   expansion with an explicit first asymptotic correction (Theorem 2.4).

**Part II** (batch-39 manuscript 03; unchanged apart from dated batch-42
pointers in Sections 20.1, 21.4 and 24.1–24.2, and new labels on the last two
subsections). For a nonzero polynomial `q`, let
`H_N(q) = det(sum_r q_r C_(i+j+r))_(0 <= i,j < N)`, so that
`D_N^(m)(a,b) = H_N(x^m (a + b x))`. Write
`q(x) = gamma x^m (x-4)^ell prod_i (x - c_i)^(t_i)` with distinct
`c_i` outside `{0, 4}` and `c_i = 2 + z_i + 1/z_i`. It proves:

1. `H_N(q)` is a sum over labels `0 <= k_i <= t_i` of polynomials `P_k(N)`
   times `lambda_k^N`, `lambda_k = (-1)^(ell + sum t_i) gamma prod_i z_i^(2k_i - t_i)`,
   and **each `P_k` has exact degree**
   `binom(m,2) + binom(ell+1,2) + sum_i k_i (t_i - k_i)` (Theorem 14.2), with
   a nonzero product formula for its leading coefficient (Theorem 18.1). The
   two endpoints contribute different triangular numbers.
2. When the rates are distinct, the minimal characteristic polynomial is
   `prod_k (X - lambda_k)^(d_k + 1)`, of order
   `prod_i (t_i + 1) * (binom(m,2) + binom(ell+1,2) + 1 + sum_i t_i (t_i - 1)/6)`
   (Theorem 14.2, equation (14.12)); the order is maximal exactly off
   resonance. For one repeated interior root the generic order is
   `t + 1 + binom(t+1, 3)` — cubic, not the classical `2^t` (Corollary 14.3);
   for example `(2x-9)^4` has order 15, with characteristic polynomial
   `(X-1)(X-4)^4(X-16)^5(X-64)^4(X-256)` (equation (21.2)).
3. A secondary Hankel determinant factors explicitly and vanishes exactly on
   the resonance locus (Theorem 14.5).
4. At every parameter, the minimal polynomial is obtained by grouping equal
   rates (Theorem 20.1); with the proved order bound, a finite prefix of
   `2R` values certifies the minimal recurrence (Theorem 20.2), giving a
   root-free algorithm for rational (or exact algebraic) coefficients via
   square-free decomposition (equation (20.6)).
5. Worked examples: recovery of Part I's sharp order and exceptional orders
   as a second proof by a different route; a resonance cancelling an entire
   branch, `H_N((x-2)^2) = N + 1`; a distinct-root resonance of order 2;
   `H_N((x-2)^4) = (N+1)(N+2)^2(N+3)/12` proved from nine values (order 5
   instead of 15); `x^2 + 1` of order 4 (Section 21). Exact fixed-parameter
   asymptotics (Section 22).

**Part III** (batch-42 manuscript 01). One repeated root: the multiplier is
`(x - c)^t` with `c` outside `{0, 4}`, `c = 2 + z + 1/z`, and
`L = ord(z^2)` (possibly infinite); the rates are `lambda_k = (-1)^t z^(2k-t)`.
It proves:

1. **Every characteristic multiplicity** at every noncentral parameter
   (Theorem 30.1). For `L > t` the order is the generic `t + 1 + binom(t+1, 3)`
   (Part II's Corollary 14.3). For `3 <= L <= t`, with `eta = 1` when `t` and
   `L` have the same parity (else 0), the exponent of each residue class of
   sector indices mod `L` is its maximal degree plus one, less a **defect**
   `delta` in {0, 1} on at most one class, and
   `R(t,c) = L(3t^2 - L^2 + 13 - 3 eta)/12 - delta` (30.10). The defect is 1
   exactly when `eta = 1` and `(-1)^(L(t+1)/2) z^(Lt) = -1`; elementarily,
   when `t, L` are even with `L = 2 mod 4`, or both odd with
   `z^L = (-1)^((t-1)/2)` (Corollary 30.3). "One defect" is measured **after**
   grouping equal rates; grouping itself lowers the generic order by much more.
2. **The question's parameter list is incomplete.** `t` and `L` do not
   determine the order: for `t = 3`, `c = 1` and `c = 3` both have `L = 3`
   but orders 7 and 6, `(X+1)(X^2-X+1)^3` versus `(X^2+X+1)^3` (38.1)–(38.2);
   in general the orders at `c` and `4 - c` differ by one exactly when `t, L`
   are odd and `L <= t` (Corollary 35.2). The sign of `z^L` is necessary.
3. **Central root** `c = 2` (Theorem 30.4): `H_N((x-2)^(2m)) = B_(m,m)(N)`,
   `H_N((x-2)^(2m+1)) = (-1)^(N(N+1)/2) B_(m,m+1)(N)` with the rectangular
   product `B_(a,b)(N) = prod (N+i+j-1)/(i+j-1)`; minimal polynomials
   `(X-1)^(m^2+1)` and `(X^2+1)^(m(m+1)+1)`. This is **Cigler's known product**
   (arXiv:2111.14492, Theorem 1, eq. (23)) after a change of normalization,
   credited, with a self-contained condensation proof.
4. The mechanism: an exact subset formula for every sector (Theorem 32.1), its
   leading coefficient and first centred correction via a signed Vandermonde
   identity (Lemma 33.1, Theorem 33.2), an exact reflection of the sector
   polynomials (Proposition 33.3), and the unique possible tied pair
   `k_± = (t ∓ L)/2` (Lemma 34.2). Only a real root `±1` can lose multiplicity
   (Corollary 34.3).
5. The exceptional parameters for fixed `t` are exactly
   `2 + 2 cos(pi a/L)`, `2 <= L <= t`, `gcd(a, L) = 1`, so there are
   `sum_{L=2}^t phi(L)` of them, all real in `(0, 4)` (Corollary 35.1); for
   fixed `L >= 3` the order is a quadratic quasipolynomial `L t^2/4 + O_L(1)`
   in `t` (Corollary 35.3).
6. A **root-free factorization** over the field of `c`, from two scalar
   recurrences in `c - 2`, in `O(t)` field operations for the factored answer
   (Theorem 37.1; not a bit-complexity bound). Worked examples include
   `t = 8`, `c = 2 + sqrt 3`: order 82 (grouped 83, generic 93) (38.4).
7. All rational roots (Corollary 38.1): generic order unless `c` is 1, 2 or 3;
   the table of `R(t,1), R(t,2), R(t,3)` for `t <= 12`, and through `t = 20` in
   the data.

Consistency with Part II (checked for this merge by a separate exact
computation, not shipped): all twelve single-root entries of
`data/02-root-collisions-resonances.json` (`c = 1, 2, 3`, `t = 1..4`) have
exactly the characteristic polynomials given by Theorems 30.1, 30.4 and 37.1,
and their orders equal the rows `t <= 4` of `data/03-cyclotomic-orders_c1_c2_c3.csv`
(0 mismatches); `(x-2)^3` in `rational_input_examples.json` is the case
`m = 1` of Theorem 30.4; Part II's `H_N((x-2)^2) = N + 1` and quartic
product are `B_(1,1)` and `B_(2,2)`; Part III's leading coefficients (33.3)
reproduce the five leading coefficients of Part II's `(2x-9)^4` table.

Theorem and equation numbers refer to the shipped `article.pdf`.

## Not claimed

- **Part I:** no claim of first discovery or of an exhaustive determination
  of present-day open status. The Christoffel identity, the Jacobi
  representation, the shifted Catalan product and general rationality are
  credited, not presented as new; the literature search was bounded (see
  `notes/provenance.md`).
- **Part II:** general polynomial-multiplier rationality, the Christoffel
  formula and its confluent form, and the general order bound `2^D`
  (Krattenthaler, Section 8, Corollary 9, crediting Elouafi) are classical.
  The claimed contribution is the exact branch degree, its nonzero leading
  constant, the minimality classification off resonance, and their
  consequences. No novelty is claimed for the secondary-Hankel identity of an
  arbitrary exponential polynomial (Lemma 19.2). An equivalent earlier
  formulation in Schur-function, Toeplitz/Hankel or orthogonal-polynomial
  literature has **not** been ruled out; the searches were targeted, and a
  first-discovery claim would need expert review and a broader search.
- Part II gives no short closed classification of resonant cancellations;
  on the resonance locus it gives an exact rule and a terminating algorithm
  only. *(Re-scoped 29 September 2026, batch 42: Part III gives that
  classification for one repeated root away from the endpoints, and shows
  that Part II's Section 24.1 asked for it in too few parameters — the sign
  of `z^L` is needed besides `t` and `ord(z^2)`. For several distinct roots,
  or with endpoint factors, none is known here; Section 24.2 is answered only
  inside the tied groups of one root.)* Its asymptotics are for fixed
  parameters; uniform endpoint and root-collision limits are posed, not
  proved. Its eight research directions (Section 24) are tasks relative to the
  manuscript, not asserted to be globally open.
- **Part III:** the Christoffel formula and its confluent form, Andréief's
  identity, Desnanot–Jacobi condensation, general rationality and the
  order-at-most-`2^t` construction (Krattenthaler), Part II's generic degree
  law and recovery algorithm, and **Cigler's central product** are not
  presented as new; the signed Vandermonde evaluation and the minimality lemma
  are elementary uses of known techniques. The proposed contribution is the
  first centred sector coefficient, the noncentral one-defect theorem, the
  minimal polynomial at every cyclotomic specialization and the sign-sensitive
  order laws, with their corollaries. First-discovery priority is **not**
  established: an equivalent result in Wronskian, orthogonal-polynomial or
  symmetric-function notation has not been ruled out, and targeted searches
  that found nothing are not evidence of absence. The endpoints `c = 0, 4`
  are outside its theorems; it does not solve multi-root resonance, claims no
  uniform collision asymptotics, and does not transfer its characteristic-zero
  minimality to positive characteristic. `O(t)` counts field operations for
  the factored answer, not bits, and exact equality tests are required. Its
  22,124 checks (`t <= 12` on the main grid) do not prove an
  unbounded-multiplicity claim. Its eight research directions (Section 40)
  are tasks relative to the manuscript, not asserted to be globally open.
- The theorems are over characteristic zero and are not to be transported
  unchanged to small positive characteristic. For arbitrary complex inputs
  "algorithm" presupposes exact field operations and equality tests; the
  cost estimate `O(R^4)` counts arithmetic operations, not bits.
- Of the extensions Part I's Section 11 named, Part II addresses only the
  multiple-factor one. A combinatorial interpretation of `c_(N,m,k)`, a
  product formula for the minors `M_(m,ell)(N)`, and joint limits with
  growing `m` or `a -> 0` remain open (dated pointer in Section 11).
- The finite computations are audits. A successful interpolation for twelve
  parameter patterns does not prove Theorem 18.1; only for a *particular*
  specialization, once the all-index order bound is proved, is a finite
  prefix a proof (Theorem 20.2).

## Labels

Part I's 109 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`,
`cor:`, `app:`) and are unchanged, with unchanged numbers. Part II added
**111** labels, all with the prefix `rc:` ("root collisions"): the
manuscript's 104 labels, prefixed, and 7 new ones. Part III added **123**
labels, all with the prefix `cyc:` ("cyclotomic"): the manuscript's 112
labels, prefixed, and 11 new ones (the seven of Section 28, the conclusion,
the remark on the meaning of one defect, and `cyc:x:rcq1`, `cyc:x:rcq2` on
Part II's research subsections 24.1 and 24.2). Total: 343 (220 before
batch 42). No label was renamed or removed, and no number of Parts I–II
moved (compared in the `.aux` files of a build of the committed text and the
new build; their page numbers moved: by one page in Parts I and II, because
the contents grew, and Part I's appendices past Part III). Parts II and III start at Sections 12 and 28; Part I's
appendices come after Part III and keep their letters. The notation tables
are Table 1 (Part II) and Table 2 (Part III); Part I has no numbered tables.

## Notation

Part II keeps the manuscript's symbols, which reuse many of Part I's letters
with other meanings; Table 1 (Section 12.3) lists them with the tempting false
reading. Watch in particular for:

- `q(x)` in Part II is the **multiplier**; Part I's `q(t) = 1 - (a+2b)t + b^2 t^2`
  is the quadratic denominator. Part II's generating-function variable is `u`.
- `H_N(q)` is the weighted determinant; Part I's `H_N^(m) = H_N(x^m)` and
  `D_N^(m)(a,b) = H_N(x^m (a + b x))`.
- `ell` is the multiplicity of the root 4 (Part I: the column index of
  `M_(m,ell)`); `s` is the number of interior roots and `s(z) = 1/(z - 1/z)`
  (Part I: the sign `s_m` and Barry's shift `s`); `d_k` are sector degrees
  (Part I: `d = binom(m,2)`); `P_k(N)` are sector polynomials in `N`
  (Part I: the numerator `P_m(t)`); `M_N` is the Christoffel matrix (Part I:
  minors `M_(m,ell)`); the shift operator is sans-serif `E` (Part I: `E` and
  the endpoint polynomial `E_m(N)`); `a`, `b` in Part II are local letters
  (roots, indices, block counts, a leading coefficient) except in
  Sections 13.1 and 21.1, where they are Part I's parameters.
- **Renamed:** the manuscript's maximal order `R_0` is printed `𝓡_0`, since
  Part I's `R_0(y) = 1` is the first of its polynomials (4.1). No
  normalization changed.

Part III keeps its manuscript's symbols, with nothing renamed and no
normalization changed (its rates and canonical sector polynomials are
Part II's for one root, `gamma = 1`); Table 2 (Section 28.3) lists them.
Watch in particular for:

- `H_N^(t)(c)` is `H_N((x-c)^t)`: the superscript is the **multiplicity**,
  whereas Part I's `H_N^(m)` has the **shift** as superscript.
- "Resonant range" means `3 <= L <= t` and omits the central `c = 2`
  (`L = 2`), which is resonant for `t >= 2` in Part II's sense; for one root,
  Part II's resonance is exactly Part III's "exceptional" (`L <= t`).
- "One defect" is a loss **after** grouping equal rates; the baseline
  `R_grp` is the degree of Part II's grouped annihilator `Psi_q` (20.3).
- `L = ord(z^2)` (Part II's `L_k` are leading coefficients); `T = binom(t,2)`
  (Part II's `T = sum t_i`); `q` is a multiplier in (31.5) but an
  indeterminate in Lemma 33.1; `ell_(t,k)` is a leading coefficient (Part II's
  `ell` is the multiplicity at 4); `B_(a,b)(N)` is the rectangular product with
  integers `a, b`; `D_t(N)` is Cigler's middle-binomial determinant (Part I's
  `D_N^(m)(a,b)`); `sigma(S)` is a subset sum but bare `sigma = z^L`;
  `Q_(t,k)(w)` is a remainder and `Q_a(X)` a quadratic factor; `E_a` is an
  exponent (sans-serif `E` is still the shift); `mu_n` are centred moments,
  not measures.
- One evident index slip of the manuscript was corrected: the multiplier in
  (31.7) is printed `prod_u (x - a_u)`, where the manuscript has
  `prod_a (x - a_a)` (disclosed in the merge note after Lemma 31.1).

## Files

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 77 pages (title page; contents pp. 2–5;
                                                     Part I pp. 6–21; Part II pp. 22–47; Part III pp. 48–74;
                                                     Part I's appendices pp. 75–76; references p. 77)
README.md                                            this guide
Makefile                                             Part I's make targets (pdf, test, clean); `test` rewrites data/ in place
notes/provenance.md                                  Part I: primary sources, version audit, novelty scope
code/catalan_hankel.py                               Part I: exact standard-library implementation
code/verify.py                                       Part I: independent determinant, coefficient, recurrence,
                                                     exceptional-case, reciprocity and asymptotic checks
data/verification.json                               Part I: machine-readable outcome and check counts
data/verification.txt                                Part I: captured console report of that run
data/sequences.csv                                   Part I: 1,395 integer values with explicit (m,a,b,N) columns
data/coefficient_rows.json                           Part I: coefficient rows, m = 0..8, N = 0..12
data/generating_functions.json                       Part I: uniform numerator/denominator arrays, m = 0..7,
                                                     four nonexceptional integer parameter pairs
data/minor_polynomials.json                          Part I: exact polynomials M_(m,ell)(N), m = 0..7
data/two_branch_polynomials.json                     Part I: polynomial multipliers of 4^N and 1^N, a = 1, b = 2, m = 0..7
02-root-collisions-provenance.md                     Part II: source/version audit, novelty scope, limitations
                                                     (delivered as notes/provenance.md)
code/02-root-collisions-catalan_collisions.py        Part II: exact rational reference implementation
code/02-root-collisions-verify.py                    Part II: verification suite (checks stay active under -O)
code/02-root-collisions-Makefile                     Part II: the delivered root Makefile (check, pdf, clean)
data/02-root-collisions-verification.json            Part II: recorded outcome, 2,843 checks, PASS
data/02-root-collisions-verification.txt             Part II: the same run as text
data/02-root-collisions-sectors.json                 Part II: sector polynomials, leading constants and characteristic
                                                     polynomials for twelve nonresonant patterns
data/02-root-collisions-resonances.json              Part II: exact minimal recurrences at 15 parameter choices
                                                     (12 single-root, 3 inter-root; see the data notes)
data/02-root-collisions-rational_input_examples.json Part II: three root-free rational-coefficient examples
data/02-root-collisions-central_root_certificate.json  Part II: the nine-value certificate for H_N((x-2)^4)
data/02-root-collisions-fourth_power_sequence.csv    Part II: exact H_N((2x-9)^4), N = 0..35 (CRLF)
03-cyclotomic-SOURCES.md                             Part III: pinned snapshot, literature inspected, contribution and
                                                     limitations (delivered as SOURCES.md)
code/03-cyclotomic-verify.py                         Part III: exact standard-library audit and root-free factorization
                                                     (delivered as code/verify.py)
code/03-cyclotomic-Makefile                          Part III: the delivered root Makefile (pdf, verify, quick, clean)
data/03-cyclotomic-verification_summary.json         Part III: recorded outcome, 22,124 checks, PASS, twenty counts
data/03-cyclotomic-verification_run.txt              Part III: console transcript of that run (per-order lines + summary)
data/03-cyclotomic-cyclotomic_orders.json            Part III: 264 principal cases (primitive order M = 3..24 of z,
                                                     t = 1..12) with minimal orders and multiplicities by k mod L
data/03-cyclotomic-orders_c1_c2_c3.csv               Part III: R(t,1), R(t,2), R(t,3) and the generic order,
                                                     t = 1..20 (CRLF)
```

The eleven `02-root-collisions-` files were staged in the placement commit
`e2b1f016a`, and the seven `03-cyclotomic-` files in `3609d0473`, all
byte-identical to the deliveries. The two CSVs are all-CRLF as delivered
(written by Python's `csv` module) and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`; never re-save them.

Data conventions (all parts): polynomial arrays are in ascending powers;
rational values are exact strings such as `"8/3"` or `"8/81"`, never rounded
decimals.

- Part I: in `coefficient_rows.json`, entry `k` is the coefficient of
  `a^k b^(N-k)`, not `a^(N-k) b^k`; in `minor_polynomials.json`, entry `j` is
  the coefficient of `N^j`; `generating_functions.json` uses powers of `t`;
  in `two_branch_polynomials.json`, `P_plus` and `P_minus` are polynomial
  multipliers of exponential sequences, **not** the generating-function
  numerator `P_m`; negative indices in the minor tests use polynomial
  binomial coefficients.
- Part II: a sector polynomial is a polynomial in the determinant size `N`,
  not a generating-function numerator. A characteristic list
  `[g_0, …, g_r]` means `sum_j g_j H_(N+j) = 0` for **every** `N >= 0`.
  `resonances.json` holds the single roots `c = 1, 2, 3` with multiplicities
  1–4 (proved bound, minimal order, characteristic polynomial, initial values)
  and three inter-root resonances; `rational_input_examples.json` holds
  `x^2 + 1` (order 4), `(x^2 + 1)^2` (order 15) and `(x - 2)^3` (order 6,
  characteristic polynomial `(X^2 + 1)^3`), the last only in the data.
  Although the file and Part II's Section 27 describe it as recording
  resonant parameters, five of its twelve single-root entries (`t = 1` for
  `c = 1, 2, 3`, and `t = 2` for `c = 1, 3`) are nonresonant, with the generic
  order; by Part III's Corollary 35.1 a single root is resonant exactly when
  `ord(z^2) <= t`. The other seven lie below the generic order.
- Part III: orders are minimal recurrence orders `R(t,c)`, valid from
  `N = 0`. In `cyclotomic_orders.json`, `primitive_z_order` is the order `M`
  of `z` in the audit ring `Z[z]/Phi_M`, `order_z_squared` is
  `L = M/gcd(M,2)`, and `multiplicities_by_k_mod_L` maps a residue class of
  sector indices to its exponent in the minimal polynomial (actual grouped
  multiplicities, not generic bounds; for `L > t` the keys are simply the
  `t + 1` sector indices; a class that cancels completely has exponent 0, as
  for `M = 6`, `t = 3`, which is `c = 3`). Odd `L` occurs twice, as `M = L` and `M = 2L`, with
  opposite signs of `z^L`. The CSV's columns are `t, c1_order, c2_order,
  c3_order, generic_order`.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex` until the cross-references stabilize (packages: `newtx`,
`mathtools`, `amsthm`, `microtype`, `geometry`, `hyperref`, `titlesec`,
`fancyhdr`, `listings`, `longtable`, `enumitem`). Build in a scratch copy of
`article.tex` so that no auxiliary files land here (Part I's `make pdf` builds
in place). The shipped PDF was built with MiKTeX (pdfTeX) with no errors, no
undefined or multiply defined references, no duplicate destinations and no
overfull or underfull boxes; a build of the committed text before each
addition was equally clean. No font files are included. The Part III
manuscript's own build used `tocloft` and `xurl` as well; the merged
article does not need them.

## Rerun the checks

Both suites are standard-library Python 3.10+, use exact integers and
rationals, and **rewrite their data files**. Run them only on a copy; on
Windows they also write CRLF line endings. Commands are for Git Bash or
another POSIX shell, from this directory (`py` may replace `python3`).

**Part I** (do not pass `-O`: it uses assertions):

```sh
W=/path/to/scratch/part1
mkdir -p "$W/code" "$W/data" "$W/recorded"
cp code/catalan_hankel.py code/verify.py "$W/code/"
for f in coefficient_rows.json generating_functions.json minor_polynomials.json \
         sequences.csv two_branch_polynomials.json verification.json verification.txt; do
  cp "data/$f" "$W/recorded/"; done
cd "$W"
python3 code/verify.py --out data > data/verification.txt
python3 code/catalan_hankel.py 8 3 --a 2 --b 3 --direct
```

The first command regenerates the six data files and its console report; the
second prints a direct and a formula evaluation. Rerun this way on
28 September 2026 (Python 3.14.4), all outputs equalled the recorded ones
apart from Windows line endings. From Python, with `code` on the import path:

```python
from catalan_hankel import coefficients, hankel_formula, hankel_direct
from catalan_hankel import generating_function, minimal_denominator

assert coefficients(3, 2) == (30, 54, 27, 4)
assert hankel_formula(3, 2, 1, 1) == 115
assert hankel_direct(3, 2, 1, 1) == 115
p, q = generating_function(2, 1, 1)
assert p == [1, 1]
assert q == [1, -6, 11, -6, 1]
assert minimal_denominator(2, -4, 1) == [1, 3, 3, 1]
```

`generating_function` deliberately returns the uniform, possibly unreduced
representation at exceptional parameters; `minimal_denominator` handles the
exceptions. The public routines are designed for integer `a, b`; the theorems
hold for complex parameters. Coefficient generation costs `O(N + m^2)`
arithmetic operations, not a bit-complexity bound.

**Part II.** Its files still use the delivered names. Run in place,
`code/02-root-collisions-verify.py` fails with `ModuleNotFoundError`, because
it does `from catalan_collisions import …` and the module is shipped as
`02-root-collisions-catalan_collisions.py`; and even with the import repaired,
its default `--out data` would **overwrite Part I's `data/verification.json`
and `data/verification.txt`** and add five unprefixed files. The delivered
Makefile (`code/02-root-collisions-Makefile`) runs `python3 code/verify.py
--out data`, which here is **Part I's** verifier. Restore the delivered layout
in a scratch copy instead:

```sh
W=/path/to/scratch/root-collisions
mkdir -p "$W/code" "$W/recorded"
for f in code/02-root-collisions-*.py; do cp "$f" "$W/code/${f#code/02-root-collisions-}"; done
for f in data/02-root-collisions-*; do cp "$f" "$W/recorded/${f#data/02-root-collisions-}"; done
cd "$W"
python3 code/verify.py --out data     # writes seven files to $W/data; compare with $W/recorded
```

Run this way on 28 September 2026 (Python 3.14.4, about 3 s) it printed
`TOTAL: 2843` (PASS), with 222 direct parameter cases and 12 nonresonant
patterns; the CSV was byte-identical and the six other outputs equal apart
from Windows line endings. The recorded counts: 304 endpoint-jet identities,
1,554 original-moment versus Christoffel determinant comparisons, 12 order
sums, 15 secondary-Hankel factorizations, 48 sector degree and leading-constant
checks, 328 exponential-expansion evaluations, 200 + 204 nonresonant and
resonant recurrence residuals, 9 + 12 + 3 minimal-recurrence recoveries
(nonresonant, resonant, inter-root), 111 root-free multiplicity profiles,
3 root-free recoveries and 40 central-root product evaluations. The two
determinant constructions share the low-level Gaussian elimination routine;
their moment and orthogonal-polynomial constructions differ. The root-free
routine, from the same scratch directory:

```python
import sys
sys.path.insert(0, "code")
from catalan_collisions import recurrence_from_coefficients

chi, bound = recurrence_from_coefficients([1, 0, 1], max_bound=16)  # q(x) = x^2 + 1
print(bound)  # 4
print(chi)    # Fractions 1, -5, 4, -5, 1: X^4 - 5X^3 + 4X^2 - 5X + 1
```

It is a transparent fallback that computes original determinants through
size `2*bound - 1`, so a large bound can be expensive; `max_bound` refuses
unexpectedly large requests. When rational roots are known,
`christoffel_values` uses a fixed-size determinant and is faster.
`minimal_recurrence` on its own is valid only for a sequence with a
**proved** all-index order bound; a finite prefix alone is not that proof.

**Part III.** Its files still use the delivered names. Run in place,
`code/03-cyclotomic-verify.py` defaults to `--output` = the report's
`data/` and would add three **unprefixed** files there
(`verification_summary.json`, `cyclotomic_orders.json`,
`orders_c1_c2_c3.csv`; no shipped file is overwritten); the transcript
`verification_run.txt` is its console output, not a file it writes. The
shipped name is not importable as a module. The delivered Makefile
(`code/03-cyclotomic-Makefile`), run from this directory, is worse: `verify`
runs **Part I's** `code/verify.py`, which rewrites Part I's `data/`; `quick`
passes that verifier options it rejects; `pdf` and `clean` build and clean
the merged `article.tex` in place. Restore the delivered layout in a scratch
copy instead:

```sh
W=/path/to/scratch/cyclotomic
mkdir -p "$W/code" "$W/recorded"
cp code/03-cyclotomic-verify.py "$W/code/verify.py"
for f in data/03-cyclotomic-*; do cp "$f" "$W/recorded/${f#data/03-cyclotomic-}"; done
cd "$W"
python3 code/verify.py --output data > verification_run.txt   # three files in $W/data
```

Run this way on 29 September 2026 (Python 3.14.4, about 30 s) it passed all
22,124 checks; `orders_c1_c2_c3.csv` was byte-identical and the two JSON files
and the transcript equal to the recorded ones apart from Windows line endings.
`python3 code/verify.py --quick --output data_quick` runs the smaller grid
(marked `"quick": true` in its output). The root-free factorization, from
the same scratch directory (the delivery README's example):

```python
import sys
sys.path.insert(0, "code")
from verify import CyclotomicRing, root_free_factors

ring = CyclotomicRing(12)
c = ring.add(ring.integer(2), ring.add(ring.zp(1), ring.zp(-1)))  # c = 2 + sqrt(3)
L, factors = root_free_factors(8, c, ring)
assert L == 6
assert sum((len(p) - 1) * e for p, e in factors) == 82   # (X-1)^17 (X+1)^7 (X^2+X+1)^13 (X^2-X+1)^16
```

`root_free_factors` reads neither the spectral generator nor the cyclotomic
order; it returns `(ascending coefficients, exponent)` pairs over the exact
ring interface of the audit. The subset expansion in the program is
deliberately exponential in `t` and is for testing only.

## Discrepancies and delivery names

- **Delivery names.** `code/02-root-collisions-verify.py` imports
  `catalan_collisions` and writes `data/verification.json`,
  `data/verification.txt`, `data/sectors.json`, `data/resonances.json`,
  `data/rational_input_examples.json`,
  `data/central_root_certificate.json` and `data/fourth_power_sequence.csv`;
  its docstring says it regenerates "all shipped numerical data" and that the
  theorem is proved in `article.tex` (now Part II of this `article.tex`).
  `code/02-root-collisions-Makefile` names `code/verify.py` and the root
  `article.tex`; it was delivered at the package root. The recorded
  `data/02-root-collisions-verification.json` says the universal arguments
  are "in article.tex". `02-root-collisions-provenance.md` was delivered as
  `notes/provenance.md`; its "present article" is the manuscript (Part II).
  The article (Sections 23 and 27) quotes the shipped names beside the
  delivered ones, and prints the delivered reproduction commands with the
  warning above.
- **Unshipped files.** The manuscript's own `article.tex`, its 23-page
  `article.pdf` and its delivery README are not shipped (they survive in
  `74f7f5bdb`); `article.pdf` here is a new build of the merged text.
- **Part I's instructions.** Part I's Section 10.3 and its `Makefile` run
  `code/verify.py --out data` in place, which rewrites the shipped Part I
  data; Section 10.3 now carries a dated pointer, and the recipe above uses a
  copy. Part I's `notes/provenance.md` is unchanged.
- **Overlap.** Part II re-derives, without assuming Part I, the Catalan
  orthogonality and `det(C_(i+j)) = 1`, the Christoffel identity (in a more
  general confluent form), a binomial determinant, the minimal-annihilator
  lemma (Part II's Lemma 19.1 restates Part I's Lemma 6.1, with the
  manuscript's proof kept as a second proof), and Part I's sharp order and
  exceptional orders. These are marked in the text; no Part I statement was
  changed. The observation that Part II's leading coefficient for `q = x^m`
  is Part I's `h_m`, and that the row `b = 0` of Part I's Theorem 2.3 is the
  case `s = 0` of Corollary 14.4, are the merge's own and are labelled so.
- **Bibliography.** The manuscript's items for Barry and for Krattenthaler's
  Ramanujan Journal paper (cited there as arXiv:2101.04225v5) are Part I's
  references [1] and [3]; its Cigler–Krattenthaler and Uvarov-formula items
  are added as [7] and [8]; its item for the pinned repository report is
  replaced by Part I and the pin in Section 12.1.
- **Part III delivery names.** `code/03-cyclotomic-verify.py` says in its
  docstring that "the universal proofs are in article.tex" (now Part III of
  this `article.tex`) and "Run from any directory: python3 code/verify.py
  [--quick] [--output PATH]"; it writes unprefixed `verification_summary.json`,
  `cyclotomic_orders.json` and `orders_c1_c2_c3.csv`.
  `code/03-cyclotomic-Makefile` names `article.tex` and `code/verify.py` (and
  `data_quick/`); it was delivered at the package root.
  `03-cyclotomic-SOURCES.md` was delivered as `SOURCES.md`; its "new article"
  is the manuscript (Part III), and its "Nothing was committed to the user's
  repository" describes the delivery, before placement. The recorded
  transcript `data/03-cyclotomic-verification_run.txt` is console output
  (22 per-order lines and the summary JSON). The article (Sections 39 and 43)
  quotes the shipped names beside the delivered ones, prints the delivered
  rebuild commands with the warning above, and marks in a merge note that the
  manuscript's "No code was added to the ProveIt repository" is superseded by
  the placement.
- **Part III unshipped files.** The manuscript's `article.tex`, its 22-page
  A4 `article.pdf` and its delivery README are not shipped (they survive in
  `8315d24e3`). The delivery README's content — result summary, status,
  rerun and build commands, and the root-free example — is covered by
  Sections 28 and 39 and by this README.
- **Part III overlap.** Part III re-derives, without assuming Parts I–II, the
  Catalan measure and orthogonality (a third time), the confluent Christoffel
  identity (Part II's (15.8) for `q = (x-c)^t`), the minimal-annihilator lemma
  (Lemma 34.1 = Part I's Lemma 6.1 = Part II's Lemma 19.1; a third proof),
  and the one-root degree law and generic order (Part II's Theorem 14.2 and
  Corollary 14.3, by a different route), and contains Part II's central
  examples at `t = 2, 4`. All are marked in the text; no statement of
  Parts I–II was changed. The comparisons with Part II's data and leading
  coefficients, and the third route to the even central case (below), are the
  merge's own observations and are labelled so.
- **Part III bibliography.** Its Krattenthaler (arXiv:2101.04225v5) and Barry
  items are Part I's [3] and [1]; Cigler's arXiv:2111.14492 is added as [9]
  (the manuscript does not state the version; the sibling reports cite v3);
  its item for the pinned repository report is replaced by Parts I–II and the
  pin in Section 28.1.
- **Part III editorial fix.** One index slip, `prod_{a=1}^t (x - a_a)` in the
  manuscript's display (31.7), is printed `prod_{u=1}^t (x - a_u)`, with a
  merge note.

## Relation to neighbouring reports and to the formal project

The sibling reports in `hankel-determinants/catalan-and-ballot/`
(`ballot-polynomial-hankel-determinants`, `cigler-conjecture-16-parity`,
`cigler-conjecture-8-schur`) treat Cigler's conjectures for ballot and middle
binomial moments; `cigler-conjecture-16-parity` also proves a Christoffel
identity, for its own moment sequence. None states a result about weighted
Catalan Hankel determinants, and Part II names none of them, so no reciprocal
note was written. Part II's research direction 24.3 (a Schur-function
description of the sector polynomials) is only a possible point of contact
with `cigler-conjecture-8-schur`; no connection is established.

Part III does touch those siblings. All three concern conjectures (8, 13–15,
16) of the Cigler paper arXiv:2111.14492 whose **proved** Theorem 1, eq. (23),
Part III uses for the central root. As an observation of this merge (Section
28.5), `cigler-conjecture-8-schur` proves an even-shift Hankel–Schur identity
for Cigler's polynomials `b_m(t)` (its Theorem 3.1), with `b_m(1)` the middle
binomial coefficient, and at `t = 1` the dimension product
`prod_{i,j<=k} (n+i+j-1)/(i+j-1)` (its Proposition 7.2); together these give
`D_(2k)(n) = B_(k,k)(n)`, the even case of the central product of Part III's
Theorem 30.4, by a Schur-function route. The odd case is not covered there.
No reciprocal note was written in that report in this change; it would be a
natural one.

The report sits in the research-report collection of the `SetTheory/Cardinals`
Lean project. That placement confers no formal status: no Lean or Rocq
declaration anywhere in ProveIt formalizes a result of Parts I–III as stated. The
nearest Lean material, the Catalan-number and generic moment-Hankel modules of
`Analysis/FabiusFunction/Lean/FabiusFunction/` (for example
`CatalanGeneratingFunction.lean`, `MomentHankelMatrix.lean`), concerns other
objects and states no result of this report. Classical Prony material in
`Algebra/SurrealNumbers/Surreal/Algebra/PronyHankel.lean` is related but
narrower: `Surreal.Prony.det_hankel_moment` is the Vandermonde factorization
of the Hankel determinant of `sum_i w_i a_i^r`, which is the case of Part II's
Lemma 19.2 (not claimed new there) in which every exponential polynomial is
constant, and `Surreal.Prony.monic_annihilator_unique` is a uniqueness
statement for monic annihilators under an invertible Hankel matrix; neither
formalizes a theorem of Parts I–III. Part II's Section 23.3 and Part III's
Section 40.8 propose formalization routes (jets, confluent Vandermonde, the
maximal-degree Cauchy–Binet lemma, finite-prefix certification; the
exponential-block minimality lemma, the nearest-representative and square-sum
lemmas, and the implication from the two sector coefficients to the one-defect
law); none has been started.

## Sources and attribution

Paul Barry, *Notes on the Hankel transform of linear combinations of
consecutive pairs of Catalan numbers*, arXiv:2011.10827v1 (21 November 2020),
p. 4. https://arxiv.org/abs/2011.10827

Christian Krattenthaler, *Hankel determinants of linear combinations of
moments of orthogonal polynomials, II*, The Ramanujan Journal 61 (2023),
597–627 (arXiv:2101.04225); Theorem 1, Proposition 5 and Section 8,
Corollary 9. https://doi.org/10.1007/s11139-021-00514-8

Johann Cigler and Christian Krattenthaler, *Hankel determinants of linear
combinations of moments of orthogonal polynomials*, International Journal of
Number Theory 17 (2021), 341–369. https://arxiv.org/abs/2003.01676

Christian Krattenthaler, *A determinant identity for moments of orthogonal
polynomials that implies Uvarov's formula …*, arXiv:2103.03969 (a starting
point for a research direction, not an input to any proof).

Johann Cigler, *Hankel determinants of middle binomial coefficients and
conjectures for some polynomial extensions and modifications*,
arXiv:2111.14492 (2021); Theorem 1, eq. (23), the central product used in
Part III (version not stated by the manuscript).
https://arxiv.org/abs/2111.14492

Dougherty, French, Saderholm and Qian (J. Integer Sequences 14 (2011)), DLMF
18.5.7 and OEIS A000108, A001519, A001906 are cited in Part I. Part I's
sources were checked on 19 September 2026 and Part II's on 28 September
2026; Part III's manuscript is dated 29 September 2026 and its source notes
do not date their checks. The three provenance notes record the versions
inspected and the limits of each search. No third-party paper PDFs, font files, compiler auxiliaries or
bytecode are included.
