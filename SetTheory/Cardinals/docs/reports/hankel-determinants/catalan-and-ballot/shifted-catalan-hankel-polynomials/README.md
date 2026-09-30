# Shifted Catalan Hankel Polynomials

**Exact coefficients, sharp recurrences, and a denominator conjecture; with root collisions and sharp recurrences for arbitrary polynomial multipliers, cyclotomic resonances of one repeated root, two-endpoint confluence, interior root collisions, and growing shifts**

This is a research report in six parts. Part I is the original report of
19 September 2026, on the shifted linear multiplier `x^m (a + b x)`. Part II
was added on 28 September 2026 in batch 39 of ProveIt's incoming-report
intake, from a later manuscript that takes up the extension Part I named and
left open (its Section 11): "multiple distinct linear factors in the
multiplier lead to more exponential sectors and new collision patterns".
Part III was added on 29 September 2026 in batch 42, from a manuscript that
answers Part II's first research question, "Closed classification of
cyclotomic resonances" (Section 24.1), for one repeated root, and shows that
the question's proposed parameters do not suffice. Part IV was added on
29 September 2026 in batch 53, from a manuscript that answers the endpoint
half of Part II's research question "Uniform endpoint and root-collision
limits" (Section 24.4). Part V was added on 29 September 2026 in batch 55,
from a manuscript that answers the other half, collisions of roots away from
the endpoints (which Part IV had left open as its first research question,
Section 57.1), for fixed degree and fixed nonendpoint bases; limits uniform
up to the endpoints stay open. Part VI was added on 29 September 2026 in
batch 57, from a manuscript that takes up the regime Part I (Sections 8 and
11) and Part IV (Section 44.4) left open, the shift `m` growing with the
determinant size `N`: for the one-factor family `D_N^(m)(a,b)` with real
`a/b >= 0` it treats every relative growth of `N` and `m`, and it partly
answers Part IV's research question 57.4 ("Multiplicities growing with
determinant size", for `ell = 0` and one displaced root), which it does not
cite. Parts I–III were prepared with OpenAI ChatGPT
for Vladimir Reshetnikov; Part IV's manuscript is AI-assisted research
prepared for him and does not name the assistant; Part V's names no
assistant on its title page, but its PDF metadata gives the author as
"OpenAI ChatGPT; prepared for Vladimir Reshetnikov"; Part VI's is
"AI-assisted research prepared for Vladimir Reshetnikov" and names no
assistant, on its title page or in its PDF metadata. All six are
AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 19 Sep 2026 (*Shifted Catalan Hankel Polynomials: Exact coefficients, sharp recurrences, and a denominator conjecture*) | `catalan_hankel_conjecture_solution.zip` | (none) | unpacked `a3fe9660e`, in ProveIt since `dc54c3cb3` | Part I: Sections 1–11 (pp. 10–25) and Appendices A–B (pp. 158–159) |
| 02 | batch 39, manuscript 03 (*Root Collisions and Sharp Recurrences for Polynomially Weighted Catalan Hankel Determinants*, 28 Sep 2026, 23-page PDF as delivered) | `ProveIt_Catalan_Root_Collisions.zip` (inner `ProveIt_Catalan_Root_Collisions/`, main file `article.tex`) | `fbba58593` | `e2b1f016a` (prefix `02-root-collisions-`) | Part II: Sections 12–27 (pp. 26–52) |
| 03 | batch 42, manuscript 01 (*A One-Defect Law for Cyclotomic Catalan Hankel Recurrences: Complete single-root classification, a necessary sign parameter, and the central exception*, 29 Sep 2026, 22-page A4 PDF as delivered) | `ProveIt_Cyclotomic_Catalan_Recurrences.zip` (inner `cyclotomic_catalan/`, main file `article.tex`) | `9754e8360` (and blob `b29ea42f` of this `article.tex`) | `3609d0473` (prefix `03-cyclotomic-`) | Part III: Sections 28–43 (pp. 53–79) |
| 04 | batch 53, manuscript 02 (*Two-Endpoint Confluence for Catalan Hankel Determinants: An exact even finite-size expansion, the first interaction law, and a sharp critical scale*, 29 Sep 2026, 20-page A4 PDF as delivered) | `Two_Endpoint_Catalan_Confluence.zip` (inner `Two_Endpoint_Catalan_Confluence/`, main file `article.tex`) | `1ee53d57d` (and blob `e5a4d814` of this `article.tex`) | `1dc874990` (prefix `04-endpoint-confluence-`) | Part IV: Sections 44–60 (pp. 80–103) |
| 05 | batch 55, manuscript 03 (*Interior Root Collisions in Catalan Hankel Determinants: Convergent sector expansions, multiple clusters, and phase-dependent zero motion*, 29 Sep 2026, 24-page A4 PDF as delivered) | `ProveIt_Interior_Collision_Research.zip` (inner `ProveIt_Interior_Collision_Research/`, main file `article.tex`) | `e1afd75e3` (README only; no blob recorded) | `26473dfa0` (prefix `05-interior-collision-`) | Part V: Sections 61–80 (pp. 104–132) |
| 06 | batch 57, manuscript 02 (*A Catalan Law Behind Growing Shifts: Three critical scales, an all-orders hierarchy, and uniform Hankel asymptotics*, 29 Sep 2026, 21-page A4 PDF as delivered) | `ProveIt_Catalan_Growing_Shifts.zip` (inner `Catalan_Growing_Shifts/`, main file `article.tex`) | `1085b506d` (and blob `b23831b8` of this `article.tex`, blob `ce3436af` of this README) | `70b39943a` (prefix `06-growing-shifts-`) | Part VI: Sections 81–99 (pp. 133–157) |

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

The pin `1ee53d57d` is ProveIt commit
`1ee53d57de253d16cdaad79d1f54bbd95d76d682` (the first batch-52 arrival); the
batch-53 manuscript read this report's combined `article.tex` there (blob
`e5a4d81408c80f0385ae66c26fbd11bba7dfdb09`, which it records) and its README,
through the GitHub connector. The report's `article.tex` is unchanged between
the pin and the placement commit (same blob, unchanged since the batch-42 write
`e9f425f4f`), so Part IV's "repository", "source" and "report" are Parts I–III
as printed here, and the section numbers it cites (Part II's 22 and 24.4) are
this report's. The archive arrived in `148a906aa`. Its manuscript, PDF and
delivery README are not shipped; they survive in the arrival commit. Its
source notes and proof audit are shipped verbatim as
`04-endpoint-confluence-SOURCES.md` and `04-endpoint-confluence-PROOF_AUDIT.md`.
Part IV prints every result, proof, example, remark, limitation and question
of the manuscript; Section 44 records the provenance, the notation, what
Part IV answers, and where the merge had to choose.

The pin `e1afd75e3` is ProveIt commit
`e1afd75e35a4de734d5aa47aec5cdb917b82ed3e` (the batch-53 record in the
incoming-report README). The batch-55 manuscript records no blob: through the
GitHub connector it read only this report's README there, which described
three parts, because the combined `article.tex` at that commit is still blob
`e5a4d81408c80f0385ae66c26fbd11bba7dfdb09` (Parts I–III; Part IV was written
in `e300500cb`, after the pin). By its source notes it took Part II's
question from the standalone Part II manuscript and Part IV's scope and
question from the standalone batch-53 manuscript, both read from Vladimir's
file library; that manuscript's "Section 13.1" is Section 57.1 here. The body
of Section 24.4 is unchanged between the pin and the placement commit apart
from its label and the dated batch-53 note, and Section 57.1 as printed here
is the passage the manuscript paraphrases, so Part V's "repository" and
"inspected repository reports" are Parts I–III as printed here, its
"root-collision report" is Part II, and its "endpoint continuation" is
Part IV. The archive arrived in `2d4919838`. Its manuscript, PDF, delivery
README and checksum list are not shipped; they survive in the arrival commit
(the checksum list, 13/13, was verified at placement and retired). Its source
audit and proof status are shipped verbatim as
`05-interior-collision-SOURCES.md` and `05-interior-collision-PROOF_STATUS.md`.
Part V prints every result, proof, example, remark, limitation and question
of the manuscript; Section 61 records the provenance, the notation, what
Part V answers (with one observation of the merge, Remark 61.1), and where
the merge had to choose.

The pin `1085b506d` is ProveIt commit
`1085b506d65e207a05b7e9c861bb1fe88432fe38` (a fix commit for the batch-54
Fabius-tree arrivals). Through the GitHub connector the batch-57 manuscript
read this report's combined `article.tex` there (blob
`b23831b8f20efab08342b11bb4939809d0a8047e`, Parts I–IV) and its README (blob
`ce3436af04afdb64c683d9d36be3f0b45c6ccf5e`), both of which it records, and
Part V's already shipped `05-interior-collision-SOURCES.md`. The pin precedes
Part V, written in `b2aed2d23`, which is the only change to the report
between the pin and the placement commit; the passages Part VI continues
(Part I's Sections 8 and 11 and Theorem 2.1, Part IV's Section 44.4 and
questions of Section 57) are textually unchanged since the pin apart from
Part V's dated notes and one label, so its "repository" and "inspected
reports" are Parts I–IV as printed here. The line numbers in its source
audit are those of the pinned files. The archive arrived in `6ad01e9c8`. Its
manuscript, PDF, delivery README, delivered figures and checksum list are not
shipped; they survive in the arrival commit (the checksum list, 17/17, was
verified at placement and retired). Its source audit, proof audit and build
check are shipped verbatim as `06-growing-shifts-SOURCES.md`,
`06-growing-shifts-PROOF_AUDIT.md` and `06-growing-shifts-BUILD_CHECK.md`.
Part VI prints every result, proof, remark, limitation and question of the
manuscript; Section 81 records the provenance, the notation, what Part VI
answers (with observations of the merge), and where the merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. All six
parts give written all-parameter proofs; their exact-arithmetic suites (and
the high-precision diagnostics of Parts IV and V and the floating-point
diagnostics of Part VI) are finite audits and debugging checks, not
substitutes for those proofs.

## Results

Write `C_n = binomial(2n, n)/(n + 1)` and let `N` be the determinant size
(not the last index), with the empty determinant equal to 1.

**Part I** (unchanged apart from dated pointers in the abstract and
Sections 8, 10.3, 11 (four) and Appendix B, two title-page lines (the second
shortened in batch 55 to "cyclotomic resonances, two-endpoint confluence,
and interior root collisions" and extended in batch 57 to "cyclotomic
resonances, two-endpoint confluence, interior root collisions, and growing
shifts", the pair now set one size smaller), title-page vertical spaces
reduced (by 3 mm in batch 42, by 12 mm in all in batch 53, by a further 7 mm
in batch 55 and by another 7 mm in batch 57, so that the page still fits),
contents entries for the six parts, two bibliography entries used only by
Part II, one used only by Part III, three used only by Part IV, one used only
by Part V and three used only by Part VI, a bibliography label column
widened for twelve entries, and the closing note on source dates). For

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
pointers in Sections 20.1, 21.4 and 24.1–24.2, dated batch-53 and batch-55
pointers in Sections 22 and 24.4, and new labels on Sections 24.1, 24.2, 24.4
and 24.5). For a
nonzero polynomial `q`, let
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

**Part III** (batch-42 manuscript 01; unchanged apart from new labels on
Sections 40.2 and 40.4). One repeated root: the multiplier is
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

**Part IV** (batch-53 manuscript 02; unchanged apart from dated batch-55
pointers after its introductory paragraph and in Sections 44.4 and 57.1, a
new label on Section 57.2, and dated batch-57 pointers in Sections 44.4 and
57.4 with a new label on Section 57.4). Two endpoint clusters: `m` roots
`c_i^- = 2 - 2 cos(sqrt(y_i)/nu)` near 0 and `ell` roots
`c_j^+ = 2 + 2 cos(sqrt(v_j)/nu)` near 4 (square roots only through entire
power series), `d = m + ell`, **`nu = N + d/2`**, `h = 1/nu`,
`kappa = binom(m,2) + binom(ell+1,2)` (Part II's `kappa`), and the normalized
determinant `Z_N = (-1)^(N ell) nu^(-kappa) H_N(q_N)`. Negative real
coordinates mean outward motion. It proves:

1. **An exact even expansion** (Theorem 47.1): `Z_N = sum_j A_j / nu^(2j)`, a
   convergent series that is the Taylor series of an even holomorphic
   function of `h`, locally uniform in the coordinates including every
   collision pattern inside each cluster (and after differentiation); no odd
   power of `1/nu` occurs at all. The leading term factorizes,
   `A_0 = 2^(ell - m ell) K_m^-(1; y) K_ell^+(1; v)` (47.2), into confluent
   cosine and sine Wronskian-type kernels (46.8)–(46.9), whose derivative
   columns are **not** factorial-normalized.
2. **The first interaction law** (Theorem 47.2, (47.3)): the complete `A_1`,
   entire (no division by `A_0`), with a mixed term
   `-(d_t K_m^-)(d_s K_ell^+)/4`, so multiplying two one-endpoint expansions
   gives the wrong correction; an Euler-operator form (47.4).
3. **Endpoint values** (Corollary 47.3): `A_0(0,0) = 2^(ell - m ell +
   binom(m,2) + binom(ell,2)) prod_{r<m} r!/(2r)! prod_{r<ell} r!/(2r+1)!` and
   `A_1/A_0 = -(a(a-1) + b(b-1) + 6ab)/24` at 0, `a = binom(m,2)`,
   `b = binom(ell+1,2)`.
4. **A sharp outward scale** (Theorem 47.4): for nonnegative outward
   displacements, `R_N = H_N(q~_N)/H_N(x^m (x-4)^ell) -> 1` **if and only if**
   `N^2 max(displacement) -> 0`; with finite limits of `N^2`·displacement the
   limit is a ratio of kernels (47.10), larger than 1 unless all limits are 0;
   if `N^2 max(displacement) -> infinity` then `R_N -> infinity`.
5. The mechanism: an exact centred hyperbolic alternant (Lemma 49.1), a
   product of `sinhc` within clusters and `cosh` between them that generates
   every coefficient (49.3), with its quadratic term (49.5); an explicit
   conservative remainder bound (Theorem 50.2); positive Schur expansions of
   the outward profiles (Theorem 52.1).
6. **The answer in Part II's own scaling** (Corollary 54.1): for
   `c_N = 2 + 2 cosh(tau/N)` with normalization `(-1)^(tN) N^(t(t+1)/2)`, and
   `c_N = 2 - 2 cosh(tau/N)` with `N^(t(t-1)/2)`, the limits `F_t^+(tau)` and
   `F_t^-(tau)` (54.1), entire and even, their values at `tau = 0` (54.5), and
   the `O(1/N)` term (54.6), which is exactly the centring `N -> N + t/2`;
   exact spatial displacements `h^2 y`, `4 - h^2 v` also give an even
   expansion (54.7).
7. Worked examples: one root at either endpoint (`F_1^- = cosh tau`,
   `F_1^+ = 2 sinh(tau)/tau`), one at each (55.1), two coincident roots (55.2)–(55.3),
   `H_N(x^2 (x-4)^2) = (N+1)(N+2)^2(N+3)/12` (55.4), and a confluent
   two-cluster numerical table; ten research directions (Section 57).

Consistency with Parts II–III (checked for this merge by a separate exact
computation, not shipped; Section 44.4): the endpoint value (47.5) equals
Part II's leading coefficient (18.8) for `q = x^m (x-4)^ell`, in general and
by exact arithmetic for `m, ell <= 3`, so Corollary 47.3 is a second route to
the case `s = 0` of Theorem 18.1, and at exact endpoints Part II's single
sector polynomial is a polynomial in `nu = N + d/2` with only powers of the
parity of `kappa`; (55.4) is the same polynomial as Part II's `H_N((x-2)^4)`,
i.e. Part III's `B_(2,2)(N)` (observed, not explained); the small
determinants of Section 59 agree with direct evaluation for `N <= 7`.

**Part V** (batch-55 manuscript 03). Roots colliding away from the
endpoints: `d` roots `c_i = 2 + 2 cosh(w + u_i/nu)` at a fixed base
`c = 2 + 2 cosh w` outside `{0, 4}` (`w` not in `pi i Z`), with
**`nu = N + d/2`**, `h = 1/nu`, scaled coordinates `u_i` in compact complex
sets (any collision pattern), `D = binom(d,2)` (**not** Part II's
`D = deg q`, which is `d` here), and `r = d - k`. It proves:

1. **A convergent collision-sector expansion** (Theorem 64.1, (64.7)): for
   all large `N`, exactly,
   `H_N(q_N) = (-1)^(N d) sum_k e^((2k-d) nu w) nu^(k(d-k)) F_k(1/nu; u, w)`,
   where each amplitude `F_k` is holomorphic near `h = 0`, symmetric and
   entire in `u`, with a **convergent** Taylor series whose leading term is
   `B_(d,k)(w) S_(d,k)(u)` (64.8): a universal profile (64.4)–(64.5) times a
   nonzero base constant (64.6); the remainder bound is absolute (64.9), not
   relative, and includes every collision and coordinate derivatives. Values
   and symmetries of the profile (Proposition 64.2).
2. **The first correction** (Theorem 66.1, (66.2)), with multiplication by
   `U = sum u_i` and the Euler operator; it vanishes for the central sector
   when `d = 2m` and `U = 0`. An all-orders finite coefficient algorithm
   (Section 66.1). Unlike Part IV's endpoint expansion, **the expansion is not
   even** (remark closing Section 66).
3. **An explicit Cauchy remainder** (Theorem 67.1, (67.3)) with explicit
   radius (67.1) and constant (67.2), conservative, including collisions.
4. **Several separated clusters** (Theorem 68.1): one global `nu = N + d/2`,
   leading amplitudes a product of `B S` factors and explicit nonzero cross
   factors `T_ab` (68.3), (68.5); separation of the bases is essential
   (Remark 68.2).
5. **Inside the interval** (`w = i theta`): the even and odd total
   multiplicity laws (Corollary 69.1, (69.1)–(69.2)); the odd case has two
   tied phases and need not have an `N`-independent limit.
6. **Sine-kernel duality** (Lemma 70.1, Theorem 70.2): the profile
   `S_(2t,t)(ix, iy)` is `2^t det[sinc(x_i - y_j)]/(Delta(x) Delta(y))`,
   strictly positive for `x = y` real at every collision pattern.
7. **Two equal-multiplicity roots** at `2 + 2 cos(theta +- tau/(N+t))`
   (Theorem 71.1, (71.7)): `H_N/(A_t(theta) nu^(t^2)) = Phi_t(tau) +
   (-1)^t sin(2 nu theta) Psi_t(tau)/(nu sin theta) + O(nu^-2)`, `nu = N + t`;
   `Phi_t` is the normalized oscillatory Jacobi (kissing-polynomial) Hankel
   determinant at frequency `2 tau` (Proposition 71.2); `Phi_(2m) > 0` on the
   real line (Corollary 71.3); large-frequency parity asymptotics and the large
   simple zeros of odd `t` (Lemma 72.1, Proposition 72.2).
8. **Zero transport** (Theorems 73.1, 73.2): near a simple real profile zero
   there is exactly one finite-size zero, real and simple, with explicit first
   displacement (73.2), and a **convergent** expansion (73.5) whose `l`-th
   coefficient is a Laurent polynomial of degree at most `l` in the phase
   `e^(2 i nu theta)`, `b_1` explicit (73.6).
9. Examples: the exact two-simple-root formula (74.1) with `Phi_1 = sin(2
   tau)/(2 tau)`; periodic and quasiperiodic scaled zero motion (Corollary
   74.2: a whole interval of limits when `theta/pi` is irrational, finitely
   many when rational, exact zeros at `theta = pi/2`); `Phi_2` (74.6); the
   centre law (74.7). Nine research directions (Section 77).

What Part V answers (Section 61.4): Part II's Section 24.4, second version,
and Part IV's question 57.1, for fixed degree and fixed nonendpoint bases,
with the oscillatory sectors retained; the caveat closing Part II's
Section 22 for collisions away from the endpoints. The manuscript states the
pair law only in centred coordinates; as an **observation of this merge**
(Remark 61.1, derived from Theorem 71.1 and checked numerically for `t = 1`,
not shipped), in Section 57.1's uncentred coordinates `z e^(+-tau/N)` the
`1/nu` term gains the non-oscillatory summand `t tau Phi_t'(tau)`. Not
answered: limits uniform up to the endpoints (Part V's own question 77.1),
Part IV's question 57.2 (generalized, not answered, in 77.2), Part III's
Sections 40.2 and 40.4 (not discussed).

Consistency with Parts II–IV (Section 61.4, observations of this merge): at
`u = 0` the sector rates `(-1)^d z^(2k-d)` and growth `N^(k(d-k))` are Part
II's Corollary 14.3 (leading constants not compared symbolically); at
`theta = pi/2` the centre law (74.7) has no `1/nu` term, and its constant
`A_t(pi/2) = prod_{j<t} j!^2 / prod_{j<2t} j!` is the leading coefficient of
Part III's central product `B_(t,t)(N)` (Theorem 30.4), a polynomial in
`nu = N + t` of the parity of `t^2` (checked by hand; `t = 1, 2` give `nu` and
`nu^2 (nu^2 - 1)/12`); Lemma 63.1 is a fifth route to the Christoffel
identity, and Lemma 65.1 uses Part IV's centring `alpha_j = j - (d-1)/2`
(Lemma 49.1), which the manuscript does not cite.

**Part VI** (batch-57 manuscript 02). A growing shift: the one-factor
family `D_N^(m)(a,1)` with integers `N >= 1`, `m >= 0` and **arbitrary
relative growth**, normalized by `v = m + 1/2`, `B = N + m + 1`,
`c = v/(N B)`, `mu = N B/(4 v)`, `a = tau/mu` and
`R(tau) = D_N^(m)(tau/mu, 1)/H_N^(m+1) = 2F1(-N, B; v; -c tau)`; the
concentration index is `beta = (1 + c (v + 3/2))/(v + 1)` and the shape
`theta_(N,m) = 1/((v + 1) beta)`, in `(0, 1)`. (For `b > 0`,
`D_N^(m)(a,b) = b^N D_N^(m)(a/b, 1)`; the probabilistic and sharp-order
statements need `a/b >= 0`.) It proves:

1. **Exact coefficients and an invisibility criterion** (Proposition 84.1,
   Corollary 84.2): `R(tau) = sum_k A_(N,m)(k) tau^k/k!` with
   `A(k) = prod_(j<k) (1 - j/N)(1 + j/B)/(1 + j/v)` in `(0, 1]` — Part I's
   Theorem 2.1 at `b = 1` (84.5), credited — so `1 + tau <= R(tau) <= e^tau`,
   and for `a >= 0` the ratio `D_N^(m)(a,1)/H_N^(m+1)` tends to 1 **if and
   only if** `a N (N+m+1)/(4 (m + 1/2)) -> 0`, for every growth of `m`.
2. **Inverse-zero weights** (85.1)–(85.2): `w_j = 1/(mu x_j) > 0` over the
   zeros `x_j` of the Jacobi polynomial, `sum w_j = 1`,
   `R(tau) = prod_j (1 + tau w_j)`; an exact rational Riccati recurrence for
   all power sums `S_r` (Proposition 85.1), `S_2 = beta`; `beta -> 0` iff
   `N, m -> infinity`, and `theta_(N,m) -> (1 + rho)/(1 + rho + rho^2)` when
   `m/N -> rho` (Lemma 85.2).
3. **A uniform majorant** (Theorem 86.1): `S_r <= C_(r-1) (2 beta)^(r-1)`,
   so the largest weight is `W <= min(1, 8 beta)` (8 is not claimed sharp).
4. **The first critical scale** (Theorem 87.1, Corollary 87.2):
   `0 <= log R(tau) - tau + beta tau^2/2 <= (8/3) beta^2 tau^3` for
   `tau >= 0`, a complex disk bound, and `R(tau)/e^tau -> 1` iff
   `beta tau^2 -> 0`, with limit `e^(-s^2/2)` at `tau sqrt(beta) -> s`.
5. **The shifted Catalan law** (Theorem 88.2): the size-biased inverse-zero
   measure `sum_j w_j delta_(w_j/beta)` converges to the law of
   `1 - theta + theta Y`, `Y` Marchenko–Pastur of parameter one (the Catalan
   density on `(0, 4)`), with moments
   `d_r(theta) = sum_j binom(r-1, j) C_j theta^j (1 - theta)^(r-1-j)` (88.5).
6. **Every fixed critical level** (Theorem 89.1): at
   `z = u beta^(-(q-1)/q)`, after the exact first `q - 1` logarithmic terms
   are subtracted, the limit is `exp((-1)^(q+1) d_q(theta) u^q/q)`; the lower
   moments must be the exact finite-parameter ones (Remark 89.2).
7. **The free energy** (Theorem 90.1): `beta log R(t/beta) -> F_theta(t)`
   uniformly with derivatives, `L_theta = F_theta'` the positive root of
   `theta t L^2 + L = 1/(1 + (1 - theta) t)` (90.3); `F_0 = log(1 + t)` and
   an explicit `F_1` (90.5); a central limit theorem for the coefficient law
   `K_tau` on that scale (Corollary 90.2).
8. **The nominal-Poisson transition** (Theorems 91.1, 91.2):
   `d_TV(K_tau, Pois(lambda)) <= beta tau (1 + 8 beta tau)` with the exact
   mean `lambda`, and, if `beta tau -> 0` and `beta tau^(3/2) -> sigma`,
   `d_TV(K_tau, Pois(tau)) -> 2 Phi(sigma/2) - 1`; so the determinant's
   threshold `beta^(-1/2)` and the nominal-Poisson threshold `beta^(-2/3)`
   are different (Remark 91.3).
9. **A uniform saddle prefactor** (Theorem 92.1): for `m/N` and `t` in
   compact subsets of `(0, infinity)`,
   `R(N t) = A(r, b, t) exp(N f(q; r, b, t)) (1 + O(1/N))`, with a local
   central limit theorem, the coefficient rate function (92.13) and the
   consistency identity `b_rho f_(rho,t)(q) = F_theta(b_rho t)` (92.15).
10. Boundary regimes (Section 93): fixed `m` gives
    `0F1(; m + 1/2; (m + 1/2) tau)` (93.1) and fixed `N` gives
    `(1 + tau/N)^N` (93.2); the orders of magnitude of `a` in three
    regimes; a two-threshold table for `N = m` up to 16384 (Section 94.1);
    ten research directions (Section 96).

What Part VI answers (Section 81.4): the joint limits with growing `m` left
open by Part I's Sections 8 and 11 (and their batch-39 and batch-53 notes)
and by Part IV's Section 44.4, for this one-factor family with `a/b >= 0`;
and, **uncited by the manuscript**, Part IV's question 57.4 in part, for
`ell = 0` and the cluster `x^m (x + eps)` with one outward displacement.
Several displaced roots, `ell > 0`, the first correction and an
approximation uniform in `1 <= m <= N` (Part VI's own question 96.3) stay
open, as do coalescing roots and `a/b < 0`. Consistency (observations of this
merge, Section 81.4): (84.5) is Part I's (2.1) at `b = 1`; for fixed `m`,
Corollary 84.2 reduces to Part IV's threshold `N^2 eps -> 0`
(Theorem 47.4), and the limit `0F1(; m + 1/2; y/4)` when `N^2 eps -> y`
must be Part IV's profile ratio (47.10) at the coordinates `(0, …, 0, y)` —
checked by hand for `m = 0, 1` (`cosh sqrt(y)` and `sinh sqrt(y)/sqrt(y)`);
the table of Section 94.1 is a rounded copy of the shipped
`data/06-growing-shifts-critical_scales.csv`.

Theorem and equation numbers refer to the shipped `article.pdf`. Part IV's
are the manuscript's shifted by 44 sections: its number `n.j` is `(n+44).j`
here (its Theorem 3.1 is Theorem 47.1), and its Appendices A and B are
Sections 59 and 60. Part V's are the manuscript's shifted by 61 sections
(its Theorem 3.1 is Theorem 64.1, its Theorem 10.1 is Theorem 71.1), its
Appendices A and B are Sections 79 and 80, and its two data tables are
Tables 5 and 6. Part VI's are the manuscript's shifted by 81 sections
(its Theorem 2.1 is Theorem 83.1, its Theorem 7.2 is Theorem 88.2), its
Appendices A and B are Sections 98 and 99, and its two figures are
Figures 1 and 2 (the report's only figures).

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
  proved there; Part IV proves the endpoint ones (batch 53), and Part V the
  ones away from the endpoints, at fixed nonendpoint bases and fixed degree
  (batch 55); limits uniform up to the endpoints remain open. Its eight
  research directions (Section 24) are tasks relative to the manuscript, not
  asserted to be globally open.
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
- **Part IV:** the fixed-size Christoffel reduction and its confluence
  (Krattenthaler; re-proved in the manuscript's normalization), the Gram
  (Andréief) integral, characteristic-polynomial determinants, integrable
  kernels and hard-edge limits from random matrix theory (Strahov–Fyodorov,
  Akemann–Fyodorov, cited for context only), and the Mehler–Heine phenomenon,
  of which the one-variable cosine and sine limits are elementary
  half-integer cases (DLMF 18.11(ii)), are credited, not presented as new.
  The proposed contribution is the combined package: the simultaneous
  two-endpoint, collision-uniform theorem, the centre `N + d/2`, the
  convergent expansion without odd powers, the first interaction operator,
  the all-orders coefficient generator, the explicit bound and the sharp
  outward criterion. The literature check was bounded; worldwide priority
  for every identity or corollary is **not** established. It does not solve
  the nonendpoint collision half of Section 24.4 *(re-scoped 29 September
  2026, batch 55: that half is proved in Part V for fixed degree and fixed
  nonendpoint bases)*, hard-edge universality for
  arbitrary weights, or limits with multiplicities growing with `N`: `m` and
  `ell` are fixed, and the constants and the analytic radius are not claimed
  uniform in them *(re-scoped 29 September 2026, batch 57: for `ell = 0` and
  one displaced root, growing `m` is treated in Part VI; question 57.4
  stays open otherwise)*. The if-and-only-if scale criterion is for **outward,
  nonnegative** displacements only; inside the interval, zeros and
  oscillation may break it. The remainder bound favours transparency over
  sharpness. Its 810 recorded checks (710 exact, 100 at 100 digits) count
  executions, not universal theorems; the high-precision checks are
  diagnostics, **not** outward-rounded interval certificates; the shipped
  program checks the leading term and first correction and is not an
  arbitrary-order coefficient engine. Its ten research directions
  (Section 57) are research directions, not assertions that every item is
  globally open.
- **Part V:** the Catalan measure and orthogonal polynomials, the
  Christoffel polynomial-modification identity, its bilinear kernel variant
  and divided-difference confluence (Krattenthaler; re-proved in the
  manuscript's normalization), orthogonal-polynomial kernel determinants and
  sine-kernel bulk limits for characteristic polynomials (Strahov–Fyodorov,
  context only), and the oscillatory Jacobi (kissing-polynomial) Hankel
  determinant with its even-degree nondegeneracy, odd-degree degeneracy and
  large-frequency analysis (Celsus–Deaño–Huybrechs–Iserles) are credited, not
  claimed; the centred exponential Vandermonde is an elementary repackaging of
  the ordinary one, and parallels Part IV's centred alternant. The claimed
  contribution is the collision-uniform convergent amplitude package: the
  first-coefficient operator, the explicit Cauchy bound, the separated-cluster
  constants, and the convergent phase-dependent zero expansion. The
  literature audit was bounded (the kissing-polynomial paper's full text could
  not be retrieved, so no theorem-by-theorem comparison with it was made);
  worldwide priority is **not** established. Not claimed: uniformity as a base
  approaches an endpoint or another base; growing degree, unbounded or
  `N`-dependent scaled coordinates, or zero indices growing with `N`; nonsimple
  zeros or a classification of all recurrence resonances; any
  constant-coefficient recurrence for a moving multiplier `q_N`; validation of
  every theorem or file of the repository. The pair law and zero transport are
  stated in centred coordinates; the translation to Section 57.1's
  coordinates (Remark 61.1) is the merge's. The 518 recorded assertions
  (392 exact, 126 at 100 digits) are finite audits; the CSV experiments are
  not certificates, and numerical root decimals are not certified isolating
  intervals; no interval arithmetic and no proof assistant is used. Its nine
  research directions (Section 77) are proposed continuations, not claims
  that every formulation is open in the published literature.
- **Part VI:** the Catalan moment measure, the one-factor Christoffel
  identity (Krattenthaler; re-derived in the manuscript's normalization), the
  finite Jacobi hypergeometric representation (DLMF 18.5.7), Part I's
  coefficient formula (credited, (84.5)), the fixed-`m` `0F1` limit (a
  standard special-function phenomenon), large-parameter Jacobi-zero
  asymptotics (Dette–Studden, context only), the Barbour–Hall Bernoulli-sum
  Poisson bound (the only Poisson estimate used) and mod-Poisson and
  higher-order Chen–Stein approximation (Méliot–Nikeghbali–Visentin, context
  only) are credited, not claimed. The claimed contribution relative to the
  inspected reports is the integrated calculation: the exact normalization
  and index `beta`, the uniform inverse-zero bound, the size-biased Catalan
  law in every growth regime, the all-orders hierarchy, the distinct
  determinant and nominal-Poisson thresholds, and the algebraic resummation
  with a proportional-growth prefactor. Equivalent formulations may exist in
  the orthogonal-polynomial literature; first-discovery priority is **not**
  established (the Krattenthaler and Dette–Studden PDFs could not be
  fetched; only their abstracts were read). Not claimed: several moving
  factors or arbitrary growing-degree multipliers; both endpoint exponents
  growing; negative perturbations (the positive-axis statements need not
  survive across zeros); an extreme-zero theorem (`W/beta -> 1 + 3 theta` is
  left open) or convergence of the largest atom or of individual zeros;
  uniformity in the hierarchy order `q`, or replacing the lower `S_r` by
  their limits without a rate; replacing the exact mean by `Q_theta/beta` in
  the nonlinear central limit theorem; a saddle prefactor uniform as `m/N`
  or `t` approaches 0 or infinity; failure of **every** Poisson
  approximation at `beta^(-2/3)` (only the nominal one fails there);
  exhaustive inspection of the repository. The recorded checks (270 direct
  determinants, 420 moment parameter pairs comprising 5,040 moment
  equalities, 5,040 majorant inequalities on the same pairs, 60
  limiting-recurrence checks, 16 floating-point Jacobi-root parameter pairs)
  are finite audits, not to be summed as independent samples; the four CSV
  tables are floating-point diagnostics, not outward-rounded certificates,
  and the program is not the certified algorithm of question 96.9. Its ten
  research directions (Section 96) are proposals, including a staged Lean
  formalization (96.10) that has not been started.
- The theorems are over characteristic zero and are not to be transported
  unchanged to small positive characteristic. For arbitrary complex inputs
  "algorithm" presupposes exact field operations and equality tests; the
  cost estimate `O(R^4)` counts arithmetic operations, not bits.
- Of the extensions Part I's Section 11 named, Part II addresses only the
  multiple-factor one. A combinatorial interpretation of `c_(N,m,k)`, a
  product formula for the minors `M_(m,ell)(N)`, and joint limits with
  growing `m` remain open, except for the one-factor family with real
  `a/b >= 0`, which Part VI treats at every relative growth (batch 57;
  Corollary 84.2 and Theorems 83.1, 88.2, 90.1, 92.1) (`a -> 0` at fixed
  `m` is answered in Part IV: for real `a/b >= 0` the ratio
  `D_N^(m)(a,b)/D_N^(m)(0,b)` tends to 1 exactly when `a/b = o(N^-2)`,
  Theorem 47.4 and Section 44.4; dated pointers in Sections 8 and 11).
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
Part II's research subsections 24.1 and 24.2). Total after batch 42: 343
(220 before it). No label was renamed or removed, and no number of Parts I–II
moved (compared in the `.aux` files of a build of the committed text and the
new build; their page numbers moved: by one page in Parts I and II, because
the contents grew, and Part I's appendices past Part III).

Part IV added **92** labels, all with the prefix `tec:` ("two-endpoint
confluence"; `rg -c "tec:" article.tex` was 0 before): the manuscript's 66
labels, prefixed, and 26 new ones (the seven of Section 44, the manuscript's
sixteen sections, its first research subsection `tec:x:q1`, and
`tec:x:rcq4`, `tec:x:cycendpoint` on Part II's Section 24.4 and Part III's
Section 40.2). Total: **435** (343 before batch 53). No label was renamed or
removed, and no number of Parts I–III moved (all 343 earlier labels compared
in the `.aux` files of a build of the committed text and the new build;
every page number moved, by one page in Parts I–III because the contents
grew by a page, and Part I's appendices past Part IV). Parts II, III and IV
start at Sections 12, 28 and 44; Part I's appendices come after Part IV and
keep their letters. The notation tables are Table 1 (Part II), Table 2
(Part III), Table 3 (Part IV) and Table 4 (Part V); Part I has no numbered
tables, and Part V's two data tables are Tables 5 and 6.

Part V added **135** labels, all with the prefix `ic:` ("interior
collisions"; `rg -c "ic:" article.tex` was 0 before): the manuscript's 117
labels, prefixed (six of them, `thm:main`, `sec:main`, `sec:examples`,
`eq:measure`, `eq:R`, `eq:Jacobi`, would otherwise have collided with
Part I's bare labels), and 18 new ones (the eight of Section 61, the
manuscript's four unlabelled sections — its Section 2, its conclusion and its
two appendices — three of its research subsections, `ic:x:bridge`,
`ic:x:mixed`, `ic:x:jacobi`, and `ic:x:rcq5`, `ic:x:cycuniform`, `ic:x:tecq2`
on Part II's Section 24.5, Part III's Section 40.4 and Part IV's
Section 57.2). Total: **570** (435 before batch 55). No label was renamed or
removed, and no number of Parts I–IV moved (all 435 earlier labels compared
in the `.aux` files of a build of the committed text and the new build; every
page number moved, by one page in Part I and the first pages of Part II and
by two pages after that, because the contents grew by a page and Part II's
two dated notes by another, and Part I's appendices past Part V).

Part VI added **131** labels, all with the prefix `gs:` ("growing shifts";
`rg -c "gs:" article.tex` was 0 before): the manuscript's 105 labels,
prefixed (two of them, `eq:measure` and `eq:h`, would otherwise have
collided with Part I's bare labels), and 26 new ones (the seven of
Section 81 — the section, its five subsections and Table 7 — the
manuscript's conclusion and two appendices, its second figure, four of its
subsections (82.1, 93.1, 93.2, 94.1), its ten research subsections
`gs:x:edge` … `gs:x:formal`, and `gs:x:tecq4` on Part IV's Section 57.4).
Total: **701** (570 before batch 57). No label was renamed or removed, and no
number of Parts I–V moved (all 570 earlier labels compared in the `.aux`
files of a build of the committed text and the new build); every page
number moved, by two or three pages in Parts I–V (the contents grew by two
pages, and the dated notes of Sections 8 and 11 by part of a page), and
Part I's appendices past Part VI. Part VI's notation table is Table 7, and
its figures are the report's Figures 1 and 2.

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

Part IV keeps its manuscript's symbols, with nothing renamed and no
normalization changed; Table 3 (Section 44.3) lists them. Watch in
particular for:

- `t` is the variable of the kernels `C(t,y) = cos(t sqrt y)`,
  `S(t,y) = sin(t sqrt y)/sqrt y`, `K^-`, `K^+` in Sections 46–53, but the
  **multiplicity** of one repeated root in (45.2) and Section 54, as in
  Part II's question; `C(t,y)` is not a Catalan number `C_n`.
- The kernel derivative columns (46.8)–(46.9) are **not** divided by
  factorials, whereas repeated-root rows are (Section 59).
- `d = m + ell` is the degree of the multiplier (Part II's `D`), not Part I's
  `d = binom(m,2)`; `kappa` agrees with Part II's (14.5); `rho = binom(m,2) +
  binom(ell,2)`, not Part II's modulus bound or Part III's ratio; `nu` is the
  centred size (Part II's `nu_u` are block multiplicities); `h = 1/nu`
  (Part III's `h = t - k`).
- `M_N = N^2 * max displacement` and `R_N` is a ratio of determinants, not
  Part II's Christoffel matrix `M_N` or Part III's order `R(t,c)`; `mathcal R`
  is the hyperbolic generator (Part IV has no `mathcal R_0`, Part II's
  maximal order).
- `a, b` are local (binomial exponents in Corollary 47.3, limits of scaled
  displacements in Theorem 47.4), except in Section 44.4 and the dated note
  in Section 11, where they are Part I's parameters; `eta_(j,N)` is a
  displacement (Part III's `eta` is a parity indicator); `lambda` is a
  partition and `s_lambda` a Schur polynomial (Part II's `lambda_k` are rates).

Part V keeps its manuscript's symbols, with no normalization changed; Table 4
(Section 61.3) lists them. One function was renamed: the manuscript's
`shc z = sinh z / z` is printed `sinhc`, Part IV's name for the same function;
its upright `Re` is printed `ℜ` (`\Re`). Watch in particular for:

- `D = binom(d,2)` is **not** Part II's `D = deg q`, which is Part V's `d`
  (as in Part IV); `e_k = binom(k,2) + binom(d-k,2)`.
- `w` is the spectral coordinate of the base, `c = 2 + 2 cosh w`, `z = e^w`
  (Part II's and Part III's `z`), **not** Part III's centred size
  `w = N + t/2`; `theta` with `w = i theta` is the base angle inside `(0, 4)`.
- `nu = N + d/2` is Part IV's formula, but Part V's expansions are in `1/nu`,
  **not** `1/nu^2`; for a symmetric pair (`d = 2t`) it is `nu = N + t`.
- `t` is the multiplicity of each root of a pair from Section 71 on (as in
  Part III), but a formal branch-counting variable in (65.3) and in the proof
  of Theorem 68.1 (`t_a`), and Part IV's kernel variable elsewhere in the
  report; `(i tau)^t` in a tuple means `t` repeated entries, not a power.
- `tau` is a trigonometric collision coordinate, `2 + 2 cos(theta +- tau/nu)`;
  Section 57.1's hyperbolic `z e^(+-tau/N)` is Part V's `tau` times `-i`
  (Remark 61.1).
- `Z_N` (73.1) is normalized by `A_t(theta) nu^(t^2)`, not like Part IV's
  `Z_N` (46.7); `S_(d,k)` is a profile (Part IV's `S(t,y)` is a sine
  function); `B_(d,k)(w)` a base constant (Part III's `B_(a,b)(N)` is a
  product); `L(h; u, w)` and `L_j` are two different objects within Part V
  (Part III's `L = ord(z^2)` a third); `m` is half the degree in Sections 69
  and 72 (Parts I, II, IV use `m` otherwise); `s` is the number of clusters
  and `s_t` a constant.

Part VI keeps its manuscript's symbols, with no normalization changed; its
determinants are Part I's `D_N^(m)(a,b)` and `H_N^(m)`, at `b = 1` except in
Section 93.2. Table 7 (Section 81.3) lists the symbols. Two macros were
renamed in the source only (`\R` → `\Rgs` for calligraphic `R`, `\E` →
`\Egs` for blackboard `E`); they print as in the manuscript. Watch in
particular for:

- `beta` is the concentration index `(1 + c (v + 3/2))/(v + 1) = S_2`, not a
  Jacobi exponent (those are `m - 1/2` and `1/2` here) nor Part I's
  `beta_j^+-`; `c = v/(N B)`, not Part I's `c_(N,m,k)` nor the base `c` of
  Parts II, III and V; `mu = N B/(4 v)` is a scalar, not a measure.
- `nu_(N,m)` and `nu_theta` are probability measures, **not** Part IV's and
  Part V's centred size `nu`; `d_r(theta)` are limiting moments (Part I's
  `d = binom(m,2)`); `Phi` is the standard normal distribution function
  (Part V's `Phi_t` are profiles), and `N(0,1)` a normal law.
- `t` is `beta tau` in Sections 83 and 90 but `tau/N` in Section 92, and `b`
  is Part I's parameter in Section 93.2 but `(N + m + 1)/N` in Section 92;
  both clashes are inside the manuscript. In Section 92, `r = (m + 1/2)/N`
  (elsewhere `r` indexes moments), `q` is the saddle point (Part I's `q(t)`,
  Part II's multiplier `q`), `ell` an auxiliary (not the multiplicity of the
  root 4), `h(x) = -f''(x)` (Part I's `h_m`, Parts IV–V's `h = 1/nu`).
- `p_j` are Bernoulli parameters, while `p_N^(m)` is the monic orthogonal
  polynomial (Part I's); `K_tau` is the coefficient distribution (Part I's
  `K = (m-1)^2`, Part IV's kernels `K^+-`); `L = R'/R` (Part III's
  `L = ord(z^2)`); `A_(N,m)(k)` is a normalized coefficient (Part IV's `A_j`,
  Part V's `A_t(theta)`); `w_j` are weights (Part V's spectral base `w`);
  `omega` is Part I's measure `mu_0`.

## Files

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 161 pages (title page; contents pp. 2–9;
                                                     Part I pp. 10–25; Part II pp. 26–52; Part III pp. 53–79;
                                                     Part IV pp. 80–103; Part V pp. 104–132; Part VI pp. 133–157;
                                                     Part I's appendices pp. 158–159; references pp. 160–161)
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
04-endpoint-confluence-SOURCES.md                    Part IV: pinned source, literature consulted, contribution
                                                     boundary (delivered as SOURCES.md)
04-endpoint-confluence-PROOF_AUDIT.md                Part IV: dependency chain, delicate conventions, trust
                                                     boundary (delivered as PROOF_AUDIT.md)
code/04-endpoint-confluence-verify.py                Part IV: exact (Fraction) and 100-digit (mpmath) checks
                                                     (delivered as code/verify.py)
data/04-endpoint-confluence-verification.json        Part IV: recorded outcome, 810 checks, per-case numerical rows
data/04-endpoint-confluence-verification.txt         Part IV: the same counts as text
data/04-endpoint-confluence-requirements.txt         Part IV: mpmath==1.3.0 (delivered as requirements.txt)
05-interior-collision-SOURCES.md                     Part V: pinned README, library manuscripts read, literature
                                                     audit and contribution boundary (delivered as SOURCES.md)
05-interior-collision-PROOF_STATUS.md                Part V: proved statements, classical ingredients, computational
                                                     audit, not claimed (delivered as PROOF_STATUS.md)
code/05-interior-collision-verify.py                 Part V: exact (Fraction) and 100-digit (mpmath) checks and the
                                                     CSV experiments (delivered as code/verify.py)
code/05-interior-collision-Makefile                  Part V: the delivered root Makefile (pdf, verify, clean);
                                                     do not run it from this directory
data/05-interior-collision-verification.json         Part V: recorded run, 518 assertions in twelve counts,
                                                     maximal discrepancies, multi-cluster metrics
data/05-interior-collision-finite_size_corrections.csv  Part V: leading and first-corrected errors of Theorem 71.1,
                                                     t = 1..3, N = 40..320 (CRLF)
data/05-interior-collision-zero_transport.csv        Part V: profile zeros, finite-N zeros and predicted shifts,
                                                     t = 1, 3, N = 40..320 (CRLF)
data/05-interior-collision-jacobi_parity_audit.csv   Part V: large-frequency profile residuals, t = 1..5 (CRLF)
data/05-interior-collision-multiple_clusters.csv     Part V: two-cluster leading-term experiment, N = 40..320 (CRLF)
data/05-interior-collision-requirements.txt          Part V: mpmath==1.3.0 (delivered as requirements.txt)
06-growing-shifts-SOURCES.md                         Part VI: pinned repository and blobs, literature consulted and
                                                     its limits (delivered as SOURCES.md)
06-growing-shifts-PROOF_AUDIT.md                     Part VI: definitions, delicate proof steps, finite audit, what is
                                                     not established (delivered as PROOF_AUDIT.md)
06-growing-shifts-BUILD_CHECK.md                     Part VI: build and layout checks of the delivered 21-page PDF
                                                     (delivered as BUILD_CHECK.md; not about this report's PDF)
code/06-growing-shifts-verify.py                     Part VI: exact (Fraction) audit and NumPy/SciPy diagnostics
                                                     (delivered as code/verify.py)
code/06-growing-shifts-make_figures.py               Part VI: figure script (delivered as code/make_figures.py;
                                                     imports verify, so it runs only under the delivered names)
code/06-growing-shifts-Makefile                      Part VI: the delivered root Makefile (all, audit, figures, pdf,
                                                     clean); do not run it from this directory
data/06-growing-shifts-verification_summary.json     Part VI: recorded run, five exact and five numerical counts,
                                                     versions, status
data/06-growing-shifts-critical_scales.csv           Part VI: the two transition profiles, N = m = 64..16384 (CRLF)
data/06-growing-shifts-spectral_moments.csv          Part VI: moment ratios S_k/beta^(k-1) against d_k(theta),
                                                     k = 2..6, five (N, m) pairs (CRLF)
data/06-growing-shifts-free_energy.csv               Part VI: beta log R(t/beta) against F_theta(t), four (N, m)
                                                     pairs, t = 0.25, 1, 4 (CRLF)
data/06-growing-shifts-saddle_prefactor.csv          Part VI: relative saddle error and N times it, N = 32..2048,
                                                     m/N = 1/4, 1, 4, t = 0.2, 1, 3 (CRLF)
data/06-growing-shifts-requirements.txt              Part VI: numpy>=1.24, scipy>=1.10, matplotlib>=3.7 (unpinned;
                                                     delivered as requirements.txt)
figures/06-growing-shifts-determinant_crossover.pdf  Part VI: Figure 1 (regenerated for this merge; see below)
figures/06-growing-shifts-free_energy.pdf            Part VI: Figure 2 (regenerated for this merge; see below)
```

The eleven `02-root-collisions-` files were staged in the placement commit
`e2b1f016a`, the seven `03-cyclotomic-` files in `3609d0473`, the six
`04-endpoint-confluence-` files in `1dc874990`, and the ten
`05-interior-collision-` files in `26473dfa0`, and the twelve
`06-growing-shifts-` files outside `figures/` in `70b39943a`, all
byte-identical to the deliveries (Part IV's are LF, with no CR byte; of
Part V's and Part VI's, only the four CSVs of each contain CR bytes). The ten
CSVs of Parts II, III, V and VI are all-CRLF as delivered (written by
Python's `csv` module) and are protected by `-text` lines in
`SetTheory/Cardinals/.gitattributes`; never re-save them.

The two figure PDFs were added in the batch-57 write, and they are **not**
the delivered bytes. The delivered figures embedded DejaVu Sans as Type 3
fonts (no other font of this report is Type 3); these were regenerated by the
delivered `code/make_figures.py`, unchanged, on a copy of the delivery with
Matplotlib 3.10.8 (the version recorded in the delivered figures), NumPy
2.3.5, SciPy 1.17.0 and a local `matplotlibrc` containing
`pdf.fonttype: 42`, so they embed a TrueType (CID) subset of DejaVu Sans.
They plot the same curves (compared visually at 50 dpi); the delivered ones
survive in the arrival commit `6ad01e9c8`.

Data conventions (Parts I–III): polynomial arrays are in ascending powers;
rational values are exact strings such as `"8/3"` or `"8/81"`, never rounded
decimals. Part IV's JSON is different: its numbers are 25-digit decimal
strings of 100-digit diagnostics (see the Part IV bullet below), and Part V's
CSV values are binary floating-point decimals except the zero columns (see
the Part V bullet), as are all of Part VI's CSV values (see the Part VI
bullet).

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
- Part IV: `verification.json` holds `precision_decimal_digits` (100), the
  ten `counts` (710 exact, 100 high-precision), `total` 810, `all_passed`,
  a `qualification` (not interval certificates), and ten numerical `cases`
  (`left-one`, `right-one`, `one-at-each`, `left-double`, `right-double`,
  `both-double`, `endpoint-double`, `three-plus-two`, `inside-collisions`,
  `complex-distinct`). Each case lists its coordinates `left` (the `y_i`,
  near 0) and `right` (the `v_j`, near 4) as strings, negative real meaning
  outward, and rows at `N = 16, 32, 64, 128` with `Z`, `A0`, `A1`, the
  leading and corrected errors and their ratios to `h^2` and `h^4`,
  `h = 1/(N + d/2)`, as decimal strings rounded to about 25 digits; they are
  diagnostics, not certificates. The `both-double` rows are the table of
  Section 55.5. The exact checks record only their counts.
- Part V: `verification.json` holds `python` (3.13.5), `mpmath` (1.3.0),
  `precision_decimal_digits` (100), a `status` (not a proof-assistant or
  interval certificate), twelve `assertion_counts` (392 exact: 63 + 7 + 35 +
  35 + 252; 126 numerical: 35 + 25 + 30 + 14 + 4 + 12 + 6), `total_assertions`
  518, six `maximum_relative_discrepancies` as strings (the
  `first_correction_numeric` value, about `6.6e-13`, reflects a deliberate
  centred finite difference with step `1e-6`), `metrics` (the two-cluster rows
  of `multiple_clusters.csv` and a second-order amplitude residual) and
  `elapsed_seconds`. The CSV files are the experiments of Section 75, **not**
  among the 518 assertions: `finite_size_corrections.csv` (columns `t, N`,
  leading and corrected absolute errors, `nu^2` times the corrected error) at
  `theta = 1.1`, `tau = 0.8`, whose rows `N = 40, 160, 320` are Table 5;
  `zero_transport.csv` (`t, N`, `profile_zero`, `finite_N_zero`,
  `predicted_shift` as 25- and 18-digit strings, `scaled_shift_error`) at
  `theta = 1.1`, whose rows `N = 40, 160, 320` are Table 6 (the profile zero
  of `t = 3` is numerical, not a certified isolating interval);
  `jacobi_parity_audit.csv` (`t, s, scaled_residual`) for `t = 1..5` at
  frequencies `s = 12.3, 24.3, 48.3`, the bracket error of Proposition 72.2
  times `s^2`; `multiple_clusters.csv` (`N`, absolute error, `nu` times it)
  for two clusters of size 2 at `w = 0.8i` and `1.7i`, central sectors
  `k = (1, 1)`.
- Part VI: `verification_summary.json` holds five `exact` counts
  (`direct_determinants` 270, `moment_parameter_pairs` 420,
  `individual_moment_equalities` 5040, `moment_majorants` 5040,
  `limiting_recurrence_cases` 60), five `numerical` counts (the row numbers of
  the four CSVs, 5, 25, 12 and 36, and `root_parameter_pairs` 16), the
  `versions` (Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0) and a `status`. The
  CSVs are diagnostics: `critical_scales.csv` (`n, m, beta, det_ratio,
  det_limit, tau_poisson, tv, tv_limit, mean_shift, variance_ratio`) for
  `N = m = 64, …, 16384`, whose columns `beta`, `det_ratio` and `tv` are the
  table of Section 94.1 (there rounded); `spectral_moments.csv` (`n, m, k,
  theta, moment, limit_profile, difference`), the ratio `S_k/beta^(k-1)`
  against `d_k(theta_(N,m))`; `free_energy.csv` (`n, m, t, theta,
  scaled_logR, free_energy, difference`); `saddle_prefactor.csv` (`n, m, t,
  q, relative_error, n_times_error`), where `m = int(n * ratio)`.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex` until the cross-references stabilize (packages: `newtx`,
`mathtools`, `amsthm`, `microtype`, `geometry`, `hyperref`, `titlesec`,
`fancyhdr`, `listings`, `longtable`, `enumitem`, and, since batch 57,
`graphicx`). Build in a scratch copy of `article.tex`, with the `figures/`
directory beside it, so that no auxiliary files land here (Part I's `make pdf` builds
in place). The shipped PDF was built with MiKTeX (pdfTeX) with no errors, no
undefined or multiply defined references, no duplicate destinations and no
overfull or underfull boxes; a build of the committed text before each
addition was equally clean. No font files are included. The Part III
manuscript's own build used `tocloft` and `xurl` as well, and the Part IV
manuscript's `tcolorbox`, and the Part V manuscript's `tcolorbox`, `tocloft`
and `xurl`; the merged article needs none of them. The batch-55 build
(133 pages) has no errors, undefined or multiply defined references,
duplicate destinations, or overfull or underfull boxes; its only
informational messages ("Infinite glue shrinkage found in box being split",
ignored) come from the four `longtable` notation tables, three of which gave
the same message in the build of the committed text. Part V sets
`\emergencystretch` to the manuscript's 3em (reset to the report's 2em
after it) and prints one file name of Section 79 with `\nolinkurl` instead of
`\texttt`, so that it can break; the text is unchanged. The batch-57 build
(161 pages) is equally clean: no errors, undefined or multiply defined
references, duplicate destinations, or overfull or underfull boxes; the
informational "Infinite glue shrinkage" message now comes from five
`longtable` notation tables (four in the build of the committed text). The
Part VI manuscript's own build also used `graphicx` and `xcolor` (both
loaded here now) and its own `hyperref` options; the figures are its only
external inputs. The PDF embeds the two figures' TrueType subsets of DejaVu
Sans and no Type 3 font.

## Rerun the checks

The Part I–III suites are standard-library Python 3.10+ with exact integers
and rationals; Parts IV and V also need `mpmath` (tested with 1.3.0) for
their 100-digit checks, and Part VI needs NumPy and SciPy (and Matplotlib
for its figures). All six **write data files**: run in place, the programs of
Parts I, II and IV, and Part V's without `--out`, would overwrite recorded
files, and Part III's and Part VI's would add unprefixed ones. Run them only on a
copy; on Windows they also write CRLF line endings. Commands are for
Git Bash or another POSIX shell, from this directory (`py` may replace
`python3`).

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

**Part IV.** Run in place, `code/04-endpoint-confluence-verify.py`
**rewrites Part I's `data/verification.json` and `data/verification.txt`**:
it has no output option and takes no arguments, and it always writes
`verification.json` and `verification.txt` into the `data/` directory next
to its own parent directory (`Path(__file__).resolve().parents[1]/'data'`),
whatever the working directory. It also writes CRLF on Windows (`write_text`
without `newline`), whereas the recorded files are LF. (The delivery
README's `python -m pip install -r requirements.txt` and
`python code/verify.py` assume the delivered layout and a bare `python`; the
dependency file is shipped as `data/04-endpoint-confluence-requirements.txt`.)
Restore the delivered layout in a scratch copy instead:

```sh
W=/path/to/scratch/endpoint-confluence
mkdir -p "$W/code" "$W/recorded"
cp code/04-endpoint-confluence-verify.py "$W/code/verify.py"
for f in data/04-endpoint-confluence-verification.*; do cp "$f" "$W/recorded/${f#data/04-endpoint-confluence-}"; done
cd "$W" && python3 code/verify.py    # writes $W/data; compare with $W/recorded
```

with `mpmath` installed (`python3 -m pip install mpmath==1.3.0`, or
`uv run --no-project --with mpmath==1.3.0 python code/verify.py`). Run this
way on 29 September 2026 (Python 3.13.5, mpmath 1.3.0, about 2 s) it printed
`TOTAL: 810`, with the ten counts of the recorded run, and both outputs
equalled the recorded ones apart from Windows line endings. The checks are
`assert` statements, so do not pass `-O`. The two determinant paths
(original moment matrix and confluent Christoffel determinant) share the
scalar Gaussian elimination; the coefficient-minor checks are independent of
the first-correction kernel formula.

**Part V.** Its files still use the delivered names. Run from this directory,
`code/05-interior-collision-verify.py` with no arguments uses its default
`--out data` (relative to the working directory) and **overwrites Part I's
`data/verification.json`**, and adds four unprefixed CSVs to `data/`. The
delivered Makefile (`code/05-interior-collision-Makefile`), run from this
directory, is worse: `verify` runs `python code/verify.py --out data`, which
here is **Part I's** verifier and rewrites Part I's `data/`; `pdf` runs
`pdflatex` three times on the merged `article.tex` in place; `clean` deletes
`article.aux`, `.log`, `.out`, `.toc`, `.fls` and `.fdb_latexmk` here. Never
run it here. (The delivery README's `python -m pip install -r
requirements.txt` and `python code/verify.py --out data` assume the delivered
layout and a bare `python`; the dependency file is shipped as
`data/05-interior-collision-requirements.txt`.) Restore the delivered layout
in a scratch copy instead:

```sh
W=/path/to/scratch/interior-collision
mkdir -p "$W/code" "$W/recorded"
cp code/05-interior-collision-verify.py "$W/code/verify.py"
for f in data/05-interior-collision-*; do cp "$f" "$W/recorded/${f#data/05-interior-collision-}"; done
cd "$W" && uv run --no-project --with mpmath==1.3.0 python code/verify.py --out data   # compare $W/data with $W/recorded
```

(or `python3 -m pip install mpmath==1.3.0` and `python3 code/verify.py --out
data`). The program has no local imports, so it may also be run in place
with an explicit scratch output directory,
`uv run --no-project --with mpmath==1.3.0 python code/05-interior-collision-verify.py --out "$W/data"`,
but **never without `--out`**. Run the first way on 29 September 2026
(Python 3.13.5, mpmath 1.3.0, about 4 s) it passed all 518 assertions; the
four CSVs were byte-identical to the recorded ones (CRLF on every system,
because `csv` ends rows with CRLF and the files are opened with
`newline=''`), and `verification.json` equalled the recorded file apart from
`elapsed_seconds` (and CRLF line endings on Windows, from `write_text`;
compare after `tr -d '\r'`). The field `python` also varies with the
interpreter. The checks raise `AssertionError` explicitly, so `-O` does not
disable them. The exact and numerical determinant paths share one Gaussian
elimination routine; the moment-matrix and Christoffel constructions differ.

**Part VI.** Its files still use the delivered names. Run from this
directory, `code/06-growing-shifts-verify.py` defaults to `--output data`
(relative to the working directory) and would add five unprefixed files to
the report's shared `data/` (`verification_summary.json` and the four CSVs;
no shipped file has those names). `code/06-growing-shifts-make_figures.py`
does `from verify import …`, so run in place it would find **Part I's**
`code/verify.py` and fail; it writes unprefixed figure files into the
`figures/` directory beside its own `code/` directory. The delivered Makefile
(`code/06-growing-shifts-Makefile`), run from this directory, is worse:
`audit` runs `python code/verify.py --output data`, which here is **Part I's**
verifier (it rejects `--output`); `pdf` runs `pdflatex` three times on the
merged `article.tex` in place; `clean` deletes `article.aux`, `.log`, `.out`,
`.toc`, `.fls` and `.fdb_latexmk` here. Never run it here. (The delivery
README's `python -m pip install -r requirements.txt`, `python code/verify.py
--output data` and `python code/make_figures.py` assume the delivered layout
and a bare `python`; the dependency file is shipped as
`data/06-growing-shifts-requirements.txt`.) Restore the delivered layout in a
scratch copy instead:

```sh
W=/path/to/scratch/growing-shifts
mkdir -p "$W/code" "$W/recorded" "$W/out"
for f in verify make_figures; do cp "code/06-growing-shifts-$f.py" "$W/code/$f.py"; done
for f in data/06-growing-shifts-*; do cp "$f" "$W/recorded/${f#data/06-growing-shifts-}"; done
cd "$W" && uv run --no-project --with numpy==2.3.5 --with scipy==1.17.0 python code/verify.py --output out
printf 'pdf.fonttype: 42\n' > matplotlibrc    # TrueType, not Type 3, fonts in the figures
uv run --no-project --with matplotlib==3.10.8 --with numpy==2.3.5 --with scipy==1.17.0 python code/make_figures.py   # writes $W/figures
```

Run this way on 29 September 2026 (Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0,
a few seconds) it passed every assertion and recorded the counts of the
shipped summary; `free_energy.csv` was byte-identical to the recorded file,
the other three CSVs differed only in the last digits of floating-point
entries (largest difference `9.3e-10`, in the cancellation-limited
`n_times_error` of `saddle_prefactor.csv` at `N = 2048`, `m = 8192`,
`t = 1`), and `verification_summary.json` was identical after `tr -d '\r'`.
The CSV writer (`csv` with `newline=''`) ends rows with CRLF on every
system, which is why the delivered CSVs are CRLF; the JSON is written with
`write_text` and has CRLF line endings on Windows only. The figure step
reproduced the two shipped figures apart from the creation date in their
metadata; without the `matplotlibrc` line, Matplotlib writes Type 3 fonts
again. The exact audit uses Python's `Fraction`; the numerical layer is
floating point, and its assertions are `assert` statements, so do not pass
`-O`.

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
- **Part IV delivery names.** `code/04-endpoint-confluence-verify.py` says in
  its docstring that it checks "the accompanying article" (now Part IV of this
  `article.tex`) and "Run from any working directory; outputs go to ../data";
  it writes unprefixed `data/verification.json` and `data/verification.txt`,
  which here are Part I's files (see the rerun paragraph). The recorded
  `data/04-endpoint-confluence-verification.json` and `.txt` name no files
  (the `.txt` ends "distinguished in verification.json", its delivered name).
  `04-endpoint-confluence-SOURCES.md` and `04-endpoint-confluence-PROOF_AUDIT.md`
  were delivered as `SOURCES.md` and `PROOF_AUDIT.md`; their "this article" and
  "the article" are the manuscript (Part IV), and "the source" is Parts I–III
  at the pin. Their section references (Part II's Sections 22 and 24.4, and
  Part III) are correct in this report; the manuscript's own theorem and
  section numbers, which the unshipped PDF uses, are shifted by 44 here (its
  `n.j` is `(n+44).j`; Appendices A, B are Sections 59, 60).
  `data/04-endpoint-confluence-requirements.txt` was delivered at the package
  root as `requirements.txt`. The article (Sections 45, 56 and 60) gives the
  shipped names beside the delivered ones in merge notes, and prints the
  delivered reproduction command with the warning and the scratch-copy recipe.
- **Part IV unshipped files.** The manuscript's `article.tex`, its 20-page A4
  `article.pdf` and its delivery README are not shipped (they survive in
  `148a906aa`). The delivery README's content — result summary, status,
  rerun and build commands, file list — is covered by Section 44 and this
  README; its rerun commands (bare `python`, and "It rewrites
  `data/verification.json` and `data/verification.txt`") are superseded by
  the Part IV rerun paragraph above.
- **Part IV overlap.** Part IV re-derives, without assuming Parts I–III, the
  Catalan measure, the monic orthogonal polynomials and their trigonometric
  form (a fourth route), the Gram integral and the Christoffel identity
  (Lemma 48.1 is Part II's Lemma 15.1 for `gamma = 1`), and the endpoint jets
  (56.1) = Part II's Lemma 16.2, (16.9)–(16.10); its endpoint value (47.5) is Part II's
  leading coefficient (18.8) for `q = x^m (x-4)^ell`. All are marked in
  Section 44.5; no statement of Parts I–III was changed. The consistency
  checks of Section 44.4 are the merge's own and are labelled so.
- **Part IV bibliography.** Its Krattenthaler item (arXiv:2101.04225v5, "Theorem
  1 and the confluent discussion in Section 5") is Part I's [3]; Strahov–Fyodorov,
  Akemann–Fyodorov and DLMF §18.11(ii) are added as [10], [11], [12] (the last
  separate from Part I's DLMF item [4], §18.5); its item for the pinned
  repository report is replaced by Parts I–III and the pin in Section 44.1.
- **Part V delivery names.** `code/05-interior-collision-verify.py` says in
  its docstring "Run: python code/verify.py --out data" and writes unprefixed
  `verification.json`, `finite_size_corrections.csv`, `zero_transport.csv`,
  `jacobi_parity_audit.csv` and `multiple_clusters.csv` into its `--out`
  directory (default `data`, relative to the working directory; see the rerun
  paragraph). `code/05-interior-collision-Makefile` was delivered at the
  package root; it names `article.tex` and `code/verify.py`, both of which are
  other files here, and a bare `python`. The placement commit shipped it,
  although it must not be run here; it is kept byte-identical as delivered.
  `05-interior-collision-SOURCES.md` and `05-interior-collision-PROOF_STATUS.md`
  were delivered as `SOURCES.md` and `PROOF_STATUS.md`; their "the present
  manuscript", "the article" and "the supplied article" are the manuscript
  (Part V), their "repository" is Parts I–III at the pin, and their theorem
  and section numbers are the manuscript's, shifted by 61 here (its `n.j` is
  `(n+61).j`; its Appendix A is Section 79). `SOURCES.md` calls Part II's
  question "Section 24.4 in the combined repository report" (correct here) and
  Part IV's question the standalone manuscript's "Section 13.1" (Section 57.1
  here); it names the library files `article(20260929-023936).tex`,
  `article(20260930-010250).tex` and `article(20260930-010248).pdf`, which are
  the standalone Part II and Part IV sources in Vladimir's file library, not
  shipped here (their content is Parts II and IV). `PROOF_STATUS.md` says
  "The numbering above matches the supplied article"; in this report it
  matches after the shift. `data/05-interior-collision-requirements.txt` was
  delivered at the package root as `requirements.txt`. The article
  (Sections 62, 75 and 79) gives the shipped names beside the delivered ones
  in merge notes, and prints the delivered reproduction commands with the
  warning and the scratch-copy recipe.
- **Part V unshipped files.** The manuscript's `article.tex`, its 24-page A4
  `article.pdf`, its delivery README and its `SHA256SUMS.txt` are not shipped
  (they survive in `2d4919838`; the checksum list, which named the delivered
  paths, was verified 13/13 at placement and retired). The delivery README's
  content — result summary, file list, reproduction and build commands,
  status and attribution — is covered by Section 61 and this README; its
  commands (bare `python`, `python code/verify.py --out data`, `make pdf`,
  `make verify`, `make clean`, and "regenerate SHA256SUMS") are superseded by
  the Part V rerun paragraph above.
- **Part V overlap.** Part V re-derives, without assuming Parts I–IV, the
  Catalan measure, the monic orthonormal polynomials and their trigonometric
  form (63.3) (a fifth route), the Gram (Andréief) integral and the
  Christoffel identity (Lemma 63.1 is Part II's Lemma 15.1 for `gamma = 1`
  and Part IV's Lemma 48.1); its centred exponents are Part IV's (Lemma 49.1),
  uncited by the manuscript; and its centre law at `theta = pi/2` agrees with
  Part III's central product. All are marked in Section 61.4; no statement of
  Parts I–IV was changed. The consistency checks and Remark 61.1 are the
  merge's own and are labelled so.
- **Part V bibliography.** Its Krattenthaler item (Ramanujan J. 61 (2023),
  with arXiv:2101.04225v5) is Part I's [3], and its Strahov–Fyodorov item is
  Part IV's [10]; Celsus–Deaño–Huybrechs–Iserles is added as [13]. Its items
  for the pinned repository report, the standalone Part II manuscript and the
  standalone Part IV manuscript are replaced by Parts I–IV and the pin in
  Section 61.1, and the sentences citing them by internal references
  (Section 61.5 lists them); its "Part II, Section 24.4" is printed as a
  cross-reference with the same number, and its "Section 13.1" of the Part IV
  manuscript as Section 57.1.
- **Part V typography.** The manuscript's `\shc` is printed `\sinhc`, its
  upright `\operatorname{Re}` as `\Re` (fraktur `ℜ` in this font, the
  repository's convention), and its `\dd` (`\,\mathrm d`) as `\,\dd` with the
  report's `\dd`, so the spacing is unchanged; its title page, scope box and
  contents are replaced by Section 61.1, which quotes the abstract and the
  scope box. No mathematical text was changed.
- **Part VI delivery names.** `code/06-growing-shifts-verify.py` says in its
  docstring "Run: python code/verify.py --output data" and writes unprefixed
  `verification_summary.json`, `critical_scales.csv`, `spectral_moments.csv`,
  `free_energy.csv` and `saddle_prefactor.csv` into its `--output` directory.
  `code/06-growing-shifts-make_figures.py` imports `verify` by that name and
  writes `determinant_crossover.pdf` and `free_energy.pdf` into
  `../figures/`. `code/06-growing-shifts-Makefile` was delivered at the
  package root; it names `code/verify.py`, `code/make_figures.py` and
  `article.tex`, which are other files here, and a bare `python`. It is kept
  byte-identical as delivered, although it must not be run here.
  `06-growing-shifts-SOURCES.md`, `06-growing-shifts-PROOF_AUDIT.md` and
  `06-growing-shifts-BUILD_CHECK.md` were delivered as `SOURCES.md`,
  `PROOF_AUDIT.md` and `BUILD_CHECK.md`; their "the article", "the present
  paper" and "the manuscript" are the manuscript (Part VI), their
  "repository" and "combined source" are Parts I–IV at the pin, their line
  ranges ("Lines 180–350", "Lines 940–1070", README "lines 210–410") are
  those of the pinned files, and their section numbers (Sections 3, 10, 15)
  are the manuscript's, shifted by 81 here. `BUILD_CHECK.md` describes the
  delivered 21-page PDF (343,305 bytes, with its SHA-256), its figures and its
  ZIP, not this report's PDF. `data/06-growing-shifts-requirements.txt` was
  delivered at the package root as `requirements.txt`. The article
  (Sections 94 and 99) gives the shipped names beside the delivered ones in
  merge notes, and prints the delivered reproduction commands with the
  warning and the scratch-copy recipe.
- **Part VI unshipped files.** The manuscript's `article.tex`, its 21-page A4
  `article.pdf`, its delivery README, its two delivered figure PDFs (Type 3
  fonts; replaced by the regenerated ones above) and its `SHA256SUMS.txt` are
  not shipped (they survive in `6ad01e9c8`; the checksum list, which named the
  delivered paths, was verified 17/17 at placement and retired). The delivery
  README's content — reading map, status, reproduction and file list — is
  covered by Section 81 and this README; its commands are superseded by the
  Part VI rerun paragraph above.
- **Part VI inconsistency in the delivery.** The manuscript's Appendix B
  (Section 99) lists two `pdflatex` runs; its delivery README and Makefile
  list three. Cosmetic; the article prints Appendix B as delivered, with a
  merge note.
- **Part VI overlap.** Part VI re-derives, without assuming Parts I–V, the
  Catalan measure (Part I's `mu_0`), the one-factor Christoffel identity, the
  Jacobi hypergeometric representation (Part I's (3.3) at `x = -a`) and
  Part I's coefficient formula (84.5) = (2.1) at `b = 1`, which it credits.
  All are marked in a merge note after (84.5) and in Section 81.5; no
  statement of Parts I–V was changed. The consistency observations of
  Section 81.4 are the merge's own and are labelled so; so is the
  identification of Part IV's question 57.4, which the manuscript does not
  cite.
- **Part VI bibliography.** Its Krattenthaler item (Ramanujan J. 61 (2023),
  arXiv:2101.04225) and DLMF item (18.5.7) are Part I's [3] and [4];
  Dette–Studden, Barbour–Hall and Méliot–Nikeghbali–Visentin are added as
  [14], [15] and [16]. Its two items for the pinned repository report and its
  README and continuation notes are replaced by Parts I–IV and the pin in
  Section 81.1, and the two sentences citing them by "(Parts I and IV above,
  and this report's README at the pin)" and "(Part I, Theorem 2.1)"; the
  items' own text is quoted in Section 81.5.
- **Part VI typography.** Its `\R` and `\E` are typed `\Rgs` and `\Egs`
  (same output), its `\dd` (`\,\mathrm d`) is printed `\,\dd` with the
  report's `\dd` (same spacing), its unused `\NN`, `\supp`, `\Cat` and
  `\onehalf` are dropped, and its `\clearpage` before Appendix B is dropped;
  its title page, abstract, scope line and contents are replaced by
  Section 81.1, which quotes the abstract and the scope line; two paragraphs
  of Section 81.1 and one merge note of Section 94 are laid out so that long
  hashes and file names do not overflow. No mathematical text was changed.

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

Part IV touches no sibling report: none of them treats moving roots of a
Catalan multiplier or endpoint (hard-edge) limits. The nearest is
`cigler-conjecture-8-schur`, whose asymptotics are fixed-parameter and
expressly not uniform as its parameter `t -> 1`, a different degeneration.
No reciprocal note was written for batch 53. Its related open problems are internal to this report:
Part II's Section 24.4 (the nonendpoint half, answered by Part V in batch 55
for fixed degree and fixed nonendpoint bases), Part III's Section 40.2
(endpoint factors with a cyclotomic interior root, close to Part IV's own
question 57.2) and Section 40.4 (uniform limits near a disappearing
characteristic factor).

Part V touches no sibling report either: none treats moving roots, bulk
(sine-kernel) limits or oscillatory Jacobi determinants; no reciprocal note
was written for batch 55. Its answers and open problems are internal to this
report and are recorded there by dated notes: Part II's Sections 22 and 24.4
and Part IV's introduction and Sections 44.4 and 57.1 (answered); Part IV's
question 57.2 (generalized in Part V's 77.2, not answered) and Part III's
Sections 40.2 and 40.4 (not discussed). The oscillatory Jacobi determinant
`Phi_t` belongs to the kissing-polynomial literature (Celsus–Deaño–Huybrechs–
Iserles), which no other ProveIt report cites.

Part VI touches no sibling report either: none treats growing shifts,
inverse Jacobi zeros, Marchenko–Pastur limits or Poisson approximation of
coefficient laws (a search at placement for "Marchenko", "size-biased", "inverse-zero" and
"growing shift" over the repository's reports found no Catalan–Hankel
match), and the batch-56 Part II of `cigler-conjecture-16-parity` (Cigler's
`c_n(t)` recurrences) does not overlap; no reciprocal note was written for
batch 57. Its answers and open problems are internal to this report and are
recorded there by dated notes: Part I's Sections 8 and 11 and Part IV's
Sections 44.4 and 57.4.

The report sits in the research-report collection of the `SetTheory/Cardinals`
Lean project. That placement confers no formal status: no Lean or Rocq
declaration anywhere in ProveIt formalizes a result of Parts I–VI as stated. The
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
formalizes a theorem of Parts I–VI. The Fabius project's
`Fabius.realSinhc` (`Analysis/FabiusFunction/Lean/FabiusFunction/HyperbolicActivation.lean`)
defines the real function `sinh x / x` with value 1 at 0, the real case of
the `sinhc` of Parts IV and V, with its basic identities; it states no result
of this report. The same project's
`Fabius.polynomialMomentGramMatrix_det_eq_prod_coeff_sq_mul`
(`PolynomialMomentGramDeterminant.lean`) is the finite change-of-basis
identity `det G_n = (prod of leading coefficients)^2 det H_n` for an arbitrary
moment pairing; the evaluation of Part V's constant `Z_t` (71.11) by monic
Legendre norms is an instance of that algebra together with orthogonality,
which the module does not assume, and no statement of Part V is formalized
there. Part II's Section 23.3, Part III's Section 40.8, Part IV's
Sections 56.4 and 57.10 and Part V's Section 77.9 propose formalization routes
(jets, confluent Vandermonde, the maximal-degree Cauchy–Binet lemma,
finite-prefix certification; the exponential-block minimality lemma, the
nearest-representative and square-sum lemmas, and the implication from the
two sector coefficients to the one-defect law; the polynomial identity behind
the centred alternant, the first-coefficient table over `Q` and the minor
relations, then the Christoffel layer, then the analytic remainder; the
centred Vandermonde, row-sign sector extraction, forced valuations and the
first-coefficient identity over formal power series, then the Christoffel
layer, then holomorphic divided differences, Cauchy estimates and the
implicit-function argument), as does Part VI's Section 96.10 (the finite
hypergeometric polynomial, its differential equation as a coefficient
identity and the rational recurrence, then the positive-root factorization
and the Catalan majorant, then the logarithmic estimates and the moment
limit, separated from the external Poisson theorem); none has been started.
The Fabius project's `CatalanGeneratingFunction.lean` proves
`catalanSeries_eq` (`C = 1 + X C^2` for the Catalan power series) and its
uniqueness `eq_catalanSeries_of_eq_one_add_X_mul_sq`, which is the formal
content of the uniqueness step in the proof of Part VI's Theorem 88.2 in the
case `theta = 1` ((88.8)–(88.9)); it states nothing about Hankel
determinants or inverse zeros, and no statement of Part VI is formalized
there.

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

Eugene Strahov and Yan V. Fyodorov, *Universal results for correlations of
characteristic polynomials: Riemann–Hilbert approach*, Communications in
Mathematical Physics 241 (2003), 343–382. https://arxiv.org/abs/math-ph/0210010

Gernot Akemann and Yan V. Fyodorov, *Universal random matrix correlations of
ratios of characteristic polynomials at the spectral edges*, Nuclear Physics B
664 (2003), 457–476. https://arxiv.org/abs/hep-th/0304095
(Both cited in Part IV for context only, not as inputs to its proofs;
Strahov–Fyodorov is cited in Part V in the same way.)

NIST Digital Library of Mathematical Functions, §18.11(ii), *Formulas of
Mehler–Heine type*, https://dlmf.nist.gov/18.11 (Part IV).

Andrew F. Celsus, Alfredo Deaño, Daan Huybrechs and Arieh Iserles, *The
kissing polynomials and their Hankel determinants*, Transactions of
Mathematics and Its Applications 6 (2022), tnab005.
https://doi.org/10.1093/imatrm/tnab005, arXiv:1504.07297 (Part V: the
oscillatory Jacobi determinant, its parity phenomena and large-frequency
analysis are prior literature; the manuscript's audit could not retrieve the
full text, so no theorem-by-theorem comparison was made).

Holger Dette and William J. Studden, *Some new asymptotic properties for the
zeros of Jacobi, Laguerre and Hermite polynomials*, arXiv:math/9406224
(1994). https://arxiv.org/abs/math/9406224 (Part VI: large-parameter
zero-asymptotic context; only the abstract was read, and no specialized
theorem is invoked).

A. D. Barbour and P. Hall, *On the rate of Poisson convergence*,
Mathematical Proceedings of the Cambridge Philosophical Society 95 (1984),
473–480. https://doi.org/10.1017/S0305004100061806 (Part VI: the
Bernoulli-sum Poisson bound (91.3), the only Poisson estimate it uses).

Pierre-Loïc Méliot, Ashkan Nikeghbali and Gabriele Visentin, *Mod-Poisson
approximation schemes and higher-order Chen–Stein inequalities*,
arXiv:2210.13818 (2022). https://arxiv.org/abs/2210.13818 (Part VI: context
for higher-order Bernoulli-sum approximation, not a novelty claim).

Dougherty, French, Saderholm and Qian (J. Integer Sequences 14 (2011)), DLMF
18.5.7 and OEIS A000108, A001519, A001906 are cited in Part I. Part I's
sources were checked on 19 September 2026 and Part II's on 28 September
2026; Part III's manuscript is dated 29 September 2026 and its source notes
do not date their checks; Part IV's manuscript and source notes are dated
29 September 2026, the day it consulted DLMF; Part V's and Part VI's
manuscripts and source audits are dated 29 September 2026 (both audits give
the Pacific date). The six provenance notes record the versions inspected
and the limits of each search. No third-party paper PDFs, font files, compiler auxiliaries or
bytecode are included.
