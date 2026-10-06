# Binary Matrices of Fixed Positive Permanent (OEIS A089479)

**`C_{n,k} = (n!)² 2^C(n,2) k⁻¹ {ρ⁻ⁿ P_k(n) + O_k(2⁻ⁿ)}` for every fixed
`k ≥ 1`, with `ρ = 1.48807…` the acyclic-digraph root and `P_k` a polynomial
of exact degree `Ω(k)`; certified `P_2`, `P_3`, `P_4`; explicit all-`n`
constants; a prime-block size law; spectral, Stirling and threshold-inverse
expansions**

A research article ("Report184" of a session bundle), built from one
manuscript dated 3 October 2026. Its author line is a subtitle
("Asymptotics, canonical block laws, and reproducible certificates") and its
PDF author field reads "Research report": it names no person, tool or
addressee. The package carries no "prepared for private review" line, no
e-mail address and no personal data. The delivered README used the generic
placeholder `/absolute/path/to/new-release`; it is not reproduced here.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 184 (batch 108) | `Fixed_Permanent_Matrices_Asymptotics_and_Inverses_Source.zip` (30 files at the archive root, no wrapper directory, 659,214 bytes, SHA-256 `0863547a…6957c3112e`), arrival commit `60f54ea06`; main file `Report184.tex` (930 lines, 24 pp.) | none: the package names no ProveIt commit; it describes a bounded look at report collections (Section 14) | `602e5bd0f` (batch 108) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and nothing in the
repository's formal developments concerns permanents or acyclic-digraph
counts.

## Trust boundaries

- **What is proved by hand.** Theorem 1.1 and its ingredients (the
  marked-matching identity `k C_{n,k} = n! b_{n,k}`, the circulation bound,
  the finite kernel formula, the root isolation of `E`, the positivity
  identity, Cauchy estimates), Theorem 1.3 through Theorem 10.1, Theorem 9.1
  and Theorem 12.1. No proof of these uses a computation.
- **What rests on a classical theorem.** Robinson's strong-component
  transform (equation (19)), read by the source in de Panafieu and Dovgal,
  *Symbolic method and directed graph enumeration* (arXiv:1903.09454v2,
  Theorem 3.4), and re-derived in Section 4 in the marked form used here.
  The case `k = 1` (permanent one ↔ acyclic digraphs) is classical, and its
  asymptotic is the one stated in OEIS A003024 (Remark 1.4).
- **What rests on computation.** The rational functions `S_3`, `S_4`
  ((15)–(16)) come from enumerating finitely many kernels. The explicit
  constants of Theorem 1.2 (`M_2 = 1000`, `M_3 = 3900`, `M_4 = 170000`) and
  the effective inverse brackets (50) use the 25-digit rational interval
  enclosures of Section 7, which are the output of the shipped exact program
  `code/certify_constants.py`; the rest of Section 8 is exact rational
  arithmetic, redone by hand at intake. The tables of `π_2(m)` and of
  finite-size discrepancies are decimal diagnostics.
- **What is promised but not shipped.** Section 7.3 says that "a second
  independent rational implementation using 50 terms and formal
  Laurent-series inversion reproduces the displayed intervals". No such
  implementation is in the package (the closest program,
  `code/decimal_diagnostics.py`, is a floating Decimal computation from the
  derivative formulas). The write records this in a dated note after Section
  7.3 and as Question 7 (`fpm:q:second`). Nothing depends on it.

## What it proves

`C_{n,k}` counts labelled `n × n` binary matrices with permanent `k`
(the triangle A089479, `C_{n,k} = T(n,k)`), `k ≥ 1` fixed,
`d = Ω(k)`, `E(z) = Σ_{m≥0} (−z)^m/(m! 2^C(m,2))`, `ρ` its unique zero in
`|z| ≤ 2`, `a = −ρE'(ρ) = ρE(ρ/2)`. Statement numbers are the delivered ones.

- **Theorem 1.1 (`fpm:thm:main`)**: `C_{n,k} = (n!)² 2^C(n,2) k⁻¹
  {ρ⁻ⁿ P_k(n) + O_k(2⁻ⁿ)}`, `P_k` effectively computable of exact degree
  `d`, leading coefficient `L_k = Π h_p^{e_p}/(a^{d+1} Π e_p!)` with the
  positive prime amplitudes `h_p` of (4); `P_1 = 1/a`.
- **Theorem 1.2 (`fpm:thm:effectiveintro`)**: for `k = 2, 3, 4` and every
  `n ≥ 0`, `|k C_{n,k}/((n!)² 2^C(n,2)) − ρ⁻ⁿ P_k(n)| ≤ M_k 2⁻ⁿ`.
- **Theorem 1.3 (`fpm:thm:blocksintro`)**, proved through **Theorem 10.1
  (`fpm:thm:weighted`)**: the components of the allowed-edge graph of a
  uniform matrix of permanent `k`; with probability `1 − O_k(1/n)` exactly
  `d` are nontrivial, with prime permanents; independent limiting sizes with
  laws `π_p` (6); expansions to every fixed order in an exponentially weighted
  total-variation norm.
- **Lemma 3.1 (`fpm:lem:cycles`)**: a strongly connected digraph with `v`
  vertices and `m` arcs has at least `m − v + 1` simple cycles, so
  `m − v ≤ k − 2`. **Proposition 3.2 (`fpm:prop:kernel`)**: the finite kernel
  formula for `S_k`, `k ≥ 3`; `S_2 = −log(1 − z) − z` (11),
  `S_3 = z³(3 − 2z)/(2(1 − z)³)` (15), `S_4` (16).
- **Lemma 5.1 (`fpm:lem:root`)**: `E` has exactly one zero in `|z| ≤ 2`,
  simple, in `(37/25, 3/2)`; `|E| > 119/1000` on `|z| = 2`.
- **Lemma 6.1 (`fpm:lem:positive`)**: `Δ(e^{−z}S)(z) =
  Σ s_m z^m E(z/2^m)/(m! 2^C(m,2))`, hence `h_p > 0` and the exact pole order
  `d + 1`.
- **Section 7**: `P_2`, `P_3`, `P_4` in the binomial basis with certified
  25-digit enclosures of `ρ, a, h_2, h_3, H_4(ρ)` and all nine `c_{k,j}`.
- **Theorem 9.1 (`fpm:thm:spectral`)**: the finite-radius spectral expansion
  (standard); Section 9.1: every fixed Stirling order (21).
- **Section 11**: `C_{n+1,k} ≥ 2ⁿ C_{n,k}` (44); for the threshold
  `N_k(y) = min{n ≥ 0 : C_{n,k} ≥ y}` the two-ceiling brackets (46), (47),
  and explicit ones (50) for `k = 2, 3, 4` valid when `y > F^eff_{k,+}(50)`.
- **Theorem 12.1 (`fpm:thm:reversion`)**: the smooth root
  `r_k(y) = t + Σ_{j≤J} U_j(log t) t^{−j} + O((log t)^{J+2}/t^{J+1})`,
  `t = √(2 log y/log 2)`, with `U_0, U_1, U_2` explicit; and the truncated
  brackets (56).

Added by the write (6 October 2026), marked `[write]`:

- **Remark 1.4 (`fpm:rem:oeis`)**: the OEIS entries quoted and compared
  (next section), with two proofs: `k = 1` of Theorem 1.1 is an instance of
  the asymptotic stated in A003024 (`p = ρ`, `M = a`), and the reading of a
  comment of A003024 (since the independent check, also the joint orbits:
  the unlabelled acyclic digraphs, A003087).
- **Remark 12.2 (`fpm:rem:transseries`)**: Sections 11–12 against the
  transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`).
  (a) `C_{n,k}` is strictly increasing from `n_1` (`n_1 = 1` for `k = 1`,
  the first index with `C_{n,k} > 0` otherwise), so `p0:def:three-inverses`
  applies and `p0:thm:staircase`(1) gives `N_k = ⌈ν⌉` for every admissible
  interpolation, for `y > C_{n_1,k}`. (b) The brackets (46), (47), (50), (56)
  are **analogues, not instances** of `p0:thm:staircase`: `F_k`, `F_{k,±}`,
  `F^eff_{k,±}` sandwich the counts but do not interpolate them; at most two
  consecutive values remain, since the two ceiling arguments differ by less
  than one (said explicitly since the independent check). (c)
  Theorem 12.1 is **an instance only after a change of variable, and only
  formally**: with `G(x) = √((2/log 2) log F_k(x))`, the equation `G(x) = t`
  is of monomial–logarithmic type (`plt:def:lw-monomial-log-datum`) with data
  `(ρ_vol, μ_vol, β_vol) = (1, 2/log 2, −β/log 2)`, and its formal solution
  from `plt:thm:lw-template` is the source's series; the analytic remainder
  and `deg U_j ≤ j + 1` are the source's own. Without the square root it is
  also a direct formal instance of `p0:thm:core-reversion`
  (`x = t(1+E_vol)`, `Λ_vol = log 2`, `h_vol(u) = (log 2) u²/2`,
  `e_{j+1} = U_j`), the route of `a222959-zero-slope-matrices` (recorded
  since the independent check). The quadratic phase is not one
  of the Lambert cores of `p0:thm:lambert-core` or
  `p0:prop:factorial-core`.
- Section 1.2 (`fpm:sec:provenance`: provenance, the sources as the write
  read them, what was checked, relation to the repository, collected
  non-claims, reading conventions), notes at the end of Sections 7.3, 13 and
  14.2, Question 7 in Section 15, two bibliography entries (A245654,
  A245655).

## The OEIS entries (Remark 1.4)

Read on 6 October 2026 in the internal format; quoted verbatim.

- **A089479** (revision #31, 19 February 2026, the one the source read):
  "Triangle T(n,k) read by rows, where T(n,k) = number of times the
  permanent of a real n X n (0,1)-matrix takes the value k, for n >= 0, 0 <=
  k <= n!." Row 0 is `0, 1` (`per(∅) = 1`). Its comment gives Gordon Royle's
  row `n = 6`; the write recomputed `C_{n,k}`, `k ≤ 4`, `n ≤ 6` from (11),
  (15), (16) and the transform with its own exact code, and all agree. No
  asymptotic is stated there.
- **A089482** (revision #33): "Number of real {0,1}-matrices having
  permanent = 1.", with "a(n) = n! * A003024(n). - _Vladeta Jovovic_, Oct 26
  2009" and Alekseyev's proof: the case `k = 1` of `k C_{n,k} = n! b_{n,k}`.
- **A003024** (revision #239, 13 August 2026): "Number of acyclic digraphs
  (or DAGs) with n labeled nodes." It states (Kotesovec, Dec 09 2013)

      a(n) ~ n!*2^(n*(n-1)/2)/(M*p^n), where p = A245654 = 1.488078545599710294656246... is the root of the equation Sum_{n>=0} (-1)^n*p^n/(n!*2^(n*(n-1)/2)) = 0, and M = Sum_{n>=1} (-1)^(n+1)*p^n/((n-1)!*2^(n*(n-1)/2)) = A245655 = 0.57436237330931147691667...

  (followed by a note on the misprint `M = 0.474` in two printings of
  McKay et al. and Sloane's reply that it is a typo for 0.574, "taken from
  Stanley's 1973 paper"). **Theorem 1.1 at `k = 1` is an instance of this
  classical asymptotic, not a new result**: `p = ρ` (A245654 is "the
  smallest positive root" of `E`), and `M = a`, since the series for `M` is
  `−ρE'(ρ)` term by term. The write's 60-digit values of `ρ` and `a` agree
  with the first 55 of the 103 printed digits of A245654 and A245655; the
  independent check compared all 103 with 130-digit values of its own, and
  they agree.
- **A003024, a reading.** The comment "Also the number of n X n real
  (0,1)-matrices with permanent equal to 1, up to permutation of
  rows/columns, cf. A089482. - _Vladeta Jovovic_, Oct 28 2009" is right with
  "rows/columns" read as "rows, or columns": columns of a permanent-one matrix
  are pairwise distinct, so the column action is free and has
  `A089482(n)/n! = A003024(n)` orbits. Jointly, at `n = 2` the six
  permanent-one matrices form 2 orbits, against `A003024(2) = 3`. In
  general the joint orbits are the isomorphism classes of acyclic digraphs
  (a row permutation `π` sends the marked digraph `D` to `π(D)`), counted
  by A003087: `1, 2, 6, 31` for `n = 1, …, 4`, confirmed exhaustively
  (added after the independent check). Recorded
  only: **nothing was submitted to the OEIS.**
- **A350790** (revision #28): "Number of digraphs on n labeled nodes with a
  global source and sink."; cited by the source only for its link to
  Robinson's 1995 paper.

## What is not claimed

From the source, kept in the article (collected in Section 1.2):

- Nothing for growing `k = k(n)`, growing weight `θ` or growing order; every
  constant may depend on `k`.
- The case `k = 1` and the component transform are classical; the literature
  review is bounded and "not a worldwide priority determination"; Robinson's
  1995 paper was not obtained (its host refused connections again at the
  write).
- Decimal diagnostics are not certificates; the C++ audits are finite; no
  finite comparison proves an all-`n` statement; the constants `M_k` are
  safe, not optimized.
- No certified inverse solver, and no eventual exact rounding formula for
  `N_k(y)`; no claim that all zeros of `E` are real, no convergent sum over
  all poles; the envelope `F_k` is not an interpolation of the counts.
- PDF byte identity is promised only on the same Python/TeX stack.

The write adds: its independent checks are floating or finite; Remark
1.4(d) concerns the wording of an OEIS comment only; Remark 12.2 claims no
novelty for any inversion.

## Further questions

Section 15 of the article (`fpm:sec:questions`) keeps the source's six
questions (efficient kernel algorithms; sharper constants; explicit
correction laws for composite `k`; a certified inverse solver; growing `k`;
Robinson's paper) and adds, under Vladimir's standing rule of 4 October
2026:

7. **The second implementation** (`fpm:q:second`): the claimed second
   rational implementation is not shipped; what is missing is that
   independent certificate, written and published with its code.

A dated note there adds, on Question 2, that most of each `M_k` comes from
the circle majorants, not from the principal parts (33, 60, 99); on Question
4, that only the brackets (50) are explicit; on Question 6, that the paper
was again unreachable. **Nothing in the source was found to be wrong.**

## Checks made at intake

- At placement (batch-108 dossier, 6 October 2026; Windows 11, Python
  3.14.4): the 28 staged files (with the delivered README and
  `Report184.tex` as `article.tex`) were byte-identical to the archive; `SHA256SUMS.json` 29/29 and `data/FROZEN_SOURCE_HASHES.json`
  9/9. The dossier read the manuscript in full, found no error and rechecked
  by hand `a = ρE(ρ/2)`, `S_3(1/2) = 1`, `S_4(1/2) = 91/6`, the sum 26 in
  (27), the slack fractions `193687/14161`, `378240/14161`,
  `1244199259/1685159`, the principal-part bounds 33, 60, 99, the bound
  `P_4(x) > 0.65x² − 1.45x − 4.5` and the injection (44). It ran the suite on
  copies (next sections) and the optional C++ audits.
- At the write (6 October 2026; same machine): every proof rechecked;
  independently of the delivered code, the kernel counts `1, 2` (`k = 3`) and
  `1, 6, 24, 48` (`k = 4`) and the rational functions (15), (16) rebuilt from
  Proposition 3.2 (SymPy 1.14.0); rows `n ≤ 6`, `k ≤ 4` of A089479
  recomputed; `C_{n,1} = n! A003024(n)` for `n < 12`; all thirteen quantities
  of Section 7 at 50 digits (mpmath 1.3.0), the `c_{k,j}` by contour
  integrals rather than the derivative formulas, every value inside its
  printed interval; the slack of (49), the `π_2(m)` table and the
  discrepancy rows `n = 5, 10`; `U_0, U_1, U_2` of Theorem 12.1 by series
  algebra (and `deg U_3 = 4`); the suite rerun on a fresh extraction and from
  the shipped files (routes below).
- Sources read by the write: the OEIS entries above and A245654, A245655;
  de Panafieu–Dovgal arXiv:1903.09454v2 (Theorem 3.4) and arXiv:2001.08659v2
  (Section 2.3); Dovgal–Nurligareev arXiv:2310.05282v3 (dated 5 August 2026,
  Sections 4.3–4.4); Greenhill–Hasheminezhad–Iliffe–McKay arXiv:2601.04822v1
  (Theorems 4.2–4.5); the transseries volume (labels named above). Not read:
  Kim–Lee–Seol (2005); Robinson (1995), unreachable.
- **Independent check of the write (6 October 2026).** An adversarial check
  made by the intake after the write (`71813ce3f`), with its own code: the
  OEIS entries fetched again (revisions as quoted); `ρ` and `a` at 130
  digits agree with **all 103** printed digits of A245654 and A245655, and
  A003024(n) from its own recurrence matches `n! 2^C(n,2)/(a ρⁿ)` with
  relative errors `−1.3e−3 … −6.4e−14` at `n = 5, 10, …, 25`; every
  permanent-one matrix with `n ≤ 4` has distinct rows and columns, row and
  column orbits `1, 3, 25, 543`, joint orbits `1, 2, 6, 31` (A003087). An
  exact C++ count of all binary `n × n` matrices for `n ≤ 6` (all `2^36` at
  `n = 6`, without the transform) reproduces rows `n ≤ 6`, `k ≤ 4` and
  Royle's row; a direct count of strongly connected kernels for `m ≤ 7`
  gives `s_{m,3} = 0, 9, 84, 720, 6480, 63000` and
  `s_{m,4} = 0, 6, 256, 4940, 80400, 1259160` (`m = 2, …, 7`), the
  coefficients of (15), (16). The thirteen constants of Section 7 at 130
  digits by a third route, each inside its interval (margins ≥ 1.7e−27).
  Remark 12.2 re-derived (SymPy: `U_0, U_1, U_2`, `deg U_3 = 4`).
  No mathematical error. Added, each marked with the date: the joint-orbit
  count with its proof in Remark 1.4(d); why at most two consecutive values
  remain in Remark 12.2(b); the `p0:thm:core-reversion` route in 12.2(c);
  the full 103-digit comparison in 1.4(c). One bibliography entry (A003087).
  The check is recorded at the end of Section 13.

## Relation to the repository

**Formal status.** No statement is formalized, and placement in the
collection confers no formal status.

**The transseries volume.** Remark 12.2: the brackets are analogues of
`p0:thm:staircase`, the reversion a formal instance of `plt:thm:lw-template`
after `G = √((2/log 2) log F_k)`, and directly of `p0:thm:core-reversion`.

**Neighbouring reports** (under
`SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`):

- `a182220-source-boundary`: extensional acyclic digraphs, a subclass of the
  `k = 1` digraphs; its marked-source identity (`sbd:prop:marked`) is the
  source-vertex form of the marked-source-component sieve that proves (19).
- `a116379-bounded-identity-trees`: a different class and singularity; the
  same method of rational interval certificates of the constants (its Part
  II) and computable inverses.
- See also `a397711-bounded-indegree-dags` (batch 108): labelled DAGs with
  bounded indegree, whose unbounded count is A003024.
- The source's review also checked `a299907-lonesum-decomposable-matrices`,
  `a372395-acyclic-orientation-partitions` and
  `a108242-regular-cyclic-word-covers` and found different models; still so.
  `a000382-winding-correction` evaluates permanents of particular 0–1
  matrices, a different question.
- `code/verify_manifest.py` is byte-identical to
  `a271619-strict-twice-partitions/code/182-strict-verify_manifest.py` (blob
  `ed00651e`), a generic tool of the same bundle; it is shipped here again so
  that this package reruns on its own.

Reciprocal notes for `a182220-source-boundary` and
`a116379-bounded-identity-trees` are proposed separately; none is needed
elsewhere.

**Stale claims.** Before batch 108 no file of the repository named A089479,
A089482, A003024 or A350790. The source's statement that the report
collections contain no matching report remains true.

## Notation

A table at the end of Section 1.2 fixes the letters the manuscript reuses,
with the tempting false readings: `a` (and A003024's `M`) against matrix
entries; `b`, `c` (Taylor coefficients of `E`; `c = d + 1` in Section 12)
against `b_{n,k}`, `c_{k,j}` and the circulation `c`; `d, e, e_p, e_j`;
`h_p`, `h_k = H_k(ρ)` and `H_4(ρ)` (not an amplitude); `L`, `L_k`, `ℓ`;
`M`, `M_k`, `𝓜_k`; `q = ρ/2`, the cubic `Q`, the factors `Q_j`; the three
`t` (Sections 6 and 12, Lemma 6.1), `s`, `r`; `E`, `Δ`, `π_p`, `δ`; `N_k(y)`
against the volume's staircase and the truncation `N = 45`. No symbol was
renamed; the volume's colliding letters carry the subscript "vol" in Remark
12.2.

## Labels

Every label carries the prefix `fpm:` (none existed in the repository). The
manuscript's 83 labels (`eq:` 56, `sec:` 17, `thm:` 6, `lem:` 3, `prop:` 1)
were prefixed before anything cited them, and the 75 references to them
(60 `\eqref`, 15 `\ref`) updated. The write added 4: `fpm:rem:oeis`,
`fpm:sec:provenance`, `fpm:rem:transseries`, `fpm:q:second`. The report has 87
labels; builds of the delivered text and of this one give all 83 delivered
labels the same numbers (aux files compared). The added remarks are the last
statements of their sections, the added subsection follows the last delivered
one of Section 1, and the added displays are unnumbered.

## Files

```text
README.md                                    this guide (replaces the delivery README)
README_REPRODUCIBILITY.md                    the delivered reproducibility guide (delivered at the root)
article.tex                                  the report (delivered Report184.tex; labels prefixed, [write] additions)
article.pdf                                  compiled report, 32 pages
code/build.py                                release builder (delivered at the root)
code/test_build.py                           176 build-guard cases, simulated compiler (delivered at the root)
code/reproduce.py                            mandatory reproduction driver (delivered at the root)
code/verify_manifest.py                      manifest and safe-read helper (delivered at the root; = a271619's)
code/verify_frozen_sources.py                checks data/FROZEN_SOURCE_HASHES.json (delivered at the root)
code/check_fixed_permanent.py                kernels, exact counts to n = 20, diagonal-one checks (delivered code/)
code/certify_constants.py                    rational interval certificate of Section 7 (delivered code/)
code/test_certified_guards.py                nine invalid certificate calls (delivered code/)
code/check_effective_error.py                exact inequalities of Sections 8 and 11.3 (delivered code/)
code/decimal_diagnostics.py                  non-certified Decimal diagnostics (delivered code/)
code/check_precomputed_audits.py             checks the C++ TSV data (delivered code/)
code/test_reproduction_guards.py             18 negative and 3 positive guards (delivered code/)
code/optional-audit_counts.cpp               exhaustive count audit through n = 5 (delivered optional/audit_counts.cpp)
code/optional-audit_blocks.cpp               block-signature audit (delivered optional/audit_blocks.cpp)
data/constant_certificate.json               the certified enclosures (delivered code/constant_certificate.json)
data/certificates-exact_checks.json          reference output (delivered certificates/exact_checks.json)
data/certificates-effective_error_checks.json   reference output (delivered certificates/)
data/certificates-decimal_diagnostics.json   reference output (delivered certificates/)
data/certificates-precomputed_audit_checks.json reference output (delivered certificates/)
data/generated-BUILD_INFO.json               build receipt (delivered generated/)
data/generated-build_guards.json             build-guard receipt, 176 cases (delivered generated/)
data/generated-verification.json             verification receipt (delivered generated/)
data/optional-audit_counts.tsv               C++ count output, 220 rows (delivered optional/)
data/optional-audit_block_counts.tsv         C++ block output (delivered optional/)
data/FROZEN_SOURCE_HASHES.json               SHA-256 of 9 frozen files (delivered data/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, recoverable from the arrival commit (next section):
`Report184.pdf` (the delivered 24-page PDF, 469,648 bytes);
`SHA256SUMS.json` (2,881 bytes, 29 entries, verified at placement;
repository policy ships no checksum manifests); and the delivery `README.md`
(4,499 bytes), staged at placement and replaced by this guide (summarized
below).

**Delivered text that names the delivery layout or files not shipped.**
`README_REPRODUCIBILITY.md`, `code/build.py` (its closed `SOURCES`
inventory), `code/reproduce.py`, `code/test_build.py`,
`code/verify_frozen_sources.py`, `data/FROZEN_SOURCE_HASHES.json` and the
`data/generated-*.json` receipts use the delivered paths (`certificates/`,
`generated/`, `optional/`, `code/constant_certificate.json`,
`Report184.tex`, `Report184.pdf`, `SHA256SUMS.json`); the test of
`code/test_certified_guards.py` loads `constant_certificate.json` from
beside its own source, so no program runs under the shipped names. Section
13 of the article speaks of "the ZIP" and "the packaged README files", and
Section 7.3 of the unshipped second implementation.

**Delivered numbers that differ on Windows.** `README_REPRODUCIBILITY.md`
and `data/generated-build_guards.json` give 176 build-guard cases; on
Windows 171 run and pass (five FIFO and POSIX-only rejection cases are
skipped). The delivered builder rejects underfull boxes; under MiKTeX the
delivered text gives two underfull boxes in its bibliography (as does this
build), and the builder itself was not run.

## Retrieving the delivered package

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/Fixed_Permanent_Matrices_Asymptotics_and_Inverses_Source.zip > "$T/a.zip"
sha256sum "$T/a.zip"   # 0863547a2a49a2091bbd718b2461de28ac076922b625e18c1e26b06957c3112e, 659,214 bytes
mkdir "$T/pkg" && cd "$T/pkg" && unzip -q ../a.zip     # the 30 files are at the archive root
python3 -B verify_manifest.py                            # {"files_checked": 29, "status": "PASS"}
```

## Rerun the checks (on a scratch copy)

Python 3.10 or later, standard library only. Never run anything in the
repository.

**Route A, delivered layout** (as the delivery README gives it):

```sh
cd "$T/pkg"
python3 -B reproduce.py                 # five reference JSON files, normal and -O, byte for byte
python3 -B test_build.py && python3 -O -B test_build.py
python3 -B reproduce.py --optional-cpp  # g++ with C++17; recompiles and reruns the C++ audits
```

On Windows `reproduce.py` stops with "normal byte mismatch:
exact_checks.json", because the scripts write JSON in text mode and Windows
emits CRLF. This wrapper, saved as `crlf_reproduce.py` outside the package
and run from the package root (`py -B /path/to/crlf_reproduce.py`), changes
only the line endings before the byte comparison; it passed in about 25 s at
the write:

```python
import sys, tempfile
from pathlib import Path
root = Path.cwd(); sys.path.insert(0, str(root))
import reproduce
orig = reproduce.manifest.read_regular
reproduce.manifest.read_regular = lambda p: orig(p).replace(b"\r\n", b"\n")
with tempfile.TemporaryDirectory() as t:
    res = reproduce.run(root, Path(t) / "results")
print(res["status"], res["normal_and_optimized_identical_to_reference"])   # PASS True
```

`--optional-cpp` links dynamically; on the intake's Windows machine such
builds crash (a DLL mismatch). Compiled by hand with
`g++ -O3 -std=c++17 -UNDEBUG -static` in a scratch directory (the programs
write their TSV files into the current directory), both audits reproduced
`optional/*.tsv` after removing carriage returns, at placement (1.2 s for
the 2²⁵ matrices at `n = 5`). The PDF/ZIP builder (`build.py --output`)
needs POSIX and pdfTeX and was not run.

**Route B, from the shipped files** (tested at the write on Windows): rebuild
the delivered layout under the delivered names, then run Route A there.

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a089479-fixed-permanent-matrices
B=$(mktemp -d); cd "$B"; mkdir certificates code data generated optional
cp "$R/README_REPRODUCIBILITY.md" .
for f in build.py test_build.py reproduce.py verify_manifest.py verify_frozen_sources.py; do cp "$R/code/$f" .; done
for f in certify_constants.py check_effective_error.py check_fixed_permanent.py check_precomputed_audits.py decimal_diagnostics.py test_certified_guards.py test_reproduction_guards.py; do cp "$R/code/$f" code/; done
cp "$R/data/constant_certificate.json" code/
for f in decimal_diagnostics effective_error_checks exact_checks precomputed_audit_checks; do cp "$R/data/certificates-$f.json" "certificates/$f.json"; done
for f in BUILD_INFO build_guards verification; do cp "$R/data/generated-$f.json" "generated/$f.json"; done
for f in audit_counts audit_blocks; do cp "$R/code/optional-$f.cpp" "optional/$f.cpp"; done
cp "$R/data/optional-audit_counts.tsv" optional/audit_counts.tsv
cp "$R/data/optional-audit_block_counts.tsv" optional/audit_block_counts.tsv
cp "$R/data/FROZEN_SOURCE_HASHES.json" data/
python3 -B verify_frozen_sources.py     # 9 files PASS
```

At the write this layout (without `Report184.tex` and the delivered README,
which the suite does not read) gave: frozen sources 9/9 PASS; the CRLF
wrapper PASS, normal and optimized identical to the references, guards 18
negative and 3 positive; `test_build.py` 171 tests PASS. Use `py` where
`python3` is not on the path.

## Build the PDF

pdfLaTeX (fontenc, inputenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, array, geometry, microtype, hyperref, enumitem); the bibliography
is embedded.

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX on 6 October 2026, after
the independent check (31 pages at the write): 32 pages; no errors or warnings, no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull boxes;
two underfull boxes in delivered bibliography entries, which the delivered
text also gives (24 pages). The article keeps the delivered preamble lines
that suppress PDF dates and trailer identifiers; the delivered byte-identity
claims apply to `Report184.tex` under the delivering toolchain, not to this
build.

## From the delivery README

The delivery README (replaced by this guide) stated the main formula and
that "The k=1 DAG case and the SCC transform are classical and credited in
the manuscript. The analysis does not cover a growing-k regime or claim
worldwide historical priority"; gave the quick start of Route A ("Mandatory
Python checks use only the standard library, with both ordinary and
optimized (-O) execution"); described the release builder (absolute output
path outside the package, refusing existing paths, rejecting warnings and
boxes; outputs `Report184.pdf`, `Report184.tex`, `Report184_code.zip`,
`ARTIFACTS.json`); separated "Exact certificates versus diagnostics" (the
four certificate files, `code/constant_certificate.json`, and that "The
all-n remainder bound requires the manuscript's analytic proof in addition
to the checked rational inequalities ... No certified numerical inverse
solver is included"); and described the optional C++ audits as
"supplemental, not assumptions of the proof".

## Rights

Repository contents are MIT-0. The article quotes OEIS entries A089479,
A089482, A003024, A350790, A245654 and A245655, and `code/check_fixed_permanent.py`
embeds terms of A089479; OEIS content is published by The OEIS Foundation
Inc. under CC BY-SA 4.0 (https://oeis.org/LICENSE), and those terms remain
under that licence. No third-party PDF or code is shipped. Nothing was
submitted to the OEIS.

## Provenance

- Sources cited by the manuscript: OEIS A089479 (revision #31), A089482,
  A003024; de Panafieu and Dovgal (arXiv:1903.09454v2; arXiv:2001.08659v2);
  Dovgal and Nurligareev (arXiv:2310.05282v3); Kim, Lee and Seol, IJPAM 19
  (2005) 413–418; Greenhill, Hasheminezhad, Iliffe and McKay
  (arXiv:2601.04822v1); Robinson (1995, not obtained). Added by the write:
  OEIS A245654 and A245655; after the independent check: A003087.
- Batch 108 of `docs/incoming`, bundle Report 184; arrival `60f54ea06`,
  placement `602e5bd0f`, written 6 October 2026. Single source, so no merge
  choices. The delivered `Report184.tex` is shipped as `article.tex`; the
  delivered programs and data as listed above.
