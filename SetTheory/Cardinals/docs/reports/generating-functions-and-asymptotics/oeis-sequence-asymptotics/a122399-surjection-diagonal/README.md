# Asymptotic Enumeration and Inversion for A122399

**The diagonal of 1/(1 − u e^y(e^x − 1)): all-orders saddle expansion, exact contour, controlled inverse, block-count CLT and prime-power periodicity (Part I); Poisson defects, local limit laws and inverse thresholds for the rectangular family (Part II)**

A research report in two Parts, built from two manuscripts: Part I (dated
1 October 2026) names no author or tool (its author line reads "A proof and
reproducible research report"); Part II (dated 4 October 2026) has the
author line "ChatGPT", "Research continuation prepared for Vladimir
Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 35 | batch 77, manuscript 35 | `oeis-a122399-research.zip` (main file `a122399-report.tex`, 389 lines, 8-page PDF) | none; a scoped index search at `76c0887a6` (`proof.md:9`) | `f76fcb566` (arrival `096ee7b87`) | Part I, Sections 1–8 |
| 11 | batch 98, manuscript 11 | `A122399_Boundary_Transitions_and_Inversion.zip` (351,864 bytes; main file `article.tex`, 1,480 lines, 22-page PDF) | tree `0f93381e8` and `proof.md` blob `6f03a8be2` (both current: the report had no commit between pin and placement) | `9353a7171` (arrival `2172df76a`) | Part II, Sections 9–21 and Appendices A–B |

**Status: unrefereed; not formalized; AI-assisted delivery channel.** Both
manuscripts entered the collection through `docs/incoming`; neither has
been refereed, and no statement of either is formalized in Lean or Rocq.

For

    a_n = sum_{k=0}^{n} k^n k! S(n,k)        (OEIS A122399; 1, 1, 9, 211, 9285, ...)

**Part I** proves:

- **(2.1)–(2.3)** an exact, absolutely convergent vertical-contour formula for
  the two-size numbers `A_{m,n}` (`a_n = A_{n,n}`), via the Mittag-Leffler
  identity (2.2), with an explicit nonasymptotic tail bound;
- **(3.5)** an all-orders saddle expansion of `A_{m,n}`, uniform for `m/n`
  in compact subsets of `(0, ∞)`, with the finite coefficient formula (3.4);
- **(4.1)** `a_n = C D^n (n!)^2 n^(-1/2) [1 − 0.0600744…/n + 0.0075945…/n^2 +
  0.0037132…/n^3 − 0.00036298…/n^4 + O(n^-5)]`, with
  `D = 3.161088653865…` (= OEIS A317855), `C = 0.327628285569…`, and `c_1`
  in closed form (4.2);
- **(5.1)–(5.4)** a controlled inverse along the sequence, a Lambert-W₀
  initializer with Newton steps, and integer-threshold ceiling envelopes;
- **(6.2)** a Gaussian limit for the number of occupied blocks, mean
  `μn + μ_0`, variance `σ²n`, `μ = 1/y = 0.8737024…` (the OEIS constant
  `r`), `σ² = 0.0889169…`;
- **(7.1)** `a_{n+φ(p^r)} ≡ a_n (mod p^r)` for every prime `p`, `r ≥ 1` and
  `n ≥ r`; in particular `p − 1` is a period mod `p` from `n = 1`, which
  proves the OEIS conjecture (Peter Bala, 2022) in that sense.

**Part II** studies the number `K` of blocks of a uniform structure counted
by `A_{m,n}` and its defect `D = m − K` (not Part I's growth constant `D`),
with `r = n/m`, `λ = (m/2)e^{−r}` (not Part I's `λ = m/n`) and
`R_{m,n} = A_{m,n}/(m! m^n) = 1/P(D = 0)`. It proves:

- **Lemma 10.1** `(m−j)! S(m,m−j)/m! = [t^j] ((e^t−1)/t)^{m−j}`, a
  polynomial in `m` of degree `j`, and `1 ≤ R_{m,n} ≤ e^λ`;
- **Theorem 11.1, Corollary 11.2** for integer `n ≥ 0` the block polynomial
  `Σ_k k^n k! S(m,k) u^k` has a simple zero at 0 and `m − 1` simple zeros in
  `(−1, 0)`, interlacing as `n` grows; so `D` is exactly a sum of `m − 1`
  independent Bernoulli variables with parameters in `(0, 1/2)` (the case
  `n = 0` is Frobenius's real-rootedness of the Eulerian polynomials, and
  the method is Harper's, 1967: both credited by the write);
- **Theorem 12.1, (12.12)–(12.15)** explicit bounds for all `m ≥ 2`,
  `n ≥ 0`: `θ − Δ/2 ≤ log R_{m,n} ≤ θ`, moment bounds and
  `d_TV(D, Poisson(θ)) ≤ min{1, 2Δ}`, with `θ = ((m−1)/2)(1−1/m)^n`;
- **Theorem 13.1** for every path `n(m)`: degenerate, Poisson or Gaussian
  as `c_m = n/m − log m` tends to `+∞`, `c` or `−∞`; at
  `n = m(log m + c)`, `D → Poisson(e^{−c}/2)` and `R_{m,n} → exp(e^{−c}/2)`;
- **Theorem 14.1** a uniform lattice Edgeworth expansion of `P(D = k)` to
  every fixed order at the exact cumulants, with constants independent of
  `(m, n)`, whenever `Var D → ∞`;
- **Theorem 15.1** a complete expansion of `A_{m,n}` and of the defect
  generating function in the window `n = m(log m + O(1))`, error
  `O((1+r)^{J+1}/m^{J+1})`, with a finite rational algorithm for the
  coefficients; **(16.1)–(16.10), Proposition 16.1** explicit first
  corrections, and defects that are doubletons with probability
  `1 − 2λ²/(3m) + O((1+r)²/m²)`;
- **Theorem 17.1** the inverse `t_q = mℓ + τ_0 + τ_1/m + …`,
  `ℓ = log(m/(2β))`, `β = −log q`, for the real exponent at which the
  all-singleton probability equals `q`, to every fixed order, and the exact
  certificate `N_{1/e}(1000) = 6207`;
- **Corollary 18.1** the diagonal local limit theorem
  `P(K_n = k) = (σ√n)^{−1} φ((k − μn − μ_0)/(σ√n)) + O(1/n)` uniformly in
  `k`, with Part I's constants.

The write of Part II added (5 October 2026, `[write]`-tagged, with proofs):
a proof of the degree bound `deg_ℓ τ_h ≤ h + 1` that the manuscript only
sketches and that Theorem 17.1's error term needs; a proof that the count
half of the growing Poisson window is sharp (`R_{m,n} e^{−λ} → 1` with
`λ ≥ λ_0 > 0` iff `λ²(1+r)/m → 0`); and the third inverse coefficient
`τ_2`, computed from the shipped coefficients.

## What is not claimed

Every limitation and priority caveat of both deliveries is kept in the
article:

- The leading equivalent is Kotěšovec's (OEIS, 9 August 2018) and the growth
  constant was identified in 2013; neither is claimed as new. The methods are
  standard analytic saddle / ACSV methods; Khera–Lundberg–Melczer (lonesum
  matrices, a different denominator) is credited for directional and
  higher-order expansions. **No global novelty claim is made.**
- No least period in (7.1), and no strengthening of the prime-power case to
  `n ≥ 1` (the audit notes `a_1 = 1` and `a_3 = 211` differ mod 4).
- No canonical transseries sectors and no secondary-saddle expansion: the
  strip decomposition of Section 2 is exact but not claimed canonical, and a
  fixed-order truncation of (4.1) has algebraic, not exponential, error.
- Part I makes no growing-direction or boundary-uniform statement
  (`m/n → 0` or `∞`). *[Updated 5 October 2026: Part II proves boundary
  results on the `m/n → 0` side (Theorems 12.1, 13.1, 15.1) and
  distributional results wherever the variance diverges, including
  `m/n → ∞`; it proves no count asymptotics for `m/n → ∞` and no
  approximation joining its window to (3.5) (Question 20.3).]*
- Part I proves no local limit theorem, Edgeworth terms or large deviations
  for the block count. *[Updated 5 October 2026: Part II proves the local
  limit theorem on the diagonal (Corollary 18.1) and Edgeworth expansions to
  every fixed order at exact cumulants (Theorem 14.1). Still not proved: the
  Edgeworth terms in fixed diagonal constants (Question 20.8), growing
  marking ranges, and any large-deviation estimate.]*
- The O-constants of (3.5) and (5.1)–(5.4) are existence constants, not
  certified finite-input bounds; rounding a real inverse alone does not
  settle an integer boundary. The same holds for Part II's Theorems 15.1 and
  17.1; only the threshold certificate `N_{1/e}(1000) = 6207` is exact.
- The quadratures and 80/120-digit computations of the checks are
  high-precision diagnostics, not interval certificates. The finite checks
  do not replace the analytic proofs or verify their infinite quantifiers.
- The four questions of Section 8 are open. *[Updated 5 October 2026:
  Questions 2 and 4 are answered in part by Part II, as the dated notes at
  them say; Questions 1 and 3 are untouched.]*
- Part II: "all orders" means every fixed order with a proved remainder,
  not convergence, Borel summability, uniformity in `J`, exponential
  completeness or a Stokes analysis; its "transseries" (subtitle, name of
  Theorem 17.1) are power–logarithmic expansions of logarithmic depth one,
  which a dated note records; real-rootedness is proved for integer `n` only
  and is not used for the real-exponent inverse; the Bernoulli variables are
  distributional, not visible choices; Theorem 14.1's error is absolute, not
  a large-deviation estimate; replacing `M, V` by `θ` is not valid in
  general (Remark 13.2); interlacing (Liu–Wang) and Poisson approximation
  (Le Cam) are classical; no worldwide priority and no new general method;
  the coefficient generator's refusal of orders above 8 is a practical
  guard, and its order-4 output an example, not a complexity claim; the
  six questions 20.1–20.6, and the two added by the write (20.7: the
  total-variation half of the growing window; 20.8: fixed-constant
  diagonal Edgeworth terms), are open.
- Both deliveries' repository searches are scoped nonduplication evidence,
  not proofs of absence; no OEIS submission or other external write was
  made.

## Labels and the writes

Every label carries the prefix `a122:`. **15 → 137** in the batch-98 write.

*Part I (batch 77).* The 14 delivered labels were pandoc-generated section
names (`results-and-attribution`, `proof`, …); they were prefixed before
anything cited them (nothing did), and the write added one,
`a122:provenance`: **14 → 15**. Section and equation numbers are the
manuscript's own, typed by hand (`secnumdepth` is 0; tags such as (2.1) are
fixed `\tag`s), and none changed. No statement, proof or number of the
manuscript was changed and no symbol renamed.

Six `[write]` notes were added (all of 2 October 2026):

1. a new unnumbered section *Provenance, status and reading conventions*
   (after *Results and attribution*): provenance, pin, status, the audit;
2. in the same section, a table of the letters the manuscript reuses (`p`
   for `1/(1+e^z)`, for `x/y` and for a prime; `r` for a Taylor index, a
   Newton count, a prime-power exponent and the OEIS constant; `x, y`; `a`;
   `m`; `C, C_J, E_J`; `μ`; `D`);
3. after (5.2): the initializer is an instance of the inverse-Gamma core
   `p6:sec:gamma` (`p6:eq:gamma-core-eq` with `T = √D N`, `R = √D L/2`) of
   the transseries volume, kin to `p6:lem:core` and `p2:thm:multi-scaling`;
   only the core is shared;
4. at the end of Section 5: the rounding remarks are `p0:thm:staircase`
   (1)–(2), whose generic arithmetic is formalized (below);
5. after the proof of (7.1): Bala's credit, the formalized surjection
   formula, the secant-number neighbour;
6. after the source list: what A317855 is (checked on 2 October 2026), the
   shipped names of the scripts, and the Fubini row `n = 0`.

*Part II (batch 98, 5 October 2026).* The batch-98 write made the existing
text Part I without changing any of its labels, values or numbers (the
`.aux` of the committed text and of the new build agree on all 15), and
added dated `[write]` notes to Part I: after the abstract (the two Parts),
after (3.5) and at the end of Section 6 (the two non-claims Part II
answers in part), at Questions 2 and 4 (answered in part), and after the
source notes (the Fubini row `n = 0` in Part II). Part II carries the
sub-prefix `a122:pd:`: the manuscript's 111 labels, prefixed, and 11 new
ones (`a122:pd:part`, `a122:pd:front`, `a122:pd:rem:allorders` and eight
question labels `a122:pd:q:*`).

Part II's numbering is the manuscript's plus eight: manuscript Section `k`
is Section `k + 8`, and every equation, theorem, lemma, corollary,
proposition, remark and question number inside it shifts with it (the
manuscript's (4.10) is (12.10), its Theorem 9.1 is Theorem 17.1);
Appendices A–B and Tables 1–2 keep their names. A build of the delivered
manuscript and of this article agree on all 111 label values under this
shift. Part II's front matter (unnumbered) prints the manuscript's abstract
and status paragraph, a provenance note, a status and scope note, and a
reading-conventions note with two tables: the letters Part II shares with
Part I (`λ`, `D`, `r`, `θ`, `R`, `d_j`, `c`, `L`, `p`, `x`, `q`, `M`, `V`,
`H`, `N`, `C`, `w`, `B`) and the **symbols the write renamed** to resolve
clashes inside the manuscript, with no change of normalization:

| Part II | manuscript | clash |
|---|---|---|
| `ψ(t) = (e^t − 1)/t` | `h(t)` | `h` is the expansion index |
| `Λ(t) = log ψ(t)`, coefficients `γ_a` | `L(t)`, `ℓ_a` | `L_h`; `ℓ = log(m/(2β))` |
| `𝓔_h`, `𝓑_h` | `E_h`, `B_h` | `E_±`; `B`, `B_{2a}` |
| `ξ_i` (Bernoulli variables) | `B_i` | Bernoulli numbers |
| `\|b\| = Σ b_a`; product index `g` | `B`; `ℓ` | `B` as above; `ℓ = log(m/(2β))` |
| `𝖳_a` (Touchard) | `T_a` | `T_{m,k} = k! S(m,k)` |
| `[λ_−, λ_+]`, `O_{λ±,…}` | `[a, b]`, `O_{a,b,…}` | indices `a`, `b`, profile `b_a` |
| `𝓜_h` | `M_h` | `M = E D` |
| `τ_h(β, ℓ)` (inverse corrections) | `d_h(β, ℓ)` | `d_j(m)`: the manuscript's `d_0`, `d_1` had two meanings |
| `η` (envelope error) | `E` | `E_±`, `𝓔_h` |

Label keys keep the manuscript's names (`a122:pd:eq:d0` is `τ_0`); the
programs and data files keep the delivered names (`d0`, `d1`, `e_lower`,
`e_upper`).

Other changes to the delivered text, all disclosed in the article: the
shipped names of the two `\input` tables; the title of Section 20
("Further research questions" → "Further questions and research");
bibliography item [3] corrected (below); three bibliography items added
(Frobenius 1910, Harper 1967, Barbour–Hall 1984, marked `[write]`, not
consulted by the write); `\texttt` → `\nolinkurl` for three file names so
that they break at line ends; and, in the preamble, cleveref type aliases:
the delivered PDF printed "theorem 7.2" for Lemma 7.2 and "theorem" for
every lemma, corollary and question, because the environments share the
theorem counter; this build prints "lemma 15.2", "corollary 11.2",
"question 20.6".

`[write]` notes in Part II (all of 5 October 2026):

1. Section 9: "the earlier report" is Part I; the two missing credits
   (Frobenius for the case `n = 0`, via `P_{m,0}(u) = u^m A_m(1 + 1/u)`
   with the Eulerian polynomial `A_m`; Harper for the
   real-roots-to-Bernoulli method);
2. after Corollary 11.2: formal status (below);
3. Section 12.1: proof that the count half of the growing window is sharp;
4. after Remark 15.3: "transseries" in the subtitle and in the name of
   Theorem 17.1 overstates a power–logarithmic expansion of depth one;
5. in the proof of Theorem 17.1: proof of `deg_ℓ τ_h ≤ h + 1`, and `τ_2`
   with a numerical check (it lowers the last error of Table 2 at
   `m = 1000` from `1.38e-4` to `−1.5e-6`);
6. Section 17.1: "for sufficiently large `m`" is superfluous in the
   envelope statement;
7. after Corollary 18.1: its last sentence is a sketch, moved to Question
   20.8; the corollary answers Part I's Question 4 in part;
8. Section 19.5: shipped names, the write's replay, and the precision
   audit (below);
9. Section 20: what the write added; Question 20.4: evidence that the
   block polynomial stays real-rooted for real exponents (95 cases,
   `t ∈ {0.5, 1.5, 2.25, 3.3, 7.7}`, `m ≤ 20`; evidence only, script not
   shipped);
10. Appendix B: the pin, the shipped name of `SOURCE_AUDIT.md`, the
    neighbour `a261781-matrix-compositions`;
11. bibliography item [3].

**Standing rule (4 October 2026).** No statement of manuscript 11 was found
false. Moved to *Further questions and research*: the sharpness of the
growing Poisson window (the manuscript asserts none; the write proves the
count half, and the total-variation half is Question 20.7, with a
Barbour–Hall sketch suggesting `λ^{3/2}(1+r)/m → 0` suffices) and the
fixed-constant diagonal Edgeworth terms (Corollary 18.1's last sentence,
Question 20.8). The sketched degree bound was proved instead of moved.
Corrected on record: the word "transseries"; "for sufficiently large m";
bibliography item [3].

**Bibliography item [3].** The delivered item cited Part I as "Vladimir
Reshetnikov, ProveIt repository, …" with the disclaimer that it "names the
repository owner, not an inferred personal authorship". Part I's delivery
names no author, so the corrected item names none; the delivered wording is
quoted in the article.

## Files

```text
README.md                                         this guide (replaces both delivery READMEs)
article.tex                                       the report (Part I delivered as a122399-report.tex; Part II from manuscript 11's article.tex)
article.pdf                                       compiled report, 37 pages
proof.md                                          Part I: the delivered pre-layout Markdown source
source_review.md                                  Part I: the delivery's literature and repository-search record (1 Oct 2026)
quality_checks.md                                 Part I: the delivery's release checklist
audit-independent_audit.md                        Part I: the delivery's independent mathematical audit
02-poisson-defects-SOURCE_AUDIT.md                Part II: the delivery's source and dependency audit (delivered as SOURCE_AUDIT.md)
code/check_a122399.py                             Part I producer: exact rational phase, saddle coefficients, exact comparisons to n = 800
code/export_exact_coefficients.py                 Part I producer: exact rational corrections through order four (reads phase_coefficients.txt)
code/verify_contour_inverse.py                    Part I producer: 9 contour/tail checks, 40 inverse checks (reads numerical_results.json)
code/verify_congruences.py                        Part I producer: 1621 congruences of (7.1) in 23 prime-power cases
code/audit-independent_audit.py                   Part I: the independent audit's script (delivered as audit/independent_audit.py)
code/make_report.py                               Part I delivery-state tool: proof.md -> a122399-report.tex via pandoc
code/audit-check_transcription.py                 Part I delivery-state tool: proof.md vs a122399-report.tex (delivered as audit/check_transcription.py)
code/build.sh                                     Part I delivery-state tool: builds a122399-report.pdf
code/verify_all.sh                                Part I delivery-state tool: the full replay, in place
code/02-poisson-defects-coefficients.py           Part II: exact rational coefficients p_h, c_h, L_h and tau_0, tau_1 (default order 4, refuses > 8)
code/02-poisson-defects-verify.py                 Part II: 85 coefficient identities, 50 Sturm root counts, 272 moment-bound instances, 15 OEIS terms, inverse residual
code/02-poisson-defects-numerics.py               Part II: 18 critical-window, 12 inverse and 6 local-law cases (mpmath, --dps 80)
code/02-poisson-defects-certify_threshold.py      Part II: exact proof of N_{1/e}(1000) = 6207 (standard library only)
code/02-poisson-defects-Makefile                  Part II delivery-state tool: the delivered make targets (python3, pdflatex article.tex)
data/test_output.txt                              Part I: recorded stdout of check_a122399.py
data/numerical_results.json                       Part I: written by check_a122399.py
data/phase_coefficients.txt                       Part I: written by check_a122399.py (f_0 ... f_16)
data/exact_coefficients.txt                       Part I: written by export_exact_coefficients.py
data/contour_inverse_output.txt                   Part I: recorded stdout of verify_contour_inverse.py
data/contour_inverse_results.json                 Part I: written by verify_contour_inverse.py
data/congruence_results.json                      Part I: written by verify_congruences.py (23 cases)
data/audit-independent_audit_output.txt           Part I: recorded stdout of the audit script
data/audit-independent_audit_results.json         Part I: written by the audit script
data/audit-transcription_checks.json              Part I: written by check_transcription.py (31 displays, 182 inline)
data/audit-reviewed_hashes.json                   Part I: the audit's hash record of the delivery-state files
data/02-poisson-defects-coefficients.json         Part II: written by coefficients.py (P, C, L through order 4; inverse)
data/02-poisson-defects-coefficients.txt          Part II: written by coefficients.py (same, as text)
data/02-poisson-defects-critical_table.tex        Part II: written by numerics.py; Table 1 of the article
data/02-poisson-defects-inverse_table.tex         Part II: written by numerics.py; Table 2 of the article
data/02-poisson-defects-critical_window.csv       Part II: written by numerics.py (18 rows; CRLF, kept by .gitattributes)
data/02-poisson-defects-inverse.csv               Part II: written by numerics.py (12 rows; CRLF, kept by .gitattributes)
data/02-poisson-defects-local_limits.csv          Part II: written by numerics.py (6 rows; CRLF, kept by .gitattributes)
data/02-poisson-defects-numerical_environment.json  Part II: written by numerics.py (versions of the delivered run)
data/02-poisson-defects-verification.json         Part II: written by verify.py
data/02-poisson-defects-threshold_certificate.json  Part II: written by certify_threshold.py
data/02-poisson-defects-precision_audit.json      Part II: the 80- vs 120-digit comparison record; written by NO shipped program
data/02-poisson-defects-requirements.txt          Part II: sympy==1.14.0, mpmath==1.3.0 (delivered as requirements.txt)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. `article.tex` at the placement commit
`f76fcb566` is the delivered `a122399-report.tex` byte for byte; the
batch-77 write changed only labels and added notes, and the batch-98 write
added Part II and dated notes.

**Not shipped** (all survive in the arrival commits, see below). Part I:
the delivered README (replaced by this guide; its reproduction notes are
folded in here), the delivered 8-page PDF, `SHA256SUMS` (verified 28/28 at
placement and retired), and `audit/report-extracted.txt` (27,662 bytes of
text extracted from the delivered PDF; read by no script, and stale once
the article is rebuilt). Part II: the delivered `article.tex` (printed as
Part II), its 22-page PDF, its README (folded in here) and
`MANIFEST.sha256` (verified 21/21 at placement and retired).

**Delivered text that uses delivery names.** Part I's delivery was a flat
directory with an `audit/` subdirectory. Placement moved scripts to `code/`
and outputs to `data/`, and flattened `audit/X` to `audit-X`. Text still
naming the delivery layout: the article's source list (items 4–7; a
`[write]` note gives the shipped names), `proof.md` (same list),
`quality_checks.md` (`audit/independent_audit.md`),
`audit-independent_audit.md` (`independent_audit.py`,
`independent_audit_results.json`, `reviewed_hashes.json`,
`check_transcription.py`, `python audit/independent_audit.py`), and every
script: each reads and writes files **next to itself**, and the audit script
reads the producer outputs from its parent directory. `make_report.py`,
`build.sh`, `audit-check_transcription.py` and `verify_all.sh` name
`a122399-report.tex`/`.pdf` and `proof.md`.
Part II's delivery had `code/` and `data/` subdirectories; placement added
the prefix `02-poisson-defects-` and moved `requirements.txt` to `data/`,
`Makefile` to `code/` and `SOURCE_AUDIT.md` to the report root. Still naming
the delivered layout: Section 19 of the article (a `[write]` note gives the
shipped names), Appendix A (`data/coefficients.txt`, `data/coefficients.json`),
`02-poisson-defects-SOURCE_AUDIT.md`, the Makefile (`code/*.py`,
`python3`, `pdflatex article.tex`), and the four programs: `verify.py` and
`numerics.py` import `coefficients` and `verify` by their delivered module
names, and all four write `data/<delivered name>` next to their parent
directory.

**Stale delivery records.** `data/audit-reviewed_hashes.json`,
`data/audit-transcription_checks.json` and `quality_checks.md` record
SHA-256 values of the delivered README, TeX and PDF. The README and the
article have since been rewritten and the PDF rebuilt, so those three
entries no longer match shipped files; the code and data entries describe
the delivered bytes, which are shipped unchanged. The audit's statements are
about the delivered mathematics, which the article prints unchanged.
`data/02-poisson-defects-precision_audit.json` records a comparison of
80- and 120-digit runs that no shipped program performs (the comparison
script was not delivered); the write repeated it with its own script (see
below), so it is a reproduced record, not a program output.

## Relation to the repository

**Formal status.** Placement beside the collection's other reports, and
near the Lean developments named here, confers no formal status. No A122399
statement is formalized anywhere in the repository: not (7.1), not the
asymptotic, not the CLT, and nothing of Part II (no real-rootedness,
interlacing, Bernoulli factorization or Poisson bound). What is formalized
are generic ingredients:

- `Fabius.factorial_mul_stirlingSecond_eq_sum`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/StirlingBasisChange.lean`),
  the surjection formula `k! S(n,k) = Σ_j (−1)^(k−j) C(k,j) j^n` used in the
  proof of (7.1). With Euler's theorem (Mathlib's `Nat.ModEq.pow_totient`)
  it makes (7.1) a small formalization target; none exists.
- `Fabius.fubini` (`Analysis/FabiusFunction/Lean/FabiusFunction/OrderedBell.lean`),
  the Fubini numbers `Σ_k k! S(m,k)`, which are the row `A_{m,0}` of the
  report's two-size array.
- `Fabius.permutohedron_h_polynomial`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/EulerianPermutohedron.lean`),
  `Σ_k k! S(n,k) (X−1)^{n−k} = A_n(X)`, the substitution that turns Part II's
  Theorem 11.1 at `n = 0` into Frobenius's theorem; the real-rootedness
  itself is not formalized (Part II's Question 20.6 asks for that layer).
- `Fabius.staircase_ceil`, `Fabius.staircase_separation`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`),
  generic rounding facts for a strictly monotone interpolation; they give no
  formal status to (5.1)–(5.4), or to Part II's (17.10).

**An instance of repository results, with no novelty claimed for the
method.** The inverse initializer (5.2) solves the core equation
`T(log T − 1) = R` of the inverse-Gamma section `p6:sec:gamma`
(`p6:eq:gamma-core-eq`; general block `p6:lem:core`, scaled family
`p2:thm:multi-scaling`) with `T = √D N`, `R = √D log A / 2`, and the rounding
remarks after (5.4) are `p0:thm:staircase` (1)–(2), all in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
Only the core is shared; the report's own all-orders inverse is `ν_J` of
(5.1). The main expansion is a single-scale Poincaré series, not a
transseries, which is why the report sits in this collection and not in
`Analysis/Transseries`. Part II's expansions are power–logarithmic (depth
one, no exponentially small terms), and its inverse of Section 17 is an
explicit logarithmic inversion, not the inverse-Gamma core; so Part II too
stays here (the `5a69916e8` precedent). The same volume's chapter
`q2:sec:fubini` (`q2:thm:fubini`) gives the exact pole-lattice formula for
the Fubini row `n = 0`, which lies outside the compact-direction theorem
(3.5); Part II covers that row only qualitatively (real zeros, Gaussian
local laws).

**Neighbouring reports.**
`oeis-sequence-asymptotics/a277364-bell-asymptotics` treats another
Stirling sum, `Σ_{k ≤ n/2} S(n,k) ~ B_n`, by classical Bell/Stirling saddle
methods: same genre, different sequence and constants, no shared theorem.
`congruences-and-valuations/secant-number-periodicity` classifies when the
secant numbers A000364 are periodic modulo `m`, where the analogous OEIS
conjecture (period dividing `φ(m)`, pure from index one) fails; (7.1) is a
sibling in kind, with no shared result.
`oeis-sequence-asymptotics/a261781-matrix-compositions` (Part II there)
proves a Poisson limit for "Stirling defects" (`mxc:tp:thm:defect`) and a
Touchard-summed coverage-window expansion to every order
(`mxc:tp:thm:couponall`) for a different array: the same mechanism as Part
II here (defects made of pairs, weight `1/2!`), no shared theorem. (These
pointers are made here only; those reports are not edited by these writes.)

**Stale sentences.** `proof.md:9` (not printed in the article) and
`source_review.md` say that a search of the repository index found no
A122399 or A317855 match. That was true on 1 October 2026; the only match
now is this report. `02-poisson-defects-SOURCE_AUDIT.md` says that a scoped
search `A122399 Poisson` found no defect–Poisson transition; true of this
report then, while `a261781-matrix-compositions` has one for another array
(above).

## Rerun the checks (on scratch copies in the delivered layouts)

### Part I

The scripts read and write next to themselves, so running them from `code/`
would fail (inputs are in `data/`), and copying them into `data/` would
overwrite shipped outputs. Recreate the delivered layout in a scratch
directory (Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir "$R/audit"
cp code/check_a122399.py code/export_exact_coefficients.py \
   code/verify_contour_inverse.py code/verify_congruences.py "$R"
cp code/audit-independent_audit.py "$R/audit/independent_audit.py"
cd "$R" && export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY check_a122399.py > test_output.txt          # writes numerical_results.json, phase_coefficients.txt
$PY export_exact_coefficients.py                # writes exact_coefficients.txt
$PY verify_contour_inverse.py > contour_inverse_output.txt
$PY verify_congruences.py                       # writes congruence_results.json
$PY audit/independent_audit.py > audit/independent_audit_output.txt
```

Run them in this order (each later script reads an earlier one's output),
then compare with `diff --strip-trailing-cr` against `data/` (Windows writes
CRLF; the shipped files are LF). The delivery used Python 3.12, mpmath 1.3.0
and SymPy 1.14.0. At placement (2 October 2026, on a heavily loaded machine)
the four producer scripts took 134 s, 64 s, 137 s and 88 s, all passed, and
all seven outputs came out identical to the shipped ones modulo line
endings. **The audit script was not replayed**: it was stopped at a
170-second cap without output, so expect several minutes; its shipped
output reports PASS with largest coefficient discrepancy `2.5e-80`.

**Delivery-state tools.** `make_report.py`, `audit-check_transcription.py`,
`build.sh` and `verify_all.sh` reproduce the **delivered** TeX and PDF, not
this `article.tex`: `make_report.py` regenerates `a122399-report.tex` from
`proof.md` with pandoc (and would overwrite a file of that name),
`check_transcription.py` asserts exactly 31 displays and reads
`a122399-report.tex` by name, and `verify_all.sh` calls bare `python` and
rewrites every output, the TeX and the PDF in place. Never run them in this
directory. `check_transcription.py` also hashes the delivered PDF, which is
not shipped, so replay both tools inside an extraction of the archive (see
*Retrieving the excluded delivery files*):

```sh
cd a122399-delivery/oeis-a122399-research
py make_report.py && py audit/check_transcription.py
```

On 2 October 2026, with pandoc 3.9.0.2, this regenerated
`a122399-report.tex` identical, modulo CRLF line endings, to the delivered
file and hence to `article.tex` as placed in `f76fcb566`, and the check
passed (31 displays, 182 inline expressions, 3 new).

### Part II

The programs import each other by their delivered names and write
`data/<delivered name>` beside their own `code/` directory, overwriting the
recorded outputs. Never run them here. Rebuild the delivered layout in a
scratch directory (Git Bash, from this directory):

```sh
R=$(mktemp -d) && mkdir "$R/code" "$R/data"
for f in code/02-poisson-defects-*.py; do cp "$f" "$R/code/${f#code/02-poisson-defects-}"; done
for f in data/02-poisson-defects-*; do cp "$f" "$R/data/${f#data/02-poisson-defects-}"; done
cd "$R" && export PYTHONUTF8=1
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY code/coefficients.py --order 4     # writes data/coefficients.{json,txt}
$PY code/verify.py                     # writes data/verification.json
$PY code/numerics.py --dps 80          # writes the three CSVs, both tables, numerical_environment.json
$PY code/certify_threshold.py          # writes data/threshold_certificate.json
```

then compare each `data/` file with the shipped one (`diff
--strip-trailing-cr`). On 5 October 2026 (Windows, CPython 3.13.5, on a
loaded machine) the four programs passed in 5 s, 170 s, 19 s and 2 s; the
three CSVs came out byte-identical (Python's `csv` module writes CRLF on
every platform, which is why the shipped CSVs are CRLF and kept so by
`SetTheory/Cardinals/.gitattributes`); the other outputs were identical up
to line endings, except the Python version string in
`numerical_environment.json` (the delivery ran CPython 3.13.5 under GCC on
Linux). The copy also carries the shipped `precision_audit.json` and
`requirements.txt`, which no program rewrites. `numerics.py --dps 120` in a
second copy, compared field by field with the shipped 80-digit CSVs, gave
306, 84 and 42 equal fields (432 in all) besides the 12 root residuals, 11
of which differ: the record in `precision_audit.json`, reproduced. The
delivered `Makefile` (`code/02-poisson-defects-Makefile`) runs the same
commands with `python3` and then builds the delivered `article.tex`, which
is not shipped; GNU make is not installed on this machine.

OEIS data: `code/02-poisson-defects-verify.py` embeds the first 15 terms of
A122399 (from the OEIS, CC BY-SA 4.0), which it also recomputes exactly.

## Build the PDF

pdfLaTeX with geometry, fontenc (T1), lmodern, microtype, amsmath/amssymb/amsthm,
float, hyperref, xurl, enumitem, booktabs, array, and, for Part II,
mathtools, longtable and cleveref. Part II reads
`data/02-poisson-defects-critical_table.tex` and
`data/02-poisson-defects-inverse_table.tex`. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 37 pages, no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull or underfull boxes, and no LaTeX or package
warnings. The log carries 684 `fontmap entry ... already exists, duplicates
ignored` warnings from the delivered preamble's `\pdfmapfile{+lm.map}`
lines (MiKTeX already loads those maps); the committed text before Part II
gives the same 684 (and 10 pages). The delivered Part II manuscript uses
newtx fonts and builds to 22 pages; here it is set in the report's Latin
Modern.

## Retrieving the excluded delivery files

In a scratch directory:

```sh
git -C <repository root> show 096ee7b87:docs/incoming/oeis-a122399-research.zip > a122399.zip
unzip a122399.zip -d a122399-delivery   # files under oeis-a122399-research/
git -C <repository root> show 2172df76a:docs/incoming/A122399_Boundary_Transitions_and_Inversion.zip > a122399-pd.zip
unzip a122399-pd.zip -d a122399-pd-delivery   # files under A122399_Boundary_Transitions/
```

The first archive (395,389 bytes) holds Part I's delivered README, PDF,
`SHA256SUMS` and `audit/report-extracted.txt` besides the shipped files. The
second (351,864 bytes) holds Part II's delivered `article.tex`, its PDF,
README and `MANIFEST.sha256` besides the shipped files, in the delivered
layout, where the programs can be run as delivered.

## Provenance

- Two manuscripts. Part I: batch 77, manuscript 35
  (`oeis-a122399-research.zip`), arrival `096ee7b87`, placement `f76fcb566`,
  written in the batch-77 write phase (2 October 2026). Part II: batch 98,
  manuscript 11 (`A122399_Boundary_Transitions_and_Inversion.zip`), arrival
  `2172df76a`, placement `9353a7171`, written in the batch-98 write phase
  (5 October 2026). No merge: Part II re-proves nothing of Part I (it
  restates Part I's counting model and generating function and quotes its
  diagonal constants), so there were no merge choices.
- Pins: none for Part I's delivery; `proof.md:9` and `source_review.md`
  record a scoped search of the public repository index on 1 October 2026
  at commit `76c0887a6`. Part II's delivery pins tree `0f93381e8` and the
  `proof.md` blob `6f03a8be2`, both current at placement.
- External sources (as delivered): OEIS A122399 (inspected 1 and 4 October
  2026) and A317855; Khera, Lundberg, Melczer, *Asymptotic Enumeration of
  Lonesum Matrices*, Adv. Appl. Math. 123 (2021), 102118, arXiv:1912.08850;
  Liu and Wang, Adv. Appl. Math. 38 (2007); Le Cam, Pacific J. Math. 10
  (1960). Added by the batch-98 write, not consulted: Frobenius (1910),
  Harper (1967), Barbour and Hall (1984). The A317855 identification and
  Bala's credit were checked on the OEIS on 2 October 2026.
