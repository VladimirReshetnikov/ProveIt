# Asymptotics and Inverses for a Stable Hilbert Series

**All-orders coefficient asymptotics, an exact modular factorization and a range inverse for [qⁿ] ∏(1 + qᵏ/(1 − q)): OEIS A126348**

A research report dated 1 October 2026, built from one manuscript. Its
author line is empty.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 84 | batch 100, bundle Report 84 | `ProveIt_A126348_Hilbert_Asymptotics_and_Inverses.zip` (389,913 bytes; wrapper `A126348_Hilbert_Asymptotics_and_Inverses/`; main file `article.tex`, 450 lines, 7-page PDF) | `1512ef835` (the snapshot its source audit checked) | `36571ae0e` (arrival `60f54ea06`) | the whole article, Sections 1–8 |

**Status: AI-assisted delivery channel, unrefereed, not formalized.** The
report entered the collection through `docs/incoming`; it has not been
refereed, and no statement of it is formalized in Lean or Rocq. The
delivery's `PROVENANCE.json` (not shipped) records its status as:
"Analytic proof, independent coefficient reconstruction, and final article
transcription reviewed; numerical onset not certified." That review is the
delivery pipeline's own (`AUDIT.md`), not external peer review.

For `F(q) = ∏_{k≥1}(1 + qᵏ/(1 − q)) = Σ aₙ qⁿ` (A126348: 1, 1, 2, 4, 7,
12, 20, …), with `c = π²/6`, `A = L²/2 + L + c`, `B = L² + L + 2c`,
`V = L² + 3L + 2c + 1` and the saddle `n = e^{2L} A(L)`, `t = e^{−L}`, the
article proves:

- **Theorem 1.1** a relative all-orders expansion
  `aₙ = exp{e^L B − 1}/√(2π e^{3L} V) · (Σ_{j≤J} e^{−jL} C_j(L) + O_J(e^{−(J+1)L}(1+L)^{J+1}))`
  with rational `C_j ∈ ℚ(c, L)`, `C_j = O((1+L)^j)`, and explicit `C_1`,
  `C_2` (7), (8);
- **Theorem 2.1** the exact factorization `F(e^{−t}) = e^{K(t)} Θ(u,t)/(Q;Q)_∞`
  and the exact convergent sector expansion (13)–(14) of the theta
  quotient, with amplitudes `D_r(u)` built from partition numbers. The
  factorization itself is **not new**: it is the exact Jacobi identity (11)
  of `a291698-moving-fugacity-partitions` at the fugacity `u = 1/(1 − q)`
  (below);
- **Section 3 and Lemma 3.1** the uniform power-log expansion (15) of
  `log F` with `P_1, …, P_6`, valid on a complex neighbourhood;
- **Section 4** a minor-arc bound (16) with **no resonance sectors** (the
  fugacity is large only near `q = 1`), and the coefficient extraction;
- **Section 5** a finite exact rule (17) for every `C_j`;
- **Theorem 6.1** an explicit range inverse
  `N̂(Y) = N_0 + e^L T + (T² + 2TT')/(2V) − C_1(L)` on the carrier
  `log Y = e^L B(L)`, with `N̂(aₙ) = n + O(e^{−L}(1+L)³)` (the proof gives
  `(1+L)²`), so nearest-integer rounding recovers `n`;
- **Section 7** `aₙ > aₙ₋₁` for `n ≥ 2`, and the threshold
  `N(Y) = min{n : aₙ ≥ Y}` in an eventual two-candidate ceiling bracket.

## What is not claimed

Every limitation of the delivery is kept in the article:

- All statements are **eventual**: no effective onset `n₀`, no explicit
  constants. The numerical table and checks are "diagnostics, not an
  effective-onset certificate"; nothing is interval-certified.
- **No exact interpolation** of the sequence, **no coefficient-level
  exponentially small sectors, no Stokes classification.** The modular
  sectors of Theorem 2.1 belong to the generating function and "do not by
  themselves identify exponentially small coefficient sectors".
- The convergent exact `j`-series for `G` is not a convergent power-log
  expansion at `t = 0`; the power-log statements are finite-truncation
  asymptotics.
- Formal inversion, range inversion, the threshold staircase and inversion
  of an exact continuous interpolation are different objects; only the
  first three are treated. A single ceiling needs a separation check; at
  `Y = aₙ` use nearest-integer rounding.
- **No exhaustive-absence or priority claim:** "A bounded literature search
  did not locate a published coefficient or inverse-growth theorem for
  A126348; this does not assert exhaustive absence." The uniform
  corollary of Arabi Ardehali–Rosengren (2026) does not apply directly
  (moving fugacity), and McIntosh (1999) was seen only in its abstract
  (`source_audit.md`).

**Unproved statements of the manuscript** (standing rule of 4 October 2026)
are recorded in the new **Section 9, "Further questions and research"**:

1. *Question 9.1*: each deep truncation of the formal reversion (21) is a
   controlled range inverse — asserted, not written out;
2. *Question 9.2*: the next inverse correction `e^{−L} B_1` — stated without
   proof; the intake's numerical support (errors at n = 100, 1000, 10000
   fall from −0.0505, −0.0155, −0.0052 to 0.0088, 0.00095, 0.00011) is
   evidence only;
3. *Question 9.3*: "inverse-`L_0` corrections account for the rest of `B`"
   — **settled at this write**: the carrier root is `L = L_0 + Σ d_k L_0^{−k}`,
   a convergent series (implicit function theorem), `d_1 = −1`,
   `d_2 = 5/2 − π²/3`, `d_3 = π² − 19/3`, `d_4 = π⁴/18 − 10π²/3 + 209/12`;
4. *Questions 9.4–9.6*: effective onset; exponentially small coefficient
   sectors and Stokes data; an exact interpolation.

No claim of the manuscript was found to be wrong. One sketched step was
completed at this write: the dual Euler-product bound and the logarithm
branches in the proof of Lemma 3.1 (a `[write]` note at the end of
Section 3).

## Labels and the write

Every label carries the prefix `shs:`. The 29 delivered labels (`eq:`,
`thm:`, `lem:`, `sec:`) were bare; nothing cited them, and they were
prefixed. The write added eight (`shs:provenance`, `shs:questions`,
`shs:q:allorders`, `shs:q:B1`, `shs:q:lambert`, `shs:q:onset`,
`shs:q:sectors`, `shs:q:interpolation`): **29 → 37**. No section, theorem
or equation number changed (the `.aux` numbers of all 29 delivered labels
equal those of a build of the delivered text). No statement, proof or
number of the manuscript was changed and no symbol renamed.

The `[write]` notes (all of 5 October 2026):

1. a new subsection 1.1 *Provenance, status and reading conventions*:
   provenance, pin, status, the reruns and intake checks;
2. there, dated corrections to delivered text: the source audit's "no
   A126348, A022629, A266891, A124380 match" was true at its pin but is
   stale (A022629 is `a022629-distinct-partition-norms`, placed
   `9df4ba51a`; A266891 is its Section 20, `aa7345800`; A124380 is
   `a124380-signed-moment-asymptotics`, `4f11bc9c0`); the OEIS *name* of
   A126348 is "Limit of reversed rows of triangle A126347, …", the product
   being one of its generating functions; the delivered README's "exact
   coefficient generation through 10000 is included" means the programs
   generate them (eight values are recorded);
3. there, reading conventions: five readings that need care (the fugacity
   `1/(1 − q)` depends on `q`, not on `n`, and `u` is the theta phase, not
   a fugacity; `Q` is the nome in Section 2 but the phase series in
   Sections 4–5; `N` is `e^{2L}A(L)` in Section 6 but the integer threshold
   in Section 7; the calligraphic `𝒢` (macro `\E`) is a Gaussian moment
   functional, not `G(t)`; `C_1` in the proof of Lemma 3.1 is a constant,
   not `C_1(L)`), and a table of reused letters (`A, B, V`; `c, C`; `D`;
   `E, 𝒢, G`; `H, h`; `K`; `L, t`; `P_j, p`; `Q, R`; `r`; `T`; `u, w`;
   `δ, λ`);
4. after Theorem 2.1: the credit to a291698's identity (11) (below);
5. after Section 3: the completion of the proof of Lemma 3.1;
6. at the end of Section 6: the status of the inverse statements and the
   transseries-volume instances (below);
7. at the end of Section 8: rechecks (OEIS entry on 5 October 2026, the
   five modular-check arguments), the shipped program names, the shared
   Naranjo–Ramírez citation with a022629, and the neighbour a271619;
8. Section 9, *Further questions and research* (above).

## Files

```text
README.md                                 this guide (replaces the delivery README)
article.tex                               the report (delivered as article.tex)
article.pdf                               compiled report, 12 pages
derivation.md                             the delivered expanded derivation (delivery path inputs/derivation.md)
AUDIT.md                                  the delivery's internal analytic review, 1 October 2026 (inputs/AUDIT.md)
source_audit.md                           the delivery's literature, OEIS and repository screen (inputs/source_audit.md)
code/run_checks.sh                        delivery-state driver: runs the seven programs in checks/ (see below)
code/build_local.sh                       delivery-state TeX helper with hard-coded TeX Live paths (see below)
code/derive_symbolic.py                   P_1..P_6 from Euler-Maclaurin; C_1, transcription check of C_2 -> symbolic_results.txt
code/verify_symbolic_independent.py       Gaussian extraction of C_1, C_2 (and C_3), odd cancellation -> gaussian_coefficients.txt, independent_symbolic_results.txt
code/independent_reviewer_check.py        the delivery reviewer's separate reconstruction (P_j, C_1, C_2, carrier identities) -> independent_reviewer_check.json beside itself
code/verify_numeric.py                    exact coefficients to n = 2000 vs Theorem 1.1 with C_1, C_2 -> numeric_results.json
code/verify_inverse.py                    exact coefficients to n = 10000, inverse errors -> inverse_numeric_results.json, coefficients_selected.json
code/verify_product.py                    log F(e^-t) from the product vs (15) with P_1..P_6, t = 0.5..0.02 -> product_numeric_results.json
code/verify_modular.py                    the identity (9) at t = 0.4, 0.7, 1.0, 1.5, 2.0 -> modular_numeric_results.json
data/symbolic_results.txt                 recorded output of derive_symbolic.py
data/gaussian_coefficients.txt            recorded output of verify_symbolic_independent.py (C_1, C_2, C_3)
data/independent_symbolic_results.txt     recorded output of verify_symbolic_independent.py
data/independent_reviewer_check.json      recorded output of independent_reviewer_check.py
data/numeric_results.json                 recorded output of verify_numeric.py
data/inverse_numeric_results.json         recorded output of verify_inverse.py
data/coefficients_selected.json           recorded output of verify_inverse.py (a_n at n = 50, ..., 10000)
data/product_numeric_results.json         recorded output of verify_product.py
data/modular_numeric_results.json         recorded output of verify_modular.py
data/derive_symbolic.replay.log           stdout of derive_symbolic.py under run_checks.sh
data/verify_symbolic_independent.replay.log
data/verify_numeric.replay.log
data/verify_inverse.replay.log
data/verify_product.replay.log
data/verify_modular.replay.log            stdout records of the other programs
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `article.tex` at the placement commit
`36571ae0e` is the delivered `article.tex` byte for byte; the write changed
only labels and added the notes above.

**Not shipped** (all survive in the arrival commit, see below): the
delivered README (replaced by this guide; its content is folded in here),
the 7-page `article.pdf`, `SHA256SUMS` (32 entries, verified 32/32 at
intake), `PROVENANCE.json` (metadata and 31 file hashes, verified; its
status line and environment are quoted here), and
`checks/independent_reviewer_check.replay.log`, a byte copy of
`independent_reviewer_check.json`.

**Delivered text that uses delivery names.** The delivery had the programs
and their outputs together in `checks/`, the drivers at its root and the
notes in `inputs/`. `run_checks.sh` does `cd "$(dirname "$0")/checks"` and
runs `python -O <script>.py > <script>.replay.log`; from `code/` it fails,
and in the delivered layout it overwrites the recorded logs in place.
`build_local.sh` builds `article.tex` beside itself with hard-coded
`/usr/share/texlive/texmf-dist` and `/usr/share/texmf` and copies the PDF
back; it is a generic copy of the session's TeX helper (the same blob is at
twelve other tracked paths) and should not be run here. Six programs write
their outputs into the current directory under fixed names;
`independent_reviewer_check.py` writes `independent_reviewer_check.json`
**beside itself** (`Path(__file__).with_suffix('.json')`), i.e. into
`code/` if run from the shipped layout. `AUDIT.md` names
`check_coefficients.py`, `../derivation.md` and `../package/article.tex`:
these are the shipped `code/independent_reviewer_check.py` (same role and
docstring), `derivation.md` and `article.tex`. The delivered README's
"Contents" names `checks/` and `inputs/`.

## Relation to the repository

**Formal status.** Placement in the collection confers no formal status.
No statement of this report is formalized. The repository has two Lean
ingredients of Theorem 2.1, `Fabius.hasSum_jacobi_triple_product`
(`Analysis/FabiusFunction/Lean/FabiusFunction/JacobiTripleProduct.lean`)
and the eta inversion `Fabius.eta_modularPoint_neg_inv`
(`Analysis/FabiusFunction/Lean/FabiusFunction/QPochhammerModularAsymptotic.lean`);
neither the identity (9) nor anything after it is formalized.

**Theorem 2.1 is a special case of a291698's identity (11).**
`oeis-sequence-asymptotics/a291698-moving-fugacity-partitions` proves, in
its Section 5 (label `mfp:exact-jacobi-decomposition-and-the-finite-sector-proof`),
the exact identity (11) for `∏(1 + u qᵏ)`, `q = e^{−z}`, every fixed
`u > 1`, `Re z > 0`. At real `t` and `u = 1/δ(t) = 1/(1 − e^{−t}) > 1`, with
`log u = λ`, `u^{−1/2} = e^{−λ/2}`, `(−1/u; q)_∞ = e^{G(t)}` and
`(−1)^j e^{2πijλ/t} = e^{2πij(λ/t − 1/2)}`, (11) is (9) term by term, with
the same proof. The manuscript does not cite it; its pin `1512ef835`
predates that report's placement (`4f11bc9c0`). Checked numerically at
this write (both forms against the product, 50 digits, t = 0.3, 0.7, 1.5).
New here: the use of the identity for a `q`-dependent fugacity, the sector
expansion (13)–(14) (elementary), and the uniform complex remainder.
Unlike a291698 (fugacity `n^α`, finitely many conjugate resonance
sectors, its Theorem 2), the minor-arc bound (16) leaves no resonance
sectors. a291698's question 10.3 (fugacity with `log u` comparable to
`n^{1/6}`) concerns a different, size-dependent regime and is not
answered here. A reciprocal note for a291698 is proposed separately; this
write does not edit it.

**An instance of repository results, with no novelty claimed for the
method.** The Lambert start `L_0 = 2W(√y/2)` is the dominant block of
`p0:thm:lambert-core` (`a = 1`, `b = 2`); the reversion rule (21) is the
formal reversion of `p0:thm:perturbed-inversion` in its
Lagrange–Bürmann form for `N` (weight `dN/dH = e^L`); the threshold
bracket and its separation caveat are `p0:thm:staircase` (2), and rounding
at `Y = aₙ` is its part (3). All three are in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.

**Neighbouring reports.**
`a022629-distinct-partition-norms` treats `∏(1 + k^α qᵏ)^μ` (part-
dependent weights) and cites the same Naranjo–Ramírez paper; no shared
theorem. `a124380-signed-moment-asymptotics` is named only in the source
audit's screen. `a271619-strict-twice-partitions` (placed with this report
in `36571ae0e`) treats, in its member manuscript (bundle Report 181,
A358836), `∏(1 + qᵏ/(q;q)_k)`, another distinct-part product with a
`q`-dependent decoration reduced by Jacobi and eta; no shared theorem.

## Rerun the checks (on a scratch copy of the delivered layout)

```sh
R=$(mktemp -d); mkdir "$R/checks"
cp code/*.py "$R/checks/"
cd "$R/checks"
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python -O"
for s in derive_symbolic verify_symbolic_independent independent_reviewer_check \
         verify_numeric verify_inverse verify_product verify_modular; do
  $PY "$s.py" > "$s.replay.log"
done
for f in *.json *.txt *.replay.log; do
  diff --strip-trailing-cr "$f" <this directory>/data/"$f" >/dev/null && echo "$f identical" || echo "$f differs"
done
```

In the copy, `independent_reviewer_check.json` lands in `checks/` beside
its script, as in the delivery; `independent_reviewer_check.replay.log` is
a copy of it and has no shipped counterpart. On Windows the programs
write CRLF line endings; compare with `--strip-trailing-cr`. The delivery
was tested with Python 3.12.14, SymPy 1.14.0 and mpmath 1.3.0 (from
`PROVENANCE.json`; no requirements file was delivered). No computation
uses randomness.

Replays on 5 October 2026, at intake and again at this write; times of
the second (loaded machine): `verify_product` 11 s,
`verify_modular` 5 s, `verify_numeric` 5 s, `verify_inverse` 55 s,
`independent_reviewer_check` 32 s, `derive_symbolic` 43 s,
`verify_symbolic_independent` 23 s; all exit 0 with empty stderr, and all
16 regenerated outputs are identical to the shipped ones up to line
endings.

**Checks made at intake (independent of the delivered programs).**
Coefficients regenerated through `n = 6000` from Somos's OEIS sum formula
`1 + Σ_k x^{k(k+1)/2}/((1−x)^k (x;x)_k)`; the first 40 terms equal the OEIS
DATA, and `aₙ` increases strictly for `n ≥ 2`. At `n = 500, 1000, 3000,
6000` the relative error of Theorem 1.1 is `7.4e−3, 5.4e−3, 3.0e−3,
1.9e−3` (leading term), `−1.5e−3, −8.6e−4, −3.5e−4, −1.9e−4` (after
`C_1`), `8.7e−5, 3.6e−5, 9.2e−6, 3.8e−6` (after `C_2`). The identity (9)
holds to 60 digits at `t = 0.3, 0.7, 1.5`. The proofs were checked by
reading; Lemma 3.1's last step was completed in writing.

OEIS data are licensed CC BY-SA 4.0. No OEIS file is shipped; the
recorded coefficient values are the programs' own computations.

## Build the PDF

pdfLaTeX with fontenc (T1), lmodern, microtype, amsmath/amssymb/amsthm,
mathtools, booktabs, array, geometry, hyperref and xurl. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 12 pages, no errors,
no warnings, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations, no overfull or underfull boxes. The
delivered text builds the same way to 7 pages, also without warnings.

## Retrieving the excluded delivery files

In a scratch directory:

```sh
git -C <repository root> show 60f54ea06:docs/incoming/ProveIt_A126348_Hilbert_Asymptotics_and_Inverses.zip > a126348.zip
unzip a126348.zip -d a126348-delivery    # files under A126348_Hilbert_Asymptotics_and_Inverses/
```

The archive (389,913 bytes) holds the delivered README, the PDF,
`SHA256SUMS`, `PROVENANCE.json` and the replay-log copy besides the shipped
files, in the delivered layout, where `run_checks.sh` runs as delivered
(with `python` resolving to a suitable interpreter; it overwrites the
recorded logs).

## Provenance

- One manuscript: bundle Report 84 of batch 100
  (`ProveIt_A126348_Hilbert_Asymptotics_and_Inverses.zip`), arrival
  `60f54ea06`, placement `36571ae0e`, written in the batch-100 write
  phase (5 October 2026). No merge, so no merge choices.
- Pin: `1512ef835` (1 October 2026), the ProveIt snapshot the delivery's
  source audit checked; the manuscript continues no repository path.
- External sources (as delivered): OEIS A126348 (rechecked 5 October
  2026: no asymptotic formula); Pan and Yu, *Algebraic Combinatorics* 7(1)
  (2024), Proposition 6.10 (bibliographic data checked; the proposition's
  content not rechecked); Naranjo and Ramírez, *Integers* 26 (2026), A20;
  NIST DLMF 17.2, 17.8; McIntosh, *Ramanujan J.* 3 (1999, abstract only);
  Arabi Ardehali and Rosengren, *Constr. Approx.* (published 19 September
  2026).
