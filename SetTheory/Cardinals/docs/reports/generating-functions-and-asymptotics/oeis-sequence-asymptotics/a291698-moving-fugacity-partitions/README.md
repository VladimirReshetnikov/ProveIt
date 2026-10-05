# Moving Fugacity Asymptotics for Distinct Partitions

**Uniform coefficient expansions and inverses for [qⁿ] ∏(1 + n^α q^k): A291698 (α = 1) and A292304 (α = 2)**

A research report dated 1 October 2026, built from one manuscript. Its
author line is empty.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 34 | batch 77, manuscript 34 | `moving-fugacity-reproducibility.zip` (main file `moving-fugacity-report.tex`, 985 lines, 17-page PDF; proof note `theorem-and-proof.md`) | none (names no repository revision) | `4f11bc9c0` (arrival `096ee7b87`) | the whole article, Sections 1–10 and Appendices A–B |

**Status: AI-assisted delivery channel, unrefereed, not formalized.** The
report entered the collection through `docs/incoming`; it has not been
refereed, and no statement of it is formalized in Lean or Rocq. The
delivery's own scope line (from its retired `MANIFEST.json`): "Fixed
positive compact alpha range; fixed sector count and algebraic depth;
numerical checks are not interval certificates."

For `a_n(α) = [qⁿ] ∏_{k≥1} (1 + n^α q^k)`, uniformly for `α` in a fixed
compact subset `[a, b]` of `(0, ∞)`, with `u = n^α`, `A = −Li₂(−u)`,
`N = n + u/(12(1+u))`, `t = √(A/N)`, `s = √(AN)`, the article proves:

- **Theorem 1 (1)–(2)** an all-orders principal-sector Bessel expansion
  `a_n = (1+u)^{−1/2} Σ_{m≤M} h_m(u) t^{m+1} I_{m+1}(2s) + B₀ O(t^{M+1}/u + exp{−c/[t(1+L)²]})`,
  with a finite generator for the endpoint coefficients `h_m`;
- **Theorem 2 (3)–(4)** finitely many conjugate resonance sectors
  `|j| ≤ K`, separated by `Δ_j ~ (2√2π⁴/3) j² √n / L³`;
- **(11)** an exact Jacobi (triple product + modular) decomposition, and
  **(12b)–(12e)** exact local sector integrals with sectorwise remainders;
- **Section 6** the conjectured OEIS equivalents of A291698 (`α = 1`) and
  A292304 (`α = 2`), and the threshold: the elementary Sommerfeld form is
  relatively valid **if and only if `α ≥ 1/2`**;
- **Section 7** a specified saddle–Fourier real continuation (13), its
  monotonicity (14), a Lambert-W initializer (15) with first correction
  (15a), a controlled finite-sector inverse (16), a formal reversion
  generator (17), and the integer threshold `min{n : a_n ≥ X} = ⌈𝒜_α^{-1}(X)⌉`.

## What is not claimed

Every limitation of the delivery is kept in the article:

- Uniformity only for a fixed compact `α`-range, with the sector count `K`,
  the auxiliary count `J` and the depth `M` fixed before `n → ∞`. **No
  growing-`K` theorem, no infinite Bessel-sector sum or convergence, no
  optimal truncation, no explicit finite-input big-O constants.**
- The Euler–Maclaurin series is formal; no convergence is asserted.
- The continuation (13) is a convention, not claimed unique; an
  approximate inverse must not be rounded across an unresolved integer
  boundary.
- **Slow onset.** At `n = 20,000` the principal approximation for `α = 2`
  is still off by about −5.58 %; more algebraic depth does not help, two
  conjugate pairs reduce it to about −5.09·10⁻⁵.
- The numerical checks (100-digit evaluation, 70-digit quadrature) are
  diagnostics, not interval certificates.
- **No publication-priority or external-peer-review claim.** The
  endpoint expansion, modular ingredients, grand-canonical interpretation
  and leading saddle method are classical; Brunel (2018), Romik (2005),
  McIntosh (1999) and Arabi Ardehali–Rosengren (published 19 September
  2026) are relevant antecedents, and the comparison delimits only those
  sources.
- The four questions of Section 10 are open.

The OEIS leading equivalents are **Václav Kotěšovec's conjectures**
(A291698, 15 September 2017; A292304, 14 September 2017); the manuscript
does not name him. A `[write]` note records this, and that the delivered
proof note says the A291698 page could not be reached when it was written
(its conjecture was transcribed from an unshipped screening note); both
entries were checked on 2 October 2026 and match the displayed equivalents
exactly.

## Labels and the write

Every label carries the prefix `mfp:`. The 16 delivered labels were
pandoc-generated section names (`result-and-scope`, …); nothing cited them,
and they were prefixed. The write added one, `mfp:provenance`:
**16 → 17**. The equation tags (1)–(17) are fixed `\tag`s; no section,
subsection or tag number changed (the `.aux` numbers of all 16 delivered
labels equal those of a build of the delivered text). No statement, proof
or number of the manuscript was changed and no symbol renamed.

Five `[write]` notes were added (all of 2 October 2026):

1. a new subsection 1.3 *Provenance, status and reading conventions*:
   provenance, pin, status, the reruns;
2. in the same subsection, the two readings that need care (the fugacity
   `u = n^α` is one weight per part, not a part weight `k^α`; `C_n` means
   the Bessel scale in Section 2 but `A − L²/2` in Sections 5.2–5.3) and a
   table of reused letters (`a, b`; `A`; `B`; `c`; `v`; `y`; `z`; `m, r`;
   `x`; `D, E, g, H`; `η`; `R_K, R_P`; `t, s, N, L`);
3. at the end of Section 7: the inverse is an instance of the transseries
   volume's apparatus (below), with no novelty claimed;
4. at the end of Section 9: the two OEIS conjectures (above), and the
   relation to `a022629-distinct-partition-norms` (below);
5. in Appendix A: the shipped names of the programs.

Two reciprocal `[write]` notes were added on 5 October 2026 (batch 100);
neither adds a label (still 17) or changes a number:

6. after the proof of (11), before Section 5.1: its specialization in
   `a126348-stable-hilbert-series` (below);
7. at the end of Section 10.3: the neighbouring model of
   `a271619-strict-twice-partitions`, Part II (below).

## Files

```text
README.md                          this guide (replaces the delivery README)
article.tex                        the report (delivered as moving-fugacity-report.tex)
article.pdf                        compiled report, 20 pages
theorem-and-proof.md               the delivered Markdown proof note ("research note, 1 October 2026"), the source of the article
REPRODUCIBILITY.md                 the delivery's reproducibility report: environment, commands, scope of each check
code/checks.py                     exact restricted-partition polynomials, principal Bessel comparisons to n = 20,000, inverse checks
code/resonance_check.py            finite conjugate Bessel sums, K = 0..8, M = 9 (reads checks.json)
code/validate.py                   120 direct-product checks (n ≤ 60), 24 A292304 terms, Jacobi identity, inverses (reads checks.json)
code/sector_integrals.py           uncertified 70-digit quadrature of the local sector integrals (12c), alpha = 1, n = 20,000
code/build_pdf.sh                  delivery-state tool: builds moving-fugacity-report.tex into output/pdf/
data/checks.json                   written by checks.py --max-n 20000
data/resonance-checks.json         written by resonance_check.py
data/validation.json               written by validate.py
data/sector-integral-checks.json   written by sector_integrals.py
data/requirements.txt              mpmath==1.3.0, sympy==1.14.0
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. `article.tex` at the placement commit
`4f11bc9c0` is the delivered `moving-fugacity-report.tex` byte for byte; the
write changed only labels and added the notes above. The SHA-256 of
`theorem-and-proof.md` printed in Appendix A and in `REPRODUCIBILITY.md`
(`5a90f133…`) matches the shipped file.

`theorem-and-proof.md` carries the article's mathematics in the same order
and two source remarks the article dropped (the A291698 access failure and
the A292304 check, see above); its opening line calls it "a proof draft for
mathematical audit, not a claim of literature priority".

**Not shipped** (all survive in the arrival commit, see below): the
delivered README (replaced by this guide; its content is folded in here),
the 17-page PDF `output/pdf/moving-fugacity-report.pdf`, `SHA256SUMS` and
`MANIFEST.json` (16 entries each, both verified 16/16 at placement and
retired; the manifest's scope line is quoted above), and
`PACKAGE_FILES.txt` (a file list without hashes, replaced by the listing
above).

**Delivered text that uses delivery names.** The delivery was one flat
directory. `REPRODUCIBILITY.md` and Appendix A of the article name
`moving-fugacity-report.tex`, `output/pdf/moving-fugacity-report.pdf`,
`requirements.txt` and bare script names, and give the replay as commands
run in that flat directory. `code/build_pdf.sh` builds
`moving-fugacity-report.tex` beside itself into `output/pdf/` (with an
optional `.tex-cache/`); it cannot build `article.tex` and should not be
run here. `resonance_check.py` and `validate.py` read `checks.json` **from
their own directory**, and those two scripts and `sector_integrals.py`
write their outputs there under fixed names; `checks.py` writes to
`--output` (default `checks.json` in the current directory). Run from
`data/` they would overwrite the shipped outputs; run from `code/` they
fail. Use a flat scratch copy (below).

## Relation to the repository

**Formal status.** Placement in the collection confers no formal status.
No statement of this report is formalized anywhere in the repository, and
no Lean or Rocq development treats A291698, A292304 or moving-fugacity
partition products.

**An instance of repository results, with no novelty claimed for the
method.** The initializer (15) solves `r log r = z`, i.e.
`X + log X = log z` for `X = log r`: the dominant block
`p0:thm:lambert-core` with `a = b = 1` on the principal branch. The formal
generator (17) is the reversion formula of `p0:thm:perturbed-inversion`
read at `ε = 1` (`F = g`, `μ₀ = H`). The integer threshold is
`p0:thm:staircase` (1), and the warning against rounding is its
separation condition (2). All three are in
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.

**Neighbouring report.**
`oeis-sequence-asymptotics/a022629-distinct-partition-norms` treats
`∏_{k≥1}(1 + k^α q^k)^μ` (A022629 and relatives), where the weight depends
on the part `k`. Here the weight `n^α` depends on the size `n` and is the
same for every part (a partition with `m` parts carries `n^{αm}`). Same
distinct-part structure and the same Euler–Maclaurin/saddle/Lambert
toolkit, but a different saddle regime (here the part count approaches the
distinct-partition endpoint `√(2n)`, with conjugate resonance sectors),
different sequences and no shared theorem; neither manuscript cites the
other. That report is not edited by this write (a reciprocal note is a
separate commit).

**A specialization (5 October 2026, batch 100).**
`oeis-sequence-asymptotics/a126348-stable-hilbert-series` uses identity
(11) at the q-dependent fugacity `u = 1/(1 − q)` (its Theorem 2.1, which
was written without knowledge of this report and now credits it); a
`[write]` note at the end of Section 5's proof records this. Different
regime: no resonance sectors there; question 10.3 is not affected.

**Neighbouring report (added 5 October 2026, batch 100).**
`oeis-sequence-asymptotics/a271619-strict-twice-partitions`, Part II
(Report 181, A358836, `∏(1 + q^k/(q;q)_k)`, labels `stp:len:`) is a
distinct-part product with a q-dependent fugacity (`log u ≍ n^{1/4}`); its
equation (96) is identity (11) here at `u = e^{μ(z)}`, derived
independently. It does not answer Section 10.3's question (the regime
`log u ≍ n^{1/6}` stays open); a `[write]` note at the end of Section 10.3
records this. Its Part I treats A271619 by a two-charge phase expansion.

## Rerun the checks (on a flat scratch copy)

```sh
R=$(mktemp -d)
cp code/checks.py code/resonance_check.py code/validate.py code/sector_integrals.py "$R"
cd "$R"
PY="uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python"
$PY checks.py --max-n 20000 --output checks.json   # writes checks.json
$PY resonance_check.py                              # reads checks.json, writes resonance-checks.json
$PY validate.py                                     # reads checks.json, writes validation.json
$PY sector_integrals.py                             # writes sector-integral-checks.json
for f in checks.json resonance-checks.json validation.json sector-integral-checks.json; do
  diff --strip-trailing-cr "$f" <this directory>/data/"$f" && echo "$f identical"
done
```

Run `checks.py` first (the next two read its output). On Windows the
scripts write CRLF line endings; compare with `--strip-trailing-cr`. The
delivery was tested with Python 3.12.14, mpmath 1.3.0 and SymPy 1.14.0;
no computation uses randomness.

Replays on 2 October 2026 (on a loaded machine): `validate.py` (17 s) and
`resonance_check.py` (10 s) at placement, `checks.py --max-n 20000` (24 s)
and `sector_integrals.py` (121 s) at this write. All four outputs are
identical to the shipped files up to line endings.

**Checks made at intake (independent of the delivered programs).** A direct
expansion of `∏(1 + n^α q^k)` reproduced `1, 1, 2, 12, 20, 55, 294, 497,
1224, 2520` (`α = 1`) and `1, 1, 4, 90, 272, 1275, 49284, 124901, 536640,
1620648` (`α = 2`), the OEIS DATA of A291698 and A292304; at `n = 500, 2000`
the ratio `a_n/B₀ − 1` is `−0.036, −0.00062` for `α = 1` and `+1.08,
−0.48` for `α = 2`, an illustration of the slow onset the article warns
about. The proofs were not re-derived.

## Build the PDF

pdfLaTeX with fontenc (T1), inputenc, lmodern, amsmath/amssymb/amsthm/
mathtools, geometry, microtype, booktabs, longtable, array, enumitem, xurl,
hyperref, fancyhdr and needspace. From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory: 20 pages, no errors,
no undefined references or citations, no multiply defined labels, no
duplicate PDF destinations, no overfull or underfull boxes. The log carries
101 `fontmap entry ... already exists, duplicates ignored` warnings from the
delivered preamble's `\pdfmapfile{+…}` lines (MiKTeX already loads those
maps); the delivered text gives the same 101 and builds to 17 pages.

## Retrieving the excluded delivery files

In a scratch directory:

```sh
git -C <repository root> show 096ee7b87:docs/incoming/moving-fugacity-reproducibility.zip > mf.zip
unzip mf.zip -d mf-delivery    # files under moving-fugacity-research/
```

The archive (418,896 bytes) holds the delivered README, the PDF,
`SHA256SUMS`, `MANIFEST.json` and `PACKAGE_FILES.txt` besides the shipped
files.

## Provenance

- One manuscript: batch 77, manuscript 34
  (`moving-fugacity-reproducibility.zip`), arrival `096ee7b87`, placement
  `4f11bc9c0`, written in the batch-77 write phase (2 October 2026). No
  merge, so no merge choices.
- Pin: none; the delivery names no ProveIt revision and continues no
  repository path.
- External sources (as delivered): OEIS A291698 and A292304 (Kotěšovec's
  conjectures; checked for this write on 2 October 2026); Brunel,
  arXiv:1709.04955 / Ann. Phys. (2018); Romik, Eur. J. Combin. 26 (2005);
  Arabi Ardehali–Rosengren, Springer, published 19 September 2026;
  McIntosh, Ramanujan J. 3 (1999, full text not reviewed by the delivery);
  NIST DLMF 10.40, 17.8, 20.7.
