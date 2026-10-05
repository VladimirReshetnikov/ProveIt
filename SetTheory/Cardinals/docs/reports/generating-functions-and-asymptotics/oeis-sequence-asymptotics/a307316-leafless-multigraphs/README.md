# Leafless Loopless Multigraphs by Number of Edges

**Refined logarithmic asymptotics, connectedness and inversion for OEIS
A307316 and A307317**

A research article dated 2 October 2026 ("Report 131" of a session bundle),
built from one manuscript. Its title page and PDF metadata name no author and
no tool (the PDF author field is empty); the package carries no "prepared for
private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 131 (batch 100) | `A307316_A307317_Refined_Asymptotics_Connectedness_and_Inversion_Source.zip` (wrapper directory `report131/`, 447,331 bytes), arrival commit `60f54ea06`; main file `report131.tex` | none: the package names no ProveIt commit, path or report | `36571ae0e` (batch 100) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs, and the main theorem is **conditional on a
classical theorem that neither the source nor the ProveIt intake has checked
against its original** (next section). The exact finite checks test
definitions, identities and the supplied tables; they certify no asymptotic
statement.

## Trust boundary: Wright's 1972 theorem

The upper half of the main theorem rests on Wright's 1972 Theorem 5
(Bull. Amer. Math. Soc. 78, 1032–1034), specialised in the article as
`lfm:eq:wright` to `S_m = T(2m, m)`, the unlabelled simple graphs with `m`
edges and no isolated vertices. **The source checked the statement only in an
OCR'd online reproduction of the paper and in an AMS Notices abstract
(January 1972); it obtained neither the original scan nor the 1974 PLMS
proof.** It says so itself (Section 2.1, "Source-verification boundary"). The
ProveIt intake did not inspect the original either.

What depends on it, as traced in the `[write]` note of Section 2 and on the
title page: `S_m ~ Q_m` and the coarse bound `log S_m ≤ F(m) + O(log² m)`
(`lfm:eq:S`), hence the upper bound `A_m ≤ (1+o(1)) e^w H_m`
(`lfm:eq:upperH`), the upper half of `log a_m = J(m) + O(log m)`, the ratio
`C_m/A_m = 1 − O(w³/m)` and the threshold `ν_a(X) = m_0 + O(1)`. What does
**not** depend on it: the lower bound `C_m ≥ (1−o(1)) H_m` (Section 5.2 uses
only Lemmas 3.3 and 4.1, Stirling's formula and a symmetry-weighted count),
hence `log a_m ≥ J(m) − O(log m)`; the labelled-model results of Section 8;
the Euler-product identities; and Proposition 9.1's unconditional half.
Checking Wright's statement against an original scan is further question 5
(below).

## What it proves

`A_m` (A307316) and `C_m` (A307317) count isomorphism classes of loopless
multigraphs with `m` edges and minimum degree at least two (`C_m`:
connected); vertices and edges are unlabelled, and `A_0 = C_0 = 1` by the
OEIS convention. With `w = W(2m)` (principal Lambert function), `v = e^w =
2m/w`, `F(m) = m(w − log w − 1 + 2/w)`, `J = F + w²/4` and
`H_m = exp{J − 3w/2 − 1} / sqrt(2π m (w+1))`:

- **Theorem 1.1 (`lfm:thm:main`), conditional on Wright as above:**
  `(1−o(1)) H_m ≤ C_m ≤ A_m ≤ (1+o(1)) e^w H_m`;
  `log a_m = J(m) + O(log m)` for `a ∈ {A, C}`;
  `C_m/A_m = 1 − O(w³/m)`, proved directly for isomorphism classes by a
  component convolution; and the first threshold `ν_a(X) = min{m : a_m ≥ X}`
  equals `m_0 + O(1)` with `J(m_0) = log X`, with no monotonicity assumed.
- `S_m ~ Q_m` (`lfm:eq:S`), a refinement of Wright's equivalent in the
  scale `F(m)`.
- Lemma 3.3 (`lfm:lem:rare-lower`): a relative lower bound for the
  minimum-degree probability in the uniform weak-composition model
  `U(n, m)`; Lemma 4.1 (`lfm:lem:cuts`): small-component bounds in that
  labelled model. Lemmas 3.1 (Harris) and 3.2 (the Pólya-urn coupling) are
  classical and proved for completeness.
- Section 7: the boxed `log a_m = F(m) + W(2m)²/4 + O(log m)`; every fixed
  order in `1/log(2m)`, with terms through `ℓ²(2ℓ−3)/(3L³)`; the explicit
  inverse `M = F^{-1}(y)` through order three and its effective recurrence;
  and the shift `m_0 = M − ω²/(4(ω − log ω)) + o(1)`.
- **Theorem 8.1 (`lfm:thm:star`):** an exact star-conditioning sandwich for
  i.i.d. multiplicities, and **Corollary 8.2 (`lfm:cor:exactrelative`):**
  `P_U(n,m)(δ ≥ 2) ~ exp{−n(1+2m/n) e^{−2m/n}}` when `2m/n = log n + o(1)`,
  uniformly on shrinking envelopes (labelled model).
- Section 9: initial values, the Euler product `Σ A_m z^m =
  Π (1−z^k)^{−C_k}` and its recurrence (standard), the scope of the checks,
  the source's open problems and related models.

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Proposition 9.1 (`lfm:prop:deficit`):** for `m ≥ 4`,
  `A_{m−2} ≤ A_m − C_m ≤ A_{m−2} + Σ_{k=3}^{⌊m/2⌋} A_k A_{m−k}` (the map
  `G ↦ G ⊔ D_2`, `D_2` a doubled edge, is injective on classes); and **if
  `A_m ~ κ H_m` for a constant `κ > 0`, then `(A_m − C_m)/A_m ~ A_{m−2}/A_m ~
  w⁴/(4m²)`**, so the source's candidate for the leading disconnected
  correction follows from a relative equivalent.
- A proof of the source's unproved closing remark in Lemma 4.1 (the first
  bound of `lfm:eq:cuts` holds with one constant for `|λ − log n| ≤ 1`).
- The dependency trace of Wright's theorem above.

## What is not claimed

From the source, kept in the article (collected in the note at the end of
Section 1):

- **No relative equivalent:** `A_m ~ H_m` and `C_m ~ H_m` are not proved; the
  sandwich leaves a factor `e^w = 2m/w`.
- No historical priority and no novelty certificate; the absence of a formula
  on an OEIS page is not evidence of novelty. Wright's 1972 and 1974 work
  must be credited, and Lupanov's earlier graph-by-edges work was not
  inspected.
- Lemma 4.1 and Section 8 are statements about the vertex-labelled
  composition model, not about unlabelled classes.
- Fixed truncations of the inverse series do not inherit the additive `O(1)`.
- The Greenhill–McKay (labelled vertices, prescribed degrees) and
  Cameron–Prellberg–Stark (labelled edges) counts do not transfer to this
  problem by division by `m!`.
- The identification with symmetric kinematic-polynomial counts
  (Komiske–Metodiev–Thaler) and the comparison with OEIS A226919 are
  conjectural and unused.
- The finite checks do not certify uniform asymptotic estimates, Wright's
  theorem, error bounds at infinity, source quotations or novelty; the OEIS
  b-files are supplied snapshots, not a fresh retrieval; hashes are not a
  signature.

The write adds: Proposition 9.1's asymptotic half is conditional on
`A_m ~ κ H_m`, which is open; the m ≤ 50 numbers below are evidence only.

## Further questions

Section 9.4 of the article ("Further questions and research", `lfm:sec:further`)
states every unproved claim of the source as an open question, with its
sketch and what is missing (Vladimir's standing rule of 4 October 2026). The
intake found **no false claim** in the source.

1. **Sharp equivalent** `A_m ~ H_m`, `C_m ~ H_m` (`lfm:q:sharp`): needs
   vertex-count tails and automorphism weights of leafless classes, or a
   direct unlabelled enumeration. A route suggested by the write (not
   attempted): an exact automorphism-controlling formula, or an automorphism
   estimate, of the kind the a007716 report proves for bipartite multigraphs
   (its Reports 88 and 92).
2. **Leading disconnected correction** (`lfm:q:deficit`): the candidate
   `A_{m−2}/A_m ~ w⁴/(4m²)` now follows from any relative equivalent
   `A_m ~ κ H_m` (Proposition 9.1); unconditionally it is open.
3. **Minimum degree `r > 2`**, and uniformity in growing `r`
   (`lfm:q:degree`): only "suggested" by the source.
4. **Full expansions** (`lfm:q:expansions`): relative corrections,
   exponentially small terms, transseries; the source asserts no convergence.
5. **Checking Wright and Lupanov** (`lfm:q:wright`): the original 1972 scan
   (prefactor, choice of `V`, range condition, `q ≤ C(n,2)/2`), the 1974 proof,
   Lupanov's work, and a literature search on these two sequences.
6. **The kinematic-polynomial identification and A226919**
   (`lfm:q:kinematic`).

**Evidence only (m ≤ 50, computed by the intake from the shipped b-files):**

| m | log A_m | log H_m | log(e^w H_m) | 1 − C_m/A_m | A_{m−2}/A_m | w⁴/(4m²) | w³/m |
|---|---|---|---|---|---|---|---|
| 10 | 8.048 | 7.468 | 9.673 | 0.1841 | 0.0892 | 0.0591 | 1.072 |
| 20 | 22.979 | 22.630 | 25.326 | 0.0668 | 0.0382 | 0.0331 | 0.981 |
| 30 | 40.728 | 40.437 | 43.434 | 0.0364 | 0.0244 | 0.0224 | 0.897 |
| 40 | 60.296 | 60.037 | 63.251 | 0.0244 | 0.0177 | 0.0167 | 0.830 |
| 50 | 81.251 | 81.014 | 84.400 | 0.0181 | 0.0137 | 0.0131 | 0.776 |

`log(A_m/H_m)` falls from 0.580 (m = 10) to 0.237 (m = 50), monotonically on
`10 ≤ m ≤ 50`, against a sandwich width `w = W(100) ≈ 3.39` at m = 50: the
counts sit near the lower bound. The deficit `1 − C_m/A_m` is about 43 times
smaller than `w³/m` at m = 50 and is `1.32 A_48/A_50`; its quotient by
`A_{m−2}/A_m` falls 2.07, 1.75, 1.49, 1.38, 1.32 at m = 10, 20, …, 50.
For every `4 ≤ m ≤ 50` the terms satisfy `H_m ≤ C_m ≤ A_m ≤ e^w H_m` and
both bounds of Proposition 9.1 (the lower with equality exactly at m = 4, 5).
None of this bears on the limit.

## Checks made at intake

On 5 October 2026 (Windows, Python 3.14.4) the intake restored the delivered
layout from the arrival commit's archive in a scratch directory and ran:

- `integrity.py`: `PACKAGE_INTEGRITY_PASS 21 files` (against the delivered
  `CHECKSUMS.sha256`, also verified with `sha256sum -c`: 21 of 21).
- `checks/verify.py`: refuses to run on Windows by design (`VERIFICATION
  FAILED: safe file output requires POSIX O_NOFOLLOW and O_DIRECTORY`).
  Imported instead (route below), its six mathematical sections
  (`verify_inputs`, `enumerate_graphs`, `euler_checks`,
  `composition_checks`, `polya_checks`, `formal_checks`) and both SHA keys
  reproduced `checks/results-normal.json` exactly, key by key, under `py -B`
  and `py -B -O`, in about 2.5 s. The thirty adversarial cases (symlinks,
  `O_NOFOLLOW`) were not run; their count (30) is in the recorded JSON. The
  counts match the verifier's README: 46,686 candidate compositions; 1,296
  moment and 28 cut identities; 791 / 3,465 / 1,281 coupling checks; 70
  monotonicity comparisons; the Euler relation for `0 ≤ m ≤ 50`.
- `test_output_guard.py`: `PASS` (24 negative runs).
- `test_integrity.py`: stops at `os.mkfifo`, which Windows lacks (a platform
  limit, not a failure).
- `build.py` and `reproduce.py` were not run: they require TeX Live pdfTeX
  1.40.26 for byte-identical PDFs. The delivered source builds with MiKTeX
  pdfLaTeX in 18 pages with no warnings.
- Every staged file was compared with the archive: all 20 are byte-identical
  to their delivered counterparts (the delivery README and `report131.tex`
  as they were before this write).

The placement dossier also checked the main proof steps by hand and with
high-precision spot checks (the saddle identities for `φ_m`, `g'`, the
inverse coefficients and the shift `lfm:eq:inverse-shift`); none failed.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats multigraph enumeration or
Wright's theorem, and the report's place in the collection confers no formal
status.

**Neighbouring reports** (no shared theorem):

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a007716-bipartite-multigraphs`
  (batch 100, Reports 88 and 92): bipartite multigraphs with distinguished
  shores, counted by edges. It proves a *relative* equivalent
  `a_n ~ B_n² e^{W(n)²/2}/n!` (`B_n` Bell numbers) through an exact
  invariant-partition formula controlling all vertex automorphisms, and shows
  the parallel-edge factor `e^{W(n)²/2}` to be non-negligible; the analogous
  factor `e^{w²/2}` appears in this report's upper bound
  (`lfm:eq:supportmain`). **Scale clash:** there `w = W(n)` for `n` edges,
  here `w = W(2m)` for `m` edges. Its second source, Report 92, proves for
  that model that a nontrivial vertex automorphism has probability
  `2W(n)³/n + O((1+W(n))⁷/n²)` and that disconnection has probability
  asymptotic to `W(n)²/n`, usually through one isolated-edge component, by a
  component-removal bijection; Proposition 9.1 here uses the leafless
  counterpart of that bijection (`G ↦ G ⊔ D_2`) and gets the asymptotic only
  conditionally, because no relative equivalent is known here. Report 92
  cites Wright's 1967 paper on connectedness (Proc. LMS (3) 17), not the 1972
  theorem used here.
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  (not a collection report): `p0:thm:lambert-core` and
  `p0:thm:core-reversion` treat Lambert-core inversions in general, and
  `p0:thm:staircase` recovers integer thresholds of *strictly increasing*
  sequences; this report's threshold needs no monotonicity (a note after
  Section 7.4; coefficients were not compared). The forward series of
  Section 7.2 is the classical asymptotic expansion of `W` at infinity.

**Stale claims.** The manuscript makes no claim about the repository and has
no pin; nothing to correct.

## Notation

The article reuses letters with local meanings. A table in the `[write]` note
at the end of Section 1 fixes each one, with tempting false readings: `B` (the
good event `{δ ≥ 2}`, but `B_i` the *bad* event at vertex `i`, `B_0` a
constant, `B(z)` a series), `A` (the counts, the correction series `A(z)` of
`W(2m)`, events), `J` (`J(m)`, a vertex set), `ℓ` (`log n`, or `log log 2m`),
`u` (`W(m)`, or `log log 2y`), `M` (`N − c`, the count `M_m`, `F^{-1}(y)`),
`t` (Chernoff parameter, `e^{−g'(m/2)}`), `c` (cut size, star constant), `K`
(`C(s,2)`, a truncation order, a threshold constant, `K_μ`), `q` (Wright's
edge count, an integer near `w³`, the bad-vertex probability), `a`, `T` and
`W`. No symbol was renamed.

## Labels

Every label carries the prefix `lfm:`. The manuscript's 73 labels (59 `eq:`,
7 `sec:`, 4 `lem:`, 2 `thm:`, 1 `cor:`) were prefixed before anything cited
them, and every reference was updated (50 `\eqref`, 14 `\ref`). The write
added 13: `lfm:sec:checks`, `lfm:sec:unresolved`, `lfm:sec:related`,
`lfm:sec:further`; the six questions `lfm:q:sharp`, `lfm:q:deficit`,
`lfm:q:degree`, `lfm:q:expansions`, `lfm:q:wright`, `lfm:q:kinematic`; and
`lfm:prop:deficit` with `lfm:eq:deficit-sandwich`, `lfm:eq:deficit-asym`.
The report has 86 labels; a build of the delivered text and of this one give
every delivered label the same number.

The write also added the `[write]` notes: the trust boundary (title page);
provenance, repository relations, the notation table and the collected
non-claims (end of Section 1); the Wright dependency trace (Section 2.1); the
proof of Lemma 4.1's closing remark; the reading of "an integer `q` within
one of `w³`" (Section 5.1); credits and relations (end of Section 7); the
shipped layout and intake rerun (Section 9.1); a pointer at Section 9.2; and
Section 9.4 with Proposition 9.1. No statement, proof or number of the
manuscript was changed.

## Files

```text
README.md                            this guide (replaces the delivery README)
article.tex                          the report (delivered report131.tex; labels prefixed, [write] notes, Section 9.4)
article.pdf                          compiled report, 23 pages
checks-README.md                     the verifier's README (delivered checks/README.md)
code/build.py                        reproducible two-pass-pair PDF build with byte comparison (delivered at the root)
code/build.sh                        wrapper for build.py (delivered at the root)
code/checks-verify.py                the exact verifier (delivered checks/verify.py)
code/integrity.py                    closed-inventory check against CHECKSUMS.sha256 (delivered at the root)
code/output_guard.py                 external-only output guards used by the scripts (delivered at the root)
code/repack.py                       deterministic ZIP creation (delivered at the root)
code/reproduce.py                    immutable replay: checks, PDF builds, ZIP round trip (delivered at the root)
code/test_integrity.py               adversarial tests of integrity.py (delivered at the root)
code/test_output_guard.py            output-rejection tests (delivered at the root)
data/build-environment.txt           toolchain of the delivered PDF build (delivered at the root)
data/checks-fixtures.json            pinned fixture: OEIS terms and source digests (delivered checks/fixtures.json)
data/checks-replay-evidence.json     record of an isolated-copy replay (delivered checks/replay-evidence.json)
data/checks-results-normal.json      recorded verifier output, python (delivered checks/results-normal.json)
data/checks-results-optimized.json   recorded verifier output, python -O (delivered checks/results-optimized.json)
data/checks-source-provenance.json   URLs and digests of the b-file snapshots (delivered checks/source-provenance.json)
data/checks-sources-b307316.txt      OEIS b-file snapshot of A307316, m <= 50 (delivered checks/sources/b307316.txt)
data/checks-sources-b307317.txt      OEIS b-file snapshot of A307317, m <= 50 (delivered checks/sources/b307317.txt)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. **The two recorded result files are
byte-identical to each other** (SHA-256 `3df7b256…`, one git blob): they are
the outputs of the runs without and with `python -O`, and their equality is
the package's evidence that optimized mode (which strips `assert`
statements) changes nothing, so both are shipped as delivered.

Not shipped, and recoverable from the archive
(`git show 60f54ea06:docs/incoming/A307316_A307317_Refined_Asymptotics_Connectedness_and_Inversion_Source.zip > <scratch>/a307316.zip`):

- `report131.pdf`, the delivered 18-page PDF (405,180 bytes);
- `CHECKSUMS.sha256` (1,779 bytes), the package's "closed package
  inventory": a checksum manifest, which repository policy does not ship (21
  of 21 entries verified at placement and again at the write). Without it
  `integrity.py`, `test_integrity.py` and `reproduce.py` (which calls
  `integrity.py`) have no target in the repository layout;
- the delivery README (4,677 bytes), staged at placement and replaced by this
  guide.

**Delivered text that names the delivery layout or files not shipped.**
`checks-README.md` says to run `checks/verify.py` "from the package root"
and refers to `sources/`, `fixtures.json` and `replay-evidence.json` beside
the verifier, and to "the final report's closed inventory"; the scripts in
`code/` locate their inputs relative to themselves (`build.py` builds
`report131.tex` next to it; `reproduce.py` reads `checks/results-normal.json`
and `report131.pdf`; `integrity.py` reads `CHECKSUMS.sha256`; `verify.py`
reads `fixtures.json` and `sources/` next to it and treats its parent as the
package root). The article's Section 9.1 mentions "the README", meaning the
delivery README, and "a closed byte inventory", meaning the unshipped
manifest. **Flattening into `code/` and `data/` breaks every relative path**,
so none of the scripts runs in place; use the routes below.

**Third-party data.** The two b-file snapshots and the OEIS terms embedded in
`data/checks-fixtures.json` (and recorded in the result files) are from The
On-Line Encyclopedia of Integer Sequences (https://oeis.org; A307316 by
P. T. Komiske and A307317 by E. M. Metodiev, tables extended by A. Howroyd).
OEIS content is published by The OEIS Foundation Inc. under the Creative
Commons Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); these files are
third-party data under that licence, not MIT-0 like the rest of the
repository. Nothing contacts OEIS.

## Rerun the checks (on a scratch copy)

The suite needs a **POSIX** host (Linux or macOS): `verify.py` refuses to
write without `O_NOFOLLOW` and `O_DIRECTORY`, and `test_integrity.py` needs
`os.mkfifo`. Never run anything in the repository: the shipped layout is
flattened, and the guards require outputs outside the package. Restore the
delivered `report131/` from the arrival commit (Python 3.10 or later,
standard library only):

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A307316_A307317_Refined_Asymptotics_Connectedness_and_Inversion_Source.zip > "$T/a.zip"
cd "$T" && unzip -q a.zip && cd report131
sha256sum -c CHECKSUMS.sha256                      # 21 OK
python3 -B integrity.py                            # PACKAGE_INTEGRITY_PASS 21 files
python3 -B checks/verify.py --output "$T/normal.json"
python3 -B -O checks/verify.py --output "$T/optimized.json"
cmp "$T/normal.json" checks/results-normal.json && cmp "$T/optimized.json" checks/results-optimized.json
python3 -B test_integrity.py
python3 -B test_output_guard.py
python3 -B reproduce.py --skip-pdf --output "$T/replay.json"
```

Output files must not exist beforehand (the guards refuse to overwrite). The
full `reproduce.py` without `--skip-pdf` and `build.py` also rebuild the PDF
twice and require byte equality, which needs the delivered toolchain
(`data/build-environment.txt`: TeX Live pdfTeX 1.40.26).

**Windows (mathematical sections only).** On Windows `verify.py` stops at its
output guard, but its checks can be imported. In Git Bash, after restoring
`report131/` as above (with `py` for `python3`):

```sh
cd "$T/report131" && py -B - <<'EOF'
import importlib.util, json
from pathlib import Path
root = Path('checks').resolve()
spec = importlib.util.spec_from_file_location('verify131', root / 'verify.py')
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
fixture, digest = v.verify_inputs(root)
got = {'fixture_sha256': v.FIXTURE_SHA256, 'source_snapshot_sha256': digest,
       'exhaustive_graph_enumeration': v.enumerate_graphs(fixture),
       'euler_transform': v.euler_checks(fixture),
       'composition_identities': v.composition_checks(),
       'polya_coupling': v.polya_checks(), 'formal_series': v.formal_checks()}
ref = json.loads((root / 'results-normal.json').read_text(encoding='utf-8'))
for k, val in got.items():
    print(k, 'MATCH' if json.loads(json.dumps(val)) == ref[k] else 'DIFFER')
EOF
```

At the write this printed `MATCH` for all seven keys in about 2.5 s. The
verifier alone can also be run from the shipped files by recreating its
neighbourhood in a scratch directory: `code/checks-verify.py` as
`checks/verify.py`, `data/checks-fixtures.json` as `checks/fixtures.json`,
`data/checks-results-normal.json` as `checks/results-normal.json` and the two
`data/checks-sources-*.txt` as `checks/sources/b307316.txt` and
`b307317.txt`; the import above, run from the parent of that `checks/`,
then also prints `MATCH` seven times (tested at the write). `integrity.py`
cannot run that way (no manifest).

## Build the PDF

pdfLaTeX (geometry, fontenc, lmodern, amsmath, amssymb, amsthm, mathtools,
booktabs, microtype, hyperref, enumitem, fancyhdr, xcolor); the bibliography
is embedded. Build in a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 23 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source built the same way gives 18 pages, equally clean. The article keeps
the delivered preamble lines that fix PDF dates and trailer identifiers.

## Provenance

- Sources cited by the manuscript: OEIS A307316 and A307317 (checked by the
  source on 2 October 2026); Wright, Bull. AMS 78 (1972) 1032–1034, an online
  text reproduction and a Notices abstract, and Proc. LMS (3) 28 (1974)
  577–594 (metadata only); Gilbert, Canad. J. Math. 8 (1956); Greenhill–McKay
  (arXiv:1303.4218); Cameron–Prellberg–Stark (arXiv:0707.0664);
  Komiske–Metodiev–Thaler (arXiv:1911.04491).
- Repository input: none; the package names no ProveIt commit or path.
- Batch 100 of `docs/incoming`, bundle Report 131; arrival `60f54ea06`,
  placement `36571ae0e`, written 5 October 2026. Single source, so the write
  made no merge choices.
