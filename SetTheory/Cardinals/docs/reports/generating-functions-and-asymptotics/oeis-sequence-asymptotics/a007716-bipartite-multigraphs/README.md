# Unlabeled Bipartite Multigraphs: Asymptotic Expansions, Rare Symmetries and Connectivity

**OEIS A007716 and its inverse growth (Part I); probability laws for A007716 and asymptotic expansions for A007718 (Part II)**

This research report was merged on 5 October 2026 (batch 100) from two
manuscripts of ProveIt's incoming-reports intake, Research Reports 88 and 92
of the session bundle of Reports 1–243 that arrived in commit `60f54ea06`.
Report 88 (1 October 2026) is Part I, the base; Report 92 (2 October 2026)
is Part II. Report 92 is a sequel to Report 88, not a rival text: it calls
Report 88 "the preceding report", shipped its archive unchanged inside its
own package, and uses its estimates as explicit inputs. Both manuscripts
carry the author line and PDF metadata "Research note prepared for Vladimir
Reshetnikov with OpenAI"; neither says "prepared for private review".

| Source | Manuscript | Archive | Pin | Arrived | Placed | Printed as |
|---|---|---|---|---|---|---|
| base | batch 100, no. 01 (bundle Report 88) | `ProveIt_A007716_Asymptotics_and_Inverses.zip` (384,833 bytes; 17 files in `A007716_Asymptotics/`; `article.tex`, 469 lines, 37 labels; 10-page PDF *Asymptotic Expansions for Unlabeled Bipartite Multigraphs: OEIS A007716 and its inverse growth*) | none (names no ProveIt commit or path) | `60f54ea06` | `36571ae0e` | Part I (Sections 1–11); files prefixed `01-asymptotics-` |
| sequel | batch 100, no. 02 (bundle Report 92) | `ProveIt_A007716_Symmetry_and_A007718_Connectivity.zip` (771,866 bytes; 14 files in `A007716_Symmetry_and_A007718_Connectivity/`; `article.tex`, 414 lines, 44 labels; 10-page PDF *Rare Symmetries and Connected Bipartite Multigraphs: Probability laws for A007716 and asymptotic expansions for A007718*) | none | `60f54ea06` | `36571ae0e` | Part II (Sections 12–20); files prefixed `02-symmetry-` |

The placement commit `36571ae0e` deleted both archives from `docs/incoming`;
they survive in the arrival commit:

```
git show 60f54ea06:docs/incoming/ProveIt_A007716_Asymptotics_and_Inverses.zip > <scratch>/88.zip
git show 60f54ea06:docs/incoming/ProveIt_A007716_Symmetry_and_A007718_Connectivity.zip > <scratch>/92.zip
```

Report 92's `dependency/ProveIt_A007716_Asymptotics_and_Inverses.zip` is
byte-identical to the Report 88 archive (SHA-256 `4c503e6ba487c518…`); it is
not shipped a second time.

**Status: AI-assisted, unrefereed, not formalized.** No Lean or Rocq
development in ProveIt treats A007716 or A007718, and nothing here is
machine-checked. The intake reran both packages on copies and spot-checked
the mathematics (see "Checks by the intake"); it did not re-derive every
proof.

## Files

```
README.md                                         this guide (replaces the two delivered READMEs)
article.tex                                       the merged report (LaTeX, internal bibliography)
article.pdf                                       the compiled report, 27 pages
01-asymptotics-verification.md                    (01) scope of its checks, as delivered
02-symmetry-verification.md                       (02) its proof gates, checks and dependency scope, as delivered
code/01-asymptotics-check_cycle_formula.py        (01) cycle-type Burnside sum, 2,714 types through n = 20 (standard library)
code/01-asymptotics-check_invariant_partitions.py (01) direct fixed-partition enumeration through n = 8, 67 types (standard library)
code/01-asymptotics-check_independent.py          (01) enumeration through n = 10, mass normalization, Ewens moments (SymPy)
code/01-asymptotics-compute_first_two.py          (01) Q1, Q2 and P1 from marked profiles and Poisson moments (SymPy)
code/01-asymptotics-reconstruct_Q2.py             (01) a second, compressed reconstruction of Q1 and Q2 (SymPy)
code/02-symmetry-check_graphs.py                  (02) all partition pairs through n = 6: 44,169 pairs, 438 classes (standard library)
code/02-symmetry-check_kernel_and_giant.py        (02) 226,342 edge permutations: kernel fibers, leaf lifts, giant identity (standard library)
code/02-symmetry-check_cycles.py                  (02) 2,714 cycle types through n = 20: marked mass, Y identity, A007718, reciprocal (standard library)
code/02-symmetry-build_local.sh                   (02) its LaTeX build script, for its own delivered .tex (not shipped)
code/02-symmetry-verify_local.sh                  (02) its replay driver, for the delivered layout (see "Rerunning")
data/01-asymptotics-check_cycle_formula.json      (01) output of check_cycle_formula.py
data/01-asymptotics-check_invariant_partitions.json (01) output of check_invariant_partitions.py
data/01-asymptotics-check_independent.json        (01) output of check_independent.py
data/01-asymptotics-compute_first_two.json        (01) Q0, Q1, Q2 and P1 as SymPy expressions
data/01-asymptotics-reconstruct_Q2.json           (01) Q1, Q2, the Bell-shift coefficients and the seven contributions to Q2
data/02-symmetry-check_cycles.json                (02) output of check_cycles.py
data/02-symmetry-check_graphs.json                (02) output of check_graphs.py
data/02-symmetry-check_kernel_and_giant.json      (02) output of check_kernel_and_giant.py
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. `article.tex` is manuscript 01's
`article.tex` (staged unchanged by the placement) with manuscript 02 merged
in and the edits listed in the article's Appendix A; `article.pdf` is a
build of it, not either delivered PDF. No staged file contains a CR byte.

## Delivery names and shipped names

| Delivered (01, inside `A007716_Asymptotics/`) | Shipped |
|---|---|
| `article.tex` | `article.tex` (Part I of the merged text) |
| `README.md` | replaced by this `README.md` (the placement staged it here unchanged) |
| `verification.md` | `01-asymptotics-verification.md` |
| `code/X.py` (5 files) | `code/01-asymptotics-X.py` |
| `code/X.json` (5 files) | `data/01-asymptotics-X.json` |
| `article.pdf`, `SHA256SUMS`, `build_local.sh`, `code/reconstruct_Q2.replay.log` | not shipped (below) |

| Delivered (02, inside `A007716_Symmetry_and_A007718_Connectivity/`) | Shipped |
|---|---|
| `article.tex` | merged as Part II of `article.tex` |
| `README.md` | replaced by this `README.md` |
| `verification.md` | `02-symmetry-verification.md` |
| `build_local.sh`, `verify_local.sh` | `code/02-symmetry-build_local.sh`, `code/02-symmetry-verify_local.sh` |
| `code/X.py` (3 files) | `code/02-symmetry-X.py` |
| `code/X.json` (3 files) | `data/02-symmetry-X.json` |
| `article.pdf`, `SHA256SUMS`, `dependency/ProveIt_A007716_Asymptotics_and_Inverses.zip` | not shipped (below) |

Not shipped, all retrievable from `60f54ea06`:

- both delivered PDFs (the report ships its own build);
- both `SHA256SUMS` manifests (repository policy; the intake verified all 16
  and 13 entries against fresh extractions);
- 01's `build_local.sh`, byte-identical (blob `890ccb0f9`) to the repository
  file
  `SetTheory/Cardinals/docs/reports/enumerative-combinatorics/preorder-root-polytopes/code/15-leaf-compression-build_local.sh`;
- 01's `code/reconstruct_Q2.replay.log`, byte-identical to
  `code/reconstruct_Q2.json` (shipped as `data/01-asymptotics-reconstruct_Q2.json`);
- 02's `dependency/` archive, identical to the Report 88 archive (its
  content is Part I and the `01-asymptotics-` files);
- 02's `article.tex` and `README.md` (merged into this report).

Delivered text that still names delivery paths or unshipped files:

- Manuscript 01's delivered README (replaced by this file) promised
  `build_local.sh` and `SHA256SUMS` and gave replay lines such as
  `python -O code/check_cycle_formula.py`; none of those paths exists here.
- `01-asymptotics-verification.md` and `02-symmetry-verification.md` name
  the scripts by their delivery names (`check_cycle_formula.py`, …), and
  02's says the package's manifest passed and the prior ZIP's integrity
  check passed — statements about the delivered package.
- `code/02-symmetry-verify_local.sh` runs `sha256sum -c SHA256SUMS`, tests
  `dependency/ProveIt_A007716_Asymptotics_and_Inverses.zip`, runs
  `code/$check.py`, copies outputs to `/tmp`, calls `build_local.sh` and
  reads `build/pass-2.stdout`; none of these is valid in the shipped layout.
- `code/02-symmetry-build_local.sh` (like 01's unshipped one) hard-codes the
  TeX trees `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, builds
  into `build/` beside itself and copies `article.pdf` over the delivered
  PDF; 02's sets `TZ=UTC` and `SOURCE_DATE_EPOCH=1790899200`.
- The article's Section 11 says "The archive contains … a manifest" and
  Section 20 that the preceding estimates "are included as an explicit
  dependency"; dated notes there say what is shipped instead.

## Label prefix

Part I's labels carry `bpm:` (manuscript 01's 37 delivered labels with the
prefix, plus 19 added by the write); Part II's carry `bpm:sym:` (38 of
manuscript 02's 44 labels, plus 10 added). Manuscript 02's `eq:Z`,
`eq:allinput`, `eq:P1`, `eq:burn`, `eq:ewens` and `eq:bellshift` restate
displays of Part I and are not reprinted. 104 labels in all. Part I keeps
manuscript 01's section, theorem and equation numbers (the one display the
write numbered is tagged (28a)); Part II's section and theorem numbers are
manuscript 02's plus eleven.

## What is claimed

Write a_n for A007716 (bipartite multigraphs with n edges, no isolated
vertices and two distinguished shores, up to shore-preserving isomorphism),
w = W(n), and B_n for the Bell numbers.

Part I (Report 88):

- the relative equivalent a_n ~ (B_n^2/n!) e^{w^2/2} (Theorem 1.1), whose
  divergent factor e^{w^2/2} comes from parallel edges; this strengthens the
  logarithmic estimate of Pavlichin–Jiao–Weissman;
- an exact invariant-partition formula for the Burnside count, the positive
  weighted count Z_n with a_n/Z_n = 1 + O(log^3 n/n), and a complete
  fixed-order expansion with rational coefficients Q_j(w) and a finite
  coefficient algorithm (Theorem 1.2), with Q_1 and Q_2 explicit;
- a Bell expansion with explicit β_1 and uniform finite shifts B_{n-s}/B_n;
- smooth inverse models F_J with integer-threshold brackets and a
  compositional inverse rule;
- A007716 is not P-recursive (Proposition 8.1);
- for r ≥ 3 shores the identity term is a relative equivalent, with first
  excess W(n)^r/(2n^{r-2}) (Proposition 9.1).

Part II (Report 92), for the uniform measure on isomorphism classes:

- P(Aut(G) ≠ 1) = 2w^3/n + O((1+w)^7/n^2), and every group other than the
  trivial one and a single leaf-transposition C_2 has probability
  O((1+w)^6/n^2) (Theorem 12.1), via the exact leaf-transposition mass
  Y_{n-2} (Lemma 14.1) and the positive residual (Lemma 15.1);
- the connected counts c°_n (A007718 at positive indices) satisfy
  c°_n = Σ_{j≤J} ρ_j a_{n-j} + O_J(a_{n-J-1}) with 1/A(z) = Σ ρ_j z^j
  (Theorem 12.2); disconnection has probability w^2/n plus an explicit second
  term, usually by one isolated edge (exact probability a_{n-1}/a_n);
  exact fragment law P(fragment = Γ) = c°_{n-j}/a_n;
- all-orders expansion of c°_n with P°_1 = P_1 − w^2 and P°_2 explicit,
  inverse brackets for A007718, and A007718 is not P-recursive (Section 18).

Part II answers Part I's further question 2 (a scaled description of rare
vertex automorphisms) at leading order; the question stays open for the next
coefficient (dated note in Section 10; Part II's Question II.1).

## What is not claimed

From the sources, kept in the article: no convergence of any infinite
series; no effective constants or numerical onset; no classification of
exponentially small sectors or Stokes data; no exact interpolation or
unconditional single-ceiling inverse; no exhaustive or first-in-literature
priority (Bell saddles, Burnside averaging, Dobinski's identity, Poisson
moments, the ODE criterion and the component method are classical); the
reciprocal and Euler product are formal; probabilities are for the uniform
measure on classes, not a labelled or automorphism-weighted one; the
connected count uses c°_0 = 0 where OEIS A007718 lists 1; the exact programs
check finite identities and transcription, not the asymptotic tail proofs;
manuscript 02 does not re-audit Report 88's analytic estimates; neither is
refereed or a Lean formalization.

Standing rule (unproved claims are never dropped; Vladimir, 4 October 2026).
No claim of either manuscript was found to be wrong. The write records as
open questions, with source, sketch and what is missing:

- Part I, Question I.5: the all-orders uniformity of the Bell saddle
  (Section 4), argued in one paragraph;
- Part I, Question I.6: the exponents M_J, M'_J of Theorem 1.2 and the
  expansion (28a), shown to exist but not computed for J ≥ 2;
- Part I, Question I.7: the order-one remainder O((1+w)^10/n^2), asserted
  from three displayed error sizes;
- Part I, Question I.8: Q_2, printed without derivation and resting on the
  two delivered programs (the write's independent check covers its unmarked
  part only; below);
- Part II, Question II.4: the existential exponents of Theorem 12.2,
  (55), the estimate of a_{n-2}/a_n and Theorem 18.1;
- Part II, Question II.5: Part II's dependence on Part I's sketched steps.

Part I's own four further questions (Section 10) and Part II's three
research directions (Questions II.1–II.3) are printed as delivered; the
second of Part I's is re-scoped by a dated note.

## Notation

The two manuscripts reuse letters for different notions (R_n, c, b, D, K, L,
E, η, F_J, x_J, and others); manuscript 02 itself uses D for the cutoff and
for a ratio correction, and c for cycle counts and for A007718. Part I is
printed in its own letters; every rename is in Part II, listed with the
false readings to avoid in the article's Table 1 and Appendix A. The most
visible: c°_n for A007718 (02: c_n), ρ_j for the reciprocal coefficients
(02: b_j), δ(w) (02: D(w)), the residual 𝓡_n (02: R_n), Λ(G) for the
number of leaf transpositions (02: L(G)), Ω_G for the parallel-edge kernel
(02: K_G), P°_j for the connected coefficients (02: C_j), and F°_J, x°_J for
the connected model and its inverse (02: G_J, x_J). Manuscript 02 writes
η = Cw/n where Part I proves η = C' log n/n; the two are equivalent since
w ~ log n.

## Relation to other reports

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a277364-bell-asymptotics`
  already proves the order-one Bell expansion that Part I's (15) records,
  with the same β_1 (its P(r) = −β_1) and error; Part I's derivation is a
  second route, credited in a dated note in Section 4. The all-orders form
  and the shifts are not there.
- `.../a260700-parabolic-double-cosets` names A120733, the labelled analogue
  Σ M_{k,l}(n) of Part I's weighted count Z_n = Σ M_{k,l}(n)/(k! l!).
- `.../a307316-leafless-multigraphs` (batch 100, written before this report)
  counts unlabelled loopless multigraphs with minimum degree two on the scale
  W(2m) by a different method and leaves a sharp unlabelled equivalent open
  (`lfm:q:sharp`), naming Part I's invariant-partition formula and Part II's
  automorphism estimate as a possible route; its `lfm:prop:deficit` uses the
  leafless counterpart of Part II's isolated-edge bijection, conditionally,
  and its upper bound `lfm:eq:supportmain` carries the analogous factor
  e^{w^2/2} with w = W(2m) (a scale clash with this report's w = W(n)).
- `.../a088714-bell-scale-growth` compares A088714 with the Bell numbers.

No theorem is shared with any of them. A reciprocal note for a260700 is
proposed separately; a307316 already cites this report.

## Checks by the intake

Before placement (dossier, 5 October 2026): both manifests verify; the
symbolic identities Q_1 = R_1 + w^3, P_1 = Q_1 + 2β_1 − 1/12, β_1 from the
printed Gaussian correction plus 1/12, the Φ' identity (to 1e-165 at
x = 5, 50, 1000), δ(w) = −α_1 + (w−1)/(2(w+1)), w^2 δ + 3w^4 =
w^3(3w^3+5w^2+3w+2)/(w+1)^2 and the P°_2 formula were confirmed with
SymPy/mpmath; n(B_n/lead − 1) = −0.36781, −0.47929, −0.59479 against
β_1 = −0.36733, −0.47919, −0.59477 at n = 200, 1000, 5000; n·Y_{n−2}/Z_n =
73.75, 141.91 against w^3 = 77.07, 144.67 at n = 300, 1000; and
n((Z_n + Y_{n−2})/lead − 1) = 88.50, 180.06 against Q_1 = 88.47, 177.23.

Write (5 October 2026): all eight programs rerun on copies in the delivered
layout. 01's under `uv run --no-project --with sympy==1.14.0 python -O`
(Python 3.13.5): check_cycle_formula 2 s, check_invariant_partitions 3 s,
check_independent 22 s, compute_first_two 9 s, reconstruct_Q2 16 s. 02's
under `py` (Python 3.14.4): check_graphs 5 s, check_kernel_and_giant 11 s,
check_cycles 1 s. All print PASS, and every output equals the shipped JSON
after removing CR bytes (on Windows `Path.write_text` writes CRLF).
Independent partial check of Q_2: the four contributions of
`data/01-asymptotics-reconstruct_Q2.json` without selected cycles sum to the
second coefficient R_2(w) of Z_n; evaluating Z_n by the exact mass formula
(Part I, (5)) to 40 digits, the ratio of n^2(Z_n/lead − 1 − R_1/n) to
R_2(W(n)) is 1.0412, 1.0400, 1.0245, 1.0144, 1.0076, 1.0040 at n = 100,
300, 1000, 3000, 10^4, 3·10^4 (numerical evidence for the unmarked part of
Q_2 only).

Independent check of the batch-100 write (7 October 2026): an adversarial
check by the intake after the write (`72091374c`) re-derived every
statement the write added, with its own code, from fresh extractions of both
archives. Provenance facts, label counts (104: Part I 37 + 19, Part II 38
of 44 + 10) and the numerals of both texts were recounted; OEIS A007716
(#55), A007718 (#18) and A120733 (#102) were fetched again (the Euler
transform of A007718 with c°_0 = 0 gives A007716 to n = 50; the reciprocal
coefficients are 1, −1, −3, −3, −8, −8, −38; Σ M_{k,l}(n) is A120733 for
n ≤ 8); the cited passages of a277364, a260700 and a307316 and
Pavlichin–Jiao–Weissman's Theorem 12 were read. The four unmarked
contributions of `data/01-asymptotics-reconstruct_Q2.json` add up to the
printed R_2, and Z_n computed independently of the mass formula, as
Σ_d [n, n−d](B_{n−d}/B_n)² with exact Stirling numbers of the first kind,
gives the ratios 1.04124, 1.04000, 1.02454, 1.01443, 1.00760, 1.00404 at
the six sizes above. No mathematical error and no defect of the write was
found; the check is recorded at the end of Appendix A.

## Building

```
cp article.tex <scratch>/ && cd <scratch>
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX here); 27 pages, no warnings, no overfull boxes. Copy only
`article.pdf` back.

## Rerunning

Every program writes its JSON beside itself (`Path(__file__).with_suffix('.json')`),
so run it on a copy, never in `code/`: in place it would create
`code/01-asymptotics-X.json` next to the shipped program. Recreate the
delivered layout in a scratch directory:

```
mkdir -p <scratch>/A007716_Asymptotics/code <scratch>/A007716_Symmetry/code
for f in check_cycle_formula check_invariant_partitions check_independent compute_first_two reconstruct_Q2; do
  cp code/01-asymptotics-$f.py <scratch>/A007716_Asymptotics/code/$f.py; done
for f in check_graphs check_kernel_and_giant check_cycles; do
  cp code/02-symmetry-$f.py <scratch>/A007716_Symmetry/code/$f.py; done
cd <scratch>/A007716_Asymptotics && for f in check_cycle_formula check_invariant_partitions check_independent compute_first_two reconstruct_Q2; do
  python -O code/$f.py; done        # SymPy 1.14.0 for three of them
cd <scratch>/A007716_Symmetry && for f in check_graphs check_kernel_and_giant check_cycles; do
  python code/$f.py; done           # standard library only
```

then compare each `code/X.json` with the shipped `data/01-asymptotics-X.json`
or `data/02-symmetry-X.json` (strip CR on Windows). On this machine use `py`
or `uv run --no-project --with sympy==1.14.0 python` for `python`.
`code/02-symmetry-verify_local.sh` and the build scripts work only in the
delivered layout on a POSIX host with TeX Live at the hard-coded paths:
re-extract the arrival commit's archive there and run `bash verify_local.sh`.

## Third-party data

`code/01-asymptotics-check_cycle_formula.py` and
`code/02-symmetry-check_cycles.py` embed the terms a_0..a_20 of A007716 (and
the second also c_0..c_20 of A007718) from the OEIS, and the outputs
`data/01-asymptotics-check_cycle_formula.json`,
`data/01-asymptotics-check_independent.json`,
`data/01-asymptotics-check_invariant_partitions.json` and
`data/02-symmetry-check_cycles.json` record some of them. OEIS data are
licensed CC BY-SA 4.0, not MIT-0. Nothing was submitted to the OEIS.
