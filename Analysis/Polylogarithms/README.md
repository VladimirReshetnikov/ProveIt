# Polylogarithms

The canonical reading artifact is the unified manuscript [Polylogarithms and their Arithmetic Bridges](docs/manuscript/polylogarithms.pdf), with [editable LaTeX source](docs/manuscript/polylogarithms.tex) and a [source reconciliation ledger](docs/manuscript/EDITORIAL-LEDGER.md). It consolidates the 39 drafts into a single mathematical development and corrects superseded claims. The original articles, reports and PDFs described below are historical source evidence; the manuscript supersedes them. Its final layout audit is in progress.

Special values and functional equations of polylogarithms and their relatives:
- multiple polylogarithms and multiple zeta values at roots of unity;
- polygamma functions of positive and negative order, and Γ at rational
  arguments;
- Hurwitz-zeta jets and generalized Stieltjes constants;
- Clausen values, polylogarithm ladders and Bloch-group elements;
- the Herglotz–Zagier function.

The project holds 8 articles and 31 research reports from Vladimir
Reshetnikov's PolyLog research programme. **Nothing here is formalized.**
Results are classical (attributed), derived (with proofs in the text), or
experimental (numerically verified at stated precisions, with PSLQ/`lindep`
under the canary discipline). Each article states the epistemic status of each
result.

## Provenance

- **Source.** The material was developed in the private repository
  `VladimirReshetnikov/Smithereens`, project `src/PolyLog`, between 2026-05-31
  and 2026-07-16. Its documents are dated 2026-06-02 to 2026-06-28.
- **Arrival.** It came as `PolyLog.zip` in ProveIt commit `f220191c8`
  (2026-10-07) and was placed in `13f0d8f20`. Only the archive's content was
  placed; the rest of Smithereens `src/PolyLog` was not imported.
- **Byte-identity.** Every file but one is byte-identical to Smithereens
  `da7026ec1369`, at `src/PolyLog/docs/article/` (the two Gaussian articles and
  the MZV introduction), `src/PolyLog/docs/articles/` (the other five) and
  `src/PolyLog/docs/reports/`. The exception is
  `reports/gammaprover-analysis-and-lattice-reducer__38c270ec5048.md`, whose
  header named a local user-profile path to the subject notebook; at Vladimir's
  instruction that path was redacted at placement, with a dated note in the file.
- **Pins.** Each document records its own Smithereens creation time and
  `Repository HEAD`. Those commits, and the Smithereens URL in five article
  footnotes, are in a private repository. Paths written `src/PolyLog/...`
  inside the documents mean this project's root.
- **AI assistance.**
  - The documents were prepared with agentic assistance (Anthropic Claude).
    Five articles say so in their author footnote; the rest come from the same
    sessions.
  - `stieltjes-antiderivative-ladder` records an external referee-style review
    (OpenAI ChatGPT), whose sign correction is in the text.
  - `reports/report-1.tex`, `report-2.md`, `report-3.md` and `report-4.txt` are
    unsigned external AI research outputs. They are kept only as the inputs that
    `polylog-stackexchange-special-value-question-catalog` names; they are not
    results of this project.
- **Not here.** The Smithereens project also holds things this tree does not
  have, and the documents cite them:
  - the verified identity stores (`identities/*.wl`);
  - the reducers, the certificate checker and the verification scripts
    (`tools/`, `tools/scratch/`, `tests/`);
  - the method notes `docs/reduction-method.md`, `docs/proof-certificates.md`,
    `docs/roadmap.md` and `docs/prior-notebooks*.md`;
  - the companion Hypergeometric project (`src/Hypergeometric`, for example
    `central-binomial-arcsin-ladder`).

  Links of the form `../../tools/…`, `../../identities/…`, `../reduction-method.md`
  and `../proof-certificates.md` therefore do not resolve here.

## Layout

```
docs/
  articles/   8 articles: <name>.tex + <name>.pdf (LuaLaTeX)
  reports/    31 reports: 12 .tex + .pdf, 13 .md session reports,
              2 Stack Exchange catalogs, report-1..4 (external inputs)
```

Report filenames keep their Smithereens suffix `__<12 hex>`, a Smithereens
commit prefix. Article ↔ report links are listed below.

| Thread | Article | Source and companion reports |
|---|---|---|
| Multiple polylogarithms and MZVs | `multiple-polylogarithms-introduction` (expository); `gaussian-multiple-polylog-depth`; `gaussian-eisenstein-double-polylogs` | `mzv-wolfram15-verification`; `eisenstein-gaussian-mixed-cuberoot-doubles` (completes the double-polylogarithm article's mixed points) |
| Polylog ↔ polygamma | `polylog-polygamma-bridge` | `loggamma-integrals-clausen-bridge`, `binet-malmsten-lambert-bridge` |
| Γ at rationals | `gamma-lattice-and-certificates` | `gammaprover-analysis-and-lattice-reducer`, `trigroot-gamma-identities`, `phase3-multiplier-certificates-round1` |
| Polygamma at CM points | `eisenstein-row-sums-cm-polygamma` | `polygamma-complex-arguments-cm-lattices` |
| Stieltjes antiderivatives, ψ^(−n) | `stieltjes-antiderivative-ladder` | `stieltjes-antiderivatives-moments`, `negapolygamma-landscape` |
| Stieltjes parameter derivatives | `stieltjes-parameter-derivative-tower` | `stieltjes-derivative-relations`, `stieltjes-second-parameter-derivative-s3-layer`, `stieltjes-general-k-duality-and-gamma2-tables`; precursor `stieltjes-linear-relations-hunt` |
| Herglotz function | – | `herglotz-tables-verification`, `herglotz-rational-values`, `herglotz-bridges`, consolidated in `herglotz-arithmetic-study`; follow-up `herglotz-stark-regulators` |
| Ladders and Bloch groups | – | `golden-polylog-ladders`, `ladders-as-bloch-elements`, `dilogarithm-ladders-verification` |
| Clausen values, special points | – | `clausen-roots-of-unity`, `polylog-vertical-line`, `cleo-arctan-sin-chi2` |
| Literature | – | `polylog-stackexchange-special-value-question-catalog` (inputs `report-1`…`report-4`), `polygamma-stackexchange-special-value-question-catalog` |

## Status of claims, and known defects

These items were found at intake (2026-10-07, placement `13f0d8f20`) and in the
continuations of 8 October 2026 (batch 138, placement `06039f4794`), and were
checked at intake. They are recorded here because the delivered files are not
edited. Corrections proposed by the continuations carry their register numbers:
`C01`-`C22` (`reports/corpus-corrections/12-relation-spaces-CORRECTIONS.md`), `X1`-`X17`
(`10-exact-structure-CORRECTIONS.txt`, numbered by its sections), `H`/`S`/`CM`/`B`
ids (`reports/herglotz-cyclotomic-obstructions/data/proposed_corrections.json`).

### False as printed

- **`reports/report-1.tex`** (external input) states
  `6 Li₂(1/3) − Li₂(1/9) = π²/6 − ln² 3`. The correct value is `π²/3 − ln² 3`;
  the printed one is short by exactly `π²/6` (C01).
- **`reports/eisenstein-gaussian-mixed-cuberoot-doubles`, `thm:parallel`** (and the
  abstract, the table at lines 170-184 and the Gaussian dimension claim at
  211-216). The four "new depth-2 constants" `Re Li₄,₁` and `Im Li₅,₁` at the mixed
  points `(i,−i)` and `(ρ²,ρ)` are not new: inverse-argument doubles
  `Li_{a,b}(z,1/z)` reduce at every weight, by partial fractions, to the `(z,1)`
  doubles and single polylogarithms (X1). For example
  `Re Li₄,₁(i,−i) = −587ζ(5)/1024 + 3ζ(2)ζ(3)/32 + 135ζ(4)log2/256`.
- **`gaussian-eisenstein-double-polylogs`, `thm:deligne` / `eq:binomial-dim` and the
  proof of `cor:depth3`.** The binomial formula `dim gr^D_p = C(n,p)` is not a
  dimension of the depth filtration: at weight 6 the depth-one part is spanned by
  `ζ(6)` and `iβ(6)` (`Li₆(−1) = −31ζ(6)/32`, `Li₆(±i) = −31ζ(6)/2048 ± iβ(6)`), so
  it has dimension at most 2, not `C(6,1) = 6`. The stated proof of "genuine depth
  three" is therefore void, not merely conditional (C10, X11).
- **Same article, `prop:7of10`.** The 13 product rows have rank 7 on the ten
  weight-6 triples, but no single triple lies in their span: seven triples can be
  eliminated in terms of three survivors and products; "seven of ten triples are
  depth two" is false as worded (C11).
- **Same article, `eq:G-def`** (and `multiple-polylogarithms-introduction`,
  lines 276-282 and 287). The increasing simplex with `a_j` on `t_j` makes
  `G(0,z⁻¹;1)` divergent; the word dictionary that follows needs the leftmost
  letter outermost (`0 < t_n < … < t_1 < 1`), and the singular letters of
  `Li_{s₁,…,s_k}(z₁,…,z_k)` are inverse **prefix** products `(z₁⋯z_j)⁻¹`, not the
  suffix products the introduction states (C07, X3).
- **Same article, `eq:eis-single`.** `Im Li_n(ρ) = Cl_n(2π/3)` holds for even `n`
  only under the corpus's (Lewin) Clausen convention; at `n = 3`,
  `Im Li₃(ρ) = 2π³/81` while `Cl₃(2π/3) = Re Li₃(ρ) = −4ζ(3)/9` (C22).
- **`multiple-polylogarithms-introduction`.**
  - "Domain of absolute convergence" (lines 231-235): `Li₁(i)` meets the printed
    hypotheses but is not absolutely convergent; a sufficient condition is
    `|z₁| < 1` or `Re s₁ > 1` (C05, X2).
  - `eq:hpl-rec`/`eq:hpl-zeros` (lines 491-499): a leading `0` does not force
    divergence (`H(0,1;z) = Li₂(z)`); line 552 identifies `π²/12 = −Li₂(−1)` with
    `+ζ(2̄)`, but with the printed convention `ζ(2̄) = −π²/12` (X4).
  - `eq:hpl-transforms` (lines 559-579): `z ↦ 1−z` and `z ↦ z²` do not preserve
    the alphabet `{0,1,−1}` (`H(−1;1−z) = log(2−z)`, `H(−1;z²) = log(1+z²)`) (X5).
  - Lines 759-763: `Li₁(z)² = 2Li₁,₁(z,1)` or `2Li₁,₁(z,z) + Li₂(z²)`, not
    `2Li₁,₁(z,z)` plus shuffles; `ζ(2)ζ(3)` is `01 ш 001`, not `001 ш 00001` (X6).
  - Line 456: the weight-6 example should compare `π⁶` and `ζ(3)²`, not `π⁴` (X16g).
- **`gaussian-multiple-polylog-depth`.** `S_p` is defined for `p ≥ 0`, but `S₀`
  diverges (terms `(−1)ⁿHₙ`; its Abel value is `−log2/2`) (C06, X7); the
  comparison with `ζ(2,1,1) + ζ(1,2,1) + ζ(1,1,2)` at line 351 uses two divergent
  series in the article's own convention (C08).
- **`ladders-as-bloch-elements`, `eq:Pm`.** Zagier's `P_m` sums to `j = m − 1`; the
  extra `Li₀` term changes even-`m` values (excess `2log²2/15` at `m = 2`, `z = i/2`).
  The supergolden value at line 96 is `P₄(z₋) = −0.916010467826…`, not
  `−0.91599…` (C09).
- **`reports/stieltjes-derivative-relations`, section 4, lines 146 and 148.** The two
  character bridges need complex conjugation on the `s = −1` side; without it they
  fail for complex characters by `−0.143865275…i` (odd quartic mod 5) and
  `−0.033916259…i` (even cubic mod 7). The two Stieltjes articles print the
  conjugate correctly (X8).
- **`polylog-polygamma-bridge`.** The Clausen component of the polygamma grid has
  parity `(−1)^{n+1}`: odd at even weight, even at odd weight, not always odd
  (lines 149-151; X13, B001, `13-tower-bundle` C6). The prediction of `sec:psim2`
  that `∫₀^{p/q} log Γ` lands in Clausen values, `ζ′(−1)` and logs fails at
  `q = 5`: the even-character term `L′(−1,χ₅)/20` remains (C14; the `1/3`, `1/4`,
  `1/6` examples stand). The same over-reach is in
  `reports/loggamma-integrals-clausen-bridge`, section 1.
- **`gamma-lattice-and-certificates`, line 121.** The raw row count is
  `⌊(N−1)/2⌋ + σ(N) − N`, not uniformly `O(N)` (X14).
- **Herglotz reports.**
  - `herglotz-arithmetic-study` `prop:collapse` (and the same proposition in
    `herglotz-rational-values`, line 139): the criterion "`F(p/q) − F(1)` reduces to
    rational-argument dilogarithms iff `rad(q) | 30`" is false. `F(1/7) − F(1)` is
    pure-logarithmic and `F(6/7) − F(1)` needs only `Li₂(6/7)` (C15, H001). The
    claimed fixed vocabulary `Li₂(1/3)`, `Li₂(1/5)`, `Li₂(2/5)` is false in the
    five-term calculus (H002). The exact formal criterion (T06) is
    `p² ≡ ±1 (mod q)` and `q² ≡ ±1 (mod p)`.
  - `prop:J` (and `herglotz-rational-values`, line 177): `J(2/q)` is also
    pure-logarithmic at `q = 2` and every `4 | q`, e.g. `J(1/2) = π²/48 + ¼log²2`;
    "`J(1/q)` always retains dilogarithms" is false for every even `q` (C16, H005).
  - `thm:deriv` (and `herglotz-rational-values` line 169, `herglotz-bridges` line 71):
    at even `q` the summand `cot(π)Cl₂(π)` is undefined; with the midpoint omitted
    and one `−log2` the law holds (checked `q = 4,5,6,7,8`). "Does not reduce to
    elementary form" is false at `q = 4`: `F′(1/2) = 2 + π²/4` (C17, H006, H007).
  - The paragraph after `thm:F2q` (line 171): `−cot²(πk/q)` has degree
    `φ(q/gcd(k,q))/2`, not `φ(q)/2` (H004); "no simpler form for `q ≥ 7`" fails for
    even `q`, where `F(2/q) = F(1/(q/2))` (H003). The coefficients `cot(2πk/q)` of
    `W(q)` need not lie in `Q(ζ_q)⁺` (`cot(2π/5)` has degree 4) (H008).
  - `herglotz-stark-regulators`: the cubic field `H₀ = Q[x]/(x³−2x²−3x+1)` has
    degree 3 and cannot be the class field `H` of `K = Q(√257)` (degree 6); `H₀` is a
    cubic subfield of `H` (C18, S001). The leading coefficient of `L_K(s,χ)` at
    `s = 0` is `h(H₀)Reg(H₀)` (C19, S002); all five tabulated cubics have
    `h(H₀) = 1` (PARI `bnfcertify`, discriminants 148, 404, 788, 257, 2708), so the
    table's numerical identity stands. At `D₀ = 257` the ray-modulus `L`-function
    differs from the primitive one by the Euler factors at 2 (factor 3) (S003).
- **`reports/polygamma-complex-arguments-cm-lattices`** (body; the article and the
  report's addendum already repair some): the bilateral sum at line 19 needs the sign
  `(−1)^{s+1}` (CM001); line 186 `N((29+12√5)/44) = 1/16`, not 121 (CM003);
  line 387 `E₆(ρ)² = −1728η(ρ)²⁴` (CM007); and "the corresponding modular forms do
  not exist" (line 114; article line 199) should read that they exist and vanish at
  the CM point (`G₄(ρ) = 0`, `G₆(i) = 0`) (CM004).

### Proposed by the continuations, not re-derived at intake

Recorded for the write phase; each is plausible on reading, none was checked
independently: in `stieltjes-antiderivative-ladder`, "the analytic interpolant" (an
interpolant is unique only up to `c·sin 2πz`), the coefficient name in the proof of
`thm:G1half`, and "`q ≥ 5`" → "`φ(q) > 2`" at lines 713-723 (X16a-c); the sign conventions for Nielsen words and kernels in
`multiple-polylogarithms-introduction` (lines 649, 730-737; X16e) and
"the full Goncharov" at line 746 (X16f); `Re G₄` at line 193 of the CM report
(CM002); the vanishing-test prefactor remarks (CM006, X16i) and the Eichler-integral
wording (X16h) of `eisenstein-row-sums-cm-polygamma`; the claimed finite-field
counterexample to an identity of the inspected arXiv v1 of Radchenko–Zagier
(EXT001, third-party, outside this tree).

### Conditional, not a theorem

- `gamma-lattice-and-certificates`, `law:ko`: completeness of the
  reflection-plus-multiplication relations is Rohrlich's conjecture (extended by
  Lang), not a Koblitz–Ogus theorem. The reducer's tables are complete relative to the
  standard relations; its formal quotient at `N ≥ 3` has dimension `φ(N)/2` (C02, X10).
  Its numerical branch-domain guard is not an exact domain certificate (C20).

### Numerical evidence stated as proof or theorem (open questions)

- The Cleo report's "proof" of minimality and non-elementarity (C03).
- The odd-weight (non-membership) half of `thm:alternation` in
  `gaussian-multiple-polylog-depth`; its even-total-weight half is now **proved** (see
  below). "Fifty new depth-2 directions" (lines 377-379) does not follow from fifty
  individual non-memberships (C13, X12c); a Champernowne canary coefficient of zero
  is a diagnostic, not a certificate (X12g, `11-reflection-transition` item 2).
- `gaussian-eisenstein-double-polylogs` `thm:gauss-5`, `thm:eis-1`: the counts are
  coranks of the stated relation matrices, i.e. upper bounds on evaluated spans (C12).
- The `Cl₃(2π/5)`, `Cl₃(π/4)`, `Cl₃(π/6)` "new atoms" and the "exactly" of
  `res:crystal` (`polylog-polygamma-bridge`) (C03, B002, X12d).
- `stieltjes-parameter-derivative-tower` `sec:atoms` (and
  `stieltjes-general-k-duality-and-gamma2-tables`, item 4 and section 6): the six
  second-derivative constants are unreduced candidates, not proved independent (C03,
  X12a, `06-zero-geometry` C1, `13-tower-bundle` C2). Its abstract's
  "elementary" remainder in the `γ₁″(1/4)` duality contains `ζ′(3)`, `ζ(3)` and
  `log A`; `β′(−1) = 2G/π` is a reduction to Catalan's constant (X16d,
  `06-zero-geometry` C4).
- `eisenstein-row-sums-cm-polygamma` `neg:sums` and `res:genus`: failed searches do
  not prove irrationality or exact degree four (C03, CM005, X12e).
- `herglotz-stark-regulators`: fitted coefficients and the unit-index explanation
  (S004); "single regulator iff `C₃`" (S005). `herglotz-arithmetic-study`: the
  irreducibility of the golden antisymmetric dilogarithm and of
  `Σ Li₂(−cot²(πk/q))` (H009).
- `eisenstein-gaussian-mixed-cuberoot-doubles` lines 104-118: the Hurwitz tail is an
  asymptotic expansion and the Wynn accelerator has no error theorem (X15).

Each is an open question, not a defect of the numerics.

### Proved since intake (8 October 2026 continuations; formal statements)

- `thm:rank` of `stieltjes-parameter-derivative-tower` (computed for `q ≤ 30`,
  `k ≤ 3`) and `prop:jetrank` of `stieltjes-antiderivative-ladder` (`q ≤ 30`,
  `k ≤ 4`) hold for every `q` and `k`, as dimensions of the formal quotient by the
  stated distribution (and reflection) relations: `φ(q) − 1`, and
  `φ(q)/2 − 1` (`k` odd) or `φ(q)/2` (`k` even) (C04, X9; three independent proofs in
  `reports/rational-grid-distribution-ranks/`, `corpus-corrections/`,
  `stieltjes-derivative-zeros/`; intake recomputed the exact ranks for `q ≤ 60`).
  They do not assert arithmetic independence of the evaluated constants.
- The trivial-zero case of `rem:parity` is
  `L′/L(k+1,χ) + conj(L″(−k,χ)/(2L′(−k,χ))) = γ + log(2π/q) − H_k`; the factor `1/2`
  is essential.
- The even-total-weight half of `thm:alternation`: for every `m ≥ 0`,
  `S_{2m+1} = (2m+1)β(2m+2) − 2β(2m+1)log2 − Σ_{j=1}^{m}(2 − 2^{−2j})β(2m−2j+1)ζ(2j+1)`
  (three independent proofs; `S₅`, `S₇` are the cases `m = 2, 3`).

### Stale PDFs

The PDFs of `herglotz-bridges`, `herglotz-rational-values` and
`herglotz-tables-verification` were compiled in one pass and show `??` for 3, 19 and 4
references. Their `.tex` sources build cleanly in two passes (C21).

### Confirmed at intake

Independent mpmath checks (20-40 digits) of displayed results in 5 articles and 7
reports all passed at the first intake; the one failure of the 59 checks is the
`report-1` value above. Batch 138 re-checked, independently: all 22 corrections
C01-C22 and the computable items of the other registers; no proposed correction was
found wrong. Results reconfirmed include the `F(1/q)` theorem at `q = 7`, the
`F(n/(n+1))` family at `n = 6`, `J(2/3)`, `J(2/5)`, the log-gamma examples at
`1/3`, `1/4`, `1/6`, and `G₁₂ = (18G₄³ + 25G₆²)/143` in the unnormalized convention.

## Continuations (batch 138, 8 October 2026)

Six external continuations, all AI-assisted research drafts pinned to `c78c7c3dc2`
or `3a6d80ed61` (whose Polylogarithms tree equals `a87af186c`), are placed as five
merged reports under `docs/reports/`, one per thematic spine. Manuscripts are not
edited; files of merge members carry the prefix of their manuscript number.

| Report | Spine | Base | Other sources |
|---|---|---|---|
| `stieltjes-derivative-zeros/` | `γ_n^{(k)}(a)` has at most `n` positive zeros for every `k`, exactly `n` for large `k`, full ray expansions; `n = 1` brackets; regularized trivial-zero bridges | 13 (`polylogarithms_research_bundle`, uniform in a Lerch deformation) | 06 (`ProveIt_Stieltjes_Zero_Geometry_Research`: exact count for `n ≤ 4` at every `k`, half-unit bracket, three-term `n = 1` law, parity kernels); 12 (sections on zeros and the bridge); 10 (spectral expansion at `a = 1`, normalized bridges) |
| `rational-grid-distribution-ranks/` | all-denominator formal ranks (character normal form), finite jets, reflection | 10 (`polylogarithms-exact-structure`, arbitrary weights in any commutative algebra) | 12, 13 |
| `alternating-harmonic-polylogarithms/` | `S_{2m+1}` at every weight; reflection for `T_{p,r}`; depth-exponent transition; inverse-argument mixed doubles | 11 (`polylogarithms_reflection_depth_transition_2026-10-07`) | 10, 12 |
| `herglotz-cyclotomic-obstructions/` | all-conductor relations of `β_q(a)`, exact five-term reduction criterion, `J(2/q)` classification, optimal truncation | 09 (`herglotz_research`, single source) | corrections credited from 12 (C15-C19) |
| `corpus-corrections/` | the correction registers of all six deliveries | 12 (`polylogarithms_research`, C01-C22) | 06, 10, 11, 13 registers; 09's `data/proposed_corrections.json` |

## Notation

- "Herglotz function" is Zagier's `F(x) = Σₙ (ψ(nx) − log nx)/n`
  (Radchenko–Zagier). It is unrelated to the Herglotz–Nevanlinna functions of
  `Algebra/SurrealNumbers/docs/surcomplex/hahn-herglotz-positivity`.
- `ψ^(−n)` follows the Wolfram `PolyGamma[−n, ·]` convention (iterated integrals
  from 0).
- `γₙ(a)` are the Laurent coefficients
  `ζ(s,a) = 1/(s−1) + Σ (−1)ⁿ γₙ(a) (s−1)ⁿ/n!`, and `Γₙ(p) = ∫₁^p γₙ`.
- `Cl_k` and `Ti₂` follow Lewin.

## Building

The articles and `.tex` reports are self-contained. They have no bibliography
database and no inputs. They build with two LuaLaTeX passes (MiKTeX), in a
scratch copy:

```powershell
lualatex -interaction=nonstopmode <name>.tex; lualatex -interaction=nonstopmode <name>.tex
```

The numerical claims were produced with Wolfram Language 15, mpmath, PARI/GP and
FLINT, through scripts that are not in this tree (see Provenance).
