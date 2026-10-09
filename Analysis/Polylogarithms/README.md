# Polylogarithms

The canonical reading artifact is the unified manuscript [Polylogarithms and their Arithmetic Bridges](docs/manuscript/polylogarithms.pdf), with [editable LaTeX source](docs/manuscript/polylogarithms.tex) and a [source reconciliation ledger](docs/manuscript/EDITORIAL-LEDGER.md). It consolidates the 39 drafts into a single mathematical development and corrects superseded claims. The original articles, reports and PDFs described below are historical source evidence; the manuscript supersedes them. The [validation record](docs/manuscript/VALIDATION.md) covers source reconciliation, 98 fresh focused checks, and the converged and visually reviewed 100-page PDF.

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

These items were found at intake (2026-10-07, placement `13f0d8f20`). They are
recorded here because the delivered files are not edited.

- **False as printed (external input).** `reports/report-1.tex` states
  `6 Li₂(1/3) − Li₂(1/9) = π²/6 − ln² 3`. The correct value is `π²/3 − ln² 3`;
  the printed one is short by exactly `π²/6`. Duplication `Li₂(x²) = 2Li₂(x) + 2Li₂(−x)`
  with Landen at `−1/3` gives the classical value.
- **Conditional, not a theorem.** `gamma-lattice-and-certificates` attributes the
  completeness of the reflection-plus-multiplication relations to Koblitz–Ogus.
  Koblitz–Ogus (appendix to Deligne, Corvallis 1979) supply the algebraicity
  direction: the Γ-monomials that satisfy their criterion are algebraic. The
  converse is that every algebraic Γ-monomial at rationals comes from the
  reflection and multiplication relations. That is Rohrlich's conjecture,
  extended by Lang to polynomial relations, and it is open; `law:ko` should be
  read as that conjecture. The reducer's tables are complete relative to the
  standard relations, and the irreducibility of its bases is conditional on the
  conjecture.
- **Numerical evidence stated as proof or theorem.**
  - The Cleo report's "proof" of minimality and non-elementarity is a
    height-bounded integer-relation search.
  - The odd-weight (non-membership) half of the depth-alternation theorem of
    `gaussian-multiple-polylog-depth` is PSLQ-negative evidence.
  - The "genuinely depth three" triples of `gaussian-eisenstein-double-polylogs`
    rest on the period conjecture.
  - The `Cl₃(2π/5)`, `Cl₃(π/4)`, `Cl₃(π/6)` "new atoms" of
    `polylog-polygamma-bridge` are new only numerically.
  - `thm:rank` of `stieltjes-parameter-derivative-tower` is computed for
    `q ≤ 30`, `k ≤ 3`.

  Each is an open question, not a defect of the numerics.
- **Stale PDFs.** The PDFs of `herglotz-bridges`, `herglotz-rational-values` and
  `herglotz-tables-verification` were compiled in one pass and show `??` for 3,
  19 and 4 references. Their `.tex` sources build cleanly in two passes.
- **Confirmed at intake.** Independent mpmath checks (20–40 digits) of displayed
  results in 5 articles and 7 reports all passed; the one failure of the 59
  checks is the `report-1` value above. These include:
  - the two Radchenko–Zagier Table 1 errata (`n = 43`, `n = 61`);
  - the `F(1/q)` and `F(2/q)` theorems;
  - the full `Γ₁(1/3)`, `Γ₁(1/4)` and `γ₁''(1/4)` displays;
  - the harmonic-number master identity and bridge law;
  - the `S₅`, `S₇` closed forms;
  - Vladimir's trig-root Γ identity;
  - every closed form of the Cleo report.

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
