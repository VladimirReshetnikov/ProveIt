# Stirling Transforms of the Catalan Numbers

**OEIS A064856 and A086662: second-kind asymptotics to every fixed order, the Bell comparison and integer-safe inversion; first-kind resummed and inverse-logarithmic asymptotics, inversion and the Catalan tilt of permutations; Spiridonov's numerical model refuted**

This is a research report built on 6 October 2026 (write batch 107) from two
manuscripts of one external research session, Reports 205 and 207 of the
session bundle of Reports 1–243, both dated 4 October 2026. With `C_k` the
Catalan numbers, `S(n,k)` the Stirling numbers of the second kind and
`c(n,k)` the unsigned Stirling numbers of the first kind, they study

`a⁽²⁾_n = Σ_k S(n,k) C_k` ([A064856](https://oeis.org/A064856)) and
`a⁽¹⁾_n = Σ_k c(n,k) C_k` ([A086662](https://oeis.org/A086662)).

Both start from one positive moment representation,
`C_k = ∫₀⁴ x^k ϱ(x) dx`, `ϱ(x) = √((4−x)/x)/(2π)` (the Marchenko–Pastur law
of ratio one; the identification is the write's). Inside each Part of the
article `a_n` is that Part's own sequence.

- **Part I** (Report 205, the base; corrected revision 2): with `r = W(n/4)`,
  `a_n = L_n{Σ_{j≤M} Q_j(r)/n^j + O_M((r/n)^{M+1})}` for every fixed `M`,
  `n!` kept exact, `Q_j` rational in `r` with `(1+r)^{3j}Q_j` a polynomial of
  degree at most `4j`; `log(a_n/B_n) ~ (log 4) n/log n` against the Bell
  numbers; an all-fixed-order inverse with a two-ceiling enclosure and an
  elementary (non-Lambert) carrier equation; and the single ceiling
  `⌈I₀(a_n)⌉ = n + 1` for all large `n`. Revision 2 credits to Bauer and
  Golinelli (2001) the spectral-moment inequality `B_k ≤ M_{2k} ≤ a_k` that
  Spiridonov's 2004 thesis stated as Conjecture 3.3, with its normalization
  and root-scale consequences (no novelty claim).
- **Part II** (Report 207): a resummed expansion with relative error
  `O_J(n^{−J−1})`; the all-fixed-order expansion in `1/log n`, whose
  coefficients diverge like `−(24/π)4^{−k}Γ(k)`, with an exact convergent
  incomplete-gamma completion; an explicit inverse about
  `t₀ = y/W₀(y/e)`, a resummed inverse with two ceilings and finite Newton
  iteration; a local mod-Poisson-type cycle law with a CLT;
  `d_TV(P_n, Ewens(4)) ~ 3√(2/π)/(8√(log n))`; an exact size-dependent Ewens
  mixture with a boundary Gamma(3/2) law.
- **Added by the write**: Remark 6.2, a proof that Spiridonov's numerical model
  is not an asymptotic; the classification of every inverse against the
  transseries volume; a finite check of `B_k ≤ M_{2k} ≤ a_k` on OEIS A094149;
  a dated correction of one sentence of Part II about Part I; Section 21.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| *The Stirling transform of Catalan numbers: Lambert-saddle asymptotics, Bell comparison, and integer-safe inversion* (author line "Report 205", 4 October 2026, "Corrected revision 2"); the base | 205 | `Report205.zip` (462,489 bytes, 19 files; `Report205.tex`, 659 lines, 17 pp.) | none | `3988bf5c4` | Part I, Sections 1–9, plus the write's Remark 6.2 |
| *First kind Stirling Catalan asymptotics and inversion* (author line "Report207", 4 October 2026) | 207 | `Report207.zip` (512,741 bytes, 15 files; `Report207.tex`, 489 lines, 16 pp.) | none | `3988bf5c4` | Part II, Sections 10–20, plus the write's Section 21 |

Both archives arrived unchanged in `60f54ea06` ("Arrival: 177 research
archives from the session bundle of Reports 1-243") and survive there
(`git show 60f54ea06:docs/incoming/<archive> > <archive>`); the placement
commit `3988bf5c4` (batch 107, cluster 107-STCAT) removed them from
`docs/incoming/`. The write is "Write batch 107
(a064856-stirling-catalan-transforms): new report, Stirling transforms of the
Catalan numbers".

**Status.** Unrefereed; not formalized; no statement has been checked by a
proof assistant. Neither manuscript names an author, a tool or an addressee,
says it is AI-assisted, or carries "prepared for private review" wording;
Report 205 sets an empty PDF author field, Report 207's reads "Report207".
Every result, proof, remark, question and limitation of the two manuscripts is
printed.

**Revision 1 of Report 205 was never received.** The bundle's README (intake
record) lists Reports 146 and 205 as archives corrected in place, with only the
latest corrected version included; the arrival holds one `Report205.zip`, and
its manuscript is revision 2. What revision 1 said (it listed proving
Spiridonov's Conjecture 3.3 as future work) and that nothing else changed are
known only from revision 2's own account: its paragraph "Correction to the
earlier release" (Section 9), its delivered README and `205-second-SOURCES.md`
("Revision status"). The write cannot verify that account.

## Why the Parts are in this order

The base is Report 205; its `Report205.tex` was staged as `article.tex`, and it
is printed first, as Part I. It is the earlier manuscript, and it closes with
the limitation that it gives no theorem "for other Stirling transforms".
Report 207 treats the first-kind transform from the same density and places
itself after "the examined earlier second-kind Stirling–Catalan work". Neither
uses a result of the other; they share only the beta integral, which each
proves (printed in both places, with a pointer).

## Files

The directory holds 29 files: 4 at the root, 6 in `code/`, 19 in `data/`.

**Report files**, written in the write: this guide, the merged article and its PDF.

```
README.md
article.pdf
article.tex
```

**Report 205, prefix `205-second-`** (13 files): the source list; `code/`: the
deterministic build driver and the standard-library exact checker; `data/`:
seven JSON data files, the manuscript guard, and the four generated TeX inputs
that `article.tex` reads with `\input`.

```
205-second-SOURCES.md
code/205-second-build.py
code/205-second-verify_exact.py
data/205-second-data-coefficients.json
data/205-second-data-exact_checks.json
data/205-second-data-exact_values.json
data/205-second-data-inverse_checks.json
data/205-second-data-numerical_checks.json
data/205-second-data-polynomial_coefficients.json
data/205-second-data-validation.json
data/205-second-manuscript_guards.json
data/205-second-tex-asymptotic_table.tex
data/205-second-tex-constants.tex
data/205-second-tex-inverse_table.tex
data/205-second-tex-pdf_settings.tex
```

**Report 207, prefix `207-first-`** (11 files): `code/`: the build driver, the
exact checker (1253 checks), the 90-digit diagnostics and the supplementary
script; `data/`: their outputs, the cell ledger, the dependency pin and the
generated tables.

```
code/207-first-build.py
code/207-first-diagnostics.py
code/207-first-supplementary.py
code/207-first-verify_exact.py
data/207-first-checks.json
data/207-first-diagnostics.json
data/207-first-exact_results.json
data/207-first-requirements.txt
data/207-first-supplementary.json
data/207-first-table_cells.json
data/207-first-tables.tex
```

**Generated TeX inputs.** `article.tex` reads Report 205's four generated
inputs from `data/205-second-tex-*.tex` (delivered as `tex/*.tex`; only the
`\input` paths changed). Report 207's generated `tables.tex` contains eight
labels; it is **inlined** in Section 17 with those labels prefixed `stc:s1:`
and is otherwise unchanged, and `data/207-first-tables.tex` stays as the
byte-identical record of the delivered build.

**Not shipped** (all retrievable from `60f54ea06`): the two PDFs;
`Report207.tex` (printed as Part II) and `README.txt` of Report 207 (Report
205's README was staged and is replaced by this guide); the two `MANIFEST.json`
files (SHA-256 manifests, 18/18 and 14/14 verified at placement; repository
policy drops checksum manifests).

## Labels and numbering

Label prefix **`stc:`** (none at HEAD before this report): Part I uses
`stc:s2:` (Report 205's 93 labels), Part II `stc:s1:` (Report 207's 57 labels
and the 8 of its `tables.tex`). One bare name occurs in both manuscripts,
`eq:h` (two different functions `h`); under the Part prefixes they are
distinct. The write added the two Part labels `stc:s2:part`, `stc:s1:part`;
labels for Part II's eleven sections (`stc:s1:sec:model`, `…:resummed`,
`…:logs`, `…:inversion`, `…:cycle`, `…:ewens`, `…:mixture`, `…:checks`,
`…:sources`, `…:further`, `…:rebuild`); Remark 6.2's `stc:s2:rem:spiridonov`,
`stc:s2:eq:spiridonov-A`, `stc:s2:eq:spiridonov-root`; the front matter's
`stc:sec:guide`, `…:status`, `…:spiridonov`, `…:oeis`, `…:inverses`,
`…:notation`, `…:provenance`, `…:trust`, `…:neighbours`; and Section 21's
`stc:sec:further` with the eight items `stc:q:effective`, `stc:q:growing`,
`stc:q:moments`, `stc:q:tv`, `stc:q:boundary`, `stc:q:circle`,
`stc:q:transforms`, `stc:q:literature`. 192 labels in all, all distinct (158
delivered, 34 added). The two bibliography keys `oeis` became `oeisA064856`
and `oeisA086662`.

| Part | Manuscript | Section here | Statements and equations |
|---|---|---|---|
| I | Report 205 | `k` (1–9, unchanged) | `k.j`, unchanged; Remark 6.2 and (6.8)–(6.9) added after Corollary 6.1 |
| II | Report 207 | `k + 9` (10–20); 21 added | renumbered within sections (below) |

Report 207 numbered its statements consecutively and its equations without
section numbers. Here: Theorem 1 → **11.1**, Theorem 2 → **12.1**,
Proposition 3 → **12.2**, Theorem 4 → **13.1**, Theorem 5 → **13.2**,
Theorem 6 → **15.1**, Theorem 7 → **16.1**; equations (1)–(5) → (10.1)–(10.5),
(6)–(14) → (11.1)–(11.9), (15)–(24) → (12.1)–(12.10), (25)–(34) →
(13.1)–(13.10), (35)–(40) → (14.1)–(14.6), (41)–(47) → (15.1)–(15.7),
(48)–(50) → (16.1)–(16.3); its Tables 1–8 → Tables 3–10 (Part I keeps Tables
1–2). A comparison of the build's `.aux` with separate builds of the two
delivered `.tex` files confirmed all 158 delivered labels under these offsets
and prefixes. The delivered READMEs, code and data use the manuscripts' own
numbers.

## Notation

No delivered symbol was renamed. The front matter's "Notation across the two
Parts" lists every letter whose meaning changes, with the tempting false
readings, and each Part opens with a short reading-conventions table. The main
collisions: **`a_n`** (A064856 in Part I, A086662 in Part II; the front matter
writes `a⁽²⁾_n`, `a⁽¹⁾_n`), **`w`** (Part II's density, which is Part I's `ϱ`,
and Part II's `w = W₀(y/e)` in the same paper; Part I's formal variable),
**`L`** (Part I's `L_n` and `L = log y`; Part II's `L = log n`), **`y`, `X`**
(Part I's threshold `y` is Part II's `X`; Part II's `y = log X` is Part I's
`L`), **`h`**, **`R_j`**, **`c`**, **`d_j`**, **`r`** (Part I's saddle `W(n/4)`;
Part II's Newton count), **`H`**, **`K`**, **`P`**, **`Q`**, **`A`**, **`B`**,
**`M`**, **`I`**, **`S`/`s`**, **`t`, `u`, `v`**, **`D`, `E`**, **`p`, `q`,
`g`**. Same in both Parts: `C_k`, `E`, `Γ`, `ψ`, Euler's `γ`, the principal
Lambert branch (Part I writes `W`, Part II `W₀`).

## What the report claims

**Part I (Report 205).**
- Theorem 1.1: the all-fixed-order expansion above, with `Q₁`, `Q₂` explicit
  and `Q₃` in `data/205-second-tex-constants.tex`; (1.7) its Stirling-form
  leading equivalent. Proposition 5.1: the denominator and degree bound that
  makes `4j + 1` exact rational evaluations a certificate.
- Lemma 2.1 (`a_n = E Kⁿ` for a mixed Poisson `K`; strict increase); the ODE
  (2.6); Lemma 3.1 (sectorial endpoint expansion); Lemma 4.1 (uniform saddle
  expansion of `n![zⁿ]e^{ce^z − bz}` at every fixed order, any fixed `c`, `b`).
- (1.8), (6.3): `log(a_n/B_n) ~ (log 4)n/log n`, `a_n/B_n → ∞`,
  `(a_n/B_n)^{1/n} → 1`; (6.1) the comparison with Touchard numbers `B_n(4)`.
- Corollary 6.1: `B_k ≤ M_{2k} ≤ a_k`, `(M_{2k}/B_k)^{1/k} → 1`,
  `M_{2k}^{1/k} ~ k/(e log k)`, from Bauer–Golinelli's Section 5.5,
  equation (9) (a consequence of a prior theorem, no novelty claim).
- Theorem 7.1: the inverse `I_M` with `d₀ = O(1)`, `d_j = O_j(ρ^{j−1})` and
  the two-ceiling enclosure (1.10); (7.25): `⌈I₀(a_n)⌉ = n + 1` for all large
  `n`, since `d₁(ρ) → −115/24`.

**Part II (Report 207).**
- (10.3): Barry's integral (prior, credited) with the marked form `A_n(u)`;
  `a_{n+1} > n a_n`.
- Theorem 11.1 (resummed expansion), Theorem 12.1 (fixed inverse-log orders,
  leading `n! n³/(48√π L^{3/2})`, `c₁ = (3/2)(47/24 − γ)`), Proposition 12.2
  (divergence and exact completion).
- Theorem 13.1 (explicit inverse `v_K`), Theorem 13.2 (resummed inverse, two
  ceilings, Newton error `(t log t)^{−(2^r−1)}`).
- (14.1)–(14.6): local analytic cycle law, mean, variance, CLT
  `(K − 4 log n)/(2√log n) ⇒ N(0,1)`; Theorem 15.1 (total variation to
  Ewens(4)); (15.7) Ewens factorial moments; Theorem 16.1 (boundary Gamma law
  with its first correction); Section 18: no representation of the Catalan
  tilt by fixed length-product weights.

**Added by the write** (all marked `[write]`, dated 6 October 2026): the front
matter; dated notes; Section 21; and **Remark 6.2** with its proof:
- Spiridonov writes the Bell asymptotic as `A_k = b^k e^{b−k−1/2}/√(log k)`,
  `b log b = k − 1/2` (thesis p. 12), and says (p. 13) that `SC_k = a_k` "is
  (by numerical estimates) ≈ (1.47^k + 1)A_k". The remark proves
  `(A_k/B_k)^{1/k} → 1` (from `k/log k ≤ b ≤ k` for `k ≥ 4`), hence, with
  (1.8), `(a_k/((β^k+1)A_k))^{1/k} → 1/β` and `a_k/((β^k+1)A_k) → 0` for
  every fixed `β > 1`. So the model is wrong as an asymptotic; the thesis
  states no range or method, and the computation may be right for the indices
  used. Exact values (`k ≤ 2000`, 60-digit `mpmath`) give the ratio
  `R_k = a_k/((1.47^k+1)A_k)`: 1.49 at `k = 10`, maximum 10.57 at `k = 56`
  over `3 ≤ k ≤ 300`, 0.0141 at 200, 1.5×10⁻¹¹⁰ at 2000; `(a_k/A_k)^{1/k}` is
  about 1.57 for `15 ≤ k ≤ 25` and 1.30 at `k = 2000`.

**The spectral moments.** Spiridonov's `M_{2k}` is
[A094149](https://oeis.org/A094149) (his own 2004 entry). The write checked
Corollary 6.1 on all thirteen listed terms (`1 ≤ k ≤ 13`): it holds, with
`M_{2k} = a_k` for `k ≤ 3`. It also checked Part I's citation of
Bauer–Golinelli (arXiv:cond-mat/0007127v2): Section 5.3 gives
`μ_{2k} = Σ_l I_{k,l} α^l`; Section 5.5 begins on p. 26, displays (9) on
pp. 26–27, and its proof ends on p. 30.

**The OEIS entries.** Both were read on 6 October 2026 (A064856 revision #33
and A086662 revision #16, both of Nov 17 2025). A064856 (Karol A. Penson, Oct
08 2001) lists the Bessel EGF (unsigned) and the hypergeometric EGF signed by
Vladeta Jovovic (Sep 11 2003); A086662 (Vladeta Jovovic, Sep 12 2003) lists
Barry's moment integral (Jul 26 2010). Neither gives an asymptotic formula.
**Nothing was submitted to the OEIS.**

**The inverses and the transseries volume**
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`).
Instances: Part II's centre `t₀ = y/W₀(y/e)` of the factorial core
`p0:prop:factorial-core` (`κ = 1`, `d = −1`); Part II's ceiling step in
Theorem 13.2 of `p0:thm:staircase` (1), with the interpolation `a(t)` of
(10.4) on a half-line where it increases, and (2) when the two ceilings agree;
Part I's seed `R = 2W(√L/4)` of the Lambert core `p0:thm:lambert-core` after
taking logarithms (`R + 2 log R = log(L/4)`, `a = 1`, `b = 2`); Part I's shift
recursion (7.21) of `p0:thm:core-reversion` with `h = 0`, `Λ = u = ρ + log 4`,
`t = w` (the write shows `Φ(0, Δ) = uΔ + h(ρ)` exactly). Analogue: Part II's
`v_K` is the first-order term of `p0:eq:operator-series` about the factorial
core, with its own remainder. Not instances: Part I's carrier `H(ρ) = L`
(not Lambert); Part I's brackets (7.5) and (1.10), proved directly from model
envelopes. Part I's single-ceiling failure (7.25) is the failure mode of
`p0:thm:staircase` (2); by item (3), `n = ⌊I₀(a_n) + 1/2⌋` for all large `n`.

## What the report does not claim

Every limitation is printed in place. In short: the OEIS EGFs, Barry's
integral, the Ewens limit laws, the mod-Poisson framework, Watson's lemma, the
transfer theorem and the endpoint, Gaussian and saddle methods are prior, as
the manuscripts say; neither makes a global priority claim (bounded source
checks only). Fixed truncation orders only: no growing-order control, optimal
truncation, first-neglected-term bound, exponentially small completion or
transseries (Part I), no separate `n^{−4}` endpoint sector (Part II). The
inverse constants and onsets are existential, there is no single-ceiling rule,
and finite residuals certify nothing. Part I gives no relative asymptotic for
`M_{2k}` and says nothing about the literature status of full moment
asymptotics; no theorem for varying Catalan powers or other transforms. Part
II: no whole-circle mod-Poisson result, no inverse-`n` density expansion, no
projective consistency of `P_n`; the total-variation table uses an
uncertified float recurrence with a 220-cycle cutoff; the
Maples–Nikeghbali–Zeindler theorem is not used and Ewens's 1972 paper was not
read. **Both packages**: finite exact checks prove no asymptotic remainder;
manifests and guards detect changes and validate no theorem.

## Further questions, and the standing rule

Part I's Section 9 and Part II's Section 19 are the manuscripts' own;
Section 21 collects them with the stated non-claims (Vladimir's standing rule
of 4 October 2026), with sources, sketches and what is missing:

1. effective constants, onsets and certified discrete inverses (Part I q. 1;
   Part II d. 1);
2. growing truncation orders and optimal truncation (Part I q. 2; Part II
   d. 3);
3. the spectral moments `M_{2k}`: effective bounds (Part I q. 3) and their
   relative asymptotics (a Part I non-claim). **Leads, not checked:** later
   manuscripts of the same bundle, Reports 209, 210, 212, 213 and 214, still
   archives in `docs/incoming/` at this write, study `M_{2k}`; by its abstract
   Report 213 proves `M_{2k} ~ 2B_{k+1}` and Report 214 a fixed-order
   expansion of `M_{2k}/(2B_{k+1})`. To be re-scoped when they are placed;
4. higher total-variation terms (Part II d. 2);
5. inverse-`n` sectors of the boundary law, coherence of the mixture (Part II
   d. 4);
6. the cycle law away from `u = 1` (Part II non-claim);
7. other transforms and weights, re-scoped (Part II answers the unsigned first
   kind), with the write's question about general compactly supported
   densities with an algebraic edge;
8. literature and priority.

**Refuted**: Spiridonov's numerical model `SC_k ≈ (1.47^k + 1)A_k` as an
asymptotic (Remark 6.2, from Part I's (1.8)). **Credited**: Spiridonov's
Conjecture 3.3 follows from Bauer–Golinelli (2001) (Part I, Corollary 6.1).
**Corrected**: Part II's sentence that the earlier second-kind work "expressly
deferred this first-kind transform" — the delivered revision 2 of Report 205
says only that it gives no theorem "for other Stirling transforms"; whether
revision 1 said more cannot be checked. The sentence is kept, with a dated note
beside it (Section 18). No mathematical statement of either manuscript was
found wrong.

## Relation to neighbouring reports

- No other placed report treats A064856, A086662, A094149, Spiridonov's thesis
  or Bauer–Golinelli's moments (searched 6 October 2026).
- Method neighbours: `a277364-bell-asymptotics` (Bell numbers through
  `r = W₀(n)`; Part I's Lemma 4.1 at `c = 1`, `b = 0` is of the same
  Moser–Wyman type), `a088714-bell-scale-growth`,
  `a122399-surjection-diagonal`, `a124380-signed-moment-asymptotics`,
  `a113227-powered-catalan` (a different mechanism),
  `a007716-bipartite-multigraphs` (Ewens moments in its checks).
- The transseries volume, for the inverses (above).

## Relation to formal projects

Placement in the collection confers no formal status, and no statement of this
report is formalized: no Lean or Rocq file treats these sequences (searched 6
October 2026). The nearest declaration is generic:
`Fabius.egfA_subst_exp_sub_one` in
`Analysis/FabiusFunction/Lean/FabiusFunction/StirlingTransformEGF.lean`
(the EGF of a second-kind Stirling transform is `A(e^t − 1)`, for formal power
series over a ℚ-algebra); with `a_k = C_k` it is the formal content of one step
of Part I's (2.3), not the analytic identity. Its companion
`Fabius.egfA_subst_log` is the signed first-kind transform, which Part II does
not use.

## Delivery names, renames and discrepancies

- Every delivered file keeps its bytes (the 26 staged code, data and source
  files and the two staged base files were checked against a fresh extraction
  from `60f54ea06` at the write: 0 differences; `article.tex` and this README
  then replaced the two staged base files). Only names changed (tables at the
  end).
- **Nothing runs in this directory.** Report 205's `build.py` and
  `verify_exact.py` read `Report205.tex`, `tex/`, `data/` and `MANIFEST.json`
  by their delivered names, and the manuscript guard
  (`data/205-second-manuscript_guards.json`) pins the SHA-256 of the delivered
  `Report205.tex` (`ea22e3b9…`), so it rejects this `article.tex` by design.
  Report 207's `build.py` expects all members at one level, compiles
  `Report207.tex` and rewrites its JSON, `tables.tex`, PDF and ZIP in place.
  `data/205-second-data-validation.json` and `data/207-first-table_cells.json`
  name delivered paths (`tex/…`, `diagnostics.json`, …). Rerun from the archive
  (below).
- Report 205's running heads ("Stirling–Catalan asymptotics", "Report 205") are
  not used in the merged article. Report 207's "Rebuilding the package"
  (Section 20) and Report 205's Section 8 describe the archives as delivered,
  including the PDFs and manifests, which are not shipped (dated notes there).
- Both manuscripts' source paragraphs are dated 4 October 2026; the write's
  readings of the OEIS and of the two cited works are recorded in the front
  matter.

## Rerunning the checks

Run on a copy in a scratch directory, never in this directory. Recreate the
delivered layout from the arrival commit (both archives are flat):

```
git show 60f54ea06:docs/incoming/Report205.zip > r205.zip
git show 60f54ea06:docs/incoming/Report207.zip > r207.zip
mkdir x205 x207 && unzip -q r205.zip -d x205 && unzip -q r207.zip -d x207
cd x205
python verify_exact.py
python -O verify_exact.py
python build.py --data-only          # rewrites data/ and tex/ in this copy
cd ../x207
python build.py                      # needs pdflatex; rewrites JSON, tables, PDF, ZIP in this copy
python -O build.py
```

Compare the regenerated files with a second, untouched extraction (`cmp` on
Linux or macOS). On Windows both build drivers write text with CRLF line ends,
so compare after removing carriage returns (`tr -d '\r' < f | cmp - g`).
Report 205 needs SymPy 1.14.0 and mpmath 1.3.0 for `build.py` (the checker
needs only the standard library); Report 207 needs mpmath 1.3.0
(`data/207-first-requirements.txt`). Report 205's full build (`python
build.py`, `--verify-replay`) also needs a TeX Live pdfTeX matching its
recorded environment for byte identity of the PDF and ZIP; it was not run.

Results: at placement (5–6 October 2026, Python 3.14.4, Windows, on copies,
recorded in the batch-107 dossier) and again at the write (6 October 2026,
fresh extractions): Report 205's checker passed in normal and `-O` mode, and
`--data-only` regenerated all six data files with mathematical content and all
four TeX inputs byte for byte; `data/validation.json` differs only in the
Python version (3.14.4 for 3.12.14) and in the manuscript and PDF-engine keys
that data-only mode omits. Report 207's checker (1253 checks), diagnostics,
supplementary script and table generator, driven without TeX and ZIP, reproduced
`exact_results.json`, `diagnostics.json`, `supplementary.json`, `tables.tex`
and `table_cells.json` byte for byte in normal and `-O` mode (about 13 s).
Its `compile_pdf` and ZIP steps were not run. The two delivered `.tex` files
compile with MiKTeX pdfLaTeX to 17 and 16 pages with no warnings.

## Rights

Repository contents are MIT-0. Report 205's exact check compares its
enumeration with the first 23 terms of A064856 as cited, and Report 207's
Table 3 and checker reproduce the 24 terms listed in A086662 by integer
arithmetic; OEIS data are available under CC BY-SA 4.0
([OEIS license](https://oeis.org/LICENSE)). The OEIS entries are credited for
the sequences and the exact formulas, Paul Barry for the moment integral,
Alexey Spiridonov for the thesis and A094149, Bauer and Golinelli for the
coefficientwise bounds, and the further works as the Parts cite them. Nothing
was submitted to the OEIS.

## Build

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX), in a scratch copy containing `article.tex` and the four
`data/205-second-tex-*.tex` files; commit only `article.pdf`. The build (47
pages): no errors, no undefined or multiply defined references or citations,
no duplicate destinations, no overfull or underfull boxes, no warnings. The
log carries one "Infinite glue shrinkage found in box being split" message,
from a longtable breaking across pages.

## Delivered path → shipped path

Report 205 (`205-second-`; delivered flat, no top-level directory):

| Delivered | Shipped |
|---|---|
| `Report205.tex` | `article.tex` (Part I) |
| `README.md` | replaced by this guide |
| `SOURCES.md` | `205-second-SOURCES.md` |
| `build.py`, `verify_exact.py` | `code/205-second-<name>` |
| `data/<name>.json` | `data/205-second-data-<name>.json` |
| `manuscript_guards.json` | `data/205-second-manuscript_guards.json` |
| `tex/<name>.tex` | `data/205-second-tex-<name>.tex` (read by `article.tex`) |
| `Report205.pdf`, `MANIFEST.json` | not shipped |

Report 207 (`207-first-`; delivered flat):

| Delivered | Shipped |
|---|---|
| `Report207.tex` | not shipped; printed as Part II of `article.tex` |
| `build.py`, `verify_exact.py`, `diagnostics.py`, `supplementary.py` | `code/207-first-<name>` |
| `checks.json`, `diagnostics.json`, `exact_results.json`, `supplementary.json`, `table_cells.json`, `requirements.txt` | `data/207-first-<name>` |
| `tables.tex` | `data/207-first-tables.tex` (inlined in Section 17, labels prefixed) |
| `README.txt`, `Report207.pdf`, `MANIFEST.json` | not shipped |

## Provenance

Two manuscripts (bundle Reports 205, 207) → one report; base 205, printed as
Part I. Arrival `60f54ea06`, placement `3988bf5c4`, write batch 107 (6 October
2026). Neither manuscript pins a commit. Merge choices (base first, the shared
beta integral printed in both Parts with a pointer, Part II renumbered within
sections, Report 205's generated inputs read from `data/`, Report 207's tables
inlined with prefixed labels, running heads dropped, the merged bibliography
with the two `oeis` keys split) are listed in the article's front matter,
"Provenance and merge decisions".
