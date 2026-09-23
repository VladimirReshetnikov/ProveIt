# Gamma and Zeta over the Surcomplex Numbers

**Finite lifts, the Dirichlet algebra at infinity, Stirling and Hurwitz,
phases on the horizontal tube, obstructions at infinite height, and transfer
of the Riemann hypothesis**
Merged research report, September 2026, from six manuscripts written
independently in September 2026 (five dated 22 September, 06 only
September) and placed together in commit `e4f8848`.
AI-assisted, prepared for Vladimir Reshetnikov. Unrefereed.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 82 pages
README.md     this guide
code/
  01-inverse-zeta-verification.py              source 01 checks (61; SymPy and mpmath)
  02-scale-separation-verify.py                source 02 checks (189; SymPy)
  02-scale-separation-build.sh                 source 02's build script (see "Build and reproduce")
  03-horizontal-tube-verify.py                 source 03 checks (1,670; SymPy)
  04-rh-transfer-verify.py                     source 04 checks (350; SymPy)
  05-surcomplex-fields-verify_identities.py    source 05 checks (296; SymPy)
  06-phases-and-rh-checks.py                   source 06 checks (221; SymPy)
  06-phases-and-rh-build.sh                    source 06's build script (see "Build and reproduce")
data/
  01-inverse-zeta-verification-results.json    recorded run of the 01 checks
  01-inverse-zeta-inverse-coefficients.csv     the 23 inverse-zeta coefficients C_r with r < 8 (CRLF line ends, kept as delivered)
  01-inverse-zeta-requirements.txt             sympy==1.14.0, mpmath==1.3.0
  01-inverse-zeta-source-audit.json, 01-inverse-zeta-build-quality.json
  02-scale-separation-results.json             recorded run of the 02 checks
  02-scale-separation-requirements.txt         sympy==1.14.0
  02-scale-separation-source_audit.json, 02-scale-separation-validation.json
  03-horizontal-tube-verification.json         recorded run of the 03 checks
  03-horizontal-tube-requirements.txt          sympy==1.14.0
  03-horizontal-tube-build-quality.json
  04-rh-transfer-verification.json             recorded run of the 04 checks
  04-rh-transfer-source_audit.json, 04-rh-transfer-build_review.json
  05-surcomplex-fields-verification.json       recorded run of the 05 checks
  05-surcomplex-fields-requirements.txt        sympy==1.14.0
  06-phases-and-rh-finite-checks.json          recorded run of the 06 checks
  06-phases-and-rh-proof-status.json, 06-phases-and-rh-source-audit.json,
  06-phases-and-rh-build-quality.json
```

Every label in `article.tex` carries the prefix `gz:` (222 labels). No label
of this report is cited elsewhere yet. The code and data files are
byte-identical to the delivered packages, under the prefixes above. The six
manuscripts themselves, with their PDFs and delivery READMEs, are not
shipped. The shipped audit and build records describe those manuscripts,
not this report. For example, `02-scale-separation-validation.json` records
the 29-page source 02, and `03-horizontal-tube-build-quality.json` the size
of source 03's PDF.

## Six sources, one report

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **01** | *Gamma and Zeta over the Surcomplex Numbers: strong summation, a Hurwitz–Gamma bridge, phase choices, and exact inverse-zeta fibers* (31 pp.) | `804c63c` | Inverse-zeta fibres (Section 9, in full); the twisted family `E_λ`; the left prescription `Z_{−,λ}` (Proposition 16.7); Hurwitz germs and polygamma values. |
| **02** | *Gamma and Zeta at Surcomplex Scales* (29 pp.) | `804c63c` | Independence at dilations with `x`, `L_St(x)`, `Γ_St(x)` (Sections 10.1–10.2); leading forms; phase families `E_θ` and the wing continuum (Section 13). |
| **03** | *Gamma and Zeta on the Surcomplex Horizontal Tube* (34 pp.) | `804c63c` | Base of Part IV: Gamma, zeta and ξ on the whole tube `{Im s finite}` for every phase (Sections 14–16); independence at shifts over Hahn and Gamma-containing fields (Section 10.3); the canonical wing. |
| **04** | *Gamma, Zeta, and the Riemann Hypothesis over Surcomplex Numbers* (31 pp.) | `905dd19` | The two-sign criterion and one-η converse; local conservation; protected counts; the flat Hurwitz modification; transported divisors; Hermitian tests. |
| **05** | *Gamma and Zeta over Surcomplex Fields* (28 pp.) | `905dd19` | The reflection defect at `½ + iT` (Theorem 17.1); the ratio cocycle; formal-series deformations; verified-height protection; transfer. |
| **06** | *Gamma and Zeta over the Surcomplex Numbers: canonical finite lifts, infinite Dirichlet series, phase obstructions, and the Riemann hypothesis* (28 pp.) | `905dd19` | **The base text.** Robust RH, forced poles, resonant galaxies, weak completions, heat escape; the most general exponential conventions. |

Pins: `804c63c` = `804c63c2c675be9fd4e5086460bfa795f17a6d86`, `905dd19` =
`905dd19954db43ac81f76f72036520d0eadc5710`. 06 is the base because it is the
only source spanning both the phase thread and the RH thread. Where another
source is strictly more general, its version is used. Appendix A.2 of the
article maps every numbered result of every source to its place here.
Duplicates are printed once with all proving sources credited; genuinely
different proofs are kept as marked second routes.

## How the six sources were reconciled

Before the merge the six were compared claim by claim. **No two contradict
each other** once four things are fixed: the domain, the exponential or
phase, the summation notion, and for deformation results the deformation
class. Section 2 fixes one meaning per symbol, with a table of notions and a
per-source rename table (Table 1). Section 3 (Table 2) lists every apparent
conflict and what separates its two sides. Each reconciliation is printed
again at its point of use. The main ones are these.

- **Stability classes.** 04 perturbs by `Ξ^# ± η` and J-symmetric
  `η h^#` with one fixed `η`. 05 uses formal series with both symmetries
  and `τ > 0`. 06 uses both symmetries and both signs. All three are
  subclasses of one class `𝒟_J` (06's lies in 05's; 04's and 05's are
  incomparable), and one theorem (7.9) covers them.
- **Zero-freeness beyond `𝒯_+`.** 02's warning concerns the raw `ζ_D`. The
  wing sums of 02 and 03 use a named phase (Section 13).
- **Reflection at infinity.**
  - 03 builds Gamma with reflection on the tube.
  - 06 proves that no Gamma with only ordinary poles satisfies reflection.
    This is the same fact: poles are forced on the period group
    (Theorem 14.1).
  - 05's failure at `½ + iT` concerns the vertical strip, outside the tube
    (Theorem 17.1). There 06's `Γ_{E,St} = E ∘ L_St` fails reflection at
    every point, for every exponential `E` extending `E_fp`
    (Theorem 17.1(e)).
  - 06's poles at `1 ± iT` concern resonant galaxies, also outside the tube
    (Theorem 18.2).
- **The zero at `−ω`.** 01's "nothing canonical decided" becomes: with the
  Ehrlich–Kaplan exponential the zero is present, and no functional
  equation forces it (Proposition 16.7, Remark 16.8).
- **"Canonical".** 01 calls the finite-phase `E_fp` canonical, and 02 treats
  `E_{ℓ=0}` as one choice among many. Both are replaced by `E_fp` and the
  Ehrlich–Kaplan `Exp`, which is canonical in the integer-part sense but not
  unique.
- **Hurwitz normalizations.** 03's `H` is 01's `Ĥ`, not 02's `H∞`. All are
  written `ζ_H`, `ζ̂_H`.
- **Heat variables.** `H_0(z) = Ξ(z/2)/8`.
- **Literature statuses.** Guth–Maynard is published in *Ann. of Math.* 203
  (2026). The published Platt–Trudgian abstract includes simplicity.

## What the report claims

Numbers refer to the built `article.pdf`. Tags such as [01, 03] in the article
name the proving sources, and [merge] marks results established during the
reconciliation.

1. **Finite plane.**
   - Divisor rigidity of canonical Taylor–Laurent lifts, with no displaced
     zeros (Theorem 6.3).
   - Finite RH is equivalent to RH (Theorem 7.2).
   - Protection of simple critical-line zeros under every J-symmetric formal
     deformation with a real infinitesimal parameter (Theorem 7.7). Every
     displacement coefficient is purely imaginary.
   - The two-sign criterion for real entire functions (Theorem 7.8).
   - **The unified stability theorem** (Theorem 7.9): RH plus simplicity is
     equivalent to stability over the class `𝒟_J`, and also to the test
     `ξ^# ± η` for one `η`. Its shadow form is equivalent to RH alone.
   - The source criteria (Corollary 7.10), and 04's criterion for every real
     entire function (Remark 7.11).
   - Protected counts (Theorem 7.14).
2. **Positive infinite real part `𝒯_+`.**
   - An injective realization of all arithmetic functions by strongly
     summable Dirichlet series (Theorem 8.1).
   - Euler, Möbius, logarithm and von Mangoldt identities; zero-freeness;
     tails; monotonicity (Theorem 8.5).
   - The summability dichotomy (Proposition 8.6).
3. **Inverse zeta** (01).
   - Complete fibres over every nonzero infinitesimal (Theorems 9.1 and 9.4,
     Corollary 9.6).
   - The arithmetic coefficient formula (Theorem 9.8) and the integer sector
     (Theorem 9.9).
   - The real branch is rightmost (Corollary 9.10).
4. **Independence** (02, 03).
   - `x`, `L_St(x)`, `Γ_St(x)` and all `ζ_D^(j)(kx)` are independent over `ℂ`
     (Theorem 10.8).
   - The shift jets are independent over `M_X`, `E_X` and `E_X^Γ`
     (Theorems 10.11, 10.13 and 10.14).
5. **Stirling and Hurwitz.**
   - Recurrence, Gauss and formal uniqueness (Proposition 11.1).
   - The translation formula (Theorem 11.2) and the ratio cocycle
     (Theorem 11.3).
   - The phase estimate (Proposition 11.5).
   - Phase Gamma on `𝒮_∞` (Proposition 11.7).
   - Hurwitz unit, identities and Lerch values (Theorems 12.3, 12.4 and
     12.6).
   - The flat Hurwitz modification (Proposition 12.8).
6. **Tube** (03).
   - Forced poles (Theorem 14.1).
   - Gamma on the tube, with poles `ℤ_{≤0} ∪ (𝓘(Ψ_χ) ∩ {x < −ℝ})`, which is
     `Oz_{≤0}` for `Exp` (Theorem 15.1).
   - Gauss on the tube (Theorem 15.2).
   - Zeta with extra zeros on `2𝓘(Ψ_χ)` (Theorem 16.2).
   - `ξ` with exactly the classical divisor (Theorem 16.4), and horizontal
     RH is equivalent to RH (Corollary 16.5).
   - Explicit cancellation (Proposition 16.6) and movable zeros
     (Proposition 16.7).
7. **Obstructions at infinite height.**
   - The strip defect (Theorem 17.1): a general `G` with Stirling moduli
     fails reflection except at two abscissae `σ_±(T)` per height, and
     `E ∘ L_St` fails it at every point of the strip, for every `E`
     extending `E_fp` (clause (e)).
   - Resonant galaxies (Theorem 18.2), for every phase with a resonance and
     every Gamma factor field-valued at `−2 − iT`.
   - Weak completions (Theorem 19.1).
8. **Transfer and heat.**
   - Transferred RH, including simplicity with the derivative clause
     (Theorem 20.3).
   - Zero-free layers, verified-height protection, stable proportions and
     density (Section 21).
   - Escape at negative infinitesimal time, with hypotheses stated clause by
     clause (Theorem 22.2).

**Established in the merge** ([merge], each with a complete proof, checked
again for this report, re-derived in the same AI-assisted process; not
refereed):

- evaluation of weighted series (Lemma 4.6; it completes 01's existence
  step);
- existence and failure of resonances (Proposition 5.10):
  - every ordinary-circle phase has resonances;
  - a phase built with choice has none, which settles the unproved last
    sentence of 06's Remark 7.4;
- the finite-phase locus `Ω_∞` is exactly the locus of phase independence
  (Proposition 11.6);
- the strip-wide reflection defect for every finite `0 < σ < 1`
  (Theorem 17.1). For a general `G` with Stirling moduli it has **two
  exceptional abscissae `σ_±(T)`** near `¼` and `¾`, where the modulus test
  is silent; the reconciliation plan had overstated this as an obstruction
  at every `σ`. Clause (e), added after the post-merge audit, shows that
  `E ∘ L_St` itself fails reflection at every point of the strip, including
  `σ_±(T)`, for every `E` extending `E_fp`;
- wing summability for ordinary-circle phases and its failure for one
  infinitesimal-valued phase (Propositions 13.1 and 13.3);
- wing fibres (Corollary 13.4);
- the failure of Gauss for the flat gauges of 04 and 05 (Section 11.5);
- Theorem 7.9 as one statement (its unified form);
- the constant-term step of the Gauss proof in Proposition 11.1.

## What the report does not claim

- No proof, disproof or advance of the classical Riemann hypothesis, and no
  improved classical constant.
- No canonical, unique or maximal global zeta, `ξ` or Gamma on all of
  `No[i]`. Every global object depends on a named phase, domain, summation
  and continuation class.
- **No Lean verification of any theorem here.** The only formalized material
  is imported infrastructure with Lean-proved rows in
  [FORMALIZATION.md](../../FORMALIZATION.md): the substitution clauses of
  `a:cor:complexsub`, near-one binomial powers, and fine derivatives of
  evaluated ordinary power series. Unrefereed and AI-assisted; no priority
  is certified for anything.
- The Alpöge–Furman and Lamzouri proportion results (2026) are cited as
  preprints, with their stated constants (`C_0 = 0.6725007…`, `(1+C_0)/2`),
  and are not verified. Every conclusion using them is parametric.
- Section 24 keeps **every non-claim of every source, grouped by source**, and
  the merge's own. Among the merge's own: the results of Proposition 5.10(c)
  and Proposition 13.3 use choice; a coherent galaxy zeta for a phase without
  resonance is open (Question 23.1); the class `𝒟_J` is not claimed maximal;
  combined dilation-and-shift independence is open (Question 23.2); the
  content of Pong's 2020 Addendum was not checked; for a general
  prescription with Stirling moduli nothing is claimed at `σ_±(T)` (for
  `E ∘ L_St` reflection fails there too); the resonance theorem covers
  03's arbitrary phases, 04's prescribed prime phases and exponentials with
  character values in `1 + 𝔪` only when they have a resonance.
- Corollary 21.2 assumes the simplicity statement of the published
  Platt–Trudgian abstract, which this merge did not recheck; 06's own
  argument does not need it.
- Tube reflection and the functional equation are definitions on `𝒯_−`,
  not a continuation or uniqueness theorem.
- The finite checks corroborate finite algebra and ordinary numerics only.

## Errors found and fixed

No source has a fatal error or a false main statement. Appendix A.4
(Table 3) lists 53 items with source, location, severity, issue and fix.
Appendix A.5 records, by category, the corrections made after three
independent post-merge audits (mathematics, fidelity to the sources,
non-claims and notation). The kinds of fix are these.

- **Proof gaps closed.**
  - 01's evaluation step (Lemma 4.6);
  - 02's support words, tail valuation and joint summability;
  - 03's local-ring step in its prime lemma and its fine-derivative outline;
  - 04's operator regrouping and workspace transfer;
  - 05's purely-imaginary displacement coefficients;
  - 06's real constants in the transfer language;
  - 06's unproved resonance remark (Proposition 5.10(c)).
- **Statements qualified.**
  - 02's `θ` depends on `x`.
  - 04's heat clauses (ii) and (iv) are unconditional.
  - 05's Theorem 9.1 needs "unless `F` vanishes on `U`".
  - 05's cocycle gloss holds only off the negative real axis.
  - 06's Theorem 7.3 is written out for every resonant phase, as its
    Remark 7.4 anticipates.
  - 06's `Γ_{E,St}` fails reflection at every point of the strip.
  - The flat gauges break Gauss.
- **Wording corrected.**
  - 04: "inequivalent in strength" becomes "formally stronger".
  - 05: "usually" becomes "always" (twice; once also in 06), and the two
    "right infinite" domains are separated.
  - 06: "genuine new domain result" is reworded, and 05's counting sentence
    is added to 06's text.
  - 01's stale remark about `−ω` is corrected.
- **Attributions and bibliography.**
  - `Exp` is identified with Ehrlich–Kaplan and `trigonometry:thm:globalexp`,
    and 01's `E_λ` with `e:thm-twisted`.
  - Credits added: `trigonometry:thm:characters`, `thm:infiniteperiods`,
    `cor:globalzeros`, `ex:phases`, and the `trigonometry:per:` section.
  - 03's prime lemma is identified as Pong's Theorem 5.5 for `F = ℂ`.
  - Journal data: Ehrlich–Kaplan, *JSL* 86 (2021), with the erratum in 87
    (2022); Costin–Ehrlich, *Adv. Math.* 452 (2024); Guth–Maynard,
    *Ann. of Math.* 203 (2026); Pong, *Acta Arith.* 172 (2016); MTY, RT,
    PRZZ and Platt–Trudgian.

## Relation to the neighbouring reports

**[gamma-functions](../../surreal/gamma-functions/)** constructs the
Taylor–Stirling baseline, its recurrence, Gauss formula and formal uniqueness,
the complex log-Gamma on `{x > 0, y finite}`, the phase lemma and the exact
finite-phase domain `Ω`, and the convex gauge classification. These are
**cited, not claimed** (`sec:baseline`, `lem:formal-shift`, `prop:gauss0`,
`lem:periodic`, `thm:complex-log`, `lem:phase`, `thm:phase-domain`,
`cor:headline`, `thm:main`). The sources' Bernoulli-operator and Hurwitz
proofs of the recurrence and Gauss formula are printed as second routes.

Its warning at `thm:phase-domain` declines to choose a global exponential. It
says such choices "define a different problem", and that is a non-claim, not
an open question. This report takes up that different problem, and what is
new here is:

- `Γ_χ` with a named phase on `𝒮_∞` and on the whole horizontal tube;
- Proposition 11.6: outside `Ω_∞` every value is phase data;
- the vertical-strip obstruction of Theorem 17.1;
- the Hurwitz bridge;
- the three non-uniqueness mechanisms, compared in Section 11.5.

The gamma-functions tube `𝒯 = {x > 0, y finite}` is not this report's
horizontal tube `𝒯_h = {Im s finite}`.

**[trigonometry](../trigonometry/)** has the Ehrlich–Kaplan exponential `Exp`
(`trigonometry:thm:globalexp`), the classification of phases `Ψ_χ`
(`trigonometry:thm:characters`), unavoidable infinite periods
(`trigonometry:thm:infiniteperiods`, `trigonometry:per:thm:cofinal`) and the
normalized period group (`trigonometry:per:thm:dictionary`). Source 06 cites
the trigonometry report as a whole, 03 cites only Ehrlich–Kaplan, and no
source cites these labels. The following are consequences of or
applications of those results:

- the forced poles and extra zeta zeros of Sections 14–16;
- the resonance facts of Proposition 5.10, a different notion from
  periods;
- the resonant-galaxy obstruction.

**[analysis](../analysis/)** has the canonical lift and no-displaced-zeros
result for holomorphic germs (`c:p4:def-lift`, `c:p4:liftzeros`; this
report extends them to meromorphic germs), coherent sections
(`c:p4:def-HU`, which Definition 18.1 extends to meromorphic coefficients),
the germ theorem (`b:germalgebra`) used for fine derivatives, `Exp`
(`e:thm-exp`), and the family `E_λ` (`e:thm-twisted`). That family is
exactly 01's `E_λ`.

Nothing in `docs/` treated the Riemann zeta function, Dirichlet series,
Hurwitz zeta or the de Bruijn–Newman constant before this report.

## Build and reproduce

Work on a copy of this directory. Two suites write unprefixed files next
to themselves.

```sh
cp -r docs/surcomplex/gamma-and-zeta-functions /tmp/gz && cd /tmp/gz
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
pip install sympy==1.14.0 mpmath==1.3.0
python code/01-inverse-zeta-verification.py      # 61 checks; writes code/verification-results.json and code/inverse-coefficients.csv
python code/02-scale-separation-verify.py        # 189 checks; writes code/results.json
python code/03-horizontal-tube-verify.py --output rerun-03.json          # 1,670 checks; refuses an existing path
python code/04-rh-transfer-verify.py --output rerun-04.json              # 350 checks; --output is mandatory
python code/05-surcomplex-fields-verify_identities.py --output rerun-05.json   # 296 checks
python code/06-phases-and-rh-checks.py --output rerun-06.json            # 221 checks; without --output it only prints
```

The build gives 82 pages with zero errors, zero warnings, zero overfull or
underfull boxes, zero undefined references and zero duplicate destinations.
The title page is wrapped in `pageanchor=false`.

For this merge all six suites were rerun on a copy (Python 3.14.4, SymPy
1.14.0, mpmath 1.3.0), and all passed with the recorded counts. 01's
recorded JSON has no aggregate count; its 61 is the tally of its assertions
made in the review of 01. The files
rewritten by 01 and 02 matched the shipped records in `data/`, apart from
the recorded interpreter version (recorded runs: Python 3.13.5), and 01's
CSV was byte-identical.

The checks test finite polynomial, rational and truncated-series identities,
and in 01 also ordinary-complex numerics. They do not test strong
summability, class quantification, independence of infinite families,
continuation, RH or any cited paper. A reconciliation suite (29 checks), a
merge suite (22 checks) and a check of Theorem 17.1(e) also passed; they are
described in Appendix B and are not shipped.

The shipped scripts keep their delivered docstrings, which name paths that
are not shipped here: 01's `verification.py`, 04's `code/verify.py`, and
05's `Surcomplex_Gamma_Zeta_and_RH.tex` and `verification.json`. Run them
under their shipped names as shown above.

Do not use the two build scripts. They were written for the source
manuscripts, which are not shipped.

- `code/02-scale-separation-build.sh` changes into `code/` and runs
  `pdflatex` on `surcomplex_gamma_zeta.tex`, then `checks/verify.py`. Neither
  exists there, so it fails, and it leaves `code/texput.log`.
- `code/06-phases-and-rh-build.sh` changes into `code/`, creates
  `code/build/` and runs `pdflatex` on an `article.tex` that is not in
  `code/`. It fails and leaves a log in `code/build/`. If run from a layout
  where it succeeded, it would overwrite `article.pdf`.
