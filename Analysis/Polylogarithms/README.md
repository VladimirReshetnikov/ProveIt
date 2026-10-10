# Polylogarithms

The canonical reading artifact is the collective manuscript
[Polylogarithms and their Arithmetic Bridges](docs/manuscript/polylogarithms.pdf),
with [editable LaTeX source](docs/manuscript/polylogarithms.tex) and an
[editorial ledger](docs/manuscript/EDITORIAL-LEDGER.md). Authored by
**ProveIt Contributors**, it has **379 pages, twelve chapters, thirteen figures
and 99 references**. Its development links rigorous proofs, exact finite
certificates and experiments. The preceding CM milestone proves class products,
genus ratios, all-weight quadratic degree in three discriminants, norm laws
and a dense cluster-set theorem. The S2/S4 proofs, all-weight distribution
rank theorem and Stieltjes zero counts through index seven are retained.
S6 and the distinct new S8 candidate remain conjectural despite certified
proximity. The inventory covers **439 textual provenance files**; **26
incoming archives / 1,043 members** are byte-preserved; imported ZIPs are retired from the drop zone and remain recoverable from their arrival commits. Their replay suites
pass. Integral basis, reflection torsion and modular/jet proofs are now integrated,
with a new separable multivariable product law and 210 independent raw-matrix
checks. The real-order core now includes all-parameter slit-plane and angular proofs, a rigorously enclosed Gaussian maximum and strict envelope log-concavity, and a sharp universal Euler bound supplied by a separate kernel contraction. The rational budget 57/50 applies at every positive real-order pair; the smaller critical/subcritical constant remains sharp on its triangle. Bessel, full Cayley, uniform, Lerch and Herglotz proof integration remains ongoing and explicitly tracked. The [validation record](docs/manuscript/VALIDATION.md)
separates proofs, finite certificates, numerical diagnostics, build and
rendered review. Original articles and reports remain historical evidence.

Special values and functional equations of polylogarithms and their relatives:
- multiple polylogarithms and multiple zeta values at roots of unity;
- polygamma functions of positive and negative order, and Γ at rational
  arguments;
- Hurwitz-zeta jets and generalized Stieltjes constants;
- Clausen values, polylogarithm ladders and Bloch-group elements;
- the Herglotz–Zagier function.

The original import contains 8 articles and 31 research reports from Vladimir
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

The tenth polylogarithm intake preserves Endpoint Regularization on the
harmonic-resonance spine and Twisted Stieltjes Harmonic Laurent Identities
on the correlation spine. The former distinguishes sharp cutoff, Abel and
spectral-ray constants and keeps its decorated Gamma kernel formal. The
latter retains the zero Fourier coefficient, the Dirac convolution unit and
covariant point masses. Its arctanh real-branch and unsupported
non-elementarity corrections apply to the current manuscript. Full isolated
replay and canonical analytic reconciliation are subsequent work; S6/S8
status is unchanged. Original report files and evidence are preserved.


The 10 October harmonic-resonance intake preserves five further reports under
`docs/reports/stieltjes-harmonic-resonance/` and continuations of the
Stieltjes-correlation and uniform-transition spines. Their proposed new
identities include all-integer Gauss-Hurwitz pole cancellation, nested-harmonic
regulator conversion, unequal-dilation products, separated triple correlations,
and a near-critical crossing proof. All five full isolated replays now pass. The corrected Choi pure and mixed
harmonic families have been independently proved at every order and integrated
in the 448-page ProveIt Contributors manuscript, alongside the accepted
correlation, contact and collective trace identities. The remaining new
analytic claims retain their pending integration scope and do not change S6/S8
status. The Choi audit distinguishes the confirmed factor-two correction from
the delivered visual observation of typography misprints.


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
- **Same article, lines 214-216** ("all depth-2 content of the Gaussian doubles lives
  in the antisymmetric parts `Li_{a,b}(P) − Li_{b,a}(P)`, which vanish on the
  diagonal"). At the mixed points the stuffle pairs `Li_{a,b}(x,y)` with
  `Li_{b,a}(y,x)` (`eq:g-sym-mix`), so the complementary part is the colour-swapped
  difference `Li_{a,b}(x,y) − Li_{b,a}(y,x)`, which need not vanish when `a = b`:
  `Im(Li₁,₁(−1,i) − Li₁,₁(i,−1)) = (π/2)log2 − G ≈ 0.1728` (batch 140: 19; checked
  at intake). Batch 141: also 21, with the exact value
  `Li₁,₁(i,−1) − Li₁,₁(−1,i) = π²/24 − log²2/4 + i(G − (π/2)log2)`, and 20 at weight
  four, `Im(Li₂,₂(−1,i) − Li₂,₂(i,−1)) ≈ 0.11191 > 0` (both checked at intake).
- **Same article, lines 201-203 and 397.** "`Re Li_n(i)` and `Li_n(−1)` are rational
  multiples of `ζ(n)`" (and the same for `Re Li_n(ρ)`) holds for `n ≥ 2` only; the
  `Li₁` values that occur in Family 1 are `Re Li₁(i) = −log2/2`, `Li₁(−1) = −log2`,
  `Li₁(ρ) = −log3/2 + iπ/6` (19; also 22).
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
- **`gaussian-multiple-polylog-depth`, "A sporadic relation: the generator space is
  three-dimensional"** (lines 284-292). The two same-argument shuffles
  `Li₁(i)Li₄(i)` and `Li₂(i)Li₃(i)` give two independent relations among the four
  weight-5 generators `g_{a,b} = Im Li_{a,b}(i,1)`: `eq:wt5-sporadic` is their
  `π`-free combination, and the other gives
  `g₂₃ = −6g₄₁ − 3g₃₂ − (3/32)Gζ(3) − π⁵/1536`. The generators therefore span at most
  two directions modulo `π⁵`, `Gζ(3)`, `β(4)log2`; "the single relation" and the
  "basis" `{g₄₁, g₃₂, g₂₃}` of `eq:S4-closed` are false, and `eq:S4-closed` is
  equivalent to `S₄ = (58g₄₁ + 24g₃₂)/7 + 19π⁵/3584 − 2β(4)log2` (batch 139: 14, 15,
  17; also 23, `prop:two-g`; checked at intake).
- **`ladders-as-bloch-elements`, `eq:Pm`.** Zagier's `P_m` sums to `j = m − 1`; the
  extra `Li₀` term changes even-`m` values (excess `2log²2/15` at `m = 2`, `z = i/2`).
  The supergolden value at line 96 is `P₄(z₋) = −0.916010467826…`, not
  `−0.91599…` (C09).
- **`reports/ladders-as-bloch-elements`, lines 63-65.** "The higher golden ladders
  (weights 5 through 9 …) become, in the same way, the stated `ζ(5), ζ(6), ζ(7), ζ(9)`
  multiples" fails at even weight: by `eq:Pm`, `P_m` takes the imaginary part when `m`
  is even, and every term is real at a real argument `0 < x < 1`, so `P_{2j}(x) = 0`
  there and the weight-6 golden ladder cannot become a nonzero `ζ(6)` multiple of `P_6`.
  The ordinary `Li₆` ladder stands; the report's abstract already says real-argument
  ladders give only `ζ(even)` at even weight (batch 141: 24; elementary, checked at
  intake).
- **`reports/golden-polylog-ladders`, lines 169-172.** The two degree-6 "four-seed"
  bases named there have two seeds each: the real roots in `(0,1)` of `x⁶+x²−1` and
  `x⁶+x³−1` satisfy only `r² + r⁶ = 1` and `r³ + r⁶ = 1`. A base `0 < r < 1` has two
  complementary pairs `r^a + r^b = 1` only when `r^d = ω` (24,
  `thm:complement-collisions`); the degree-6 instance is `x⁶+x⁴−1` (`r = √ω`; pairs
  `(2,10)`, `(4,6)`). That `ω` is the only four-seed base of degree at most 5 stands
  (found at intake from 24's theorem plus a numerical search; not stated by any
  delivery; pairs checked numerically for exponents below 80).
- **`reports/stieltjes-derivative-relations`, section 4, lines 146 and 148.** The two
  character bridges need complex conjugation on the `s = −1` side; without it they
  fail for complex characters by `−0.143865275…i` (odd quartic mod 5) and
  `−0.033916259…i` (even cubic mod 7). The two Stieltjes articles print the
  conjugate correctly (X8).
- **`stieltjes-antiderivative-ladder`, proof of `thm:G1half` (line 531).**
  `ln²6 − ln²3 − ln²2 = 2 ln2 ln3` is called the `ζ''(0)`-coefficient; with
  `P(s) = 6^s − 3^s − 2^s + 1`, `P(0) = P'(0) = 0`, so `(Pζ)''(0) = P''(0)ζ(0)`: it is
  the coefficient of `ζ(0)`. The displayed identities stand (X16b; batch 141: 23;
  checked at intake).
- **`eisenstein-row-sums-cm-polygamma`, lines 168-170** (and
  `reports/polygamma-complex-arguments-cm-lattices`, lines 96-97). "The alternating
  component (`Re` at odd weight, `Im` at even weight) stays opaque" is reversed: the
  differentiated line law displayed just above evaluates exactly those components
  (`Im` at weight 2, `Re` at weight 3; in general
  `Re(iᵐ(ψ⁽ᵐ⁾(z+c) − ψ⁽ᵐ⁾(z))) = R_c⁽ᵐ⁾(t)` on `Re z = (1−c)/2`); it leaves the
  complementary components (`Im` at odd, `Re` at even weight) undetermined. The
  displayed identities stand (19; checked at intake).
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
interpolant is unique only up to `c·sin 2πz`), and "`q ≥ 5`" → "`φ(q) > 2`" at lines
713-723 (X16a, X16c; X16b is now under "False as printed"); the sign conventions for
Nielsen words and kernels in
`multiple-polylogarithms-introduction` (lines 649, 730-737; X16e) and
"the full Goncharov" at line 746 (X16f); `Re G₄` at line 193 of the CM report
(CM002); the vanishing-test prefactor remarks (CM006, X16i) and the Eichler-integral
wording (X16h) of `eisenstein-row-sums-cm-polygamma`; the claimed finite-field
counterexample to an identity of the inspected arXiv v1 of Radchenko–Zagier
(EXT001, third-party, outside this tree).

Batch 139 (9 October 2026) adds two items, also not checked at intake:
`reports/binet-malmsten-lambert-bridge` section 2 calls the cubic moment
`∫₀¹ log³Γ` open; 14 cites its Tornheim-derivative evaluation by Bailey–Borwein–Borwein
(Ramanujan J. 36 (2015), Thm 6), leaving reduction in a specified smaller algebra open.
`stieltjes-antiderivative-ladder` line 1073 ("forces genuinely new constants"): the
formal rank gives residual formal directions, not new constants (15).
Batch 141: 20 (appendix A) and 23 (`sec:cubic`, with an independent proof and evaluator)
also give the Bailey–Borwein–Borwein evaluation of `∫₀¹ log³Γ`. Two third-party items,
outside this tree and not checked: 23 reports a sign misprint before a positive
quadratic sum in equations (63) and (65) of the June 2012 author preprint of
Bailey–Borwein–Borwein; 24 proves a formal-polynomial version of Conjecture 5.5 of the
March 2010 author preprint of Amdeberhan et al.
(`int_0^1 (−log sin πx)^N dx = P_N(log 2)`).

Batch 140 (9 October 2026): `gaussian-eisenstein-double-polylogs` lines 207-211 say a
kernel returns `Li₃,₃(i,i)` "in `β(4)`, `π⁴`, `ζ(3)`"; the stuffle gives
`Li₃,₃(i,i) = 9ζ(3)²/2048 + 47π⁶/1935360 − 3iπ³ζ(3)/1024` (19; the value was
checked at intake, the remark about software output was not reproduced).

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
  `stieltjes-derivative-zeros/`, and further proofs by 15 (batch 139) and by 20 and 22
  (batch 141, over a polynomial ring in independent prime weights, all finite jets);
  intake recomputed the exact ranks for `q ≤ 60`).
  They do not assert arithmetic independence of the evaluated constants.
- The trivial-zero case of `rem:parity` is
  `L′/L(k+1,χ) + conj(L″(−k,χ)/(2L′(−k,χ))) = γ + log(2π/q) − H_k`; the factor `1/2`
  is essential.
- The even-total-weight half of `thm:alternation`: for every `m ≥ 0`,
  `S_{2m+1} = (2m+1)β(2m+2) − 2β(2m+1)log2 − Σ_{j=1}^{m}(2 − 2^{−2j})β(2m−2j+1)ζ(2j+1)`
  (three independent proofs; `S₅`, `S₇` are the cases `m = 2, 3`).

### Proved since intake (9 October 2026 continuations)

- `gaussian-multiple-polylog-depth`: `eq:wt5-sporadic` and the five weight-6 identities
  `2048g₅₁ = …` to `92160g₁₅ = …` (six independent proofs, sources 14-19 of `reports/gaussian-parity-reductions/`: by the
  depth-two parity theorem of Panzer (2017), specialized, by shuffles, and (19) by a
  differential recurrence with exact double-zeta boundary data), and the three weight-4
  triple evaluations (14, 19, 21). Coefficients unchanged.
- `eisenstein-gaussian-mixed-cuberoot-doubles` `eq:gauss-w2`, `eq:eis-w2`:
  `Li₁,₁(z,1/z) = −Li₂(z/(z−1))` on the unit circle (15, 17).
- The supergolden and `x⁴+x−1` trilogarithm ladders of `golden-polylog-ladders`
  (lines 181-182; `ladders-as-bloch-elements` line 59) (14).
- `gaussian-multiple-polylog-depth` `eq:S4-closed` (24, `thm:s4`): with
  `S₄ = g₄₁ + Im Li₄,₁(i,−1)`,
  `Im Li₄,₁(i,−1) = −(3g₄₁ + 3g₃₂ + 9g₂₃)/7 + π⁵/224 − (27/224)Gζ(3) − 2β(4)log2`,
  proved by 24's exact rational certificate (911 double-shuffle and distribution rows
  plus one convergent duality), replayed at intake with the delivered standard-library
  verifier (empty residual), row schemas checked by hand and the identity confirmed to
  40 digits; no independent re-derivation of all 911 rows has been made. The 911
  standard rows are 713 convergent double-shuffle rows, 181 with one regularized
  `Li₁(1)` factor and 17 lifted convergent distribution rows; the duality is one
  convergent instance of `t ↦ (1−t)/(1+t)`; the certificate is
  `reports/gaussian-parity-reductions/data/24-rigidity-S4_certificate.json`. The schemas
  checked by hand are the duality, distribution and single-divergence schemas. The
  restricted-row obstructions of 18, 20, 21, 22 and 23 concern depth-two product rows
  only and do not conflict. Coefficients unchanged.
- The plastic (reciprocal minimal-Pisot) `Li₂` and `Li₃` ladders of
  `golden-polylog-ladders` (lines 157-158), by one Rogers pentagon and one Kummer
  specialization (24); the `Li₄` ladder (line 159) remains numerical.
- Still open: every independence or minimal-depth statement. 23 conjectures the weight-seven
  analogue `S₆ = (722/527)g₆₁ + (40/527)g₄₃ − (128/155)g₂₅ + 15191π⁷/28569600 − (3/124)Gζ(5)
  − (2373/10540)β(4)ζ(3) − 2β(6)log2` (`S_p = Σ_{n≥0}(−1)ⁿHₙ/(2n+1)^p`); it encloses the
  residual below `10⁻²⁶⁰` by exact rational arithmetic; intake confirmed it to 40 digits. It
  is not proved.

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

## Continuations (batches 138-141, 8-9 October 2026)

Six external continuations, all AI-assisted research drafts pinned to `c78c7c3dc2`
or `3a6d80ed61` (whose Polylogarithms tree equals `a87af186c`), are placed as five
merged reports under `docs/reports/`, one per thematic spine. Manuscripts are not
edited; files of merge members carry the prefix of their manuscript number. Batch 139 (9 October 2026, `d4dead2c6b`) adds four further continuations as a sixth
merged report, `gaussian-parity-reductions/` (base 14, members 15-17); batch 140
(`49a6356865`) adds members 18 and 19. Batch 141 (`3b0bae5f5a`) adds members 20 and 22
to `rational-grid-distribution-ranks/` and 21, 23 and 24 to `gaussian-parity-reductions/`.

| Report | Spine | Base | Other sources |
|---|---|---|---|
| `stieltjes-derivative-zeros/` | `γ_n^{(k)}(a)` has at most `n` positive zeros for every `k`, exactly `n` for large `k`, full ray expansions; `n = 1` brackets; regularized trivial-zero bridges | 13 (`polylogarithms_research_bundle`, uniform in a Lerch deformation) | 06 (`ProveIt_Stieltjes_Zero_Geometry_Research`: exact count for `n ≤ 4` at every `k`, half-unit bracket, three-term `n = 1` law, parity kernels); 12 (sections on zeros and the bridge); 10 (spectral expansion at `a = 1`, normalized bridges) |
| `rational-grid-distribution-ranks/` | all-denominator formal ranks (character normal form), finite jets, reflection; cyclotomic polylogarithm trace jets and conductor descent | 10 (`polylogarithms-exact-structure`, arbitrary weights in any commutative algebra) | 12, 13, 20 (`ProveIt_Polylogarithms_Distribution_Jets_2026-10-09`), 22 (`polylogarithms_conductor_descent_2026-10-09`) |
| `alternating-harmonic-polylogarithms/` | `S_{2m+1}` at every weight; reflection for `T_{p,r}`; depth-exponent transition; inverse-argument mixed doubles | 11 (`polylogarithms_reflection_depth_transition_2026-10-07`) | 10, 12 |
| `herglotz-cyclotomic-obstructions/` | all-conductor relations of `β_q(a)`, exact five-term reduction criterion, `J(2/q)` classification, optimal truncation | 09 (`herglotz_research`, single source) | corrections credited from 12 (C15-C19) |
| `corpus-corrections/` | the correction registers of all six deliveries | 12 (`polylogarithms_research`, C01-C22) | 06, 10, 11, 13 registers; 09's `data/proposed_corrections.json` |
| `gaussian-parity-reductions/` | proofs of the manuscript's Gaussian weight-5/6 candidates by parity and shuffle; triples; ladders; log-gamma moments; certified evaluators at mixed roots; signed kernels and the unique unit-circle zero; Euler and Hölder certificates; complementary depth; complementary-power rigidity; sharp and reflected log-gamma moments; `S₄` proved by 24's exact rational certificate (911 double-shuffle and distribution rows plus one convergent duality), replayed at intake with the delivered standard-library verifier (empty residual), row schemas checked by hand and the identity confirmed to 40 digits; no independent re-derivation of all 911 rows has been made | 14 (`polylogarithms_exact_reductions_20261009`) | 15 (`polylogarithm_research_20261009`), 16 (`ProveIt_Gaussian_Polylogarithms_Research`), 17 (`proveit_polylog_gap_reductions_2026-10-09`), 18 (`polylogarithms_gaussian_continuation`), 19 (`gaussian_polylogarithms_research_package_20261009`), 21 (`ProveIt_polylogarithms_complementary_depth`), 23 (`polylogarithms_research_2026-10-10`), 24 (`polylogarithms_rigidity_20261010`) |

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
