# Six Sheets, Three Escapes: the Fiber Geometry of Gao's Keller Map F6

**Every fiber, all seven multiplicity patterns, an explicit finite normalization, the omitted surface, local and global monodromy of a five-dimensional Keller map**

This is a research report of ProveIt's research-report collection (category
`jacobian-conjecture`). It continues the formal project
`Algebra/JacobianConjecture`, but its subject is **not** a map of that
project: it studies the map **F6 of Shuhong Gao**, *Counterexamples to the
Jacobian conjecture in dimensions greater than two*, arXiv:2608.00222v1,
§4.5.1, Theorem 4.5. The map, its polynomiality, its determinant −290 and
its generic degree six are Gao's. The report is dated 24 September 2026 and
built from two manuscripts, both "prepared with ChatGPT".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 02 (base) | batch 36, manuscript 02 | `ProveIt_Six_Sheets_Research` (main file `Six_Sheets_Three_Escapes.tex`, 22-page PDF; delivered in `e13affd32`) | `e21766d04` | `1a1396d4d` | the untagged, non-editorial text of Sections 1–12 and Appendices A–B (the merge's editorial text is Sections 1.2, 1.4, Appendix A as rewritten, Appendix D) |
| 05 | batch 36, manuscript 05 | `ProveIt_Keller_Fibers_Research` (*A Codimension-Three Omitted Surface for a Five-Dimensional Keller Map*, main file `article.tex`, 24-page PDF; delivered in `e13affd32`) | `e21766d04` | `1a1396d4d` | everything tagged "(source 05)", and Appendix C |

Every result, proof, example, remark, limitation and question of both
manuscripts is printed. Results proved by both are printed once and
credited to both; genuinely different proofs of source 05 are kept as
marked second routes. **Status: AI-assisted and unrefereed. Nothing in this
report is formalized in Lean or Rocq, and nothing about F6 is formalized
anywhere in ProveIt** (see "The formal project" below).

```
README.md                                        this guide (replaces both delivered READMEs)
article.tex                                      the report: source 02's text, labels prefixed, with source 05 merged in
article.pdf                                      the compiled report, 45 pages (unnumbered title page, abstract page 1,
                                                 contents pages 2–3, text pages 4–43, references pages 43–44)
02-six-sheets-SOURCE_AUDIT.md                    source 02's source audit and claim boundary, as delivered
05-keller-fibers-SOURCE_AUDIT.md                 source 05's source and attribution audit, as delivered
code/02-six-sheets-build_map.py                  source 02: sparse exact construction of F6 (SymPy)
code/02-six-sheets-verify.py                     source 02: 63 exact checks and reusable inverse functions (SymPy)
code/05-keller-fibers-verify.py                  source 05: exact rational and finite-field checks, complex_fiber_size (SymPy)
data/02-six-sheets-map_coefficients.json         source 02: the five coordinate polynomials of F6
data/02-six-sheets-normalized_discriminant.json  source 02: the 179 terms of H in (c,A,B,D,K), K = E+B^2-AD
data/02-six-sheets-requirements.txt              sympy==1.14.0
data/02-six-sheets-verification_report.txt       source 02's recorded run: ALL 63 EXACT CHECKS PASSED
data/05-keller-fibers-requirements.txt           sympy==1.14.0
data/05-keller-fibers-sextic_discriminant.txt    source 05: the expanded 54-term sextic discriminant
data/05-keller-fibers-verification.txt           source 05's recorded run: twelve PASS groups
```

Delivered names. Source 02: `Six_Sheets_Three_Escapes.tex` is shipped as the
rewritten `article.tex`; `SOURCE_AUDIT.md`, `code/build_map.py`,
`code/verify.py`, `data/map_coefficients.json`,
`data/normalized_discriminant.json`, `data/verification_report.txt` and
`requirements.txt` are shipped under the `02-six-sheets-` names above. Its
delivered README, its PDF and its checksum manifest `SHA256SUMS.txt` are not
shipped (the manifest was verified, all ten entries OK, then dropped by
repository policy). Source 05: `verify.py`, `verification.txt`,
`sextic_discriminant.txt`, `requirements.txt` and `SOURCE_AUDIT.md` are
shipped under the `05-keller-fibers-` names above; its `article.tex`,
README and `article.pdf` are not shipped (a merge member's manuscript is
printed in the merged `article.tex`). Every shipped file other than
`article.tex`, `article.pdf` and this README is byte-identical to the
delivery. `article.pdf` is a build of this text.

## Labels

Every label in `article.tex` carries the prefix `f6:`. Source 02's 72 labels
are kept, unchanged after the prefix. The merge added 65 labels: 60 for
source 05's material, with the sub-prefix `f6:kf:` (nine of source 05's
label names, such as `thm:main` and `lem:derivative`, already existed in
source 02), and five others (four on editorial text, one on source 02's unlabelled Conclusion: `f6:sec:merge`,
`f6:sec:dictionary`, `f6:tab:dictionary`, `f6:sec:conclusion`,
`f6:app:provenance`): 137 in total, all distinct. Theorem, section and
equation numbers are those of the built `article.pdf`; since this report is
new, many of source 02's own numbers have moved (for example
its Theorem 6.3 on nonproperness is Theorem 6.4 here). No label has a Lean
or Rocq mapping.

## Setting and notation

Characteristic zero throughout; geometric fibers over an algebraic closure,
counted as distinct points; nonproperness and monodromy over C. Source
`(x,y,z1,z2,z3)`, target `b = (c,A,B,D,E)`, `κ = E+B²−AD`,
`T = −A+2cB−c³κ`, `L = B−cD`. The fiber sextic is
`P_b(w) = 2w⁶−2w⁵−w³+aw²+bw+d` with `a = 1+cA`, `b = c⁴κ−2c²B+cA`,
`d = c³D−c²B`; the root is `w = γu1`. The report uses source 02's names;
source 05 is translated by a dictionary (Section 1.4, Table 1):

| This report (= source 02) | Source 05 |
|---|---|
| target `(c,A,B,D,E)` | `q = (C,p1,p2,p3,p4)` |
| sextic `P_b(w)`, coefficients `(a,b,d)` | `R_{a,b,c}(T)`, coefficients `(a,b,c)` |
| universal discriminant `Δ(a,b,d)`; normalized `H = Δ/c²` | `D(a,b,c)`; `D̃` |
| `A²+4B` | `H := p1²+4p2` |
| stage monomials `a_i`; sweep `(w1,w2,w3)`; potentials `G2,G3,G4` | `ξ_i`; `(t,s,r)`; `A, 2tA+s, B` |
| sweep quotients `Ŝ_i`; section coordinates `β_i` | `E_i`; jets `J_i` |
| free parameter on M: `t = c²B` | `η` |
| nonproperness set `NP(F)` | `S_F` |

Watch for these readings:

- `c` is the **first target coordinate** here, not the constant coefficient
  (that is `d`); `T` is a **target function**, not a root variable; `H` is
  the **normalized discriminant**, not `p1²+4p2`; `A, B, D, E` are target
  coordinates, and `E_1, E_2, E_3` are the three escape components.
- `𝒩` denotes **only** the normalization algebra of F6. Source 02 also used
  `𝒩_F` for the nonproperness set; that symbol is renamed `NP(F)` here
  (disclosed in the text).
- "Normalization" has two objects: the normalization `Z = Spec 𝒩` of the
  **map** F6, and the normalization `A²_{a,ρ} → 𝒟` of the discriminant
  **surface** in coefficient space (Proposition 6.2).
- "Degree six" for F6 means **generic fiber size six**. Its coordinate
  polynomials have ordinary degrees `(7,38,40,42,44)` and
  `(6,342,421,507,904)` monomials. The project's own five-variable map `G`
  has ordinary degree six (profile `(6,6,4,3,4)`); it is a different map.
- The project's `F = (P,Q,R)` is Alpöge's three-dimensional map, and its
  `G = (G1,…,G5)` and `p = xy²`, `q = x²yz` belong to its stable shear. The
  report's `P_b`, `q_b`, `G2,G3,G4`, `p(w)` are unrelated.

Every other symbol renamed from source 05 is listed in Appendix D, item 2;
no normalization or scalar changed.

## What the report claims

Numbers are those of the built `article.pdf`. Credit: "02" or "05" names the
source that proves it; "both" means both do.

- **Uniform chart (Theorem 3.2, 02).** The source open set `x ≠ 0` is
  isomorphic over the target to `{(b,v) : q_b(v) = 0, q_b'(v) ≠ 0}`,
  including over `c = 0`; `x = 0` maps isomorphically onto `c = 0`. The key
  is the derivative identity `γ = P_b'(w)` on the fiber (Lemma 3.1, both;
  source 05 displays the expansion). Source 05 proves the `c ≠ 0` part as a
  scheme isomorphism (Theorem 3.3) and the hyperplane on the source
  (Section 3.4).
- **Every fiber (Corollary 3.4, Theorem 4.1, both).** `#F⁻¹(b)` is the number
  of simple roots of `q_b`, plus one on `c = 0`; on `c = 0` it is 3 or 1 as
  `A²+4B ≠ 0` or `= 0`. The spectrum is exactly `{0,1,2,3,4,6}`, with an
  exact gcd test at every target.
- **Multiplicity patterns (Lemma 4.4, Propositions 4.5–4.6, 05).** Every
  sextic of the family has at least three distinct roots (Newton sums,
  `5(3−m)θ = 37`); exactly seven patterns `1⁶, 2 1⁴, 3 1³, 2² 1², 4 1², 3 2 1,
  2³` occur, with fiber sizes 6, 4, 3, 2, 2, 1, 0.
- **Omitted surface (Theorem 4.7, both).** `A⁵ ∖ F(A⁵)` is the smooth
  closed complete intersection `M ≅ G_m × A¹` of codimension three, at the
  unique parameter `(a,b,d) = (21/32, 5/32, 25/128)`, where
  `P = 2(w³−w²/2−w/8−5/16)²` (Lemma 4.3, both).
- **No stabilization from dimension ≤ 3 (Corollary 4.10, 05).** F6 is not
  polynomially equivalent to `Φ × id` for any polynomial self-map `Φ` of
  `A^m`, `m ≤ 3`. Dimension four is **not** excluded.
- **Finite normalization (Theorems 5.1–5.2, 02).** Adjoining
  `ζ = wJ(w)/c` gives a smooth finite free algebra of rank six with basis
  `1,w,…,w⁴,ζ`; the source is its complement of the ramification locus and
  three unramified components `E_1, E_2, E_3 ≅ A⁴` over `c = 0`.
- **Discriminant (Theorem 6.1, both; Proposition 6.2 and Theorem 6.6, 05).**
  `H = Δ/c²` is an irreducible polynomial with `H|_{c=0} = −108(A²+4B)` and
  trace-form discriminant `H/256` (02). The discriminant surface is
  normalized by `A²_{a,ρ}`, and its local analytic type is determined at
  every point (05).
- **Nonproperness (Theorem 6.4, both).** `NP(F) = V(cH)`, two irreducible
  components meeting transversely (05) along `c = 0, A²+4B = 0`.
- **Normal crossings (Corollary 6.7, 05).** Near `M`, `V(H)` is
  `V(ε1ε2ε3)` with local monodromy `(Z/2)³`.
- **General lemma (Theorem 7.1, 02).** A quadratic-contraction
  normalization over any domain.
- **Galois (Section 8).** Geometric monodromy `S6` (Theorem 8.1; 02 on the
  line `(1,0,0,t,0)`, 05 on the line `(1,−1,0,τ,2−τ)`); no proper
  intermediate field (Corollary 8.3, 05); arithmetic `S6` with no radical
  inverse point at `(1,0,0,1,0)` modulo 3, 13, 37 (Theorem 8.4, 02) and at
  `(1,−1,0,1,1)` modulo 7, 11, 269 (Theorem 8.5, 05).
- **Real fibers (Theorem 9.1, 02).** Sizes exactly `{0,1,2,3,4}`; off `c = 0`
  contained in `{0,1,2,4}`.
- **Proposed work.** An exact inversion procedure (Section 9.1), two Lean
  plans (Sections 10.3–10.4), and questions 1–18 (Section 11; 1–10 from 02,
  11–18 from 05).

## What the report does not claim

- F6 is Gao's construction; no new counterexample to the Jacobian conjecture
  is claimed. The plane Jacobian problem and Gao's middle-branch rigidity
  problem (his Problem 4.8, §4.5.2) are not settled.
- No Whitney stratification, no irreducible decomposition of every
  higher-contact incidence variety, and nothing about Gao's F4, F5, F7.
- Codimension three is not claimed to be a universal maximum for omitted
  sets of Keller maps, and the omitted set is not the nonproperness set.
- Smoothness of `V(H)` is asserted only along `c = 0`, `A²+4B = 0`.
- Geometric image ≠ rational image ≠ real image. The real result off
  `c = 0` is containment in `{0,1,2,4}`, not attainment; the value 1 off
  `c = 0` is open (question 15).
- The radical obstruction does not forbid an inverse by algebraic numbers.
  The `S6` certificates are starting points, not a distribution theorem;
  characteristic-zero conclusions do not transfer to characteristic p.
- Theorem 7.1 does not claim that such covers are Keller, and its
  normality hypotheses must be checked case by case.
- The scripts are computer-algebra checks, not kernel certificates. Finite
  round trips do not prove the chart isomorphism, normality, openness,
  exhaustiveness of the patterns, the local analytic types, properness or
  monodromy; those are proved in the text. Neither suite checks the
  trace-form identity `H/256` (the intake's unshipped spot check confirmed
  it at three rational targets). `reconstruct` accepts exact rational roots
  only, and `complex_fiber_size` counts geometric, not rational or real,
  points.
- The Lean plans are plans; no Lean source is supplied.
- Priority: both sources' literature and repository searches were bounded
  (see the two `SOURCE_AUDIT.md` files); neither is an exhaustive priority
  certification, and both repository audits were scoped (the repository was
  not cloned or rebuilt, and not every file was read).

## Questions answered or re-scoped by the merge

- Source 05's question on a global finite completion across `c = 0`
  (direction 11) is **answered** by source 02's normalization `Z` and its
  boundary theorem.
- Source 05's question on real image and real fiber chambers (direction 15)
  is **re-scoped**: source 02's Theorem 9.1 gives the possible real
  cardinalities; the chambers, the semialgebraic boundary of the real image
  and attainment off `c = 0` remain open.
- Source 02's question 3 (singular strata of `H`) is **re-scoped** after
  source 05's local types: the local type and singular-locus criterion in
  coefficient space are known; a Whitney stratification and explicit
  strata in the target remain open.

## The formal project

`Algebra/JacobianConjecture` proves, in kernel-checked Lean 4 and Rocq/Coq,
statements about Alpöge's three-dimensional map `F = (P,Q,R)`
(`det JF = −2`) and its stabilizations. **None of them concerns F6.** In
particular the project's dimension-five theorems are about its own stable
map `G = K ∘ (F × id²) ∘ S` of ordinary degree six (profile `(6,6,4,3,4)`),
not about Gao's F6:

- `jacobianConjectureInDimensionFive_false`
  (`Algebra/JacobianConjecture/Lean/JacobianConjecture/SimplerCounterexample.lean:332`;
  audited at `Algebra/JacobianConjecture/Lean/JacobianConjecture/Audit.lean:115`)
  and `jacobianConjectureInDimensionFive_false_over_complex` (`:340`);
- `jacobian_conjecture_dimension_five_is_false`
  (`Algebra/JacobianConjecture/Coq/SimplerCounterexample.v:356`);
- `jacobianConjectureInDimension_false_of_three_le`
  (`Algebra/JacobianConjecture/Lean/JacobianConjecture/Stabilization.lean:256`),
  the stabilization of `F` to every dimension `n ≥ 3`.

The report states no result that the project has formalized, and its
relation to the project confers no formal status on it. Outside the reports
of this collection, the only mention of Gao's paper in the repository is
`ProveIt_Walkthrough.tex` (section "Current-event context"), which cites it
as external context and not as a dependency of the Lean/Rocq proof.

## Neighbouring reports

- [`../arithmetic-local-global-fibers`](../arithmetic-local-global-fibers)
  and [`../weighted-keller-rigidity`](../weighted-keller-rigidity) study
  Alpöge's three-variable map (integral and p-adic fibers; weighted
  rigidity). They share no theorem with this report, and none of
  their results concerns F6. Both also cite Gao's paper: the first for his
  complex fiber stratification of Alpöge's map, the second for his own
  three-dimensional map of geometric degree four.

## Build

From a scratch copy of `article.tex` (MiKTeX or TeX Live, pdfLaTeX; no
bibliography program, figures or Python needed):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed build has 0 errors, 0 warnings (no undefined or multiply
defined references or citations, no duplicate destinations) and no
overfull or underfull boxes. Copy only `article.pdf` back.

## Rerunning the checks

Both scripts write their outputs **beside themselves under their delivered,
unprefixed names**, and source 02's verifier does `from build_map import
build_map`, which fails under the shipped name. Never run them in the report
directory; run each on a copy with the delivered layout. Tested with Python
3.13.5 and SymPy 1.14.0 (`uv run --no-project --with sympy==1.14.0 python …`
works).

Source 02 (about 23 s):

```sh
mkdir -p /tmp/f6-02/code /tmp/f6-02/data && cd /tmp/f6-02
cp <report>/code/02-six-sheets-build_map.py code/build_map.py
cp <report>/code/02-six-sheets-verify.py    code/verify.py
python code/verify.py
```

It rewrites `data/map_coefficients.json`, `data/normalized_discriminant.json`
and `data/verification_report.txt` in the copy (compare them with the
shipped `data/02-six-sheets-*` files) and prints `ALL 63 EXACT CHECKS
PASSED.` Run standalone, `build_map.py` also writes `data/map_coefficients.json`
and a `data/zero_section.txt`, which is not shipped.

Source 05 (about 29 s):

```sh
mkdir -p /tmp/f6-05 && cd /tmp/f6-05
cp <report>/code/05-keller-fibers-verify.py verify.py
python verify.py > verification.txt
```

It writes `sextic_discriminant.txt` beside itself even without redirection;
compare both outputs with `data/05-keller-fibers-verification.txt` and
`data/05-keller-fibers-sextic_discriminant.txt`. In the copy, source 05's
counting function is available as `from verify import complex_fiber_size`;
it takes an exact rational target `(c,A,B,D,E)`.

The intake reran both suites on such copies: they passed, and their outputs
equal the shipped files after stripping the carriage returns that Windows
text mode adds (the shipped files contain none).

## Discrepancies in delivered files

- Source 02's delivered README (not shipped) named `SHA256SUMS.txt` and
  `Six_Sheets_Three_Escapes.pdf`; neither is shipped. Its source text had a
  corrupted `\text` in equation (33) of this build (a tab followed by
  `ext`; its PDF printed "exttermsof degreeatmosttwo"); the report corrects
  it.
- Source 05's delivered README (not shipped) said `verification.txt` "ends
  with `ALL CHECKS PASSED`"; two lines restating the proof boundary follow
  it. It also named `article.pdf` (24 pages) and `README.md`, which are not
  shipped.
- `code/02-six-sheets-verify.py` imports `build_map` by its delivered name,
  and both scripts write unprefixed files (see "Rerunning the checks").
  `code/02-six-sheets-build_map.py` standalone writes the unshipped
  `data/zero_section.txt`.
- `02-six-sheets-SOURCE_AUDIT.md` and `05-keller-fibers-SOURCE_AUDIT.md`
  describe the repository at the pin `e21766d04` and name repository paths
  as they were then (`Algebra/JacobianConjecture/README.md`,
  `Algebra/JacobianConjecture/Research/README.md`,
  `Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean`,
  `ProveIt_Walkthrough.tex`); these files are unchanged since the pin.
  Source 05's audit refers to "the README" for repository paths; the paths
  are in its article, printed in Appendix B here.
- The two sources cite Gao's pages differently (source 05: PDF pages 22, 23
  and 31; source 02: printed pages 23 and 24), consistent with a PDF/printed
  offset. What each credits to Gao also differs slightly: only source 02
  credits the degree profile and the four-point fibers over the nonzero
  axis. Neither was checked against Gao's paper at the merge.
- `data/02-six-sheets-normalized_discriminant.json` names the coordinate
  `κ` as `K`.
- `data/05-keller-fibers-sextic_discriminant.txt` uses source 05's
  coefficient names `(a,b,c)`; its `c` is this report's `d`.

## Provenance

Appendix D of the report records both sources, what each contributed, the
pin, the placement commit and every choice made in the merge: source 02 as
base (its chart is uniform across `c = 0`, its normalization lemma holds
over any domain, and its normalization answers source 05's question), the
renamed symbols, the one symbol of source 02 renamed (`𝒩_F → NP(F)`), the
corrected typo, and which proofs are kept as second routes.
