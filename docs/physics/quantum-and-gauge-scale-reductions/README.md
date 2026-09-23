# Surreal Scales in Quantum Theory and Gauge Models

**Rare-event shadows, postselection cost, exact elimination, soft modes, holonomy discrimination, and quaternionic curvature**
Merged research report, 23 September 2026, from four manuscripts written
independently on that day. Prepared for Vladimir Reshetnikov.

```
article.tex      the report, standalone LaTeX with an internal bibliography
article.pdf      the compiled report, 107 pages
README.md        this guide
03-observable-limits-source_audit.md      source 03's own source and novelty audit, as delivered
08-quantum-operations-RESEARCH_AUDIT.md   source 08's own research and evidence audit, as delivered
code/            07-scales-in-physics-verify_examples.py, 07-scales-in-physics-build.sh      (source 07)
                 03-observable-limits-verification.py,
                 03-observable-limits-build.sh, 03-observable-limits-build.ps1          (source 03)
                 04-gauge-holonomy-verify.py, 04-gauge-holonomy-build.sh                (source 04)
                 08-quantum-operations-verify.py, 08-quantum-operations-build.sh        (source 08)
data/            07-scales-in-physics-verification_results.txt,
                 07-scales-in-physics-requirements.txt                                  (source 07)
                 03-observable-limits-verification_results.txt,
                 03-observable-limits-requirements.txt,
                 03-observable-limits-pdf_quality_check.txt                             (source 03)
                 04-gauge-holonomy-verification.json, 04-gauge-holonomy-verification.txt,
                 04-gauge-holonomy-requirements.txt, 04-gauge-holonomy-build-report.json  (source 04)
                 08-quantum-operations-verification.json,
                 08-quantum-operations-build_validation.json,
                 08-quantum-operations-requirements.txt                                 (source 08)
```

Every label in `article.tex` carries the prefix `qgs:` (337 labels). Material
from source 07, the base, has no sub-prefix; material from source 03 carries
`qgs:obs:`, from source 04 `qgs:hol:`, from source 08 `qgs:ops:`, and results
added in the merge `qgs:mrg:`. The sub-prefixes resolve the twenty label names
the sources shared (`thm:postselection`, `lem:spectral`, `eq:riccati`,
`eq:chi`, `eq:Delta`, `prop:shadow` and others). This is a new report: all 84
labels of the delivered base article are present as `qgs:<name>`, none was
lost, and nothing in the collection cited them before this placement. No `qgs:`
label has a Lean implementation mapping.

## Four sources, one report

| | Manuscript | Pin | Contributes |
|---|---|---|---|
| **07** | *Surreal Scales in Quantum Theory and Gauge Models* (base) | `c0a36ee` | Structure and title; leading-Gram theorem in the printed form; all-power-data obstruction; sharp cost theorem in the printed form; multiscale elimination with independently separated scales, its real-parameter counterpart and dressed dynamics; scalar trichotomy and virtual selection; evaluation-matrix proof of the composite obstruction; Wilson action theorem; two-scale plaquette; Bell and CCR obstructions; benchmarks. Files prefixed `07-scales-in-physics-`. |
| **03** | *Infinitesimal Scales, Observable Limits, and Gauge Topology* | `934810a` | Positive-support evaluation lemma; adaptive operational reduction; the weaker postselection bound; a proof of the leading-Gram theorem; support-controlled block diagonalization, inverse-splitting-scale dynamics, three-level mediated coupling, finite-depth hierarchy, Gibbs reduction; all of Section 16 (continuum gauge theory); boundaries; recursions. Files prefixed `03-observable-limits-`. |
| **04** | *Infinitesimal Gauge Holonomy as a Quantum Resource* (author line: "Mathematical development and exposition: ChatGPT") | `934810a` | The general real-closed setting; Helstrom, pure-state distance, overlap triangle; affine chart and exact Wilson defect; regular class functions; all of Section 14 (optimal query overlap, state separation, frontier, valuation law, precision certificate, calibration cost, applications, real specializations); a proof of the sharp cost theorem; quaternionic Gram lemma, simulation at full generality, bilinear proof of the composite obstruction; implementation formulas. Files prefixed `04-gauge-holonomy-`. |
| **08** | *Surreal Scales in Quantum Operations, Soft-Mode Reduction, and Non-Abelian Interferometry* | `c0a36ee` | Intrinsic leading-Gram form, mixed-output example, amplitude precision; universal rare embedding; a proof of the sharp cost theorem with the residue threshold; finite-trial accounting; entanglement filter; all of Sections 10–11 (Schur defects, displacement, Feshbach window) and 15 (dark port); general commutator identity; analytic invariant-germ obstruction; Puiseux and rank-two realizations; decision table. Files prefixed `08-quantum-operations-`. |

Both pins are ancestors of the placement commit `66d7e55`, and none of the
reports the sources inspected changed between those pins and that commit. The
source manuscripts, their PDFs and their own READMEs are not shipped; their code,
data and the two audit files are, byte-identical, under the prefixes above.
Source numbers are the delivery positions in batch 29.

**Why one report.** Every pair of sources shares a theorem: 03, 07 and 08 prove
the leading-Gram theorem; all four prove a postselection bound and give the same
tagged-state equality example; 03, 04 and 07 prove the quaternionic simulation;
04 and 07 the composite obstruction; 04, 07 and 08 commutator identities for a
small loop; 03, 07 and 08 treat effective Hamiltonians. It is filed beside, not
inside, the physics report (see "Relation to the neighbouring reports").

**Printed once** (crediting every proving source): the finite spectral theorem
(Proposition 4.1); the operational shadow (Proposition 4.3, credited to 03, 04,
07, 08 and `phys:thm:quantumshadow`); the trace-norm facts (Lemma 4.4); the
leading-Gram theorem (Theorem 5.1, 03/07/08); the sharp cost theorem
`max(p,q)·D(ρ',σ') ≤ D(ρ,σ)` (Theorem 6.1, 04/07/08, same failure-flag proof);
the tagged example (all four); finite copies (Proposition 6.6, 03/07); the
quaternionic representation and simulation (Proposition 12.1, Theorem 12.3,
03/04/07); the commutator identity (Theorem 13.1, 08, with 04's chart form as
Corollary 13.2); the Wilson action (Theorem 13.8, 07, containing 04's
Proposition 9.1); the Bell bound (Theorem 17.1, 04/07).

**Where the merge chose.** Source 03's bound `D_out ≤ 2D/p_*` is true but weaker
(a factor two, and `p_* ≤ min(p,q)` instead of `max(p,q)`); it is kept as
Corollary 6.2 with 03's own proof, which loses the factor by bounding `|p−q|`
separately. The composite obstruction keeps both proofs (Theorem 12.5, 07's
evaluation matrix; Theorem 12.6, 04's bilinear map, with a slightly different
hypothesis). Source 04's finite results are stated over any real closed field.
The three effective-Hamiltonian theorems (07: unlimited high block, independent
scales; 03: ordinary gap, support certificates; 08: soft eliminated block) are
different theorems and all are kept. Source 04's regular class-function theorem
and source 08's analytic-germ theorem are complementary and both kept.

**Notation.** One convention throughout (Conventions 1.2–1.3, Table 3): `F` real
closed, `K = F[i]` (as in the physics report; sources 04 and 07 had them the
other way round), valuation `v`, value group `Γ`, Kraus operators `M_j`,
trace distance `𝒟`, second scale `ζ = t^(1,0)` (the collection reserves `η` for
the infinitesimal phase residue, so no `η` is used), `Δ` only for source 07's
scale matrix, `κ` only for the commutator valuation, `L_j` only for leading Gram
factors, `C` only for the whitened coupling, `χ` for the quaternion
representation (no `J`). Table 3 lists every renamed symbol.

**Claim tiers.** The report adopts the physics report's firewall
(`phys:conv:tiers`): tags **[E]** exact identity checked by a program (22),
**[C]** theorem proved in the text (119), **[A]** assessment (119), and the
provenance marker **[I]** imported (20). Results added in the merge are marked
**[merge]** and proved in full.

## What the report claims

Numbers refer to the built `article.pdf`. Sections 5–15 hold over any real closed
field except where a Hahn monomial or strong evaluation is used; Section 16 uses
a Hahn field on a fixed ordinary manifold.

1. **Rare branches (Section 5).** Theorem 5.1: for a branch output `A` with
   `p = tr A > 0`, `v(p) = 2r` and `st(A/p) = G/tr G` with `G = Σ L_j L_j*`,
   `L_j = st(t^(−r) M_j R)`, intrinsic to the output; Remark 5.2: the diagonal
   case is `fsp:thm:skeleton`. Corollary 5.3: precision beyond `r` preserves the
   shadow, and the strict inequality is sharp. Theorem 5.7: two states equal
   modulo every `ε^N` with orthogonal conditional shadows. Proposition 5.8: any
   ordinary channel hides in a rare branch with identical complete shadows.
2. **Cost (Section 6).** Theorem 6.1, sharp; Corollary 6.2 (source 03's weaker
   bound); Remark 6.3: the classical case gives `δ/max(P(B),Q(B))`, halving the
   bound `2δ/b` of `fsp:thm:stability`; Corollary 6.4 valuation budget;
   Corollary 6.5 calibration cost; Proposition 6.6 finite copies; Theorem 6.7
   one-sided concentration `p_max = dλ_d`, Example 6.8 a Bell pair behind a
   product shadow.
3. **Effective Hamiltonians (Sections 7–9).** Theorem 7.1: exact elimination of
   an unlimited block with independent scales, `H_eff = S(H) − ½(𝒞S(H)+S(H)𝒞) +
   O(τ²)`; Corollary 7.3 its uniform real counterpart. Theorem 8.1: exact
   support-certified block diagonalization at an ordinary gap; Theorem 8.2
   inverse-splitting-scale dynamics (generalizing `phys:ex:amplify`); Theorem 8.4
   finite-depth hierarchy (≤ n−1 splits); Theorem 8.5 multiscale Gibbs reduction.
   Proposition 9.1: virtual transitions defeat a direct bias below every power
   of the coupling.
4. **Soft modes (Sections 10–11).** Theorem 10.3: `st S(H) = S_0 − Ξ`,
   `0 ≤ Ξ ≤ S_0`, `rank Ξ ≤ dim ker D_0`; Theorem 10.4: every such defect occurs
   with one infinitesimal; Proposition 11.1 displacement obstruction;
   Theorem 11.3 static energy window.
5. **Quaternions (Section 12).** Theorem 12.3 complex simulation; Theorems
   12.5–12.6 no naive composite (`d_m d_n − d_mn = 2mn(m−1)(n−1) > 0`).
6. **Loops (Section 13).** Theorem 13.1: `1 − Re c = 2|u_1 × u_2|²` for unit
   quaternions; Corollary 13.2 in the affine chart; Theorems 13.5 and 13.6
   (regular invariants start at second order); Theorem 13.8 gauge-invariant
   leading curvature of a positive Wilson action; Proposition 13.9 the two-scale
   plaquette, with the exact closed form for all `a, b` added in the merge.
7. **Holonomy discrimination (Section 14).** Theorem 14.1: optimal `m`-query
   overlap `T_m(s)` with finite ancillas and adaptive control; Corollary 14.2 no
   finite perfect test; Theorem 14.6: optimal unambiguous identification
   `w_m = 1 − T_m(1−w)` and the attained frontier; Theorem 14.7: valuation
   `max{0, κ − β/2}` in every divisible value group; Theorem 14.12 alignment
   certificate.
8. **Dark port (Section 15).** Theorem 15.1: the dark port heralds an exact
   `SU(2)` unitary with probability `|u_1 × u_2|²`; Propositions 15.4–15.5
   precision and background thresholds.
9. **Gauge fields (Section 16).** Theorem 16.1 exact charge rigidity;
   Theorem 16.2 action gap of valuation `2v(F_bad)`; Theorem 16.5 Hahn Kuranishi
   map under the Hodge–Green Assumption 16.4; Theorem 16.8 persistent obstruction;
   Theorem 16.9 sharp action floor; Theorem 16.10 two-scale torus obstruction.
10. **Obstructions and realizations (Sections 17–18).** Bell bound, no
    finite-dimensional CCR; convergent Puiseux and rank-two realizations.

## What the report does not claim

No non-claim of any source was dropped. Each is stated at its point of use and
listed again, by source, in Appendix E: **38** (source 03), **25** (source 04),
**31** (source 07), **29** (source 08). In outline: no empirical departure from
ordinary quantum mechanics, continuum quantum field theory, path-integral
measure, renormalization, thermodynamic limit, mass gap or confinement, no
singularity resolution, and no claim that nature contains a measurable
infinitesimal or that `No` is physically necessary; set-sized workspaces
suffice. Every source is an unrefereed AI-assisted draft; priority is certified
for nothing; nothing is Lean-verified; the programs check finite identities
only. Classical inputs are credited: Chefles–Barnett, Ivanovic–Dieks–Peres,
Acín, Vidal, Graydon, Wilson, Zanardi–Rasetti, Cirel'son, Bravyi–DiVincenzo–Loss,
Anderson–Trapp, Dusson–Sigal–Stamm, Kuranishi, Atiyah–Hitchin–Singer and Itoh.
Source 04's sentence that the absence of an Archimedean query threshold is "a
genuine structural difference from ordinary complex quantum theory" is kept with
a caveat (after Corollary 14.2): it holds only for literal infinitesimal gate
differences, which are not values of real parameters (Proposition 14.13), and
every real specialization has Acín's finite threshold.

## Stale statements corrected in this report

- At its pin `934810a`, source 04 reported that a code search for
  "postselection" found nothing; the physics report uses the word (status notes
  of `phys:ex:rare` and `phys:ex:amplify`). At pin `c0a36ee`, source 08 reported
  no Schur-related matches; the spectral-theory, hidden-negative-directions and
  Hahn–Hilbert-geometry reports use Schur complements. Neither source inferred
  absence (Section 2.3).
- Sources 03, 04 and 07 did not cite the finite-probability report; its
  `fsp:thm:skeleton`, `fsp:ex:shadowloss`, `fsp:thm:stability`,
  `fsp:eq:precision` and `fsp:thm:multisoft` are now credited where used.
  Sources 03 and 07 did not cite the spectral-theory report; `prop:effective`
  and `ex:secondorder` are now credited. Source 07 did not cite
  `squat:eq:groupcomm`, whose remainder bound is stronger than its own.
- Source 04's Lemma 6.2 (here Lemma 14.5) is the Ivanovic–Dieks–Peres bound, now named.

## Open questions, re-scoped

Section 22 lists the sources' open questions (none claimed resolved). One
collection item is **partly answered**: the vector-and-tensor-fields report's
open direction "support certificates for specific gauge-fixed nonlinear
systems" (`vtf:subsec:open`). Theorem 16.5 is such a certificate for the
Coulomb-gauge anti-self-duality equations on a closed Riemannian four-manifold,
under imported Hodge–Green hypotheses. The evolution part (Lorentzian,
hyperbolic, Einstein or Yang–Mills evolution) stays open (Section 16.7).

## Relation to the neighbouring reports

**[physics/surreal-scalars-and-spacetime](../surreal-scalars-and-spacetime/).**
Consistent with its negative stance: this report claims representation and
bookkeeping gains only. Its statement (status of `phys:thm:quantumshadow`) that
reduction cannot determine the state obtained by dividing by an infinitesimal
outcome probability is **confirmed and sharpened** (Theorem 5.7, Proposition
5.8), and the replacement datum, the leading Gram matrix, is supplied (Theorem
5.1). Its note that postselection lies outside that theorem is now priced by
Theorem 6.1. Its demand (status of `phys:ex:amplify`) that an amplification
proposal identify its gain and cost is **answered for postselection** (Theorems
6.1, 14.6, 14.7, Corollary 6.5, Propositions 15.4–15.5); for duration, Theorem
8.2 generalizes the example without a realization. Its exclusion of
conditioning on standard-probability-zero events (`phys:app:nonclaims`) is
**continued**, and the exclusion of infinite experiments stays. Stage D
(`phys:sub:stageD`) stays open. See Section 19.

**[surreal/finite-surreal-probability](../../surreal/finite-surreal-probability/).**
Commutative antecedents: `fsp:thm:skeleton` is the diagonal case of Theorem 5.1;
Theorem 6.1 improves `fsp:thm:stability` by a factor two (Remark 6.3; not a
correction, since that report does not claim sharpness); `fsp:thm:multisoft` is
the classical content of Theorem 8.5.

**[surcomplex/spectral-theory](../../surcomplex/spectral-theory/).**
`prop:effective` precedes Proposition 11.2 and the window of Theorem 11.3;
`ex:secondorder` is the three-level reduction of Section 8.4 at `r = d = 1`;
`thm:subspace` bounds what Theorem 8.1 constructs.

**[surquaternions/surquaternions](../../surquaternions/surquaternions/).**
Background algebra; `squat:eq:groupcomm` already gives the leading group
commutator of Proposition 13.9 with a stronger remainder. Theorems 13.1, 12.3
and 12.5 are new to the collection.

**[surreal/vector-and-tensor-fields](../../surreal/vector-and-tensor-fields/).**
Its open item is partly answered (above); `vtf:mink:thm:energyscale` is the
abelian analogue of Theorem 16.2.

Neighbours without overlap: `hnd:thm:twoscale` (two-scale positivity) beside
Section 10; the compact-operator part of the infinite-dimensional spectral
report beside open question 1; `e3:thm:holonomy` uses "holonomy" for spherical
excess, unrelated.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Standalone: internal `thebibliography` (44 entries), one TikZ figure, no
external files, no network access. The build gives 107 pages, zero errors,
warnings, undefined references or citations, multiply defined labels, duplicate
destinations, and overfull or underfull boxes.

## Re-running the source programs

The programs are the delivered bytes and several write files, so **run them on
a copy** of the directory, never in place. With Python and SymPy 1.14.0
(`pip install -r data/07-scales-in-physics-requirements.txt`; the four
requirement files all pin `sympy==1.14.0`):

```sh
cp -r . /path/to/copy && cd /path/to/copy
python code/07-scales-in-physics-verify_examples.py     # 43 checks; writes only with --output FILE
python code/03-observable-limits-verification.py        # 40 checks; writes nothing
python code/04-gauge-holonomy-verify.py                 # 148 checks; writes code/verification.json and code/verification.txt
python code/08-quantum-operations-verify.py             # 1,861 checks; writes data/verification.json
```

Source 04's program writes `verification.json` and `verification.txt` beside
itself, i.e. into `code/` under unprefixed names. Source 08's program writes
`data/verification.json` relative to the parent of its own directory, which as
placed is this report's directory, again under an unprefixed name. Neither
overwrites the prefixed records, but both would add files to the report if run
in place.

All four were rerun this way for the merge (Python 3.14.4, SymPy 1.14.0): 43,
40, 148 and 1,861 checks passed, exit status 0, with output identical to the
delivered records except the recorded Python version (3.13.5 in the delivered
runs) and, for the two files that 04 and 08 rewrite, CRLF line endings on
Windows.

The delivered **build scripts are not usable as placed**: `03-…-build.sh` and
`.ps1` and `04-…-build.sh` run `pdflatex article.tex` in `code/`, where there is
no article (source 04's also runs `verify.py`, an unprefixed name);
`07-…-build.sh` builds `surreal_scales_physics.tex` into `build/` and copies a
PDF over a delivered one; `08-…-build.sh` runs `python3 code/verify.py`
(unprefixed) and then `latexmk article.tex` in this directory, which would
rebuild the merged report. They are kept as delivered records. Likewise
`03-observable-limits-source_audit.md` and `08-quantum-operations-RESEARCH_AUDIT.md`
name the delivery paths (`verification.py`, `code/verify.py`,
`data/verification.json`); `data/03-observable-limits-pdf_quality_check.txt`,
`data/04-gauge-holonomy-build-report.json` and
`data/08-quantum-operations-build_validation.json` describe the sources' own
33-, 30- and 29-page PDFs (the last with SHA-256 sums of source 08's
`article.pdf` and `article.tex`), none of which is shipped.
