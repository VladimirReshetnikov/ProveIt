# Con(ZFC) in Diophantine form

**Explicit polynomials with fixed integer coefficients whose unsolvability
ZFC proves equivalent to Con(ZFC): seven wave-2 syntheses of the
native-window/Pell compiler on the blank run of K215, down to 13 positive
unknowns, superseding the eight wave-1 packages**

This report holds seven AI-assisted research packages, all dated 22 October
2026. They are batch 218 of ProveIt's incoming reports (arrival
`7be2780f26`, "Con(ZFC) in Diophantine form (wave-2)"), placed in
`8a4b00b5bf`. All seven are pinned to `3b201cdea3`, a snapshot that already
contains this report's wave-1 form. Each synthesizes the wave-1 packages,
citing them by their numbers 01–08, and adds reductions of its own.

**Wave 1 is superseded.** By Vladimir's direction the wave-2 packages
completely supersede the eight batch-217 packages, so directories
`01-explicit82/` … `08-start-only67/` were removed from the tree when wave 2
was placed. They, their recovery map and the wave-1 version of this README
are recoverable from any commit from `084e120830` to `f3af223ef7` (for
example `git show f3af223ef7:<this directory>/README.md`), and their archives
remain in arrival `2fd49a1a9d`. Wave-1 numbers 01–08 are kept as source
numbers only because the wave-2 texts use them; the wave-2 directories
continue the sequence as 09–15. Two packages bundle a copy of the wave-1
README: `14-integer29/dependencies/upstream_comparison.md` and
`15-release/evidence/diophantine_zfc_round2/review/README.upstream.md`. Both
copies describe the superseded wave.

The wave-2 packages overlap heavily, and several reach the same
construction independently. They are therefore **placed, not written**,
following the intake rule for overlapping deliveries
([docs/incoming/README.md](../../../../../../docs/incoming/README.md),
section 2):

- each package keeps its delivered layout and PDF in its numbered directory,
  with the wrapper directory removed;
- this README is the reconciliation note;
- no delivered file was edited, no PDF was built, and no delivered program
  was run at intake.

Facts below are the packages' own, taken from two read-only intake
dossiers; the few facts checked at intake say so.
[`PLACEMENT.md`](PLACEMENT.md) is the recovery map for wave 2. It covers
640 archive members: 535 staged, 93 omitted as byte-identical (up to line
ends) copies of repository files outside this report, and 12 checksum
ledgers and log files excluded by the root `.gitignore`.

## The common theorem

Each package defines polynomials or small systems with four (sometimes up to
nine) **fixed integer coefficient ports**. They are determined by a finite
recipe from the literal 215-state machine
[`candidate-k215/k215.tm`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm),
and the package proves, by ordinary mathematics formalizable in ZFC, that

> ZFC ⊢ (no solution in the stated domain) ↔ Con(ZFC).

The route is wave 1's:

1. the blank run of K215 halts iff ZFC has a finite refutation;
2. a local tile language for that run is compiled by the repository's
   native-window/Pell compiler
   ([`native-stream-queue/`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/README.md));
3. the input is removed, following wave-1 package 06's "inputless"
   interface.

On that route wave 2 combines three things:

- **02's ordinary strong Pell norm**, which brings the 15-unknown system
  from degree 60 to degree 28;
- **05's signed quadratic-root elimination**, which gives 14 unknowns;
- **08's quadratic lift**, now one register and one equation smaller.

It adds new reductions:

- weighted roots, giving 13 unknowns;
- auxiliary gaps, giving lower degree;
- signed-domain arguments, giving fewer unrestricted-integer unknowns;
- new tile alphabets, giving smaller coefficients.

## The seven packages

Numbers are the packages' own; **none was re-derived at intake.** "Ops"
counts every binary +, −, × of the displayed circuit, including
multiplication by fixed numerals. Coefficients and reuse are free, and so are
the comparisons in a system. Unknowns are strictly positive integers unless
marked ℤ (unrestricted integers).

| Dir | Archive | Title as printed | Distinctive constructions (unknowns / equations / degree / ops) |
|---|---|---|---|
| [`09-combined13/`](09-combined13/) | `con-zfc-combined-reductions.zip` | *Smaller Diophantine descriptions of ZFC consistency* | **P₁₃ 13 / 1 / 571 / 84**; 13 / 1 / 515 / 85; 13 / 4 / 544 / 78; **P₁₄ 14 / 1 / 121 / 76**; 14 / 5 / 72 / 67; 16 / 7 / 24 / 60; quadratic lift 32 / 23 / 2; 62ℤ quartic; P₁₃ over 39ℤ, degree 1142 |
| [`10-synthesis14/`](10-synthesis14/) | `con-zfc-diophantine-synthesis-2026-10-22.zip` | *Smaller Diophantine forms of Con(ZFC)* | grouped system 15 / 4 / 28 / 63; Q₅₆ 15 / 1 / 56 / 74; Ψ₁₄ 14 / 1 / 342 / 73; Φ₁₄ 14 / 1 / 293 / 75; 14 / 5 / 244 / 69; P₆₇ rebound to new coefficients; 33ℤ lifts of P₆₇/P₆₈ |
| [`11-t4/`](11-t4/) | `ZFC_Diophantine_Combined_T4_2026-10-22.zip` | *Combining explicit Diophantine encodings of ZFC consistency* | **T4 coefficients (B = 2^(5^18))**; ordinary system and P₆₉; two 33-unknown quartic lifts; 31ℤ forms (product 188 / 127, SOS 100 / 136, system 6 / 50 / 119) |
| [`12-gap-norm14/`](12-gap-norm14/) | `ProveIt_ConZFC_Diophantine_Synthesis_2026-10-22.zip` | *Smaller Diophantine forms of ZFC consistency* | **gap norm Φ₁₄^gap 14 / 1 / 219 / 75**; Ψ₁₄; S₆₀ 15 / 6 / 28 / 60; **gap system 15 / 6 / 22 / 61**; gap product 15 / 1 / 93 / 70; gap SOS 15 / 1 / 44 / 78; quadratic lift 32 / 23 / 2 |
| [`13-four-cell14/`](13-four-cell14/) | `ConZFC_Synthesis_14vars_2026-10-22.zip` | *Smaller Diophantine formulations of Con(ZFC)* | S₁₅ 15 / 6 / 28 / 61; P₆₉; SOS 15 / 1 / 56 / 78; Ψ₁₄; Φ₁₄; Q₃₃; four-cell coefficients (d = 5^28) |
| [`14-integer29/`](14-integer29/) | `con_zfc_synthesis_2026-10-22.zip` | *Smaller Diophantine forms of ZFC consistency* | ordinary system, P₆₉, SOS, Q₃₃ on 06's coefficients; **29ℤ forms**: system 6 / 50 / 113, product 188 / 121, SOS 100 / 130, products 300 / 119 and 236 / 120 |
| [`15-release/`](15-release/) | `combined_con_zfc_3b201cd.zip` | *Combining explicit Diophantine constructions for the consistency of ZFC* | P₁₄ 14 / 1 / 293 / 75; 14 / 5 / 244 / 69; double-gap product 15 / 1 / 83 / 71 and system 15 / 6 / 22 / 63; **sextic 25 / 16 / 6, octic 20 / 11 / 8**; 32ℤ (584 / 138) and 33ℤ (159 / 134) polynomials; 60ℤ quartic |

Directory numbers follow the archives' arrival (file-time) order. Each
directory's delivered `README.md` (`README.txt` for 11) is its entry point.
The articles are:

- `09-combined13/con_zfc_reductions.pdf`;
- `report.pdf` in 10, 11, 12, 13 and 14;
- `15-release/report/combined_con_zfc.pdf`.

15's complete result table is its `final_forms.csv`.

## Frontier, credits and bases (intake findings)

The table reads each criterion from the packages' own figures; the base is
the package to cite when several prove the same thing.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Fewest positive unknowns | **13** (P₁₃: 84 ops, degree 571; 85 ops at 515; 4-equation system 78 ops) | 09 only | 09 |
| 14 unknowns, lowest degree | **P₁₄ degree 121, 76 ops**; its 5-equation system degree 72, 67 ops | 09 only | 09 |
| 14 unknowns, via root elimination | Φ₁₄ 75 / 293 and Ψ₁₄ 73 / 342 (same formulas and leading forms); gap norm 75 / 219 | Φ₁₄, Ψ₁₄: 10, 12, 13; Φ₁₄ also 15 (as P₁₄); 09 emits both metrics as 05's elimination; gap norm: 12 only | 10; gap norm 12 |
| 15-unknown six-equation system | **61 ops, maximum degree 28**, symbol for symbol the same in 09, 10, 11, 13, 14 and 15; 12's S₆₀ shifts the transport quotient (z₀ = z + 1) and saves one op | six packages; S₆₀: 12 | 13; S₆₀ 12 |
| Lowest-degree 15-unknown system | **degree 22**: 12's gap system (61 ops), 15's double-gap system (63 ops) | 12, 15 | 12 |
| Fewest operations, any single equation | **67** (P₆₇, degree 155, wave-1 06/08). No package claims fewer; 10 rebinds it to new coefficients | inherited | (wave-1 06) |
| 15-unknown single equation, low degree | P₆₉ 69 / 99 in all seven (gate lists of 11 and 12 byte-identical); 12's gap product 70 / 93; 15's double-gap product 71 / 83 | all; 12; 15 | 13; 15 for degree 83 |
| Smallest system | 60 ops: 12's S₆₀ (15 / 6 / 28) and 09's retained-auxiliary system (16 / 7 / 24) | 12; 09 | — |
| Low-degree lifts (positive) | quartic: **32 unknowns / 23 quadratics** (09, 12: same unknowns, different R-elimination); 33 / 24 (10, 11, 13, 14, 15: one register and one equation fewer than 08); sextic 25 / 16 and octic 20 / 11 | 09, 12; five packages; 15 | 09; 15 |
| Fewest unrestricted integers | **29ℤ** (14); then 31ℤ (11), 32ℤ (15), 33ℤ (10, 12, 15), 38ℤ (13), 39ℤ (09) | 14 | 14 |
| Integer quartic | 60ℤ (15), 62ℤ (09); 11 notes that its 99ℤ quartic does not improve wave-1 04's 83 | 15, 09 | 15 |
| Smallest coefficients | **T4: B = 2^(5^18)**, 37,075 tiles (11) | 11 | 11 |

Wave 2 claims no result below 67 operations, so wave-1 06/08's
P₆₇ remains the minimum-operation equation; 10 and 15 carry it as a baseline.

### Coefficient recipes: use one whole tuple

Every package binds its four ports Bm1 = B − 1, Kconstant = D_C + B·D_R,
MC and the **shifted** MF = (native high mask) + B − 1 as one tuple. All
seven forbid splicing ports from different recipes.

| Dir | Local language | Tiles / windows | b, L, d (B = 2^d) | Binding file |
|---|---|---:|---|---|
| 09 | four-site T (W, C, E, S) | 71,356,645 | 5^13, 5^15, 5^28 | `COEFFICIENT_BINDINGS.json` → `compiler/tshape_constants.json` |
| 10 | projected cross | 87,923,161 | 5^13, 5^15, 5^28 | `coefficients/projected_cross_constants.json` |
| 11 | head-filtered T, tight band ("T4") | 37,075 | 5^8, 5^10, 5^18 | `INSTANCE.json` → `bridge/T4_CONSTANTS.json` |
| 12 | five-cell cross | 38,256,607,897 | 5^17, 5^19, 5^36 | `compiler/cross_constants.json` |
| 13 | four-cell | 71,356,645 | 5^13, 5^15, 5^28 | `data/four_cell_constants.json` |
| 14 | wave-1 06's nine-cell windows, unchanged | ≈1.42·10^21 | 5^33, 5^34, 5^67 | `vendor/blank67/k215_constants.json` |
| 15 | head-restricted nine-cell windows | 10,762,728,984,864 | 5^21, 5^22, 5^43 | `COEFFICIENT_BINDING.json` |

These recipes are interchangeable only **as whole tuples**, and only where
a package proves its compiler interface for that tuple:

- 10, 12 and 13 prove that wave-1 06's whole tuple also serves their new
  arithmetic, and 11 keeps it as a separate fallback. Wave 1's blanket
  warning ("a circuit from one package evaluated with another's coefficients
  means nothing") is therefore too broad for 06's tuple, though still right
  about splicing ports.
- 09's alternative five-cell recipe coincides with 12's default (the same
  start tuples, ordering and layout scalars, per the dossier).
- 11's unfiltered T variant has 09's tile count and d but a different layout,
  so its integers differ.
- 09 and 13 report the same tile count and scales. Their layouts were not
  compared at intake.

### Tensions, not adjudicated at intake

- 11 calls root elimination "not advantageous" once the inputless
  architecture exists (`comparison/COMPARISON.md:58-60`), while 09, 10, 12,
  13 and 15 use it to reach 14 or 13 unknowns. This is a difference of
  objective rather than a contradiction.
- 12 lists the 87,923,161-tile projected layout as an open problem, while 10
  delivers it as its primary recipe.
- The signed-domain reductions keep different sets of coordinates positive:
  - 14: seven coordinates, plus i odd and w a square;
  - 15: nine ports;
  - 13: twelve or thirteen;
  - 10: signs {τ, y, w, h, f, T};
  - 11 and 12: sign {h, f, T, γ, τ, y}.

  The 14-unknown polynomial over ℤ is 586 / 159 in 13 and 584 / 138 in 15,
  by different substitutions.
- 11's `comparison/COMPARISON.md` (around line 164) still recommends 08's
  34 / 25 lift and never mentions T4. Its `bridge/BRIDGE_AUDIT.md:5` uses
  06's coefficients in 08's quartic.
- 15 itself flags that inherited "Input-ignoring machine" contract wording
  in older packets describes the normalized-machine template, not raw K215
  (`COEFFICIENT_BINDING.json:15`).
- No wave-2 package says a wave-1 statement or the wave-1 README was
  *wrong*. 09's audit finds "no new gap" in 06, and 15 confirms 06's recipe.
  10 calls an unattributed divisibility shortcut "unjustified", and 14 calls
  an unattributed Δ-cancellation shortcut "illicit".

## What is not claimed

The packages say, in their own words (exceptions noted):

- **No new formal result.** The new reductions are ordinary mathematical
  proofs with finite audits. They are not Lean or Rocq theorems, not
  derivations in ZFC's proof syntax, and the endpoint builds were not rerun.
- **No consistency proof.** The theorems are equivalences. All but 09
  explicitly decline the stronger "neither side is provable", which needs an
  extra soundness hypothesis such as Σ₁-soundness; 09 mentions only the
  second-incompleteness hypotheses.
- **Positive domain only.** The positive-domain equations must not be read
  over ℤ (stated explicitly by 11, 13, 14 and 15; 09 gives the
  natural-number shift). Unrestricted-integer forms are separate constructions with their
  own positivity arguments.
- **No materialized coefficients.** Every recipe is finite and exact.
  Nothing is expanded: even 11's smallest Bm1 would take about 477 GB in
  binary. No accepting K215 computation or Pell witness is given.
- **No optimality.** No global minimum is claimed for any criterion, and
  nothing below 67 operations. The repository's Lean theorem
  `Jones1982.nine_unknowns` proves only the existence of a nine-unknown
  representation, with no degree. The packages compare with Jones's papers
  and leave a concrete nine-unknown specialization open.
- **No new universal bound.** 09 and 14 say so explicitly, and the others
  do not address it. In any case, fixed-input constructions do not change the
  universal 84-operation, 18-witness, degree-187 frontier recorded in
  `Computability/HilbertTenthProblem/README.md`.

## Relation to the formal developments

- **Machine endpoint.** All seven cite
  `KEndpoint215.blank_halts_iff_zfc_refutation` and
  `KEndpoint215.nonhalting_iff_zfc_consistency`
  (`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean:44,49`,
  present at `HEAD`, not rebuilt at intake). The claim that **ZFC proves**
  the Diophantine equivalence does not go through Lean's soundness. It
  rests on the formalizability in ZFC of the ordinary K215 calibration
  argument, which the Lean/Rocq theorems mirror.
- **Hilbert's tenth problem.** The compiler, its Pell lemmas and masks are
  the research-wip notes under
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`,
  which are not Lean-formalized.
- **Nothing in this report is formalized.** Neither project gains formal
  status from it.

## Delivery discrepancies

These are disclosed here and were not fixed in the delivered files.

- **Omitted copies.** Reports and drivers name vendored copies of repository
  files that are not in this tree (see `PLACEMENT.md`). Examples:
  - `vendor/k215.tm` in 13, `data/k215.tm` in 14 and `compiler/k215.tm` in
    09 and 12;
  - 10's `machine/` and `evidence/lean/`;
  - 14's `dependencies/`.

  The ignored checksum ledgers and logs are also absent, so 11's
  `verify_all.py` (whose first step checks the hash manifest) and 12's
  `reproduce.py` (which authenticates retained source files) fail in place.
  Rerun from the arrival commit, as `PLACEMENT.md` explains.
- **Table differences inside a package.**
  - 12's README recommends the degree-22 gap system, while its abstract and
    theorem centre S₆₀ (degree 28), and its README omits several integer
    rows.
  - 15's `final_forms.csv` lacks the 14-unknown sum of squares (82 ops,
    degree 488) that its TeX gives. Its 139-degree normalized double-gap row
    appears only in the CSV, as a cross-check.
  - 09's 39ℤ, degree-1142 row is in its TeX but not in its README table.
- **Intermediates retained by their authors**:
  - 09's section 5 and its cross recipe;
  - 10's five-cross recipe;
  - 11's signed33 forms, nine-port form and alternative T/cross layouts;
  - 12's Φ₁₄ (293) and Ψ₁₄^gap (268);
  - 15's degree-139 packet, kept "only as an arithmetic cross-check".
- **Not delivered.** 15's research emitters and some historical scripts
  (its `DEPENDENCIES.md:19`).
- **Attribution.** 15's `NOTICE.md` records "OpenAI-assisted synthesis";
  11's baseline row reproduces wave-1 01's own figures.

## Further questions and research

These are the open problems the packages list, merged and credited:

1. **Formalize the bridge**: the weighted-root lemma, signed-quotient,
   signed-domain and rank lemmas, the quadratic-lift equivalence and the
   compiler interfaces (09, 10, 11, 12, 13, 14, 15).
2. **Fewer unknowns without a degree explosion**: below 13 or 14 unknowns,
   or a concrete nine-unknown specialization (09, 12, 13, 15).
3. **Smaller tile languages and coefficients**: head-side marking, further
   globally sound pruning, the projected layout, a materializable benchmark,
   and charging coefficient bit length (09, 12, 13, 14, 15).
4. **Compile the C222 calculus directly** (12, 13, 14).
5. **Fewer positivity conditions** over ℤ: release i, or reduce the seven or
   nine positive ports (12, 14, 15).
6. **Smaller lifts**: remove another register from the 32- or 33-unknown
   quadratic systems (13, 14, 15).
7. **Better finalizers and combinations**: fewer operations from the
   four-port circuit (10), 07's signed repunit with the X = wq scale (15),
   root elimination with the ordinary strong equation (15), and a better
   product finalizer (14).
8. **Internalization in PA** or weaker arithmetic (12).

## Licence and provenance

Every package was prepared for ProveIt and reuses MIT-0 repository material.
The licence and notice files each package ships are kept in place.

| Pin | Arrival | Placement | Superseded wave 1 |
|---|---|---|---|
| `3b201cdea32d2c816f5f3d20734051f25fd3ef14` | `7be2780f26` | `8a4b00b5bf` | arrival `2fd49a1a9d`; placement `084e120830` to audit fixes `f3af223ef7` |

## Files

Every staged file, grouped by source directory (generated from the tree):

- `09-combined13/`: `COEFFICIENT_BINDINGS.json`, `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `con_zfc_reductions.pdf`, `con_zfc_reductions.tex`, `verify_arithmetic.py`, `verify_compiler.py`
- `09-combined13/arithmetic/`: `amalgam14_product76.json`, `amalgam14_sos81.json`, `amalgam14_system67.json`, `build_candidates.py`, `candidate_receipt.json`, `outer14_73.json`, `p13_initial.json`, `p67_source.json`, `p80_source.json`, `p82_source.json`, `polynomial13_84.json`, `polynomial13_lowweight85.json`, `product14_75.json`, `sos13_89.json`, `sos13_lowweight90.json`, `system13_78.json`, `system13_lowweight79.json`
- `09-combined13/compiler/`: `README.txt`, `blank_helical.py`, `compiler_verification.json`, `count_blank_alphabet.py`, `cross_compiler_constants.py`, `cross_constants.json`, `cross_count_verification.json`, `tshape_compiler_constants.py`, `tshape_constants.json`, `tshape_count_verification.json`, `tshape_helical.py`, `verify_k215.py`
- `09-combined13/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`
- `09-combined13/low_degree/`: `README.txt`, `build_systems.py`, `integer_quartic62.json`, `integer_quartic62.py`, `integer_quartic62_checks.json`, `ordinary15_system61.json`, `quartic32.json`, `quartic32.py`, `quartic32_checks.json`, `retained16_system60.json`, `sparse_polynomial.py`, `system_checks.json`
- `09-combined13/proofs/`: `AUDIT_STATUS.md`, `COEFFICIENT_REDUCTION_PROOF.md`, `INDEPENDENT_ROOT13_AUDIT.md`, `INTEGER_QUARTIC62_INDEPENDENT_REVIEW.md`, `LOW_DEGREE_PROOF.md`, `ROOT_AMALGAMATION_PROOF.md`, `SIGNED_CORE_AND_INTEGER62.md`
- `09-combined13/upstream/`: `06_k215_constants.json`, `06_report.tex`, `COMPARISON_AT_PIN.md`
- `09-combined13/upstream/compiler/`: `02_PELL_INTERFACE_LEMMAS.md`, `06_blank_helical_proof.md`, `06_compiler_constants.py`, `06_fixed_blank_67_proof.md`, `06_pell_lemma_audit.md`, `SOURCES.json`
- `09-combined13/upstream/logic/`: `KEndpoint215.lean`, `NineMain.lean`
- `09-combined13/upstream/pell/`: `02_FIXED_INPUT75_ORDINARY_PROOF.md`, `complete75_asymmetric_scale_tradeoffs.md`, `complete84_signed_quotient_absorption.md`, `complete84_signed_quotient_soundness_scout.md`
- `09-combined13/verification/`: `pdf_review.json`, `verification_summary.json`
- `10-synthesis14/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `provenance.json`, `report.pdf`, `report.tex`
- `10-synthesis14/circuits/`: `fixed_blank_67_integer33.json`, `fixed_blank_68_integer33.json`, `ordinary_blank_four_sos_74.json`, `ordinary_blank_four_system_63.json`, `ordinary_blank_product69.json`, `ordinary_blank_sos_78.json`, `ordinary_blank_system_61.json`, `ordinary_quartic33.json`, `root14_outer73.json`, `root14_product75.json`, `root14_system69.json`
- `10-synthesis14/code/`: `build_ordinary.py`, `build_root14.py`, `projected_cross_compiler.py`, `verify.py`, `verify_signed_and_root.py`
- `10-synthesis14/coefficients/`: `cross_count_verified.json`, `projected_cross_constants.json`
- `10-synthesis14/evidence/`: `base67.json`, `original_constants.json`, `source_catalogue.md`
- `10-synthesis14/evidence/legacy-code/`: `blank_helical.py`, `compiler_constants.py`, `count_blank_alphabet.py`, `verify_k215.py`
- `10-synthesis14/evidence/licenses/`: `LICENSE.Wade`
- `10-synthesis14/evidence/proofs/`: `blank_helical_proof.md`, `fixed_blank_67_proof.md`, `start_only_quartic34_proof.md`
- `10-synthesis14/evidence/reports/`: `02-system63.tex`, `05-fixed15-16.tex`
- `10-synthesis14/proofs/`: `COEFFICIENT_REVIEW.md`, `ORDINARY_REDUCTION.md`, `projected_cross_proof.md`, `signed_domain.md`
- `10-synthesis14/sections/`: `ordinary_section.tex`, `projected_cross_section.tex`
- `10-synthesis14/verification/`: `circuit_audit.json`, `cross_count_full.json`, `document.json`, `ordinary.json`, `projected_cross.json`, `signed_root.json`, `summary.json`, `table_binding.json`
- `11-t4/`: `INSTANCE.json`, `LICENSE.ProveIt`, `README.txt`, `SOURCE_PINS.json`, `VALIDATION.json`, `report.pdf`, `report.tex`, `verify_all.py`
- `11-t4/bridge/`: `BRIDGE_AUDIT.md`, `T4_CONSTANTS.json`, `check_cross_counts.py`, `check_t4.py`, `cross_count_receipt.json`, `t4_verification.json`, `t4_windows.json`
- `11-t4/bridge/sources/`: `blank_helical.py`, `compiler_constants.py`, `k215_audit_notes.md`, `k215_transitions.json`, `proof_dependencies.json`
- `11-t4/checks/`: `CORE_CHECK.json`, `independent_core_check.py`
- `11-t4/comparison/`: `COMPARISON.md`, `HYBRID_PROOF.md`, `HYBRID_VALIDATION.json`, `PACKET_CIRCUIT_AUDIT.json`, `audit_packet_circuits.py`, `build_hybrid.py`, `hybrid_product69.json`, `hybrid_sos78.json`, `hybrid_system61.json`, `overview_README.md`, `product67_T4.json`, `tree_manifest.json`
- `11-t4/comparison/sources/01-explicit82/`: `README.txt`
- `11-t4/comparison/sources/01-explicit82/native/`: `k215_native72_system.json`, `k215_native82_source.json`, `polynomial_audit.json`
- `11-t4/comparison/sources/01-explicit82/tag/`: `tag91_dimensions.json`
- `11-t4/comparison/sources/02-system63/`: `FIXED_INPUT75_ORDINARY_PROOF.md`, `PELL_INTERFACE_LEMMAS.md`, `README.md`, `REVIEW_ORDINARY_STRONG75.md`, `fixed_input63_ordinary_system.json`, `fixed_input74_ordinary_square_marker.json`
- `11-t4/comparison/sources/03-system64/`: `README.md`
- `11-t4/comparison/sources/03-system64/artifacts/`: `fixed_marker_systems.json`
- `11-t4/comparison/sources/03-system64/proofs/`: `INDEPENDENT_REVIEW.md`
- `11-t4/comparison/sources/04-poly73/`: `README.md`
- `11-t4/comparison/sources/04-poly73/data/`: `polynomial73.json`, `system65.json`
- `11-t4/comparison/sources/04-poly73/provenance/`: `FIXED_INPUT_AUDIT.md`
- `11-t4/comparison/sources/05-fixed15-16/`: `README.md`
- `11-t4/comparison/sources/05-fixed15-16/arithmetic/`: `fixed15_outer80_degree346.json`, `fixed15_product82_degree295.json`, `fixed16_system66_degree34.json`
- `11-t4/comparison/sources/05-fixed15-16/proofs/`: `fixed_input_proof_notes.md`
- `11-t4/comparison/sources/06-blank67/`: `README.md`
- `11-t4/comparison/sources/06-blank67/data/`: `fixed_blank_67.json`, `fixed_blank_68.json`, `fixed_blank_system_61.json`, `fixed_blank_system_62.json`, `k215_constants.json`
- `11-t4/comparison/sources/06-blank67/proofs/`: `blank_helical_proof.md`, `fixed_blank_67_proof.md`, `pell_lemma_audit.md`
- `11-t4/comparison/sources/07-fixed70/`: `README.md`
- `11-t4/comparison/sources/07-fixed70/artifacts/`: `CIRCUIT_FORMAT.md`, `fixed_input.json`, `fixed_input_notes.md`
- `11-t4/comparison/sources/08-start-only67/`: `README.md`
- `11-t4/comparison/sources/08-start-only67/evidence/diophantine_zfc_encoding/`: `start_only_quartic34.json`, `start_only_quartic34_proof.md`
- `11-t4/comparison/sources/08-start-only67/evidence/diophantine_zfc_review/`: `start_only_polynomial67.json`, `start_only_system61.json`
- `11-t4/quartic/`: `audit_quartic33.py`, `audit_quartic33_ordinary.py`, `quartic33_audit.json`, `quartic33_normalized.json`, `quartic33_ordinary.json`, `quartic33_ordinary_audit.json`, `quartic33_ordinary_proof.md`, `quartic33_proof.md`
- `11-t4/quartic/sources/`: `README.md`, `diophantine_zfc.tex`, `start_only_quartic34.json`
- `11-t4/reduction/06-blank67/code/`: `build_fixed.py`
- `11-t4/reduction/06-blank67/data/`: `fixed_blank_67.json`, `fixed_blank_system_61.json`
- `11-t4/reduction/06-blank67/`: `report.tex`
- `11-t4/reduction/08-start-only67/`: `README.md`, `diophantine_zfc.tex`
- `11-t4/reduction/`: `ODD_AUXILIARY_PROOF.md`, `ODD_SIGNED_VALIDATION.json`, `SIGNED_DOMAIN_PROOF.md`, `SIGNED_VALIDATION.json`, `SOURCE_PINS.json`, `build_odd_signed.py`, `build_signed.py`, `signed31_product.json`, `signed31_sos.json`, `signed31_system.json`, `signed33_product.json`, `signed33_sos.json`, `signed33_system.json`
- `11-t4/review/`: `INDEPENDENT_CHECKS.json`, `INDEPENDENT_T4_CHECKS.json`, `QUARTIC_INDEPENDENT_CHECKS.json`, `independent_quartic_checks.py`, `independent_review_checks.py`, `independent_t4_checks.py`
- `12-gap-norm14/`: `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `coefficient_recipe.tex`, `gap_auxiliary.tex`, `gap_root_elimination.tex`, `provenance.json`, `report.pdf`, `report.tex`, `reproduce.py`, `root_elimination.tex`, `verification.json`
- `12-gap-norm14/arithmetic/`: `algebra_verification.json`, `baseline67.json`, `blank14_gap_norm75.json`, `blank14_gap_norm75_over_Z32.json`, `blank14_gap_outer75.json`, `blank14_gap_outer75_over_Z32.json`, `blank14_norm75.json`, `blank14_norm75_over_Z32.json`, `blank14_outer73.json`, `blank14_outer73_over_Z32.json`, `build_fourteen.py`, `build_gap.py`, `build_improved.py`, `gap_verification.json`, `integer_lift_verification.json`, `ordinary_blank69.json`, `ordinary_blank69_over_Z33.json`, `ordinary_blank_sos77.json`, `ordinary_blank_sos77_over_Z33.json`, `ordinary_blank_system60.json`, `ordinary_blank_system60_over_Z33.json`, `ordinary_gap70.json`, `ordinary_gap70_over_Z33.json`, `ordinary_gap_sos78.json`, `ordinary_gap_sos78_over_Z33.json`, `ordinary_gap_system61.json`, `ordinary_gap_system61_over_Z33.json`, `root_elimination_verification.json`
- `12-gap-norm14/compiler/`: `blank_helical.py`, `count_blank_alphabet.py`, `cross_constants.json`, `cross_constants.py`, `cross_geometry_review.json`, `review_cross_geometry.py`, `verify_k215.py`
- `12-gap-norm14/licenses/`: `LICENSE.Wade`
- `12-gap-norm14/proofs/`: `CROSS_COMPILER_PROOF.md`, `GAP_AUXILIARY_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `ROOT_ELIMINATION_PROOF.md`, `quartic32_proof.md`
- `12-gap-norm14/quadratic/`: `build_quartic32.py`, `check_gap_identities.py`, `gap_independent_review.json`, `quartic32.json`, `quartic32_checks.json`, `sparse_poly.py`
- `12-gap-norm14/upstream/`: `blank_helical_proof.md`, `collection_README.md`, `fixed_blank_67_proof.md`, `k215_audit_notes.md`, `pell_lemma_audit.md`
- `12-gap-norm14/verification/`: `pdf_qa.json`
- `13-four-cell14/`: `MANIFEST.sha256`, `Makefile`, `PROVENANCE.json`, `README.md`, `SYMBOLS.json`, `document_qa.json`, `report.pdf`, `report.tex`, `verification_receipt.json`, `verify.py`
- `13-four-cell14/code/`: `four_cell_compiler.py`, `ordinary_start.py`, `quartic33.py`, `root14_independent_audit.py`, `root_elimination.py`
- `13-four-cell14/data/`: `four_cell_constants.json`, `ordinary_start_checks.json`, `ordinary_start_poly69.json`, `ordinary_start_sos78.json`, `ordinary_start_system61.json`, `quartic33_verified.json`, `root14_independent_checks.json`, `root14_outer73.json`, `root14_outer73_integer38.json`, `root14_product75.json`, `root14_product75_integer38.json`, `root_elimination_checks.json`
- `13-four-cell14/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `13-four-cell14/proofs/`: `FOUR_CELL_PROOF.md`, `ORDINARY_START_PROOF.md`, `ROOT14_ARITHMETIC_REVIEW.md`, `ROOT_ELIMINATION_INDEPENDENT_REVIEW.md`, `ordinary_quartic_lifts.md`
- `13-four-cell14/references/package02/`: `FIXED_INPUT75_ORDINARY_PROOF.md`, `PELL_INTERFACE_LEMMAS.md`
- `13-four-cell14/references/package05/`: `fixed_input_zfc.tex`
- `13-four-cell14/references/package06/`: `blank_helical_proof.md`, `fixed_blank_67_proof.md`, `k215_audit_notes.md`, `pell_lemma_audit.md`
- `13-four-cell14/references/package08/`: `start_only_quartic34_proof.md`
- `13-four-cell14/vendor/`: `fixed_blank_67.json`, `k215_transitions.json`
- `14-integer29/`: `Makefile`, `README.md`, `SOURCE_MANIFEST.json`, `VERIFICATION.json`, `report.pdf`, `report.tex`
- `14-integer29/data/`: `blank_normalized_integer29_poly119.json`, `blank_normalized_integer29_poly120.json`, `blank_ordinary_integer29_poly121.json`, `blank_ordinary_integer29_sos130.json`, `blank_ordinary_integer29_system113.json`, `blank_ordinary_poly69.json`, `blank_ordinary_quartic33.json`, `blank_ordinary_sos78.json`, `blank_ordinary_system61.json`, `build_receipt.json`, `integer29_verification.json`, `verification.json`
- `14-integer29/dependencies/`: `blank_helical_proof.md`, `fixed_blank_67_proof.md`, `k215_audit_notes.md`, `ordinary_pell_interface.md`, `pell_lemma_audit.md`, `upstream_comparison.md`
- `14-integer29/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`
- `14-integer29/proofs/`: `independent_signed_review.md`, `integer29_degrees.md`, `ordinary_strong.md`, `signed_domain_proof.md`
- `14-integer29/src/`: `build_integer29.py`, `build_ordinary.py`, `check_odd_multiplier.py`, `reproduce.py`, `verify_combinations.py`
- `14-integer29/vendor/blank67/`: `blank_helical.py`, `compiler_constants.py`, `count_blank_alphabet.py`, `fixed_blank_67.json`, `fixed_blank_68.json`, `fixed_blank_system_61.json`, `k215_constants.json`, `k215_transitions.json`, `parent_quartic34.json`, `verify_k215.py`
- `15-release/`: `COEFFICIENT_BINDING.json`, `DEPENDENCIES.md`, `FINAL_CHECKS.json`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `REPLAY_VALIDATION.json`, `final_forms.csv`, `final_forms.json`, `run_checks.py`
- `15-release/checks/`: `check_final_forms.py`
- `15-release/evidence/diophantine_zfc_encoding/`: `start_only_quartic34.json`, `start_only_quartic34_proof.md`
- `15-release/evidence/diophantine_zfc_review/`: `SOURCE_PINS.json`, `START_ONLY_DEGREE_CERTIFICATE.md`, `start_only_polynomial67.json`, `start_only_system61.json`
- `15-release/evidence/diophantine_zfc_round2/audit/`: `COMBINED_MATHEMATICAL_AUDIT.md`, `arithmetic_checks.json`
- `15-release/evidence/diophantine_zfc_round2/compiler/`: `RAW_MACHINE_COEFFICIENTS.md`, `count_windows_independent.cpp`, `count_windows_independent.json`, `raw_coefficients_audit.json`, `raw_coefficients_audit.py`, `raw_coefficients_specification.json`
- `15-release/evidence/diophantine_zfc_round2/integers/`: `COMPACT_INTEGER_LIFT_RECEIPT.json`, `INDEPENDENT_INTEGER_AUDIT.json`, `INTEGER_LIFT_RECEIPT.json`, `README.md`, `SIGNED_DOMAIN_PROOF.md`, `normalized25_integer_43_degree10.json`, `normalized25_integer_52_degree6.json`, `normalized34_integer_52_degree8.json`, `normalized34_integer_61_degree4.json`, `ordinary20_integer_38_degree16.json`, `ordinary20_integer_47_degree8.json`, `ordinary33_integer_51_degree8.json`, `ordinary33_integer_60_degree4.json`, `start_only_integer32_polynomial138_degree584.json`, `start_only_integer33_polynomial130_degree304.json`, `start_only_integer33_polynomial134_degree159.json`, `verify_integer_artifacts_independent.py`
- `15-release/evidence/diophantine_zfc_round2/integers/parents/`: `ordinary_octic20.json`, `ordinary_quartic33.json`, `start_only14_polynomial75.json`, `start_only_ordinary_sheared71.json`, `start_only_polynomial67.json`, `start_only_quartic34.json`, `start_only_sextic25.json`
- `15-release/evidence/diophantine_zfc_round2/pell/`: `POSITIVE_GAP_SHEARS.md`, `START_ONLY14_PROOF.md`, `build_sheared_tradeoffs.py`, `build_start_only14.py`, `sheared_tradeoff_audit.json`, `start_only14_arithmetic_audit.json`, `start_only14_polynomial75.json`, `start_only14_system69.json`, `start_only_ordinary69.json`, `start_only_ordinary69_sos.json`, `start_only_ordinary69_system.json`, `start_only_ordinary_sheared71.json`, `start_only_ordinary_sheared71_sos.json`, `start_only_ordinary_sheared71_system.json`, `start_only_sheared69.json`
- `15-release/evidence/diophantine_zfc_round2/quadratic/`: `LOW_DEGREE_PROOF.md`, `independent_low_degree_audit.md`, `independent_sparse_audit.json`, `independent_sparse_audit.py`, `ordinary_octic20.json`, `ordinary_quartic33.json`, `start_only_sextic25.json`
- `15-release/evidence/diophantine_zfc_round2/review/01-explicit82/native/`: `k215_native72_system.json`, `k215_native82_source.json`
- `15-release/evidence/diophantine_zfc_round2/review/01-explicit82/`: `report.tex`
- `15-release/evidence/diophantine_zfc_round2/review/02-system63/`: `FIXED_INPUT73_PROOF.md`, `FIXED_INPUT75_ORDINARY_PROOF.md`, `QUADRATIC_LIFT.md`, `README.md`, `SQUARED_MARKER_PROOF.md`, `fixed_input63_ordinary_system.json`, `fixed_input63_system.json`, `fixed_input72_square_marker.json`, `fixed_input74_ordinary_square_marker.json`
- `15-release/evidence/diophantine_zfc_round2/review/03-system64/artifacts/`: `fixed_marker_systems.json`, `fixed_marker_variants.json`
- `15-release/evidence/diophantine_zfc_round2/review/03-system64/proofs/`: `DEGREE_295.md`, `FIXED_MARKER.md`
- `15-release/evidence/diophantine_zfc_round2/review/03-system64/`: `report.tex`
- `15-release/evidence/diophantine_zfc_round2/review/04-poly73/data/`: `polynomial73.json`, `quadratic83.txt`, `system65.json`
- `15-release/evidence/diophantine_zfc_round2/review/04-poly73/`: `zfc_diophantine.tex`
- `15-release/evidence/diophantine_zfc_round2/review/05-fixed15-16/arithmetic/`: `fixed15_outer80_degree346.json`, `fixed15_product82_degree295.json`, `fixed16_product74_degree157.json`, `fixed16_product75_degree125.json`, `fixed16_product76_degree113.json`, `fixed16_system66_degree34.json`
- `15-release/evidence/diophantine_zfc_round2/review/05-fixed15-16/paper/`: `fixed_input_zfc.tex`
- `15-release/evidence/diophantine_zfc_round2/review/05-fixed15-16/proofs/`: `fixed_input_proof_notes.md`
- `15-release/evidence/diophantine_zfc_round2/review/06-blank67/code/`: `blank_helical.py`, `compiler_constants.py`, `count_blank_alphabet.py`
- `15-release/evidence/diophantine_zfc_round2/review/06-blank67/data/`: `blank_alphabet_cardinality.json`, `fixed_blank_67.json`, `fixed_blank_68.json`, `fixed_blank_system_61.json`, `k215_constants.json`, `k215_transitions.json`
- `15-release/evidence/diophantine_zfc_round2/review/06-blank67/proofs/`: `blank_helical_proof.md`, `fixed_blank_67_proof.md`, `pell_lemma_audit.md`
- `15-release/evidence/diophantine_zfc_round2/review/06-blank67/`: `report.tex`
- `15-release/evidence/diophantine_zfc_round2/review/07-fixed70/artifacts/`: `fixed_input.json`, `fixed_input_notes.md`
- `15-release/evidence/diophantine_zfc_round2/review/07-fixed70/report/`: `zfc_diophantine.tex`
- `15-release/evidence/diophantine_zfc_round2/review/`: `COMPARISON.md`, `README.upstream.md`, `SOURCE_PINS.json`, `blank67_start_only67_identity.json`, `independent_circuit_review.json`, `independent_circuit_review.py`
- `15-release/evidence/diophantine_zfc_round2/root/`: `COEFFICIENT_REVIEW.md`
- `15-release/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`
- `15-release/report/`: `PDF_QA.json`, `REPORT_EQUATION_CHECK.json`, `build_report.sh`, `check_report_equations.py`, `combined_con_zfc.pdf`, `combined_con_zfc.tex`, `integer_results.tex`, `verification_results.tex`
- top level: `README.md` (this file), `PLACEMENT.md`
