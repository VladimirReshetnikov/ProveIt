# Con(ZFC) in Diophantine form

**Eight independent fixed-input specializations of the native-window/Pell
compiler to the blank run of K215: explicit polynomials with fixed integer
coefficients whose positive-integer unsolvability ZFC proves equivalent to
Con(ZFC)**

This report holds eight AI-assisted research packages, all dated 22 October
2026. They are batch 217 of ProveIt's incoming reports (arrival `2fd49a1a9d`,
"Con(ZFC) in Diophantine form") and were placed in `084e120830`. All eight
prove the same theorem, independently and on the same day; none cites
another. The packages are therefore **placed, not written**: each keeps its
delivered layout, file names and PDF in a numbered directory with its
wrapper directory removed, and this README is the reconciliation note that
the intake procedure asks for when several deliveries overlap
([docs/incoming/README.md](../../../../../../docs/incoming/README.md),
section 2, "Placement only"). No delivered file was edited, no PDF was
built, and no delivered program was run at intake. Facts below are taken
from the packages and labelled as theirs; the few facts checked at intake
say so.

[`PLACEMENT.md`](PLACEMENT.md) is the recovery map: 600 archive members,
329 staged, 264 omitted as byte-identical copies of repository files (each
mapped to a repository path with the same bytes) and 7 checksum ledgers
excluded by the root `.gitignore`.

## The common theorem

Each package defines a polynomial P (or a small system) in a fixed number of
unknowns, with a handful of **fixed integer coefficients** determined by a
finite recipe from the literal 215-state binary machine
[`candidate-k215/k215.tm`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm)
(all eight bundle byte-identical copies of it, SHA-256 `fdbcef08…0090`), and
proves by ordinary mathematics formalizable in ZFC that

> ZFC ⊢ (P has no solution in strictly positive integers) ↔ Con(ZFC).

The route is the same in all eight:

1. the blank run of K215 halts iff ZFC has a finite refutation (the
   repository's machine endpoint, see below);
2. the machine is folded or normalized into a local "window" language and
   compiled by the repository's native-window/Pell compiler
   ([`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/README.md));
3. the universal compiler's **ordinary input is fixed** (to x = 1, a blank
   tape, or no input at all), which removes the input Pell block and a few
   witnesses, and the deleted witnesses are shown to be restorable on every
   solution.

All eight start from the repository's universal 84-operation polynomial
(`complete84_scaled_strong_output`, 18 positive witnesses plus the input,
degree 187) or its 74/75/85/92 relatives, all pinned at
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

## The eight packages

Numbers are the packages' own (delivery README and TeX agree unless noted);
**none was re-derived at intake.** "Ops" counts every binary +, −, × of the
displayed circuit, including multiplication by fixed numerals; fixed
coefficients are free and their bit length is not charged. "Unknowns" are
strictly positive integers unless marked.

| Dir | Archive | Title as printed | Headline constructions (unknowns / equations / degree / ops) |
|---|---|---|---|
| [`01-explicit82/`](01-explicit82/) | `ZFC_Diophantine_Explicit_82_2026-10-22.zip` | *An explicit Diophantine specialization for Con(ZFC)* | 18 / 1 / 187 / 82 = 46M+36A; 20 / 9 / ≤42 / 72; its SOS 20 / 1 / 84 / 98; quadratic lift 180 naturals / 82 / 2; tag route 22 naturals / 11 / ≤174 |
| [`02-system63/`](02-system63/) | `zfc_diophantine.zip` | *A fixed Diophantine representation of Con(ZFC)* | 16 / 7 / 28 / 63 = 34M+29A; P72 16 / 1 / 157 / 72; P74 16 / 1 / 101 / 74; SOS 16 / 1 / 56 / 83; 64 integers / 1 / 112 / 211; quadratic lift 79 naturals / 70 / 2 |
| [`03-system64/`](03-system64/) | `zfc-diophantine.zip` | *Explicit Diophantine formulations of Con(ZFC)* | 16 / 7 / 28 / 64; SOS 16 / 1 / 56 / 84; products 74/75/76 at degrees 157/125/101; P15 15 / 1 / 295 / 82; 15 / 6 / 244 / 71; integer forms (45 / 1 / 590), (48 / 7 / 56), (48 / 1 / 112); quadratic lift 128 integers / 87 / 2 |
| [`04-poly73/`](04-poly73/) | `zfc_diophantine (1).zip` | *A 16-variable Diophantine encoding of ZFC consistency* | P = ΔU 16 / 1 / 156 / 73 = 41M+32A; U 16 / 1 / 144 / 74; 16 / 7 / 60 / 65; SOS 16 / 1 / 120 / 85; 44 integers / 1 / 312 / 171; quadratic 83 integers / 46 / 2 |
| [`05-fixed15-16/`](05-fixed15-16/) | `ZFC_Diophantine_15_16_2026-10-22.zip` | *Fixed-input Diophantine forms of ZFC consistency* | 16 / 7 / 34 / 66; SOS 16 / 1 / 68 / 86; products 74/75/76 at 157/125/113; Φ15 15 / 1 / 295 / 82; Ψ15 15 / 1 / 346 / 80; 45 integers / 1 / 590 / 187; 48 integers / 1 / 136 / 198 |
| [`06-blank67/`](06-blank67/) | `zfc_diophantine_67.zip` | *Explicit Diophantine equations for Con(ZFC)* | 15 / 6 / ≤60 / 61 = 34M+27A; 15 / 6 / ≤46 / 62; **P67 15 / 1 / 155 / 67 = 39M+28A**; P68 15 / 1 / 123 / 68; SOS 78/79 at 120/92; 41 integers / 1 / 310 or 246 / 158 or 159 |
| [`07-fixed70/`](07-fixed70/) | `zfc_diophantine_fixed70.zip` | *Fixed-input Diophantine equations for the consistency of ZFC* | P70 16 / 1 / 169 / 70 = 40M+30A; P71 16 / 1 / 156 / 71; P73 16 / 1 / 157 / 73; 17 / 8 / ≤28 / 61; its SOS 17 / 1 / 56 / 84; 64 integers / 1 / 338 / 198 |
| [`08-start-only67/`](08-start-only67/) | `diophantine_zfc_cdd582b.zip` | *Explicit Diophantine equations for the consistency of ZFC* | 15 / 6 / ≤60 / 61 = 34M+27A; **P 15 / 1 / 155 / 67 = 39M+28A**; SOS 15 / 1 / 120 / 78; retained-index 18 / 9 / ≤34 / 61; quadratic 34 unknowns / 25 / 2 (one quartic); 60 integers / 1 / 310 |

Directory numbers follow the archives' arrival (file-time) order; they are
this report's source numbers and are not batch positions. Each directory's
delivered `README.md` (`README.txt` for 01) is its own entry point, and the
article is the PDF beside the TeX: `01-explicit82/report.pdf`,
`02-system63/report.pdf`, `03-system64/report.pdf`,
`04-poly73/zfc_diophantine.pdf`, `05-fixed15-16/paper/fixed_input_zfc.pdf`,
`06-blank67/report.pdf`, `07-fixed70/report/zfc_diophantine.pdf`, and
`08-start-only67/diophantine_zfc.pdf` (with a second document,
`08-start-only67/direct_stack_core.pdf`).

What each one adds beyond the common route (as the packages describe it):

- **01** folds two rows of complete84 into numerals (47M+37A → 46M+36A) at
  input x = 1, keeps all 18 witnesses, and gives a nine-equation
  specialization of complete74. Its `tag/` directory is a second, different
  route through the repository's Lean tag-system chain (`Sys91`): a 240-state
  TM0 adapter and a 131,144-slot counter program, whose new adapters are
  "not kernel-checked here" (`report.tex:26`).
- **02** replaces the variable-input Pell bridge by a fixed marker
  W0 = 2^(2d+b), merges two witnesses (γ = ρ + σ) and drops the 2d
  subtraction by restoring the raw slack; its 72/74 single polynomials use a
  squared budget residual and are equivalent to the system only in
  *existence* of solutions, not tuple by tuple (`README.md:31-35`).
- **03** reaches the same 16-unknown, seven-equation system as 02 by a
  different proof order (restoring δ, ρ, σ before power recovery), one
  operation dearer throughout; it then eliminates the strong root f by the
  complete92 norm trick to get **P15**, 15 unknowns.
- **04** forces the marker by an affine unit guard N0 = 3W + 1 − 3W0 instead
  of a squared factor, and uses a two-sided normalizer (220 states, three
  symbols) instead of a folded one-sided tape.
- **05** fixes x = 1 and W0, deletes the input Pell norm with a constructive
  positive inverse on every reduced solution, then eliminates f by a
  quadratic norm to reach Φ15 (82 ops) and Ψ15 (80 ops, degree 346); it
  emits every circuit, including two all-integer forms, in `arithmetic/`.
- **06** removes the input entirely ("fixed blank computation"): Start is
  K215's actual first transition, selector 1 is a locally valid but globally
  impossible window, and no normalized machine is built (a 439-symbol
  alphabet on raw K215). Its layout satisfies 2D_C − D_R ≡ 3 (mod 5), so no
correction bit is needed (`report.tex:545-549`).
- **07** keeps the factor U0 = q − βJ signed and proves its sign only after
  X = 2^R is recovered, and changes the first scale to X = wq²; P70 is its
  smallest evaluator.
- **08** is "inputless" as well: an input-erasing normalized machine with a
  forced Start, so no End marker is needed and selector 1 becomes the window
  (7,…,7). It also gives the lowest-degree complete lift of the eight
  (25 quadratics in 34 unknowns, one quartic) and a **retained-index
  fallback** (18 unknowns, 9 equations, 61 ops) that uses the historical
  Start/End ordering and must not be mixed with its new K
  (`README.md:16-20`).

## Overlap, base and credits (intake findings)

- **Smallest single polynomial: P67, 15 unknowns, 67 = 39M+28A, exact
  degree 155, found twice.** 06 and 08 display the same polynomial and the
  same 61-operation six-equation system symbol for symbol, up to renaming
  (T→o, N_K→N_I, S→L), with the same factor degrees 22, 18, 60, 7, 2, 46 and
  the same leading form (06 `report.tex:157-187, 1081`; 08
  `diophantine_zfc.tex:79-111, 464`). Their fixed coefficients are built
  independently and are **different integers**. 06 works on raw K215 with a
  439-symbol alphabet, an impossible boundary window and d = 5^67, and gives
  every parameter numerically. 08 uses a 435-state normalizer with 4366
  tiles, keeps a correction bit and states its parameters only by formula.
  **Base: 06**, because its coefficient recipe is fully numeric and needs no
  correction bit; 08 is credited with the same arithmetic skeleton, found
  independently.
- **Fewest unknowns: 15**, in 03 (P15, 82 ops), 05 (Φ15 at 82 ops; Ψ15 at
  80), 06 and 08 (P67 at 67 ops). The 67-operation polynomial dominates the
  others on operations and degree.
- **Lowest-degree small system: 16 unknowns, seven equations, maximum degree
  28**, in 02 (63 ops) and 03 (64 ops), with its sum of squares at degree 56
  (83 and 84 ops). 07's eight-equation system also reaches degree ≤28 and
  61 ops, but with 17 unknowns. **Base: 02.**
- **Quartic forms.** Every package that gives one lifts its circuit to
  quadratics and takes a sum of squares: 08 (34 unknowns) < 02 (79
  naturals) < 04 (83 integers) < 03 (128 integers) < 01 (180 naturals).
- **Sixteen-unknown single polynomials**: 07's P70 (70 ops, degree 169),
  02's P72 (72, 157), 04's P73 (73, 156), and the 74/75/76 products of 02,
  03 and 05. 04's degree-156 product is 02/03's degree-157 normalized
  product with the degree-2 marker factor replaced by the degree-1 affine
  guard.
- **The coefficients are not interchangeable.** Every package normalizes
  K215 differently, so its four to six coefficient "ports" are its own
  integers:

  | Dir | Machine as compiled | Tiles | b, d |
  |---|---|---:|---|
  | 01 | 437 states, 8 symbols | 3510 | by formula only |
  | 02 | 436 states, 8 symbols | 3502 | 5^43, 5^87 |
  | 03 | 436 states, 6 symbols | 2628 | 5^42, 5^85 |
  | 04 | 220 states, 3 symbols (two-sided) | 669 | 5^35, 5^71 |
  | 05 | 436 states, 10 symbols | 4376 | 5^45, 5^90 |
  | 06 | raw K215, 439 symbols | — | 5^33, 5^67 |
  | 07 | 435 states, 10 symbols | 4366 | 5^44, 5^89 |
  | 08 | 435 states, 10 symbols | 4366 | by formula only |

  All eight agree that the source port `MF` is the **shifted** mask
  M_F + B − 1, not the native mask. A circuit from one package evaluated with
  another's coefficients means nothing.
- **Tensions noted, not adjudicated at intake.** 01 and 03 warn against the
  older complete76 masks, while 04 says it uses "the exact complete76
  compiler layout" (`provenance/COEFFICIENT_RECIPE.md:3-5`) with the
  strengthened complete75 bound, so this looks like a clash of wording, not
  of substance. 04 says a folded one-sided simulation is unnecessary, while
  01, 02, 03 fold. 07 makes Start unique through a marker bijection, while
  06 and 08 prove uniqueness unnecessary. 06 and 08 state different upper
  bounds for the same R (06 `report.tex:600`, 08 `diophantine_zfc.tex:199`).
  05 describes the removed input bridge as one Pell norm with three
  witnesses, 07 as a four-equation block with five coordinates. These may be
  different layers of the same source.

## What is not claimed

Every package says, in its own words:

- **No new formal result.** The Diophantine bridge is a mathematical proof
  supported by finite audits. It is not a Lean or Rocq theorem and not a
  derivation encoded in ZFC's own proof syntax. The proof-assistant builds
  of the machine endpoint were not rerun.
- **No consistency proof.** The theorem is an equivalence. It neither
  assumes nor decides Con(ZFC), and if ZFC is consistent, ZFC does not prove
  that P has no solutions. Several packages add that passing from mere
  consistency to the stronger "neither side is provable" needs an extra
  soundness hypothesis such as Σ₁-soundness.
- **No materialized coefficients.** Each coefficient is a specific integer
  defined by a terminating finite recipe, with no free program index or
  oracle. None is expanded: B alone has about 5^67 to 5^90 binary digits,
  and the window enumerations (from about 1.4·10^21 windows in 06 to about
1.2·10^29 in 05) were not run. The
  finite checks use small or synthetic coefficients and are algebra and
  machine diagnostics, not accepting computations or Pell witnesses.
- **No optimality.** No global minimum over Diophantine constructions is
  claimed for unknowns, degree, operations or coefficient height, which are
  different criteria. The repository's own Lean theorem
  `Jones1982.nine_unknowns`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean`,
  checked at intake) already gives nine unknowns at astronomically larger
  degree.
- **No new universal bound.** Fixing the input is not a varying-input
  universal construction. The repository's universal operation frontier
  (**84 operations, 18 witnesses, degree 187**, recorded in
  `Computability/HilbertTenthProblem/README.md` and the native-stream-queue
  README) is unchanged; 01, 03, 04 and 07 say so explicitly.

## Relation to the formal developments

- **Machine endpoint (Busy Beaver ZFC).** All eight rest on the repository's
  checked K215 endpoint,
  `KEndpoint215.blank_halts_iff_zfc_refutation` and
  `KEndpoint215.nonhalting_iff_zfc_consistency`
  (`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean:44,49`,
  both present at `HEAD`, checked at intake), together with
  `ConstructibleChoice.zf_refutation_iff_zfc_refutation` and
  `KEndpoint.c222_iff_zf_refutation`. That endpoint is a Lean/Rocq theorem
  about the proof predicate `BProv`. The step from it to "ZFC proves the
  Diophantine equivalence" is the packages' ordinary argument and is not
  formalized here.
- **Hilbert's tenth problem.** The compiler, its Pell lemmas and its masks
  are the research-wip notes under
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`,
  which are themselves not Lean-formalized; the formal project proves MRDP
  and Jones's nine-unknown theorem, but not this compiler.
- **None of the eight packages' own theorems is formalized.** Neither
  project gains formal status from this report.

## Delivery discrepancies

These are disclosed here and were not fixed in the delivered files:

- **Omitted copies.** Delivered READMEs, manifests and verifiers name their
  vendored copies of repository files at delivery paths
  (`vendor/`, `upstream/`, `evidence/**/sources/`, `k215.tm` and others).
  Those copies are not in this tree (see `PLACEMENT.md`). To rerun a
  package, extract its archive from `2fd49a1a9d` into a scratch directory
  and run it there. Several drivers also verify the checksum ledgers, which
  are not staged.
- **Near-copies kept.** Some inherited files differ from the repository only
  by a final newline and were therefore staged, for example
  `02-system63/NineMain.lean` (one extra trailing newline against the
  repository's `NineMain.lean`, checked at intake) and the inherited
  `complete75_*.md` notes in `02-system63/`, as its `ATTRIBUTION.md`
  (lines 61-65) says.
- **Files named but never delivered.** 03's
  `proofs/INDEPENDENT_REVIEW.md:30` and `proofs/FORMAL_STATUS.md:65` cite
  `fixed_marker_review.json` and `fixed_marker_review.md`, which its archive
  does not contain; the nearest delivered file is
  `checks/independent_review.json`. 06's `code/README.md:45-48` describes
  two 45-integer-variable forms that it regenerates but does not ship.
- **Reviews of drafts.** 04's `provenance/FIXED_INPUT_AUDIT.md` reviewed
  working drafts (`design_work/…`), and its final TeX contains later
  clarifications (`provenance/README.md:44-45`). The one-sided normalizer
  that its `COEFFICIENT_RECIPE.md:13-14` calls "an alternative" is not in
  the package.
- **08's secondary documents.**
  `08-start-only67/direct_stack_core.pdf` is a one-stack local polynomial
  for the repository's twelve-rule C222 calculus. It is explicitly not a
  fixed-arity encoding and not compiled in Lean or Rocq.
  `evidence/diophantine_zfc_encoding/constructive_compiler_fallback.md` is
  "not a completed build". It targets Glazer's **K230** machine
  (`machine/k230.tm`, omitted here as identical to
  `Computability/BusyBeaver/Research/ZFC/candidate-k228/ingredients/k230.tm`),
  not K215, and claims no count.
- **Minor internal inconsistencies, as found by the intake dossiers.**
  - 05's §1 table omits rows that its appendix and README give.
  - 07's `artifacts/fixed_input_notes.md:461-465` says "degree at most 338"
    where its TeX says exact.
  - 08's README omits its two SOS rows.
  - 05 and 06 call Jones's nine unknowns "nonnegative" and "positive"
    respectively.

## Further questions and research

These are the open problems the packages list, merged and credited:

1. **Formalize the bridge.** Prove the fixed-marker or Start-only lemmas and
   connect them to a verified machine-to-polynomial compiler in Lean, ending
   at `KEndpoint215`. Proposed by 01 (through the existing `TMCounter`,
   `tag_iff91` and `Sys91` chain), 03, 04, 05, 06, 07 and 08.
2. **Compile the C222 calculus directly**, skipping the Turing-machine
   normalization. Proposed by 02 (`normalization.md:230-252`), 05, 07 and 08,
   whose `direct_stack_core` is a first step.
3. **Coefficient height.** Find smaller machine, tableau or register-machine
   encodings, or charge coefficient size in the metric. Proposed by 03, 04
   and 07.
4. **Fewer unknowns.** Remove the F or α slack, or the positivity witnesses
   and Pell scales (05, 06, 07). Find an effective nine-variable
   specialization (06) or instantiate low-variable universal forms (08).
5. **Pareto front.** Optimize degree, operations and unknowns jointly
   (05, 07, 08); give a symbolic window sum (08); shorten the signed-root
   proof (05).
6. **Arithmetic internalization.** State the equivalence in PA rather than
   ZFC, which needs a separate arithmetization (03, 07).
7. **Generic fixed-marker theorem** for the native parent compiler (04).

## Licence and provenance

Every package was prepared for ProveIt and reuses MIT-0 repository material.
The licence and notice files each package ships are kept in place, including
`06-blank67/licenses/LICENSE.Wade` (Andrew James Wade's MIT-0 notice, as
shipped). The
pin of all eight is `cdd582bec13f908df3711fa9e05d1ddac368a5db`; the arrival
commit is `2fd49a1a9d`, and the placement commit is `084e120830`.

## Files

Every staged file, grouped by source directory (generated from the tree):

- `01-explicit82/`: `LICENSE.ProveIt`, `NOTICE.txt`, `README.txt`, `SOURCE_PINS.json`, `VALIDATION.json`, `report.pdf`, `report.tex`, `verify_files.py`
- `01-explicit82/native/`: `README.md`, `audit_native_specialization.py`, `audit_nine_equations.py`, `audit_polynomial.py`, `complete74_factored_first_norm.json`, `complete75_half_binomial_compiler.json`, `complete84_scaled_strong_output.json`, `k215_native72_system.json`, `k215_native82_source.json`, `k215_native_definition.py`, `k215_native_definition_checks.json`, `make_quadratic_lift.py`, `native_specialization_audit.json`, `nine_equation_audit.json`, `nine_equation_system.txt`, `normalized_437_machine.json`, `polynomial_audit.json`, `quadratic_system.json`
- `01-explicit82/tag/`: `audit_k215_tm0_adapter.py`, `compile_k215_counter.py`, `k215_counter_compiler_audit.json`, `k215_counter_program.json`, `k215_tm0_240.json`, `k215_tm0_adapter_audit.json`, `tag91_closed_formula_toy_audit.json`, `tag91_closed_formula_toy_audit.py`, `tag91_dimensions.json`, `tag_alternative.txt`
- `02-system63/`: `ATTRIBUTION.md`, `FIXED_INPUT73_PROOF.md`, `FIXED_INPUT75_ORDINARY_PROOF.md`, `NineMain.lean`, `PELL_INTERFACE_LEMMAS.md`, `PROVENANCE.json`, `QUADRATIC_LIFT.md`, `README.md`, `REVIEW_COMPILER.md`, `REVIEW_FIXED_INPUT73.md`, `REVIEW_ORDINARY_STRONG75.md`, `REVIEW_QUADRATIC_LIFT.md`, `REVIEW_SQUARED_MARKER.md`, `SQUARED_MARKER_PROOF.md`, `check_quadratic_lift_review.py`, `check_square_marker_review.py`, `check_window_count.py`, `complete75_coupled_index_linear88.md`, `complete75_half_binomial_compiler.py`, `complete75_normalized_strong87.md`, `complete75_reversed_auxiliary89.md`, `constants.md`, `emit_sos_variants.py`, `explore_fixed_raw_universal_76.py`, `fixed_compiler.py`, `fixed_compiler_checks.json`, `fixed_constants.json`, `fixed_input63_ordinary_system.json`, `fixed_input63_system.json`, `fixed_input72_square_marker.json`, `fixed_input73.json`, `fixed_input73_validation.json`, `fixed_input74_ordinary_square_marker.json`, `fixed_input75_ordinary.json`, `fixed_input75_ordinary_validation.json`, `integer64_sos.json`, `normalization.md`, `normalization_checks.json`, `normalized_k215.py`, `ordinary_strong_review_checks.json`, `positive16_sos.json`, `quadratic_lift.json`, `quadratic_lift.py`, `quadratic_lift_checks.json`, `quadratic_lift_review_checks.json`, `report.pdf`, `report.tex`, `report_qa.json`, `reproduce.py`, `reproduction_checks.json`, `sos_variants_checks.json`, `square_marker_review_checks.json`, `square_marker_validation.json`, `test_fixed_compiler.py`, `verify_fixed_input.py`, `verify_fixed_input_ordinary.py`, `verify_square_marker.py`, `window_count_checks.json`
- `02-system63/upstream_licenses/`: `LICENSE.ProveIt`
- `02-system63/upstream_licenses/candidate-k215/`: `NOTICE.md`
- `02-system63/upstream_licenses/candidate-k215/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`
- `02-system63/upstream_licenses/candidate-k215/provenance/partial-selector/`: `NOTICE.md`
- `03-system64/`: `README.md`, `report.pdf`, `report.tex`
- `03-system64/artifacts/`: `circuit_64.tex`, `circuit_82.tex`, `coefficient_recipe.json`, `compiler_checks.json`, `domain_variants.json`, `fixed_marker_systems.json`, `fixed_marker_variants.json`, `folded_machine.json`
- `03-system64/checks/`: `MANIFEST.json`, `independent_review.json`, `pdf_qa.json`, `reproduction.json`
- `03-system64/proofs/`: `COMPILER.md`, `DEGREE_295.md`, `DOMAIN.md`, `FIXED_MARKER.md`, `FORMAL_STATUS.md`, `INDEPENDENT_REVIEW.md`, `PROVENANCE.md`
- `03-system64/source/`: `compiler_k215.py`, `domain_variants.py`, `fixed_marker.py`, `render_circuits.py`, `review_fixed_marker.py`, `verify.py`
- `03-system64/vendor/`: `manifest.json`
- `04-poly73/`: `LICENSE`, `README.md`, `build.sh`, `zfc_diophantine.pdf`, `zfc_diophantine.tex`
- `04-poly73/data/`: `constants_recipe.json`, `fixed_input_linear_guard_sources.json`, `integer44.json`, `normalized_k215.json`, `polynomial73.json`, `polynomial74.json`, `quadratic83.json`, `quadratic83.txt`, `sos85.json`, `system65.json`
- `04-poly73/provenance/`: `COEFFICIENT_RECIPE.md`, `DIRECT_NORMALIZER_PROOF.md`, `FIXED_INPUT_AUDIT.md`, `README.md`, `upstream_sources.json`
- `04-poly73/src/`: `audit_compiler_transcription.py`, `diophantine.py`, `k215_constants.py`, `normalize_k215_direct.py`, `quadratic_elimination.py`, `verify_all.py`
- `04-poly73/verification/`: `arithmetic.json`, `compiler_transcription.json`, `document.json`, `full.json`, `normalizer.json`
- `05-fixed15-16/`: `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `inherited_files.json`, `provenance.json`, `quality_checks.json`, `verification.json`, `verify.py`
- `05-fixed15-16/arithmetic/`: `INTEGER_DOMAIN.md`, `algebra_verification.json`, `build_fixed_sources.py`, `build_integer_sources.py`, `fixed15_outer80_degree346.json`, `fixed15_product82_degree295.json`, `fixed16_product74_degree157.json`, `fixed16_product75_degree125.json`, `fixed16_product76_degree113.json`, `fixed16_sos86_degree68.json`, `fixed16_system66_degree34.json`, `integer45_product187_degree590.json`, `integer48_sos198_degree136.json`, `integer_verification.json`, `source_verification.json`, `verify_closed_forms.py`
- `05-fixed15-16/coefficients/`: `bridge_verification.json`, `coefficient_note.tex`, `coefficient_recipe.py`, `coefficient_specification.json`, `fixed_machine.py`, `machine_receipt.json`, `normalized_machine.json`, `verify_bridge.py`
- `05-fixed15-16/notices/k215/`: `NOTICE.md`
- `05-fixed15-16/notices/k215/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`
- `05-fixed15-16/notices/k215/provenance/partial-selector/`: `NOTICE.md`
- `05-fixed15-16/paper/`: `fixed_input_zfc.pdf`, `fixed_input_zfc.tex`
- `05-fixed15-16/proofs/`: `check_local_identities.py`, `fixed_input_proof_notes.md`, `fixed_machine_coefficient_review.md`, `h10_audit_notes.md`, `k215_bridge_notes.md`
- `06-blank67/`: `Makefile`, `README.md`, `circuit.tex`, `cross_counts.tex`, `report.pdf`, `report.tex`, `verification_receipt.json`
- `06-blank67/code/`: `README.md`, `blank_helical.py`, `build_fixed.py`, `build_tables.py`, `compiler_constants.py`, `count_blank_alphabet.py`, `verify_all.py`, `verify_k215.py`
- `06-blank67/data/`: `blank_alphabet_cardinality.json`, `blank_helical_checks.json`, `document_verification.json`, `fixed_blank_67.json`, `fixed_blank_67_over_Z41.json`, `fixed_blank_68.json`, `fixed_blank_68_over_Z41.json`, `fixed_blank_system_61.json`, `fixed_blank_system_62.json`, `k215_constants.json`, `k215_transitions.json`, `proof_dependencies.json`, `upstream_manifest.json`
- `06-blank67/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`
- `06-blank67/proofs/`: `blank_helical_proof.md`, `fixed_blank_67_proof.md`, `k215_audit_notes.md`, `pell_lemma_audit.md`
- `07-fixed70/`: `LICENSE`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `VALIDATION.md`, `build_report.py`, `verify.py`
- `07-fixed70/artifacts/`: `CIRCUIT_FORMAT.md`, `domain_variants.json`, `domain_variants.py`, `fixed_input.json`, `fixed_input.py`, `fixed_input_notes.md`
- `07-fixed70/artifacts/compiler/`: `COEFFICIENTS.md`, `LICENSE`, `NORMALIZATION.md`, `compiler_manifest.json`, `compiler_metadata.json`, `finite_window_constants.py`, `k215_one_sided.py`, `normalization_checks.json`, `normalized_machine.json`
- `07-fixed70/artifacts/compiler/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`
- `07-fixed70/artifacts/compiler/provenance/partial-selector/`: `NOTICE.md`
- `07-fixed70/artifacts/review/`: `FIXED70_REVIEW.md`, `FIXED_INPUT_SEMANTICS_REVIEW.md`, `independent_review.json`, `review_fixed70.py`
- `07-fixed70/artifacts/verification/`: `check_1.txt`, `check_2.txt`, `check_3.txt`, `check_4.txt`, `check_5.txt`, `receipt.json`
- `07-fixed70/report/`: `circuit70.tex`, `coefficient_recipe.tex`, `zfc_diophantine.pdf`, `zfc_diophantine.tex`
- `08-start-only67/`: `DOCUMENT_QA.json`, `MANIFEST.json`, `Makefile`, `OWNED_RUNNABLES.txt`, `README.md`, `REPRODUCIBILITY.json`, `diophantine_zfc.pdf`, `diophantine_zfc.tex`, `direct_stack_core.pdf`, `direct_stack_core.tex`
- `08-start-only67/checks/`: `reproduce.py`
- `08-start-only67/evidence/diophantine_zfc_audit/`: `START_ONLY_AUDIT.md`
- `08-start-only67/evidence/diophantine_zfc_compiler/`: `CONSTANTS.md`, `INDEPENDENT_AUDIT.md`, `PACKAGING_CHANGES.md`, `START_ONLY_CONSTANTS.md`, `compiler_audit.json`, `constant_expression_dag.json`, `explicit_constants.py`, `independent_audit.py`, `independent_audit_original_hashes.txt`, `independent_audit_receipt.json`, `start_only_audit.json`, `start_only_constants.py`, `start_only_expression_dag.json`
- `08-start-only67/evidence/diophantine_zfc_core/`: `METATHEORY.md`, `audit_table_binding.py`, `table_binding.json`
- `08-start-only67/evidence/diophantine_zfc_core/sources/`: `manifest.json`
- `08-start-only67/evidence/diophantine_zfc_encoding/`: `constructive_compiler_fallback.md`, `noinput_quadratic_reduced.json`, `source_manifest.json`, `start_only_quartic34.json`, `start_only_quartic34_proof.md`
- `08-start-only67/evidence/diophantine_zfc_review/`: `START_ONLY_DEGREE_CERTIFICATE.md`, `fixed_input_system61.json`, `quadratic_reduction_independent_audit.json`, `quartic34_independent_audit.json`, `review_source_manifest.json`, `start_only_arithmetic_audit.json`, `start_only_polynomial67.json`, `start_only_system61.json`, `verify_quadratic_reduction.py`, `verify_quartic34.py`, `verify_start_only_packets.py`
- `08-start-only67/evidence/diophantine_zfc_root/`: `ROOT_INPUTLESS_AUDIT.json`, `audit_inputless.py`
- top level: `README.md` (this file), `PLACEMENT.md`
