# Con(ZFC) in Diophantine form

**Explicit polynomials with fixed integer coefficients whose unsolvability
ZFC proves equivalent to Con(ZFC): seven wave-4 syntheses on the blank run of
K215, with 17 unrestricted integers, nine positive unknowns, twelve positive
unknowns at degree 1069, and coefficients with B = 2^(5^9)**

This report holds seven AI-assisted research packages dated 22–23 October
2026. They are batch 220 of ProveIt's incoming reports (arrival `375cc6e3d7`,
"Con(ZFC) in Diophantine form (wave-4)"), placed in `604b1416b5`. Six are
pinned to `ae3007ca44` and 26 to `a477d0fc8b`; both snapshots contain this
report's audited wave-3 form. The packages cite wave-3 packages by their
source numbers 16–23. No wave-4 package mentions another.

## Earlier waves are superseded

Vladimir directed for wave 4 the same treatment he chose for wave 3, so
wave 4 supersedes wave 3 and directories `16-integer27/` … `23-separating12/`
were removed from the tree when wave 4 was placed.

| Wave | Batch | Arrival (archives) | Directories in every commit from … to … | Audited README |
|---|---|---|---|---|
| 1 | 217 | `2fd49a1a9d` | `084e120830` … `8a4b00b5bf^` | `f3af223ef7` |
| 2 | 218 | `7be2780f26` | `8a4b00b5bf` … `da064316ea^` | `5b0c9ae9fd` |
| 3 | 219 | `cbf94cb552` | `da064316ea` … `604b1416b5^` | `a477d0fc8b` |
| 4 | 220 | `375cc6e3d7` | `604b1416b5` … | this file |

Source numbers 01–23 are kept only because the packages' texts use them; the
wave-4 directories continue the sequence as 24–30.

All seven wave-4 packages bundle a copy of the audited wave-3 README, so every
copy describes a superseded wave. The copies are identical up to line ends;
three have one extra final newline (checked at intake):

| Dir | Bundled copy |
|---|---|
| 24 | `upstream/collection_at_pin.md` |
| 25 | `upstream/COMPARISON_AT_PIN.md` |
| 26 | `references/README.md` |
| 27 | `COMPARISON_AT_PIN.md` |
| 28 | `vendor/COMPARISON_AT_PIN.md` |
| 29 | `references/COMPARISON_AT_PIN.md` |
| 30 | `review/README.upstream.md` |

**Wave-3 results that wave 4 does not reproduce** now survive only in
history. Read the wave-3 README and directories at `a477d0fc8b`, e.g.
`git show a477d0fc8b:<this directory>/README.md`. This list is an intake
comparison; where a wave-4 package itself says a result stays better, that is
noted.

- **27 unrestricted integers.** 23's 27ℤ product of degree 172 in 116 ops
  (system 46 / 107) and its other 27ℤ products. The wave-4 packages say these
  remain better tradeoffs. The 27ℤ forms of degree 1004 and 1116 (16, 18,
  19, 20) are also lost.
- **13 positive unknowns at degree 515, 84 ops** (16, 20).
- **19's 15-unknown grouped sums of squares** (degree 44 at 76 ops and the
  other nondominated choices). 27 says these remain better.
- **19's 28ℤ forms** (258 / 128 and 426 / 127).

Wave-2 results listed as lost in the wave-3 README remain lost: the
32-unknown positive quartic is now improved to 31 unknowns (30), but the
positive sextic and octic, the degree-22 systems and the 14-unknown forms are
not reproduced. The 67-operation equation P₆₇ (wave-1 06/08) remains the
fewest-operations form; 24 and 25 ship it rebound to their coefficients.

## How this report was made

The packages overlap, as before, so they are **placed, not written**
([docs/incoming/README.md](../../../../../../docs/incoming/README.md),
section 2):

- each keeps its delivered layout and PDF in its numbered directory, with the
  wrapper removed;
- this README is the reconciliation note;
- no delivered file was edited, no PDF was built, and no delivered program
  was run at intake.

Facts are the packages' own, from two read-only intake dossiers, whose
scripts also evaluated delivered circuits modulo a large prime to tell
polynomials apart. Agreement at random points is strong evidence of identity,
not proof; disagreement proves difference.
[`PLACEMENT.md`](PLACEMENT.md) is the recovery map for wave 4. Of the 871
archive members:

- 831 were staged;
- 25 were omitted as byte-identical (up to line ends) copies of repository
  files outside this report;
- 15 checksum ledgers and logs were excluded by the root `.gitignore`.

## The common theorem

Each package defines polynomials or small systems with four **fixed integer
coefficient ports**: Bm1 = B − 1, Kconstant = D_C + B·D_R, MC, and the
**shifted** MF = (native high mask) + B − 1. The ports are determined by a
finite recipe from the literal 215-state machine
[`candidate-k215/k215.tm`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm),
and each package proves, by ordinary mathematics formalizable in ZFC, that

> ZFC ⊢ (no solution in the stated domain) ↔ Con(ZFC).

The route is unchanged: the blank run of K215 halts iff ZFC has a finite
refutation, and a local tile language of that run is compiled by the
repository's native-window/Pell compiler
([`native-stream-queue/`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/README.md))
with its input interface removed. The nine-variable forms add Jones's
nine-variable reduction applied to a fixed quartic.

## The seven packages

Numbers are the packages' own; **none was re-derived at intake.** "u / e / d
/ o" means unknowns / equations / degree / operations. Operations count every
binary +, −, × including multiplication by fixed numerals; reuse and system
comparisons are free. Unknowns are strictly positive unless marked ℤ
(unrestricted integers) or ℕ (naturals).

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`24-integer24/`](24-integer24/) | `con_zfc_synthesis_2026-10-22.zip` | *Smaller explicit Diophantine forms of ZFC consistency* | 24ℤ / 1 / 1936 / 167 (system 1920 / 162); **12 / 1 / 1069 / 123** (system 1060 / 118), 1073 / 121, 1081 / 120; refactors of 21's polynomial to 113 ops (system 108) and of 22's 13-unknown forms to 319 / 89 (system 288 / 81); P₆₇ and retained59 rebound; coefficients with d = 6,364,399, materialized (gzip) |
| [`25-hybrid12/`](25-hybrid12/) | `con-zfc-hybrid12-2026-10-22.zip` | *Smaller Diophantine forms of ZFC consistency* | 12 / 1 / 1081 / 116 (system 111, SOS 119), variants 117 and 118; P₆₇ and retained59 rebound; **B = 2^(5^9)**, materialized (gzip; 977,220 raw bytes) |
| [`26-ratio12/`](26-ratio12/) | `con_zfc_synthesis_2026-10-22 (1).zip` | *Smaller explicit Diophantine forms of ZFC consistency* | 12 / 1 / 1081 / 116 (system 111, shifted system 110); 24ℤ / 1 / 2432 / 163 (system 159, shifted 157, SOS 4832 / 166); parity layout at B = 2^(5^10), largest port 9,766,251 bits |
| [`27-wave4/`](27-wave4/) | `ZFC_Diophantine_Wave4_Synthesis_2026-10-23.zip` | *Smaller Diophantine presentations of ZFC consistency* | 12 / 1 / 1081 / 120; 24ℤ / 1 / 2432 / 163 and 24ℤ / 1 / 1936 / 168; **nine positive unknowns**: 1537 ops (degree 120764·5^33 + 368) or 1480 ops (package 18's polynomial); 59-op systems of degree 12, 10, 8, 6 (17–20 unknowns); 51ℤ quartic, 42ℤ sextic, 36ℤ octic; B = 2^(5^9), materialized (raw and gzip) |
| [`28-compact-norms/`](28-compact-norms/) | `ProveIt_ConZFC_Compact_Norms_2026-10-23.zip` | *Smaller separating norms and a signed finalizer for Diophantine ZFC consistency* | 12 / 1 / 1081 / 116 (system 112, SOS 119); 9ℕ / 1 / 93264·5^33 + 288 / 20,547; 19's Wang943 bytes |
| [`29-simpler-forms/`](29-simpler-forms/) | `ConZFC_Simpler_Forms_2026-10-22.zip` | *Smaller explicit Diophantine forms of ZFC consistency* | 12 / 1 / 1097 / 116 (shifted system 110, SOS 118); **17ℤ signed Jones / 1 / 424296·5^33 + 53824 / 20,607** (on the T4 tuple); 51ℤ quartic, 42ℤ sextic, 36ℤ octic |
| [`30-quartic31/`](30-quartic31/) | `con-zfc-nine-quartic31-ae3007c.zip` | *Smaller explicit Diophantine forms for Con(ZFC)* | **12 / 1 / 1081 / 111 (system 107)**; 24ℤ / 1 / 2240 / 165; 25ℤ / 1 / 920 / 131; **26ℤ / 1 / 214 / 123** (system 128 / 117); **31-unknown quartic** (22 quadratics; SOS 130 ops); **9ℕ / 1 / 120724·5^32 + 366 / 1840**; package 18's polynomial in 1704 ops; materialized index z = 2^45933757 (`nine/z_index.bin`) |

Directory numbers follow the archives' arrival (file-time) order. Each
directory's `README.md` is its entry point. The articles are:

- 24: `con_zfc_synthesis.pdf`;
- 25, 26, 27, 28 and 29: `report.pdf`;
- 30: `report/synthesis_report.pdf`, with Markdown sources.

## Frontier, credits and bases (intake findings)

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Fewest unrestricted integers | **17ℤ**: a signed Jones construction, one equation of degree 424296·5^33 + 53824 in 20,607 ops, on the T4 tuple | 29 only | 29 |
| Fewest unrestricted integers, moderate degree | **24ℤ**: these are different polynomials except where noted. 26's and 27's 2432 / 163 are the same polynomial, found independently (26's shifted system: 157). 24's 1936 / 167 and 27's 1936 / 168 differ, and 30 has 2240 / 165. Also 25ℤ at 920 / 131 and 26ℤ at 214 / 123 (30) | 24, 26, 27, 30 | 24; 26 for operations |
| Nine unknowns | **9 positive, delivered as a circuit**: 27 (1537 ops with its new majorant, degree 120764·5^33 + 368; 1480 ops for 18's polynomial). Over ℕ: 30 has the lowest degree, 120724·5^32 + 366, at 1840 ops; 28 has 93264·5^33 + 288 at 20,547 ops. These are three different new polynomials; 27 and 30 also re-evaluate 18's polynomial in 1485 and 1704 ops | 27; 30; 28 | 27 for positive; 30 for degree |
| Twelve positive, lowest degree | **1069** at 123 ops (system 1060 / 118) | 24 only | 24 |
| Twelve positive, fewest operations | **111** product, **107** system (degree 1081) | 30 only | 30 |
| Twelve positive at degree 1081 | six different polynomials: 24 (120 ops), 25 (116), 26 (116), 27 (120), 28 (116) and 30 (111); 29 has degree 1097 at 116 | 24–28, 30; 29 | 24 |
| Thirteen positive | 22's forms refactored to 319 / 89 (system 288 / 81) | 24 | 24 |
| Low-degree lifts | **31-unknown positive quartic** (22 quadratics; 65-op system, 130-op SOS); integer lifts 51ℤ quartic, 42ℤ sextic, 36ℤ octic (not compared between 27 and 29 at intake) | 30; 27, 29 | 30; 27 |
| 59-operation systems | the 16 / 7 / 24 system rebound (24, 25); 27 lowers the degree to 12, 10, 8, 6 with 17–20 unknowns | 24, 25; 27 | 27 |
| Fewest operations | **67** (P₆₇, wave 1), unchanged | — | (wave-1 06) |
| Smallest coefficients | **B = 2^(5^9)** (25, 27: two different tuples sharing β and MC bytes, differing in K and MF); 24's d = 6,364,399; 26 keeps 2^(5^10) but lowers the largest port to 9,766,251 bits | 25, 27; 24; 26 | 25 |

### Coefficient recipes: use one whole tuple

| Dir | Tiles | B | Materialized | Binding |
|---|---:|---|---|---|
| 24 | 943 | 2^6364399 (d = 529·12031) | gzip, 3,545,690 raw bytes | `coefficients/COEFFICIENT_BINDING.json` |
| 25 | 943 | 2^(5^9) | gzip, 977,220 raw bytes | `coefficients/COEFFICIENT_BINDING.json` |
| 26 | 943 | 2^(5^10) | gzip; the canonical binding names raw `.bin` files that are not shipped (replay creates them) | `coefficients/COEFFICIENT_BINDING.json` |
| 27 | 943 | 2^(5^9) | raw `expanded/*.bin` (977,220 bytes) and gzip | `INSTANCE.json` |
| 28 | 943 | 2^(5^10) (19's tuple) | gzip, byte-identical to 19's | `INSTANCE.json` |
| 29 | 943 / 37,075 | 2^(5^10) (19's tuple); the 17ℤ form uses T4, 2^(5^18) | gzip (19's bytes); T4 not expanded | `COEFFICIENT_BINDING.json` |
| 30 | 943 | 2^(5^10) (19's tuple) | raw and gzip (19's bytes); also the nine-variable index z | `COEFFICIENT_BINDING.json` |

- Every package binds its four ports as one tuple and forbids splicing.
- 25 and 27 share the β and MC bytes but differ in K and MF, so their ports
  must not be mixed.
- The packages disagree about rebinding package 18's quartic: 28 and 30
  rebind it to Wang943 by citing 19's interface theorem, while 29 says
  rebinding needs a fresh proof of the quartic/compiler interface.
- No package checks another wave-4 package's tuple.
- The intake dossiers decoded 24's, 25's, 26's and 27's tuples and found
  them consistent with their bindings. 28's gzip files are byte-identical to
  19's, and 30's `nine/z_index.bin` equals 2^45933757. These checks confirm
  bytes, not the compiler theorem the bytes instantiate.

### Tensions, not adjudicated at intake

- **Operation records under different conventions.** 25 and 26 present
  116 operations as tying the best twelve-unknown product. 24 brings the same
  1353-degree polynomial of wave-3 21 down to 113 operations (system 108) by
  sharing an odd factor that 25's and 26's evaluators do not use. 25 counts
  21's system as 111 under a direct-comparison convention; 26 cites it at 112.
- **Rebinding 18's quartic.** See the coefficient section above.
- **Sun's ten-integer theorem.** 25, 26 and 29 cite "Sun 2026" (arXiv
  2609.01594, as v2 in 25 and v1 in 26) as a general ten-integer
  representation result that they do not instantiate. This was not checked
  at intake.
- **Name collision.** 28's `compact12` (degree 1081) and 29's
  `compact_norm12` (degree 1113, a superseded intermediate) are different
  polynomials.
- **No package calls wave 3 wrong.** 26 and 25 call some wave-3 weights
  unnecessarily large (20's factors), and 27 says the wave-3 README's
  in-place driver failures are not defects of the sealed archives.

## What is not claimed

The packages say, in their own words (exceptions noted):

- **No new formal result.** New reductions are ordinary proofs with finite
  audits; no Lean or Rocq end-to-end certificate and no fresh endpoint build.
- **No consistency proof.** The theorems are equivalences. 24, 27, 28, 29
  and 30 say that the stronger two-sided claim needs an extra soundness
  hypothesis or is not made. 25 says only that it "assumes neither side",
  and 26 that its theorem "does not decide which side holds", adding the
  second-incompleteness remark.
- **Domains.** Positive-domain formulas must not be read over ℤ, and the
  nine-variable equations must not be read over ℤ either. 28 notes that its
  twelve-unknown proof uses h > 0.
- **Coefficients.** Materialized bytes confirm a recipe, not the compiler,
  the K215 endpoint or consistency. Compressed size is not coefficient height
  (27). The nine-variable index constants are recipes, except 30's z, which
  is materialized. The other y and coefficient leaves are not.
- **No optimality.** No global minimum is claimed for any measure. Nothing
  below 67 operations is claimed, nor eight positive unknowns or eleven
  positive unknowns. The nine-variable forms are specializations of Jones's
  theorem, not new representation theorems.

## Relation to the formal developments

- **Machine endpoint.** The packages rest on the ordinary K215 calibration
  that the Lean/Rocq endpoint `KEndpoint215.blank_halts_iff_zfc_refutation`
  (`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`, present
  at `HEAD`, not rebuilt) mirrors. The ZFC-provability claim does not go
  through Lean's soundness.
- **Jones nine-variable theorem.** The packages relate the nine-variable
  forms to the parametric
  `Jones1982.Nine.wset_iff_nine`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean:46`):
  - 27 at ν = 32 and x = 1;
  - 30 at ν = 31, claiming its data satisfy `Jones1982.Index 31 P31 z u y`;
  - 28 citing `Nine.ratio_complete` and `Nine.ratio_sound`.

  None of these is an instance of the existence theorem
  `Jones1982.nine_unknowns`, which fixes ν = 58 internally. 27 and 30 say so
  explicitly. Every new finalizer and majorant is an ordinary, unformalized
  derivation: Lean's `wset_iff_nine` concerns `nineValue`, not the new
  polynomials. Nothing is formalized.
- The native compiler notes under
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`
  remain unformalized.

## Delivery discrepancies

These are disclosed here and were not fixed in the delivered files.

- **Drivers fail in place.** Each package's main driver reads copies omitted
  at intake (the vendored `k215.tm`, `KEndpoint215.lean`, Lean sources) or
  ignored ledgers:

  | Dir | Driver | Note |
  |---|---|---|
  | 24 | `verify.py` | |
  | 25 | `reproduce.py` | contrary to its README's statement |
  | 26 | `reproduce.py` | |
  | 27 | `verify.py` | needs SymPy; `requirements.txt` was omitted |
  | 28 | `reproduce.py` | |
  | 29 | `reproduce.py --materialize-coefficients` | the default run reads only present files, per the dossier |
  | 30 | `verify_release.py` | needs NumPy and demands an exact file set |

  Rerun from the arrival commit, as `PLACEMENT.md` explains.
- **Licence and attribution.**
  - Notices of AI assistance:
    - ChatGPT: 24, 28.
    - OpenAI: 25, 26, 27.
    - AI-assisted: 29.
    - None: 30.
  - Several notices disclaim external human review or authorship (24, 25,
    26, 28, 29).
  - 27 states no licence for its new material and ships no K215 machine
    notice (no `LICENSE.Wade` or `NOTICE-K215`).
  - 30 ships only `licenses/LICENSE.ProveIt` and `licenses/NOTICE.txt`, with
    no root licence and no statement for its new material.
  - The repository's MIT-0 default applies to both unless Vladimir decides
    otherwise. 24, 25, 26, 28 and 29 offer their new material under MIT-0.
  - 27 calls wave-3 package 20 "our previous delivered packet", and 30 calls
    19's results its "previous round".
- **Inside the packages.**
  - 24: three pins hashed by `verify.py` were omitted at intake.
  - 25:
    - its README suggests the directory name `24-hybrid12/`;
    - its audits cite paths absent from the package.
  - 26: its canonical coefficient binding names raw `.bin` files that only
    replay creates.
  - 27:
    - three sub-READMEs (`integers/`, `norms/`, `operations/PROOF.md`) still
      name older tuples, overridden by a "Release binding" banner;
    - it has no open-questions section.
  - 28: `INSTANCE.json` points to `18-jones9/…`, which is no longer in the
    tree.
  - 29:
    - `build_shifted_norm12.py` still imports the superseded
      `compact_norm12` intermediate;
    - `signed17/signed17_section.tex` is an alternate section not loaded by
      `report.tex`;
    - a low-degree audit cites a nonexistent path.
  - 30:
    - `positive/README.md` points to a nonexistent `coefficients/` folder;
    - `check32/` and `rebuilt_nu31/` are not delivered.
- **Retained intermediates.**
  - 24: its monic refactors, presented as a comparison.
  - 27: its split-weight 24ℤ form.
  - 29: `compact_norm12`.
  - 30:
    - the 2,915-operation rewrite;
    - a dominated 24ℤ form of degree 2256;
    - a 26ℤ alternative of degree 236;
    - `integers/parents/`;
    - an 1800-operation ν = 31 baseline;
    - `.inert` copies of received code.

## Further questions and research

These are the open problems the packages list, merged and credited:

1. **Formalize the bridge.** This covers the separation, saturation,
   root-recovery and signed zero-case lemmas, the finalizers, and the
   interface boundary (25, 26, 28, 30).
2. **Fewer unknowns.**
   - Eleven positive, which needs gcd(E, H) = 1 or extra arithmetic
     (24, 25).
   - The new norm over fewer unrestricted integers (28), using further
     signed or odd canonical coordinates only where soundness and
     completeness survive (30).
   - Instantiating Sun's ten-integer route (25, 26, 29).
3. **Lower degree and cheaper norms.**
   - The degree bottleneck of the new norm (28).
   - A smaller shared scalar norm evaluator that keeps the pre-recovery
     root bounds (30).
   - Other norm eliminations and fewer guards (24); a weaker inverse that
     removes another guard (26).
4. **Nine variables.** Generalize the signed divisibility finalizer and
   improve the structured majorants (28). Compare the lower-degree and
   fewer-operation forms by objective, and continue sparse radix-five
   scheduling (30).
5. **Low degree.** Another relation-aware register elimination in the
   quadratic system (30).
6. **Smaller coefficients.** A smaller tile language or layout (24, 25),
   coefficient geometry optimized independently of the algebra (28), and
   an optimized native compiler that keeps the four-port interface (30).
7. **A reproducible comparison frontier** (28).

## Licence and provenance

Every package was prepared for ProveIt and reuses MIT-0 repository material;
see the licence notes above. Every licence, notice and attribution file the
packages ship is kept in place.

| Pins | Arrival | Placement |
|---|---|---|
| `ae3007ca4467011e0e051c84acb4a1dd13971b0e` (24, 25, 27–30); `a477d0fc8b` (26) | `375cc6e3d7` | `604b1416b5` |

## Files

Every staged file, grouped by source directory (generated from the tree):

- `24-integer24/`: `Makefile`, `NOTICE.md`, `README.md`, `con_zfc_synthesis.pdf`, `con_zfc_synthesis.tex`, `reproduce.py`, `verify.py`
- `24-integer24/circuits/`: `baseline67.json`, `optimized_merger12_product.json`, `optimized_merger12_system.json`, `optimized_merger13_product.json`, `optimized_merger13_system.json`, `optimized_norm12_product.json`, `optimized_norm12_system.json`, `optimized_separating_saturated12_product.json`, `optimized_separating_saturated12_sos.json`, `optimized_separating_saturated12_system.json`, `optimized_tight_separating12_product.json`, `optimized_tight_separating12_sos.json`, `optimized_tight_separating12_system.json`, `optimized_tightest_separating12_product.json`, `optimized_tightest_separating12_sos.json`, `optimized_tightest_separating12_system.json`, `retained59_system.json`, `signed_separating_saturated24_product.json`, `signed_separating_saturated24_sos.json`, `signed_separating_saturated24_system.json`
- `24-integer24/code/`: `assemble_report.py`, `audit_materialized_coefficients.py`, `bind_coefficients.py`, `build_coefficients.py`, `build_optimized_1069.py`, `build_optimized_1073.py`, `build_optimized_1081.py`, `build_signed24.py`, `check_exact_identities.py`, `check_signed24_leading.py`, `circuit_tools.py`, `degree_check.py`, `package_release.py`, `refactor_comparison_circuits.py`
- `24-integer24/coefficients/`: `COEFFICIENT_BINDING.json`, `K0.bin.gz`, `MC.bin.gz`, `MF.bin.gz`, `beta.bin.gz`
- `24-integer24/evidence/`: `BASELINE_PROVENANCE.json`, `CIRCUIT_INDEX.json`, `CLEAN_UNPACK_VERIFICATION.json`, `COMPARISON_REBUILD.json`, `EXACT_IDENTITIES.json`, `FINAL_VERIFICATION.json`, `PDF_BUILD_AND_VISUAL_REVIEW.json`, `REPRODUCTION.json`, `SOURCE_PINS.json`, `coefficients_build.json`, `independent_materialized_coefficient_audit.json`, `monic_optimization_checks.json`, `nested_optimization_checks.json`, `optimized_separating_saturated12_checks.json`, `optimized_tight_separating12_checks.json`, `optimized_tightest_separating12_checks.json`, `signed24_checks.json`, `signed24_full_degree_checks.json`, `signed24_leading_certificate_checks.json`
- `24-integer24/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `24-integer24/proofs/`: `PROOF_DEPENDENCIES.md`
- `24-integer24/sections/`: `circuits.tex`, `coefficients.tex`, `front.tex`, `integer.tex`, `positive.tex`, `references.tex`, `report_wrapper.tex`, `reproduction.tex`
- `24-integer24/upstream/`: `baseline67_source.json`, `blank_helical_proof.md`, `collection_at_pin.md`, `fixed_blank_67_proof.md`, `merger12_product_source.json`, `merger12_system_source.json`, `merger13_product_source.json`, `merger13_system_source.json`, `monic_merger_proof.md`, `norm12_product_source.json`, `norm12_proof.md`, `norm12_system_source.json`, `odd_scale27.md`, `ordinary_blank_proof.md`, `retained59_proof.md`, `retained59_source.json`, `signed_domain29.md`, `wang943_compact_layout.md`, `wang943_language.md`, `wang943_tiles.json`
- `25-hybrid12/`: `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `RESULTS.json`, `report.pdf`, `report.tex`, `reproduce.py`
- `25-hybrid12/arithmetic/`: `HYBRID12_CHECKS.json`, `build_hybrid12.py`, `hybrid12_square_unweighted_product.json`, `hybrid12_square_unweighted_sos.json`, `hybrid12_square_unweighted_system.json`, `hybrid12_square_weighted_product.json`, `hybrid12_square_weighted_sos.json`, `hybrid12_square_weighted_system.json`, `hybrid12_sum_weighted_product.json`, `hybrid12_sum_weighted_sos.json`, `hybrid12_sum_weighted_system.json`
- `25-hybrid12/baselines/`: `product67.json`, `retained59.json`
- `25-hybrid12/coefficients/`: `CHECKS.json`, `COEFFICIENT_BINDING.json`, `INDEPENDENT_CHECKS.json`, `PROOF.md`, `README.md`, `build_coefficients.py`, `verify_independent.py`, `wang943_tiles.json`
- `25-hybrid12/coefficients/coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `25-hybrid12/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `25-hybrid12/proofs/`: `COEFFICIENT_PROOF.md`, `HYBRID12_PROOF.md`, `INDEPENDENT_COEFFICIENT_AUDIT.md`, `INDEPENDENT_HYBRID12_AUDIT.md`
- `25-hybrid12/provenance/`: `SOURCES.json`
- `25-hybrid12/upstream/`: `09_ROOT_AMALGAMATION_PROOF.md`, `BLANK_HELICAL_PROOF.md`, `COMPARISON_AT_PIN.md`, `FIXED_BLANK_67_PROOF.md`, `KEndpoint215.lean`, `NORM12_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `RETAINED59_PROOF.md`, `ROOT12_PROOF.md`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `complete84_signed_quotient_absorption.md`, `complete84_signed_quotient_soundness_scout.md`
- `25-hybrid12/verification/`: `CLEAN_EXTRACTION.json`, `FINAL_TRANSCRIPTION_REVIEW.json`, `FIXED_INSTANCE_CHECKS.json`, `HYBRID12_INDEPENDENT_CHECKS.json`, `PDF_QA.json`, `REPRODUCTION.json`, `arithmetic_builder.log.txt`, `arithmetic_independent.log.txt`, `audit_hybrid12.py`, `coefficient_builder.log.txt`, `coefficient_independent.log.txt`, `fixed_instance.log.txt`, `verify_fixed_instance.py`
- `26-ratio12/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `RESULTS.json`, `SOURCE_PROVENANCE.json`, `coefficient_section.tex`, `comparison.csv`, `integer_section.tex`, `positive_section.tex`, `report.pdf`, `report.tex`, `reproduce.py`, `verification_section.tex`
- `26-ratio12/arithmetic/`: `CHECKS24.json`, `build24.py`, `build_ratio12.py`, `integer24_product.json`, `integer24_sos.json`, `integer24_system.json`, `integer24_system_shifted.json`, `ratio12_checks.json`, `ratio12_product.json`, `ratio12_system.json`, `ratio12_system_shifted.json`
- `26-ratio12/arithmetic/upstream/`: `build_norm12.py`
- `26-ratio12/coefficients/`: `COEFFICIENT_BINDING.json`, `COEFFICIENT_REPLAY.json`, `PARITY_COEFFICIENT_PROOF.md`, `README.md`, `SOURCE_PROVENANCE.json`, `reproduce_coefficients.py`
- `26-ratio12/coefficients/audit/`: `INDEPENDENT_PARITY_COEFFICIENT_REVIEW.md`, `PARITY_CROSS_AGENT_CHECKS.json`, `PARITY_INDEPENDENT_CHECKS.json`, `audit_parity_cross_agent.py`, `audit_parity_independent.py`
- `26-ratio12/coefficients/compiler/`: `COEFFICIENT_BINDING.json`, `PARITY_GEOMETRY.json`, `PARITY_MATERIALIZATION.json`, `WANG943_COEFFICIENTS.md`, `build_parity.py`, `build_wang943.py`, `check_wang_helices.py`, `materialize_parity.py`, `parity_layout.json`, `wang943_independent_language_receipt.json`, `wang943_layout.json`, `wang943_receipt.json`, `wang943_tiles.json`
- `26-ratio12/coefficients/compiler/coefficients_parity/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `26-ratio12/coefficients/compiler/upstream/`: `BRIDGE_AUDIT.md`
- `26-ratio12/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `26-ratio12/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-monic12.md`, `NOTICE-norm12.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE-separating12.md`
- `26-ratio12/proofs/`: `INDEPENDENT_24_INTEGER_REVIEW.md`, `INDEPENDENT_RATIO12_REVIEW.md`, `INDEPENDENT_REVIEW24.md`, `MANUSCRIPT_REVIEW.md`, `PROOF24.md`, `RATIO12_PROOF.md`
- `26-ratio12/references/19-wang943/audit/`: `RATIONAL_AUXILIARY_PELL_SATURATION.md`
- `26-ratio12/references/19-wang943/compiler/`: `WANG943_COMPACT_LAYOUT.md`
- `26-ratio12/references/19-wang943/roots/`: `ROOT12_SATURATED_PROOF.md`
- `26-ratio12/references/20-root12/amalgamation/`: `ROOT12_PROOF.md`
- `26-ratio12/references/21-norm12/arithmetic/`: `build_norm12.py`, `norm12_product.json`, `norm12_system.json`
- `26-ratio12/references/21-norm12/proofs/`: `INTEGER26_PROOF.md`, `NORM12_INDEPENDENT_AUDIT.md`, `NORM12_LOWER_DEGREE.md`, `NORM12_PROOF.md`
- `26-ratio12/references/21-norm12/upstream/`: `BLANK_HELICAL_PROOF.md`, `FIXED_BLANK_67_PROOF.md`, `K215_AUDIT_NOTES.md`, `ORDINARY_BLANK_PROOF.md`, `PELL_LEMMA_AUDIT.md`, `PRODUCT67.json`, `SIGNED_DOMAIN_29.md`, `SIGNED_DOMAIN_29_REVIEW.md`
- `26-ratio12/references/22-monic12/data/`: `retained16_system59.json`
- `26-ratio12/references/22-monic12/proofs/`: `RETAINED59_PROOF.md`, `merger_proof.md`
- `26-ratio12/references/22-monic12/reference/`: `retained_low_degree_proof.md`
- `26-ratio12/references/23-separating12/proofs/`: `INTEGER26_PROOF.md`, `ODD_SCALE_27_PROOF.md`
- `26-ratio12/references/23-separating12/upstream/`: `ordinary_strong_proof.md`
- `26-ratio12/references/`: `README.md`
- `26-ratio12/verification/`: `INDEPENDENT_CIRCUIT_CHECKS.json`, `PDF_QA.json`, `REPRODUCTION.json`, `audit_new_circuits.py`
- `27-wave4/`: `COMPARISON_AT_PIN.md`, `INSTANCE.json`, `LICENSE.ProveIt`, `NEGATIVE_CONTROLS.json`, `PDF_QA.json`, `README.md`, `SOURCE_ADDITIONS.json`, `VERIFICATION.json`, `negative_controls.py`, `report.pdf`, `report.tex`, `verify.py`
- `27-wave4/coefficients/`: `COEFFICIENTS.json`, `COEFFICIENT_BINDING.json`, `COEFFICIENT_PROOF.md`, `INDEPENDENT_CHECKS.json`, `README.txt`, `audit_independent.py`, `build_mixed.py`, `load_coefficients.py`, `wang943_tiles.json`
- `27-wave4/coefficients/expanded/`: `K.bin`, `K.bin.gz`, `MANIFEST.json`, `MC.bin`, `MC.bin.gz`, `MF_source.bin`, `MF_source.bin.gz`, `beta.bin`, `beta.bin.gz`
- `27-wave4/coefficients/sources/`: `k215_transitions.json`
- `27-wave4/coefficients/upstream/`: `ODD_SCALE_27_PROOF.md`
- `27-wave4/coefficients/upstream/audit/`: `WANG943_INDEPENDENT_AUDIT.md`
- `27-wave4/coefficients/upstream/compiler/`: `COMPACT_COEFFICIENT_BINDING.json`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `build_wang943.py`, `build_wang943_compact.py`, `materialize_wang943_compact.py`, `wang943_compact_layout.json`, `wang943_compact_materialization_receipt.json`, `wang943_tiles.json`
- `27-wave4/coefficients/upstream/integers/`: `COEFFICIENT_TRANSFER.md`
- `27-wave4/integers/`: `COEFFICIENT_BINDING.json`, `INTEGER24_CHECKS.json`, `INTEGER24_PROOF.md`, `INTEGER24_RATIO_WEIGHT_PROOF.md`, `INTEGER24_SPLIT2_PROOF.md`, `LICENSE.ProveIt`, `LOW_DEGREE_CHECKS.json`, `LOW_DEGREE_PROOF.md`, `PROVENANCE.json`, `README.md`, `build_integer24.py`, `build_low_degree.py`, `integer24_original_product.json`, `integer24_original_sos.json`, `integer24_original_system.json`, `integer24_original_system_comparison.json`, `integer24_original_system_residual.json`, `integer24_ratio_product.json`, `integer24_ratio_sos.json`, `integer24_ratio_system.json`, `integer24_ratio_system_comparison.json`, `integer24_ratio_system_residual.json`, `integer24_split2_product.json`, `integer24_split2_sos.json`, `integer24_split2_system.json`, `integer24_split2_system_comparison.json`, `integer24_split2_system_residual.json`, `integer36_degree8.json`, `integer42_degree6.json`, `integer51_degree4.json`
- `27-wave4/integers/sources/17-primitive12/proofs/`: `INTEGER26_PROOF.md`
- `27-wave4/integers/sources/19-wang943/integers/`: `COEFFICIENT_TRANSFER.md`, `INTEGER26_UNSCALED_PROOF.md`
- `27-wave4/integers/sources/21-norm12/arithmetic/`: `build_norm12.py`
- `27-wave4/integers/sources/21-norm12/proofs/`: `INTEGER26_PROOF.md`, `NORM12_LOWER_DEGREE.md`, `NORM12_PROOF.md`
- `27-wave4/integers/sources/23-separating12/`: `NOTICE.md`
- `27-wave4/integers/sources/23-separating12/code/`: `build_integer26.py`, `build_integer27.py`
- `27-wave4/integers/sources/23-separating12/coefficients/`: `REFINED_COMPILER_PROOF.md`, `T5263_CONSTANTS.json`
- `27-wave4/integers/sources/23-separating12/data/integer27/`: `normalized27_poly114.json`, `ordinary27_system107.json`
- `27-wave4/integers/sources/23-separating12/licenses/`: `LICENSE.ProveIt`
- `27-wave4/integers/sources/23-separating12/proofs/`: `INTEGER26_PROOF.md`, `ODD_SCALE_27_PROOF.md`, `TWELVE_VARIABLE_PROOF.md`
- `27-wave4/integers/sources/23-separating12/upstream/`: `baseline_quartic32.json`, `previous_low_degree_proof.md`, `signed_domain_29.md`
- `27-wave4/integers/sources/previous-deliverable/domains/`: `DOMAIN_REDUCTION_PROOF.md`, `integer39_degree8.json`, `integer45_degree6.json`, `integer54_quartic.json`, `sparse_poly.py`
- `27-wave4/nine/`: `IMPROVEMENT_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_improved.py`, `verify_fixed_binding.py`, `verify_improved.py`
- `27-wave4/nine/generated/`: `COEFFICIENT_ALIASES.json`, `FIXED_BINDING_VALIDATION.json`, `VALIDATION.json`, `ledger.json`, `nine_literal_dag.json`, `nine_literal_positive_dag.json`, `nine_literal_specialized_dag.json`, `nine_literal_specialized_positive_dag.json`, `nine_majorant_dag.json`, `nine_majorant_positive_dag.json`, `nine_majorant_specialized_dag.json`, `nine_majorant_specialized_positive_dag.json`, `nine_natural-majorant_dag.json`, `nine_natural-majorant_positive_dag.json`, `nine_natural-majorant_specialized_dag.json`, `nine_natural-majorant_specialized_positive_dag.json`
- `27-wave4/nine/source/`: `COEFFICIENT_BINDINGS.json`, `LICENSE`, `NOTICE.md`, `README.md`
- `27-wave4/nine/source/base/`: `normalized_quartic32.json`, `quartic32.upstream.json`
- `27-wave4/nine/source/code/`: `fixed_coefficients.py`
- `27-wave4/nine/source/nine/`: `check_nine.py`, `nine_compressor.py`, `nine_section.tex`, `verify_fixed_instance.py`
- `27-wave4/nine/source/nine/generated/`: `constants.json`, `index_bound_s.json`, `nine_checks.json`
- `27-wave4/nine/source/proofs/`: `independent_review.md`, `nine_source_audit.md`
- `27-wave4/norms/`: `COEFFICIENT_BINDING.json`, `README.md`, `SEPARATION_CHECKS.json`, `SOURCE_PROVENANCE.json`, `TWO_WEIGHT_CHECKS.json`, `TWO_WEIGHT_PROOF.md`, `TWO_WEIGHT_SECTION.tex`, `build_two_weight_norm12.py`, `check_separation.py`, `two_weight_norm12_product.json`, `two_weight_norm12_sos.json`, `two_weight_norm12_system.json`
- `27-wave4/norms/sources/20-root12/amalgamation/`: `ROOT12_PROOF.md`
- `27-wave4/norms/sources/21-norm12/`: `LICENSE`, `NOTICE.md`
- `27-wave4/norms/sources/21-norm12/arithmetic/`: `build_norm12.py`, `build_norm12_lower_degree.py`
- `27-wave4/norms/sources/21-norm12/proofs/`: `NORM12_LOWER_DEGREE.md`, `NORM12_PROOF.md`
- `27-wave4/norms/sources/22-monic12/code/`: `build_mergers.py`
- `27-wave4/norms/sources/22-monic12/proofs/`: `merger_proof.md`
- `27-wave4/operations/`: `COEFFICIENT_BINDING.json`, `PROOF.md`, `VERIFICATION.json`, `build_operations.py`, `lift17_Y59.json`, `lift17_Y59_sos.json`, `lift18_YE59.json`, `lift18_YE59_sos.json`, `lift19_YEc59.json`, `lift19_YEc59_sos.json`, `lift20_YEcA059.json`, `lift20_YEcA059_sos.json`, `retained16_auxgap60.json`, `retained16_auxgap60_sos.json`
- `27-wave4/operations/upstream/`: `COEFFICIENT_BINDING_943.json`, `GROUPED_TRADEOFF_PROOF.md`, `RETAINED59_PROOF.md`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `build_grouped_tradeoffs.py`, `build_retained59.py`, `grouped_doublegap76_degree44.json`, `retained16_system59.json`
- `27-wave4/review/`: `LOW_DEGREE_NEW_INDEPENDENT_CHECKS.json`, `NEW_SYNTHESIS_INDEPENDENT_REVIEW.md`, `NINE_IMPROVEMENTS_INDEPENDENT_CHECKS.json`, `NOVEL_NORM_INDEPENDENT_CHECKS.json`, `check_low_degree_new_independent.py`, `check_nine_improvements_independent.py`, `check_novel_norms_independent.py`
- `27-wave4/root/`: `COMPILER_REVIEW.md`, `MIXED_INDEPENDENT_CHECKS.json`, `check_mixed_independent.py`
- `28-compact-norms/`: `INSTANCE.json`, `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_MANIFEST.json`, `report.pdf`, `report.tex`, `reproduce.py`
- `28-compact-norms/audit/`: `WANG943_COMPACT_INDEPENDENT_CHECKS.json`, `WANG943_INDEPENDENT_AUDIT.md`, `WANG943_INDEPENDENT_CHECKS.json`, `audit_wang943_compact_independent.py`, `audit_wang943_independent.py`
- `28-compact-norms/circuits/`: `compact12_product.json`, `compact12_sos.json`, `compact12_system.json`
- `28-compact-norms/circuits/nine/`: `constants.json`, `index_bound_s.json`, `nine_structured_dag.json`, `shifted_quartic.json`, `verification.json`
- `28-compact-norms/code/`: `build_compact12.py`, `nine_structured.py`, `verify_compact12.py`, `verify_structured.py`
- `28-compact-norms/compiler/`: `COMPACT_COEFFICIENT_BINDING.json`, `COMPACT_PAYLOAD_MANIFEST.json`, `COMPACT_REPRODUCE.md`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `build_wang943.py`, `build_wang943_compact.py`, `check_wang_helices.py`, `materialize_wang943_compact.py`, `wang943_compact_layout.json`, `wang943_compact_materialization_receipt.json`, `wang943_compact_receipt.json`, `wang943_independent_language_receipt.json`, `wang943_layout.json`, `wang943_receipt.json`, `wang943_tiles.json`
- `28-compact-norms/compiler/coefficients_compact/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `28-compact-norms/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.norm21`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE.norm21.md`
- `28-compact-norms/proofs/`: `COMPACT12_PROOF.md`
- `28-compact-norms/sections/`: `coefficients.tex`, `nine.tex`, `overview.tex`, `references.tex`, `twelve.tex`, `verification.tex`
- `28-compact-norms/vendor/`: `COMPARISON_AT_PIN.md`
- `28-compact-norms/vendor/inherited/`: `BLANK_HELICAL_PROOF.md`, `FIXED_BLANK_67_PROOF.md`, `K215_AUDIT_NOTES.md`, `ORDINARY_BLANK_PROOF.md`, `PELL_LEMMA_AUDIT.md`, `PRODUCT67.json`, `ROOT_AMALGAMATION_13.md`, `SIGNED_DOMAIN_29.md`, `SIGNED_DOMAIN_29_REVIEW.md`
- `28-compact-norms/vendor/jones18/`: `NINE_BINDING.json`, `NINE_README.md`, `NINE_UPSTREAM_SOURCE_MANIFEST.json`, `quartic32.upstream.json`
- `28-compact-norms/vendor/norm21/`: `NORM12_LOWER_DEGREE.md`, `NORM12_PROOF.md`, `build_norm12.py`
- `28-compact-norms/verification/`: `INDEPENDENT_COMPACT12_CHECKS_OPTIMIZED.json`, `INDEPENDENT_COMPACT12_REVIEW.md`, `NINE_INDEPENDENT_AUDIT.md`, `PDF_QA.json`, `REPRODUCED.json`, `REPRODUCED_FULL.json`
- `29-simpler-forms/`: `COEFFICIENT_BINDING.json`, `INSTANCE_BINDINGS.json`, `LICENSE`, `NOTICE.md`, `README.md`, `integer17_section.tex`, `report.pdf`, `report.tex`, `reproduce.py`
- `29-simpler-forms/coefficients/`: `UPSTREAM_BINDING.json`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `build_wang943.py`, `build_wang943_compact.py`, `check_wang_helices.py`, `materialize_wang943_compact.py`, `wang943_compact_layout.json`, `wang943_compact_materialization_receipt.json`, `wang943_compact_receipt.json`, `wang943_layout.json`, `wang943_receipt.json`, `wang943_tiles.json`
- `29-simpler-forms/coefficients/coefficients_compact/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `29-simpler-forms/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`
- `29-simpler-forms/low_degree/`: `INDEPENDENT_AUDIT.md`, `ODD_SCALE_LIFTS_PROOF.md`, `build_odd_scale_lifts.py`
- `29-simpler-forms/low_degree/generated/`: `ODD_SCALE_LIFTS_CHECKS.json`, `integer36_degree8_odd_scale.json`, `integer42_degree6_odd_scale.json`, `integer51_degree4_odd_scale.json`
- `29-simpler-forms/low_degree/upstream/19-wang943/`: `COEFFICIENT_BINDING.json`
- `29-simpler-forms/low_degree/upstream/19-wang943/compiler/`: `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`
- `29-simpler-forms/low_degree/upstream/19-wang943/compiler/coefficients_compact/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `29-simpler-forms/low_degree/upstream/20-root12/coefficients/`: `COEFFICIENTS.json`, `COEFFICIENT_PROOF.md`
- `29-simpler-forms/low_degree/upstream/20-root12/domains/`: `DOMAIN_REDUCTION_PROOF.md`, `build_domains.py`, `build_tradeoffs.py`, `integer39_degree8.json`, `integer45_degree6.json`, `integer54_quartic.json`, `sparse_poly.py`
- `29-simpler-forms/low_degree/upstream/23-separating12/proofs/`: `ODD_SCALE_27_PROOF.md`
- `29-simpler-forms/norm12/`: `COMPACT_NORM12_CHECKS.json`, `COMPACT_NORM12_PROOF.md`, `SHIFTED_NORM12_CHECKS.json`, `SHIFTED_NORM12_PROOF.md`, `build_compact_norm12.py`, `build_norm12.py`, `build_norm12_lower_degree.py`, `build_shifted_norm12.py`, `compact_norm12_product.json`, `compact_norm12_residual_system.json`, `compact_norm12_sos118.json`, `compact_norm12_sos_unshifted.json`, `compact_norm12_system110.json`, `compact_norm12_system111.json`, `shifted_norm12_product.json`, `shifted_norm12_residual_system.json`, `shifted_norm12_sos118.json`, `shifted_norm12_sos_unshifted.json`, `shifted_norm12_system110.json`, `shifted_norm12_system111.json`
- `29-simpler-forms/references/`: `BLANK_HELICAL_PROOF.md`, `COMPARISON_AT_PIN.md`, `FIXED_BLANK_67_PROOF.md`, `KEndpoint215.lean`, `NORM12_LOWER_DEGREE.md`, `NORM12_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `PELL_LEMMA_AUDIT.md`, `RETAINED59_PROOF.md`, `ROOT_AMALGAMATION_13.md`, `SIGNED_DOMAIN_29.md`
- `29-simpler-forms/signed17/`: `README.md`, `SIGNED17_PROOF.md`, `SOURCE_PINS.json`, `build_signed17.py`, `signed17_section.tex`
- `29-simpler-forms/signed17/generated/`: `signed17.json`, `signed17_checks.json`
- `29-simpler-forms/signed17/upstream/`: `COEFFICIENT_BINDINGS.json`, `LICENSE`, `NOTICE.md`
- `29-simpler-forms/signed17/upstream/base/`: `quartic32.upstream.json`
- `29-simpler-forms/signed17/upstream/code/`: `fixed_coefficients.py`
- `29-simpler-forms/signed17/upstream/coefficients/`: `T4_CONSTANTS.upstream.json`, `t4_windows.json`
- `29-simpler-forms/signed17/upstream/nine/generated/`: `constants.json`, `index_bound_s.json`
- `29-simpler-forms/signed17/upstream/nine/`: `nine_compressor.py`, `nine_section.tex`, `verify_fixed_instance.py`
- `29-simpler-forms/signed17/upstream/upstream/licenses/`: `LICENSE.ProveIt`
- `29-simpler-forms/signed17/upstream/upstream/machine/`: `NOTICE.md`
- `29-simpler-forms/signed17/upstream/upstream/machine/licenses/`: `LICENSE.Wade`
- `29-simpler-forms/signed17/upstream/upstream/t4/bridge/`: `BRIDGE_AUDIT.md`
- `29-simpler-forms/signed17/upstream/upstream/t4/bridge/sources/`: `blank_helical.py`, `compiler_constants.py`, `k215_transitions.json`
- `29-simpler-forms/verification/`: `BUILD_AND_RENDER.json`, `OPTIONAL_MATERIALIZATION_CHECK.json`, `REPRODUCTION.json`
- `30-quartic31/`: `COEFFICIENT_BINDING.json`, `PORTABILITY_TRANSFORMS.json`, `README.md`, `RELEASE_MANIFEST.json`, `audit_selected_nine.py`, `verify_release.py`
- `30-quartic31/arithmetic/`: `AUDIT.json`, `LOW_OPERATION_REPORT.md`, `QUARTIC31_PROOF.md`, `SOURCE_LEDGER.json`, `build_arithmetic.py`, `quartic31.json`, `quartic31_circuit.json`, `quartic31_expanded.json`, `quartic31_system.json`, `retained16_gap_system60.json`
- `30-quartic31/arithmetic/upstream/`: `RETAINED59_PROOF.pinned.md`, `quartic32.pinned.json`, `retained16_system59.pinned.json`
- `30-quartic31/audit/`: `RATIONAL_AUXILIARY_PELL_SATURATION.md`, `WANG943_COMPACT_INDEPENDENT_CHECKS.json`, `WANG943_INDEPENDENT_AUDIT.md`, `pell_bound_checks.json`, `pell_bound_checks.py`, `pell_independent_audit.md`, `pell_independent_checks.json`, `pell_independent_checks.py`, `pell_integer_binding_checks.json`
- `30-quartic31/compiler/`: `COMPACT_COEFFICIENT_BINDING.json`, `COMPACT_COEFFICIENT_BINDING.upstream.json`, `MACHINE_SOURCE.json`, `PINNED_SOURCE_LEDGER.json`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `wang943_compact_layout.json`, `wang943_compact_materialization_receipt.json`, `wang943_compact_receipt.json`, `wang943_independent_language_receipt.json`, `wang943_layout.json`, `wang943_tiles.json`
- `30-quartic31/compiler/coefficients_compact/`: `K.bin`, `K.bin.gz`, `MC.bin`, `MC.bin.gz`, `MF_source.bin`, `MF_source.bin.gz`, `beta.bin`, `beta.bin.gz`
- `30-quartic31/integers/`: `COEFFICIENT_BINDINGS.json`, `COEFFICIENT_TRANSFER.md`, `ODD_SCALE_FAMILY_CHECKS.json`, `README.md`, `SIGNED_ODD_SCALE_FAMILY_PROOF.md`, `SOURCE_MANIFEST.json`, `SOURCE_MANIFEST.seed.json`, `build_odd_scale_family.py`, `check_odd_scale_family.py`, `integer24_pair_norm165_degree2256.json`, `integer24_sharp_pair_norm165_degree2240.json`, `integer24_system161_degree2224.json`, `integer25_small_weight131_degree920.json`, `integer25_system126_degree872.json`, `integer26_ordinary_two_root123_degree214.json`, `integer26_system117_degree128.json`, `integer26_two_root123_degree236.json`
- `30-quartic31/integers/parents/`: `integer27_weighted_root136_degree1116.json`, `integer28_normalized_amalgam128_degree258.json`
- `30-quartic31/integers/upstream/20-root12/arithmetic/`: `SMALL_WEIGHT_PROOF.md`
- `30-quartic31/integers/upstream/21-norm12/proofs/`: `NORM12_PROOF.md`
- `30-quartic31/integers/upstream/23-separating12/proofs/`: `INTEGER26_PROOF.md`, `ODD_SCALE_27_PROOF.md`
- `30-quartic31/licenses/`: `LICENSE.ProveIt`, `NOTICE.txt`
- `30-quartic31/nine/`: `COMPACT_NINE_PROOF.md`, `README.md`, `Z_MATERIALIZATION.json`, `build_compact_nine.py`, `prepare_coefficients.py`, `rebuild_nu31.py`, `verify_compact_instance.py`, `z_index.bin`, `z_index.bin.gz`
- `30-quartic31/nine/nu31/`: `ACTUAL_INSTANCE_CHECKS.json`, `COMPACT_COEFFICIENT_BINDING.json`, `COMPACT_CONSTANTS.json`, `CONSTRUCTION_CHECKS.json`, `INDEX_BOUND_CERTIFICATE.json`, `coefficients.json`, `nine_compact_magnitude_tight.json`, `nine_generic31_majorant.json`, `shifted_quartic.json`
- `30-quartic31/positive/`: `CHECK_RESULTS.json`, `COEFFICIENT_BINDING.json`, `POSITIVE12_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_positive.py`, `check_positive.py`, `positive12_product.json`, `positive12_system.json`
- `30-quartic31/report/`: `MAIN.md`, `build_report.py`, `code_breaks.lua`, `header.tex`, `synthesis_report.md`, `synthesis_report.pdf`, `synthesis_report.tex`
- `30-quartic31/review/`: `16-integer27.tree.json`, `17-primitive12.tree.json`, `18-jones9.tree.json`, `19-wang943.tree.json`, `20-root12.tree.json`, `21-norm12.tree.json`, `22-monic12.tree.json`, `23-separating12.tree.json`, `COMPARISON_REVIEW.md`, `FINAL_FROZEN_MANIFEST.json`, `FINAL_NINE_REVIEW.md`, `INDEPENDENT_REVIEW_AUDIT.json`, `INERT_SOURCE_PATHS.json`, `NU31_COMPACT_INDEX_INDEPENDENT_AUDIT.json`, `NU31_INDEPENDENT_AUDIT.json`, `QUARTIC31_INDEPENDENT_REVIEW.json`, `README.upstream.md`, `SOURCE_LEDGER.json`, `audit_modified_nine.py`, `generic_jones_circuit.py`, `independent_review_audit.py`, `inventory.json`, `optimize_nine_circuit.py`
- `30-quartic31/review/16-integer27/data/`: `improved_weight_polynomial13_84.json`, `integer27_weighted_root_polynomial139.json`
- `30-quartic31/review/17-primitive12/arithmetic/primitive12/generated/`: `primitive12_product.json`
- `30-quartic31/review/17-primitive12/proofs/`: `PRIMITIVE12_PROOF.md`
- `30-quartic31/review/18-jones9/`: `RESULTS.json`
- `30-quartic31/review/18-jones9/base/`: `quartic32.upstream.json`
- `30-quartic31/review/18-jones9/direct12/`: `radical12_product.json`
- `30-quartic31/review/18-jones9/nine/`: `README.md`, `nine_compressor.py.inert`, `nine_section.tex`
- `30-quartic31/review/18-jones9/nine/generated/`: `constants.json`, `index_bound_s.json`, `nine_checks.json`, `nine_majorant_dag.json`, `shifted_quartic.json`
- `30-quartic31/review/18-jones9/proofs/`: `independent_review.md`, `nine_source_audit.md`
- `30-quartic31/review/19-wang943/roots/`: `root12_saturated_product.json`
- `30-quartic31/review/20-root12/amalgamation/`: `ROOT12_PROOF.md`, `main_root12_product.json`
- `30-quartic31/review/20-root12/arithmetic/`: `SMALL_WEIGHT_PROOF.md`
- `30-quartic31/review/21-norm12/arithmetic/`: `norm12_product.json`, `norm12_product_integer26.json`
- `30-quartic31/review/21-norm12/proofs/`: `NORM12_PROOF.md`
- `30-quartic31/review/22-monic12/data/`: `merger12_product.json`, `merger13_product.json`, `retained16_system59.json`
- `30-quartic31/review/22-monic12/proofs/`: `RETAINED59_PROOF.md`, `merger_proof.md`
- `30-quartic31/review/23-separating12/data/integer27/`: `normalized27_poly114.json`, `normalized27_poly115.json`, `ordinary27_poly116.json`
- `30-quartic31/review/23-separating12/data/`: `polynomial12.json`
- `30-quartic31/review/23-separating12/proofs/`: `ODD_SCALE_27_PROOF.md`
- `30-quartic31/review/nine_optimized/`: `AUDIT.json`, `GENERIC_AUDIT.json`, `GENERIC_DEGREE_AUDIT.json`, `nine_generic32_majorant.json`, `nine_majorant_runs.json`
- top level: `README.md` (this file), `PLACEMENT.md`
