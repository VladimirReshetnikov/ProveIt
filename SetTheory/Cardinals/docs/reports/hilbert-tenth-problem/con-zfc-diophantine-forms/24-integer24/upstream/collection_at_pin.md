# Con(ZFC) in Diophantine form

**Explicit polynomials with fixed integer coefficients whose unsolvability
ZFC proves equivalent to Con(ZFC): eight wave-3 syntheses on the blank run
of K215, with twelve positive unknowns, nine natural unknowns via Jones,
26 and 27 unrestricted integers, and materialized coefficients**

This report holds eight AI-assisted research packages, all dated 22 October
2026. They are batch 219 of ProveIt's incoming reports (arrival
`cbf94cb552`, "Con(ZFC) in Diophantine form (wave-3)"), placed in
`da064316ea`. All eight are pinned to `f0ae4e0991`, a snapshot that already
contains this report's audited wave-2 form, and they cite wave-2 packages by
their source numbers 09–15.

## Earlier waves are superseded

By Vladimir's direction (22 October 2026) wave 3 supersedes wave 2, so
directories `09-combined13/` … `15-release/` were removed from the tree when
wave 3 was placed. Wave 2 had in turn superseded wave 1 (`01-…` to `08-…`).

| Wave | Batch | Arrival (archives) | Directories in every commit from … to … | Audited README |
|---|---|---|---|---|
| 1 | 217 | `2fd49a1a9d` | `084e120830` … `8a4b00b5bf^` | `f3af223ef7` |
| 2 | 218 | `7be2780f26` | `8a4b00b5bf` … `da064316ea^` | `5b0c9ae9fd` |
| 3 | 219 | `cbf94cb552` | `da064316ea` … | this file |

Source numbers 01–15 are kept only because the wave-2 and wave-3 texts use
them; the wave-3 directories continue the sequence as 16–23.

Seven wave-3 packages bundle a copy of the audited wave-2 README, and all
seven copies describe a superseded wave. Five are identical up to line
ends:

- `17-primitive12/inherited/COMPARISON_AT_PIN.md`
- `18-jones9/upstream/reports/COMPARISON_README.md`
- `19-wang943/review/README.upstream.md`
- `22-monic12/reference/comparison_at_pin.md`
- `23-separating12/upstream/catalogue_README.md`

Two more, `16-integer27/upstream/COMPARISON_AT_PIN.md` and
`21-norm12/upstream/REPOSITORY_COMPARISON.md`, each have one extra final
newline. The first intake check missed 16's copy; the audit found it.

**Wave-2 results that wave 3 does not reproduce** now survive only in
history (the wave-2 README and directories at `5b0c9ae9fd`, e.g.
`git show 5b0c9ae9fd:<this directory>/README.md`). Several wave-3 packages
say some of these remain better on their own measures (the quartic, the
67-operation equation, the low-degree systems); the list itself is an
intake comparison:

- the 32-unknown positive quartic lift (and the 33 / 24 lift);
- the positive 25-unknown sextic and 20-unknown octic lifts;
- the 15-unknown six-equation systems of degree 28 (61 ops, and 12's S₆₀
  at 60 ops) and of degree 22;
- 09's 14-unknown P₁₄ of degree 121, its 14 / 5 / 72 / 67 system, the
  14 / 5 / 244 / 69 system and the other 14-unknown root norms;
- the 15-unknown products of degree 83–99 and Q₅₆ (15 / 1 / 56 / 74);
- the 33ℤ / 1 / 159 / 134 polynomial, of lower degree than any optimized
  wave-3 integer polynomial with at most 33 unknowns.

The 67-operation equation P₆₇ (wave-1 06/08) remains the fewest-operations
form. No wave-3 package claims fewer; 17 ships it rebound to its own
coefficients, and 21 ships it with instructions to bind its new tuple.

## How this report was made

The packages overlap, as before, so they are **placed, not written**,
following the intake rule for overlapping deliveries
([docs/incoming/README.md](../../../../../../docs/incoming/README.md),
section 2):

- each package keeps its delivered layout and PDF in its numbered directory,
  with the wrapper directory removed;
- this README is the reconciliation note;
- no delivered file was edited, no PDF was built, and no delivered program
  was run at intake.

Facts below are the packages' own, taken from two read-only intake dossiers;
the few facts checked at intake say so. [`PLACEMENT.md`](PLACEMENT.md) is the
recovery map for wave 3. It covers 921 archive members:

- 818 staged (811 at placement, plus 7 attribution files restored after
  the audit);
- 86 omitted as byte-identical (up to line ends) copies of repository files
  outside this report;
- 17 checksum ledgers and logs excluded by the root `.gitignore`.

## The common theorem

Each package defines polynomials or small systems with four **fixed integer
coefficient ports**: Bm1 = B − 1, Kconstant = D_C + B·D_R, MC, and the
**shifted** MF = (native high mask) + B − 1. The ports are determined by a
finite recipe from the literal 215-state machine
[`candidate-k215/k215.tm`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm).
Each package then proves, by ordinary mathematics formalizable in ZFC, that

> ZFC ⊢ (no solution in the stated domain) ↔ Con(ZFC).

The route is unchanged from wave 2:

1. the blank run of K215 halts iff ZFC has a finite refutation;
2. a local tile language of that run is compiled by the repository's
   native-window/Pell compiler
   ([`native-stream-queue/`](../../../../../../Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/README.md)),
   with its input interface removed.

Wave 3 adds:

- **twelve positive unknowns** in moderate-degree circuits, by seven
  packages that each merge the remaining Pell roots into one supplied
  coordinate, by different methods;
- **nine unknowns** at astronomic degree, by an explicit instance of
  Jones's nine-variable reduction (18): nine naturals, or nine positive
  after the shift x ↦ x − 1, which 18 describes but does not deliver as a
  circuit;
- **fewer unrestricted integers**: 26, and a 27-unknown form of low degree;
- **smaller coefficient alphabets**, two of them materialized.

## The eight packages

Numbers are the packages' own; **none was re-derived at intake.** A cell
"u / e / d / o" means unknowns / equations / degree / operations. Operations
count every binary +, −, × including multiplication by fixed numerals; reuse
and system comparisons are free. Unknowns are strictly positive unless marked
ℤ (unrestricted integers) or ℕ (naturals).

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`16-integer27/`](16-integer27/) | `con_zfc_27_integer_synthesis_2026-10-22.zip` | *Fewer integer variables in Diophantine formulations of ZFC consistency* | 13 / 1 / 515 / 84; 13 / 4 / 488 / 78; 27ℤ / 1 / 1004 / 139; 27ℤ / 4 / 952 / 133 |
| [`17-primitive12/`](17-primitive12/) | `ProveIt_ConZFC_Primitive12_2026-10-22.zip` | *Twelve positive unknowns for ZFC consistency* | primitive element: 12 / 1 / 2601 / 167, 12 / 3 / 2592 / 163, SOS 12 / 1 / 5184 / 170; 26ℤ / 1 / 5265 / 229 (system 225, SOS 232); 27ℤ / 1 / 1116 / 139; P₆₇ rebound |
| [`18-jones9/`](18-jones9/) | `ProveIt_ConZFC_9_12_27_2026-10-22.zip` | *Three explicit Diophantine forms of ZFC consistency* | **Jones specialization 9ℕ / 1 / 161844·5^33 + 484 / 20,531**; direct 12 / 1 / 1609 / 151, 12 / 3 / 1600 / 147; 27ℤ / 1 / 1004 / 137 (system 131); 27ℤ / 1 / 1116 / 136 (system 130) |
| [`19-wang943/`](19-wang943/) | `twelve-variable-con-zfc.zip` | *Twelve positive variables and materialized coefficients for the consistency of ZFC* | 12 / 1 / 1257 / 139, 12 / 3 / 1248 / 135; **26ℤ / 1 / 2465 / 192**; 27ℤ / 1 / 1116 / 136; 28ℤ / 1 / 258 / 128 and 426 / 127; grouped SOS 15 / 1 / 44 / 76; **materialized 943-tile coefficients, B = 2^(5^10)** |
| [`20-root12/`](20-root12/) | `ZFC_Diophantine_Twelve_Variables_2026-10-22.zip` | *Twelve positive unknowns and materialized coefficients for ZFC consistency* | **12 / 1 / 1145 / 123**, 12 / 3 / 1136 / 119; 13 / 1 / 515 / 84, 13 / 4 / 488 / 78; 27ℤ / 1 / 1004 / 136; low-degree ℤ lifts 54ℤ quartic, 45ℤ sextic, 39ℤ octic; **materialized 4094-tile coefficients, B = 2^(5^11)** |
| [`21-norm12/`](21-norm12/) | `con-zfc-norm12-2026-10-22.zip` | *A twelve-variable equation for Con(ZFC)* | **12 / 1 / 1353 / 116**, **12 / 3 / 1344 / 112**; lower-degree 12 / 1 / 1177 / 123; 26ℤ / 1 / 2657 / 168, 26ℤ / 3 / 2640 / 164 |
| [`22-monic12/`](22-monic12/) | `ProveIt_ConZFC_Monic12_2026-10-22.zip` | *Twelve-variable Diophantine forms of ZFC consistency* | 12 / 1 / 1529 / 117, **12 / 3 / 1520 / 112**; **13 / 1 / 319 / 91, 13 / 4 / 288 / 83**; 26ℤ / 1 / 2993 / 169, 26ℤ / 3 / 2976 / 164; **16 / 7 / 24 / 59** |
| [`23-separating12/`](23-separating12/) | `con-zfc-twelve-2026-10-22.zip` | *Twelve positive unknowns for the consistency of ZFC* | 12 / 1 / 1369 / 144, 12 / 3 / 1360 / 140; 26ℤ / 1 / 3560 / 199; **27ℤ / 1 / 172 / 116**, 27ℤ / 6 / 46 / 107, products 274 / 114 and 216 / 115 |

Directory numbers follow the archives' arrival (file-time) order. Each
directory's `README.md` is its entry point. The articles are:

- `report.pdf` in 16, 17, 18, 20, 21 and 23;
- `19-wang943/report/twelve_variable_con_zfc.pdf`;
- `22-monic12/con_zfc_synthesis.pdf`.

## Frontier, credits and bases (intake findings)

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Fewest unknowns, any domain | **9 naturals**: an explicit specialization of Jones's nine-variable theorem to the 32-unknown quartic, one equation of degree 161844·5^33 + 484 (about 1.9·10^28) in 20,531 ops; z⋆, y⋆ and the coefficients defined but not expanded | 18 only | 18 |
| Fewest positive unknowns, moderate degree | **12** (18's nine-variable form also becomes 9 positive by the shift x ↦ x − 1, at its astronomic degree, but no such circuit is delivered), by seven genuinely different polynomials (their degrees differ). Lowest degree: 20 (1145, 123 ops). Fewest ops: 21's product (116 ops, degree 1353) and the 112-op systems of 21 and 22 | 17, 18, 19, 20, 21, 22, 23 | 17 for the count; 20 for degree; 21 for operations |
| 13 positive unknowns | degree 515 at 84 ops (16, 20; different weights, not compared at intake); **degree 319 at 91 ops, 4-equation system 288 / 83** | 16, 20; 22 | 16; 22 |
| Fewest unrestricted integers | **26ℤ**: 2465 / 192 (19), 2657 / 168 (21), 2993 / 169 (22), 3560 / 199 (23), 5265 / 229 (17) | 17, 19, 21, 22, 23 | 17; 19 for degree; 21 for operations |
| 27 unrestricted integers | **172 / 116** (23's ordinary signed-scale product: lowest degree and fewest operations among the ordinary 27ℤ products; system 46 / 107; 23's normalized products use 114 and 115 ops at degrees 274 and 216). Also 1004 / 136–139 (16, 18, 20) and 1116 / 136–139 (17, 18, 19; 18's and 19's 136-op circuits are the same polynomial, per the dossier) | 23; 16, 18, 20; 17, 18, 19 | 23 |
| Low-degree unrestricted-integer lifts | 54ℤ quartic (31 quadratics), 45ℤ sextic, 39ℤ octic | 20 only | 20 |
| Smallest system overall | **59 ops** (16 / 7 / 24) | 22 | 22 |
| Low-degree 15-unknown single equation | grouped sums of squares, degree 44 at **76 ops** (wave 2: 78), and 19's other nondominated choices 50 / 75, 70 / 73, 80 / 72 | 19 | 19 |
| Fewest operations | **67** (P₆₇, wave 1), unchanged | — | (wave-1 06) |
| Smallest coefficients | **B = 2^(5^10)**, 943 tiles, materialized as four gzip payloads (20,260 bytes; 5,312,269 raw) | 19 | 19 |

The twelve-positive constructions share eleven coordinates
J, F, α, z, h, i, T, s, w, η, ζ plus one merged coordinate. They differ in
how that coordinate encodes the deleted roots f, τ, y, γ and in how
integrality is recovered:

| Package | Encoding | Integrality |
|---|---|---|
| 17 | sixteen-branch primitive element | Pell "rigidity" |
| 18 | eight-branch norm with the strong multiplier H·i | gcd(H, d) = gcd(H, Q − 1) = 1 and an SL₂ period |
| 19 | four-factor norm | Pell "saturation" applied first |
| 20 | 09's three-root witness extended by the main root | rational auxiliary-root lemma |
| 21 | two nested quadratic norms | rational-Pell lemma |
| 22 | monic resultant | algebraic-integer norm and saturation |
| 23 | separating root with the strong multiplier H·i | gcd(H, d) = 1 and a Pell-matrix period modulo Hc² |

The rigidity, saturation and rational-Pell lemmas of 17, 19, 20, 21 and 22
state essentially the same fact. The H·i multiplier with gcd and period
arguments was found independently by 18, by 23 and in 19's own earlier
restricted-i variant.

### Coefficient recipes: use one whole tuple

| Dir | Tiles | d (B = 2^d) | Materialized | Binding |
|---|---:|---|---|---|
| 16 | 5,268 | 5^17 | no | `COEFFICIENT_BINDING.json` (`P4-5268-tightband-5pow17`) |
| 17 | 5,252 | 5^16 | no (residue evaluator) | `INSTANCE.json` (`pruned-T4-5252-compact-5pow16`) |
| 18 | 37,075 (T4, unchanged) | 5^18 | no | `COEFFICIENT_BINDINGS.json` |
| 19 | 943 | 5^10 | **yes**, gzip payloads | `COEFFICIENT_BINDING.json` (`wang943-compact-5pow10`) |
| 20 | 4,094 | 5^11 | **yes**, `coefficients/expanded/*.bin` (25,421,252 bytes) | `INSTANCE.json` (`T4-4094-binary-copy-zero-padding-5pow11`) |
| 21 | 5,280 | 5^15 | no | `COEFFICIENT_BINDING.json` |
| 22 | 5,252 | 5^16 | no (mod-m evaluator) | `data/COEFFICIENT_BINDING.json` |
| 23 | 5,263 | 5^16 | no | `COEFFICIENT_BINDING.json` |

- Every package binds its four ports as one tuple and forbids splicing.
- Each proves an adapter for the common inputless interface. Some name
  earlier whole tuples (wave-1 06's, T4) as valid alternatives.
- No package checks another wave-3 package's tuple.
- 17 and 22 have the same tile count and d but different anchors and
  alphabets, so their tuples differ.
- The residues 2D_C − D_R mod 5 differ (1, 2, 3, 4). The packages explain
  that this is harmless: only invertibility matters.

The intake dossiers' read-only scripts partly re-checked the two
materialized tuples (hashes, bit lengths, β = B − 1, congruences):

- 20's four `.bin` files match their manifest hashes;
- 19's four gzip payloads decompress to the stated hashes and bit lengths.

These checks confirm the bytes, not the compiler theorem the bytes
instantiate.

### Tensions, not adjudicated at intake

- **The 27ℤ bootstrap.** 19 says the correct bootstrap for its 27ℤ form is
  h ≥ 0, calling R < k "unjustified" (`INTEGER27_INDEPENDENT_AUDIT.md:17`).
  18 proves h ≥ 1 and k > R by a separate p ≥ 3 lemma
  (`integer27_section.tex:126-159`, covering both of its weights), and 16
  proves the main Pell index is at least 3. 18's and 19's 1116-degree
  136-op circuits are the same polynomial, so for it these are two
  different proofs: 19 avoids R < k, while 18 proves k > R. 19 does not
  cite 18.
- **Positivity before root recovery.** 20 says its twelve-unknown proof
  needs positivity before root recovery, while 17, 19, 21, 22 and 23 each
  prove signed 26ℤ versions of their own twelve-unknown forms. These are
  different polynomials, not a contradiction.
- **Citing 14's theorem.** 23's independent audit cautions against citing
  14's odd-i / square-w theorem as a hypothesis
  (`proofs/INDEPENDENT_TWELVE_AUDIT.md:15-18`), and 18's review says the
  argument should be reused rather than cited.
- **No package calls wave 2 wrong.** No wave-3 package says a wave-2
  statement or the wave-2 README was *wrong*. 18 found "no new fatal
  algebraic or sign gap" in 09, 12 and 14. 19's gate audit passed all 62
  upstream circuits, but those were operation, liveness and modular-degree
  diagnostics with small test coefficients, not proofs.

## What is not claimed

The packages say, in their own words (exceptions noted):

- **No new formal result.** The new reductions are ordinary proofs with
  finite audits. They are not Lean or Rocq theorems, and the endpoint
  builds were not rerun. 18 lists binding its specialization to the Lean
  theorem `Jones1982.Nine.wset_iff_nine` as future work.
- **No consistency proof.** The theorems are equivalences. Every package
  except 20 explicitly declines the stronger "neither side is provable",
  which needs an extra soundness hypothesis.
- **Domains.** Positive-domain formulas must not be read over ℤ. 18's
  nine-variable equation is over ℕ, and its final witness must not be
  negative. Integer forms are separate constructions with their own
  positivity arguments.
- **Coefficients.** Only 19's and 20's are materialized.
  - Materialization confirms the bytes of a recipe, not the inherited
    compiler, the K215 endpoint or consistency (20
    `coefficients/expanded/README.txt`).
  - 19 says its small gzip size is "not a small-coefficient claim" in the
    height sense.
  - The other recipes are exact and finite but not expanded.
- **No optimality, no fewer operations.** No global minimum is claimed, and
  nothing below 67 operations. 18's nine-variable form is a concrete
  specialization of Jones's theorem, not a new representation theorem.
- **No new universal bound.** 17, 18, 20, 21, 22 and 23 say so, in various
  words. In any case,
  fixed-input constructions do not change the universal 84-operation
  frontier recorded in `Computability/HilbertTenthProblem/README.md`.

## Relation to the formal developments

- **Machine endpoint.** The packages rest on the ordinary K215 calibration
  that the Lean/Rocq endpoint
  `KEndpoint215.blank_halts_iff_zfc_refutation`
  (`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`,
  present at `HEAD`, not rebuilt at intake) mirrors. The ZFC-provability
  claim does not go through Lean's soundness.
- **Hilbert's tenth problem.** The parametric Lean theorem
  `Jones1982.Nine.wset_iff_nine`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean:46`)
  is the one 18 instantiates on paper. Its literal-weight comparison
  variant is an instance on the 32-unknown quartic; the headline
  new-weight polynomial (degree 161844·5^33 + 484) also relies on 18's
  unformalized majorant and two-radical finalizer lemma. The existence
  theorem `Jones1982.nine_unknowns` is not instantiated: it fixes ν = 58
  internally (`NineMain.lean:126-146`, checked at intake). Wave 2 had left
  a concrete nine-unknown specialization open, as recorded in the
  project README. 18 supplies one on paper, with expanded DAGs and residue
  checks; nothing of it is formalized. The
  native compiler notes under
  `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`
  remain unformalized.
- **Nothing in this report is formalized.**

## Delivery discrepancies

These are disclosed here and were not fixed in the delivered files.

- **Drivers fail in place.** Every package's verification driver reads files
  that are not in this tree: omitted repository copies, such as the vendored
  `k215.tm` and `KEndpoint215.lean` (see `PLACEMENT.md`), or ignored
  checksum ledgers. The drivers are:

  | Dir | Driver |
  |---|---|
  | 16 | `verify.py` (via `compiler/pruned_t4_check.py`) |
  | 17 | `verification/check_package.py` |
  | 18 | `reproduce.py` |
  | 19 | `verify_package.py` |
  | 20 | `verify.py` |
  | 21 | `verify.py` |
  | 22 | `code/reproduce.py` (via `code/check_bundle.py`) |
  | 23 | `reproduce.py` |

  Rerun from the arrival commit, as `PLACEMENT.md` explains.
- **Licence and attribution.**
  - 19 ships no licence or notice file, and 20 states no licence for its new
    material (it only retains `LICENSE.ProveIt`). Both were delivered for
    ProveIt; the repository's MIT-0 default applies unless Vladimir decides
    otherwise.
  - 16 and 21 state "OpenAI-assisted" research; 17 and 23 state AI
    assistance; 22 records "parallel assistant reviews"; 17's and 18's
    notices disclaim human authorship; 19 and 20 carry no AI-assistance
    statement.
  - 19 calls wave-2 package 15 "our previous round-two release".
  - 17's `machine/NOTICE.md` links to `machine/provenance/` and
    `machine/licenses/`, which its archive does not contain.
- **Inside the packages.**
  - 20's `domains/DOMAIN_REDUCTION_PROOF.md` still headlines a "46 at degree eight"
    octic that its `domains/README.txt` calls dominated. It also cites a
    "separate 28-variable construction" that it does not contain.
  - 21's bibliography mistitles package 14.
  - 22's `proofs/FINAL_TEX_AUDIT.md` mentions a "known erroneous draft S59
    section"; the delivered TeX carries the prescribed replacement.
  - 22's README suggests the directory name `16-monic12/`, as 17's suggests
    `16-primitive12/`.
  - 23's `proofs/INDEPENDENT_TWELVE_AUDIT_COMPILER.md` is byte-identical to
    `INDEPENDENT_TWELVE_AUDIT.md`, and its
    `coefficients/compiler5263_section.tex` is an alternate section not
    included by `report.tex`.
- **Retained intermediates and fallbacks.**
  - 16's prose-only 28ℤ fallback.
  - 17's old-anchor 5^17 row.
  - 19's dominated twelve-unknown variants and its unshipped 25.8 MB 5^11
    fallback.
  - 20's secondary packets.
  - 22 labels its 13-unknown forms "intermediate", although they are
    frontier points (degree 319 and 288) in the table above.
- **Not delivered.** 18 describes, but does not deliver, the positive-domain
  shift and the integer conversion of its nine-variable equation. 19's
  exploratory scripts need NumPy. 20's `verify.py` needs SymPy, and its
  `requirements.txt` (`sympy==1.14.0`) was omitted as a byte copy of a
  repository file.

## Further questions and research

These are the open problems the packages list, merged and credited:

1. **Formalize the bridge**: the primitive-element, saturation,
   separating-map, monic and denominator lemmas, the native-window/Pell
   bridge, and 18's binding to `Jones1982.Nine.wset_iff_nine` with its
   majorant lemma (16, 17, 18, 19, 22, 23).
2. **Fewer unknowns**: 11 positive (19). 16 asked for fewer than 13
   positive and 27 integers, which other wave-3 packages already reach.
3. **Lower degree and cost at 12 unknowns**: sharpen or reduce the
   separating weights while keeping their signed bounds (17, 23); norm
   cost (19); combine outer-root amalgamation with the signed domain (20).
4. **Smaller coefficients**: joint alphabet and anchor optimization (17),
   smaller geometry (16), coefficient height rather than byte size (19);
   compile the smaller proof calculus directly (23).
5. **Fewer than 67 operations** (16, 19).
6. **The quartic**: a bounded search by 19 failed to go below 32 positive
   unknowns; 18 asks for a smaller normalized quartic, which would shrink
   its nine-variable degree.
7. **Remove a positivity guard** (17); further elimination needs a new
   integrality argument (22).

## Licence and provenance

Every package was prepared for ProveIt and reuses MIT-0 repository material
(19 and 20 state none for their new material; see above). Every licence,
notice and attribution file the packages ship is kept in place. Seven such
files in 18's `upstream/machine/` were first omitted as repository copies;
they were restored after the audit.

| Pin | Arrival | Placement |
|---|---|---|
| `f0ae4e0991ca44a7bb4e5671d42e33d775e48035` | `cbf94cb552` | `da064316ea` |

## Files

Every staged file, grouped by source directory (generated from the tree):

- `16-integer27/`: `COEFFICIENT_BINDING.json`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `SYMBOLS.json`, `report.pdf`, `report.tex`, `verify.py`
- `16-integer27/compiler/`: `pruned_t4_check.py`, `pruned_t4_constants.json`, `pruned_t4_receipt.json`, `pruned_t4_windows.json`
- `16-integer27/data/`: `improved_weight_polynomial13_84.json`, `improved_weight_system13_78.json`, `integer27_weighted_root_polynomial139.json`, `integer27_weighted_root_system133.json`
- `16-integer27/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`
- `16-integer27/proofs/`: `COEFFICIENT_TRANSFER_REVIEW.md`, `IMPROVED_WEIGHT_PROOF.md`, `INDEPENDENT_PRUNED_T4_REVIEW.md`, `INTEGER27_PROOF.md`, `PRUNED_T4_PROOF.md`
- `16-integer27/src/`: `audit_positive.py`, `build_integer.py`, `build_positive.py`
- `16-integer27/upstream/`: `BASELINE_COEFFICIENTS.json`, `BLANK_HELICAL_PROOF.md`, `COMPARISON_AT_PIN.md`, `FIXED_BLANK_PROOF.md`, `PELL_LEMMA_AUDIT.md`, `ROOT_AMALGAMATION_PROOF.md`, `SIGNED_DOMAIN_PROOF.md`, `SIGNED_QUOTIENT_ABSORPTION.md`, `SIGNED_QUOTIENT_SOUNDNESS.md`, `T4_COEFFICIENTS.json`, `T4_COMPILER_PROOF.md`
- `16-integer27/upstream/arithmetic/`: `polynomial13_84.json`, `system13_78.json`
- `16-integer27/verification/`: `document_review.json`, `integer27.json`, `positive13.json`, `positive13_independent.json`, `summary.json`
- `17-primitive12/`: `INSTANCE.json`, `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `report.pdf`, `report.tex`
- `17-primitive12/arithmetic/`: `baseline67.json`
- `17-primitive12/arithmetic/integer26/`: `build_integer26.py`, `integer26_independent_verification.json`, `verify_integer26.py`
- `17-primitive12/arithmetic/integer26/generated/`: `integer26_product.json`, `integer26_sos.json`, `integer26_system.json`, `receipt.json`
- `17-primitive12/arithmetic/integer27/`: `build_integer27.py`, `integer27_checks.json`, `integer27_product139.json`, `parent_polynomial13_84.json`
- `17-primitive12/arithmetic/primitive12/`: `build_primitive12.py`, `verify_primitive12.py`
- `17-primitive12/arithmetic/primitive12/generated/`: `independent_verification.json`, `primitive12_product.json`, `primitive12_sos.json`, `primitive12_system.json`, `receipt.json`
- `17-primitive12/compiler/`: `COEFFICIENT_RESIDUES.md`, `PRUNED_T4_CONSTANTS.json`, `PRUNED_T4_PROOF.md`, `check_pruned_t4.py`, `coefficient_residue_verification.json`, `coefficient_residues.py`, `k215_transitions.json`, `pruned_t4_verification.json`, `pruned_t4_windows.json`
- `17-primitive12/inherited/`: `BLANK67_PROOF.md`, `BLANK_HELICAL_PROOF.md`, `COMPARISON_AT_PIN.md`, `ORDINARY_BLANK_PROOF.md`, `ORIGINAL_BLANK_CONSTANTS.json`, `PELL_LEMMA_AUDIT.md`, `ROOT_AMALGAMATION_PROOF.md`, `SIGNED_DOMAIN_PROOF.md`, `T4_BRIDGE_AUDIT.md`, `T4_CONSTANTS.json`, `polynomial13_84.json`
- `17-primitive12/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`
- `17-primitive12/machine/`: `NOTICE.md`
- `17-primitive12/proofs/`: `INTEGER26_INDEPENDENT_REVIEW.md`, `INTEGER26_PROOF.md`, `INTEGER27_INDEPENDENT_REVIEW.md`, `INTEGER27_PROOF.md`, `PRIMITIVE12_INDEPENDENT_REVIEW.md`, `PRIMITIVE12_PROOF.md`, `PRUNED_T4_PROOF.md`
- `17-primitive12/sections/`: `compiler.tex`, `integers.tex`, `overview.tex`, `primitive.tex`, `references.tex`, `verification.tex`
- `17-primitive12/verification/`: `INTEGER27_INDEPENDENT_CHECKS.json`, `check_package.py`, `package_checks.json`, `run_summary.json`
- `18-jones9/`: `COEFFICIENT_BINDINGS.json`, `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `RESULTS.json`, `report.pdf`, `report.tex`, `reproduce.py`
- `18-jones9/base/`: `index_bound_s.json`, `normalized_quartic32.json`, `quartic32.upstream.json`
- `18-jones9/code/`: `build_base.py`, `fixed_coefficients.py`
- `18-jones9/coefficients/`: `T4_CONSTANTS.upstream.json`, `t4_windows.json`
- `18-jones9/direct12/`: `PROOF.md`, `README.md`, `algebra12_build.py`, `algebra12_verify.py`, `radical12_checks.json`, `radical12_product.json`, `radical12_system147.json`, `section.tex`
- `18-jones9/integer27/`: `PROOF.md`, `SOURCES.json`, `VERIFICATION.json`, `build_integer27.py`, `integer27_product136.json`, `integer27_product137.json`, `integer27_section.tex`, `integer27_system130.json`, `integer27_system131.json`
- `18-jones9/integer27/upstream/`: `independent_signed_review.md`, `polynomial13_84.json`, `polynomial13_lowweight85.json`, `signed_domain_proof.md`
- `18-jones9/nine/`: `README.md`, `check_nine.py`, `nine_compressor.py`, `nine_section.tex`, `verify_fixed_instance.py`
- `18-jones9/nine/generated/`: `constants.json`, `index_bound_s.json`, `nine_checks.json`, `nine_literal_dag.json`, `nine_majorant_dag.json`, `shifted_quartic.json`
- `18-jones9/proofs/`: `comparison_audit.md`, `independent_review.md`, `nine_source_audit.md`
- `18-jones9/upstream/`: `README.md`, `SOURCES.json`, `_catalog_entries.json`, `_copied_content_comparison.json`, `_notices_payload.json`
- `18-jones9/upstream/licenses/`: `LICENSE.ProveIt`
- `18-jones9/upstream/machine/`: `NOTICE.md`
- `18-jones9/upstream/machine/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `SOURCE_PINS.json`
- `18-jones9/upstream/machine/provenance/partial-selector/`: `NOTICE.md`
- `18-jones9/upstream/machine/provenance/partial-selector/provenance/`: `ATTRIBUTION.md`, `k217-NOTICE.md`, `parent-ATTRIBUTION.md`
- `18-jones9/upstream/machine/provenance/permuted-commands/provenance/`: `ATTRIBUTION.md`, `K218_NOTICE.md`, `PREDECESSOR_ATTRIBUTION.md`
- `18-jones9/upstream/reports/09-combined13/arithmetic/`: `build_candidates.py`, `p67_source.json`
- `18-jones9/upstream/reports/09-combined13/low_degree/`: `quartic32.json`
- `18-jones9/upstream/reports/09-combined13/proofs/`: `AUDIT_STATUS.md`, `INDEPENDENT_ROOT13_AUDIT.md`, `LOW_DEGREE_PROOF.md`, `ROOT_AMALGAMATION_PROOF.md`
- `18-jones9/upstream/reports/09-combined13/upstream/compiler/`: `06_blank_helical_proof.md`
- `18-jones9/upstream/reports/12-gap-norm14/proofs/`: `GAP_AUXILIARY_PROOF.md`, `ORDINARY_BLANK_PROOF.md`
- `18-jones9/upstream/reports/12-gap-norm14/upstream/`: `fixed_blank_67_proof.md`, `pell_lemma_audit.md`
- `18-jones9/upstream/reports/14-integer29/dependencies/`: `ordinary_pell_interface.md`
- `18-jones9/upstream/reports/14-integer29/proofs/`: `independent_signed_review.md`, `ordinary_strong.md`, `signed_domain_proof.md`
- `18-jones9/upstream/reports/`: `COMPARISON_README.md`
- `18-jones9/upstream/t4/bridge/`: `BRIDGE_AUDIT.md`, `T4_CONSTANTS.json`, `check_t4.py`, `t4_verification.json`, `t4_windows.json`
- `18-jones9/upstream/t4/bridge/sources/`: `blank_helical.py`, `compiler_constants.py`, `k215_audit_notes.md`, `k215_transitions.json`, `proof_dependencies.json`
- `18-jones9/upstream/t4/review/`: `INDEPENDENT_T4_CHECKS.json`, `independent_t4_checks.py`
- `18-jones9/verification/`: `PACKAGING_REPLAY.json`, `PDF_QA.json`, `REPRODUCE.json`, `T4_REPLAY.json`, `base.json`, `fixed_coefficients.json`, `nine_fixed_instance.json`
- `19-wang943/`: `COEFFICIENT_BINDING.json`, `FINAL_FORMS.json`, `PORTABILITY_TRANSFORMS.json`, `README.md`, `RELEASE_CHECKS.json`, `verify_package.py`, `verify_worktree.py`
- `19-wang943/arithmetic/`: `GROUPED_AUDIT.json`, `GROUPED_TRADEOFF_PROOF.md`, `build_grouped_tradeoffs.py`, `grouped_auxgap75_degree50.json`, `grouped_doublegap76_degree44.json`, `grouped_firstgap73_degree70.json`, `grouped_ordinary72_degree80.json`, `search_elimination.py`, `search_first_3.json`, `search_first_4.json`, `search_first_main_3.json`, `search_first_main_4.json`, `search_raw_3.json`, `search_raw_4.json`
- `19-wang943/arithmetic/upstream/`: `GAP_AUXILIARY_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `SOURCE_PINS.json`, `ordinary_blank69.json`, `ordinary_blank_system60.json`, `ordinary_gap70.json`, `quartic32.json`, `quartic32_proof.md`, `start_only_ordinary69_system.json`
- `19-wang943/audit/`: `COMPILER_PORT_BINDINGS_CHECKS.json`, `FINAL_MATH_INDEPENDENT_CHECKS.json`, `FINAL_WEIGHTS_AND_INTEGER26_AUDIT.md`, `FOUR_ROOT12_INDEPENDENT_AUDIT.md`, `INTEGER27_INDEPENDENT_AUDIT.md`, `INTEGER27_INDEPENDENT_CHECKS.json`, `INTEGER28_VARIANTS_INDEPENDENT_AUDIT.md`, `RATIONAL_AUXILIARY_PELL_SATURATION.md`, `UNSCALED_FINAL_CIRCUIT_CHECKS.json`, `UNSCALED_SATURATION12_26_AUDIT.md`, `UNSCALED_SATURATION_CHECKS.json`, `WANG943_COMPACT_INDEPENDENT_CHECKS.json`, `WANG943_INDEPENDENT_AUDIT.md`, `WANG943_INDEPENDENT_CHECKS.json`, `audit_compiler_port_bindings.py`, `audit_wang943_compact_independent.py`, `audit_wang943_independent.py`, `check_final_math_independent.py`, `check_unscaled_final_circuits.py`
- `19-wang943/compiler/`: `COMPACT_COEFFICIENT_BINDING.json`, `COMPACT_PAYLOAD_MANIFEST.json`, `COMPACT_REPRODUCE.md`, `SOURCE_PINS.json`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `build_wang943.py`, `build_wang943_compact.py`, `check_wang_helices.py`, `materialize_wang943.py`, `materialize_wang943_compact.py`, `wang943_compact_layout.json`, `wang943_compact_materialization_receipt.json`, `wang943_compact_receipt.json`, `wang943_independent_language_receipt.json`, `wang943_layout.json`, `wang943_materialization_receipt.json`, `wang943_receipt.json`, `wang943_tiles.json`
- `19-wang943/compiler/coefficients_compact/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `19-wang943/compiler/exploration/`: `search_compact_layout.py`
- `19-wang943/compiler/upstream/`: `BRIDGE_AUDIT.md`, `T4_CONSTANTS.json`, `check_t4.py`, `report.tex`, `t4_windows.json`
- `19-wang943/integers/`: `COEFFICIENT_BINDINGS.json`, `COEFFICIENT_TRANSFER.md`, `FULL_INTEGER_REPLAY.json`, `INTEGER26_CHECKS.json`, `INTEGER26_PROOF.md`, `INTEGER26_UNSCALED_CHECKS.json`, `INTEGER26_UNSCALED_PROOF.md`, `INTEGER27_CHECKS.json`, `INTEGER27_PROOF.md`, `INTEGER28_AMALGAM_CHECKS.json`, `INTEGER28_AMALGAM_PROOF.md`, `INTEGER28_CHECKS.json`, `INTEGER28_PROOF.md`, `README.md`, `SOURCE_MANIFEST.json`, `build_integer26.py`, `build_integer26_unscaled.py`, `build_integer27.py`, `build_integer28.py`, `build_integer28_amalgam.py`, `integer26_four_root194_degree3185.json`, `integer26_unscaled_four_root192_degree2465.json`, `integer27_weighted_root136_degree1116.json`, `integer28_gap_norm127_degree426.json`, `integer28_normalized_amalgam128_degree258.json`, `replay_integer_forms.py`, `verify_integer26.py`, `verify_integer26_unscaled.py`, `verify_integer27.py`, `verify_integer28.py`, `verify_integer28_amalgam.py`
- `19-wang943/integers/upstream/09-combined13/arithmetic/`: `amalgam14_product76.json`, `polynomial13_84.json`
- `19-wang943/integers/upstream/09-combined13/proofs/`: `INDEPENDENT_ROOT13_AUDIT.md`, `ROOT_AMALGAMATION_PROOF.md`
- `19-wang943/integers/upstream/12-gap-norm14/arithmetic/`: `blank14_gap_norm75.json`
- `19-wang943/integers/upstream/12-gap-norm14/`: `gap_root_elimination.tex`
- `19-wang943/integers/upstream/14-integer29/`: `README.md`
- `19-wang943/integers/upstream/14-integer29/proofs/`: `signed_domain_proof.md`
- `19-wang943/integers/upstream/14-integer29/vendor/blank67/`: `k215_constants.json`
- `19-wang943/report/`: `PDF_QA.json`, `build_report.sh`, `primary_circuit.tex`, `twelve_variable_con_zfc.pdf`, `twelve_variable_con_zfc.tex`
- `19-wang943/review/09-combined13/`: `COEFFICIENT_BINDINGS.json`, `README.md`, `TREE.json`, `con_zfc_reductions.tex`
- `19-wang943/review/09-combined13/arithmetic/`: `amalgam14_product76.json`, `amalgam14_sos81.json`, `amalgam14_system67.json`, `outer14_73.json`, `p13_initial.json`, `polynomial13_84.json`, `polynomial13_lowweight85.json`, `product14_75.json`, `sos13_89.json`, `sos13_lowweight90.json`, `system13_78.json`, `system13_lowweight79.json`
- `19-wang943/review/09-combined13/compiler/`: `README.txt`, `cross_constants.json`, `tshape_constants.json`
- `19-wang943/review/09-combined13/low_degree/`: `README.txt`, `ordinary15_system61.json`, `quartic32.json`, `retained16_system60.json`
- `19-wang943/review/09-combined13/proofs/`: `AUDIT_STATUS.md`, `COEFFICIENT_REDUCTION_PROOF.md`, `INDEPENDENT_ROOT13_AUDIT.md`, `INTEGER_QUARTIC62_INDEPENDENT_REVIEW.md`, `LOW_DEGREE_PROOF.md`, `ROOT_AMALGAMATION_PROOF.md`, `SIGNED_CORE_AND_INTEGER62.md`
- `19-wang943/review/10-synthesis14/`: `README.md`, `TREE.json`, `report.tex`
- `19-wang943/review/10-synthesis14/circuits/`: `fixed_blank_67_integer33.json`, `fixed_blank_68_integer33.json`, `ordinary_blank_four_sos_74.json`, `ordinary_blank_four_system_63.json`, `ordinary_blank_product69.json`, `ordinary_blank_sos_78.json`, `ordinary_blank_system_61.json`, `ordinary_quartic33.json`, `root14_outer73.json`, `root14_product75.json`, `root14_system69.json`
- `19-wang943/review/10-synthesis14/proofs/`: `COEFFICIENT_REVIEW.md`, `ORDINARY_REDUCTION.md`, `projected_cross_proof.md`, `signed_domain.md`
- `19-wang943/review/11-t4/`: `README.txt`, `TREE.json`, `report.tex`
- `19-wang943/review/11-t4/bridge/`: `BRIDGE_AUDIT.md`, `T4_CONSTANTS.json`
- `19-wang943/review/11-t4/comparison/`: `HYBRID_PROOF.md`, `HYBRID_VALIDATION.json`, `hybrid_product69.json`, `hybrid_sos78.json`, `hybrid_system61.json`, `product67_T4.json`
- `19-wang943/review/11-t4/reduction/`: `ODD_AUXILIARY_PROOF.md`, `SIGNED_DOMAIN_PROOF.md`, `signed31_product.json`, `signed31_sos.json`, `signed31_system.json`, `signed33_product.json`, `signed33_sos.json`, `signed33_system.json`
- `19-wang943/review/12-gap-norm14/`: `README.md`, `TREE.json`, `coefficient_recipe.tex`, `gap_auxiliary.tex`, `gap_root_elimination.tex`, `report.tex`, `root_elimination.tex`
- `19-wang943/review/12-gap-norm14/arithmetic/`: `baseline67.json`, `blank14_gap_norm75.json`, `blank14_gap_norm75_over_Z32.json`, `blank14_gap_outer75.json`, `blank14_gap_outer75_over_Z32.json`, `blank14_norm75.json`, `blank14_norm75_over_Z32.json`, `blank14_outer73.json`, `blank14_outer73_over_Z32.json`, `ordinary_blank69.json`, `ordinary_blank69_over_Z33.json`, `ordinary_blank_sos77.json`, `ordinary_blank_sos77_over_Z33.json`, `ordinary_blank_system60.json`, `ordinary_blank_system60_over_Z33.json`, `ordinary_gap70.json`, `ordinary_gap70_over_Z33.json`, `ordinary_gap_sos78.json`, `ordinary_gap_sos78_over_Z33.json`, `ordinary_gap_system61.json`, `ordinary_gap_system61_over_Z33.json`
- `19-wang943/review/12-gap-norm14/compiler/`: `cross_constants.json`, `cross_geometry_review.json`
- `19-wang943/review/12-gap-norm14/proofs/`: `CROSS_COMPILER_PROOF.md`, `GAP_AUXILIARY_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `ROOT_ELIMINATION_PROOF.md`, `quartic32_proof.md`
- `19-wang943/review/12-gap-norm14/quadratic/`: `gap_independent_review.json`, `quartic32.json`
- `19-wang943/review/13-four-cell14/`: `README.md`, `TREE.json`, `report.tex`
- `19-wang943/review/13-four-cell14/data/`: `four_cell_constants.json`
- `19-wang943/review/13-four-cell14/proofs/`: `FOUR_CELL_PROOF.md`
- `19-wang943/review/14-integer29/`: `README.md`, `TREE.json`, `report.tex`
- `19-wang943/review/14-integer29/data/`: `blank_normalized_integer29_poly119.json`, `blank_normalized_integer29_poly120.json`, `blank_ordinary_integer29_poly121.json`, `blank_ordinary_integer29_sos130.json`, `blank_ordinary_integer29_system113.json`, `blank_ordinary_poly69.json`, `blank_ordinary_quartic33.json`, `blank_ordinary_sos78.json`, `blank_ordinary_system61.json`
- `19-wang943/review/14-integer29/proofs/`: `independent_signed_review.md`, `integer29_degrees.md`, `ordinary_strong.md`, `signed_domain_proof.md`
- `19-wang943/review/15-release/`: `COEFFICIENT_BINDING.json`, `README.md`, `TREE.json`, `final_forms.csv`, `final_forms.json`
- `19-wang943/review/15-release/report/`: `combined_con_zfc.tex`, `integer_results.tex`, `verification_results.tex`
- `19-wang943/review/`: `FETCHED_FILES.json`, `FETCHED_FINAL.json`, `FETCHED_MORE.json`, `INDEPENDENT_GATE_AUDIT.json`, `README.upstream.md`, `REVIEW_FINDINGS.md`, `SOURCE_PINS.json`, `independent_gate_audit.py`
- `19-wang943/root/`: `ADDITIONAL_MATHEMATICAL_REVIEW.md`, `COEFFICIENT_BYTE_QA.json`
- `19-wang943/roots/`: `COEFFICIENT_BINDING.json`, `MANIFEST.json`, `README.md`, `ROOT12_PROOF.md`, `ROOT12_SATURATED_PROOF.md`, `ROOT12_TEST_RESULTS.json`, `SOURCE_PINS.json`, `build_root12.py`, `check_root12.py`, `root12_product.json`, `root12_saturated_product.json`, `root12_saturated_system.json`, `root12_scaled_y_product.json`, `root12_scaled_y_system.json`, `root12_system.json`
- `19-wang943/roots/upstream/arithmetic/`: `amalgam14_system67.json`, `polynomial13_84.json`, `polynomial13_lowweight85.json`
- `19-wang943/roots/upstream/proofs/`: `INDEPENDENT_ROOT13_AUDIT.md`, `ROOT_AMALGAMATION_PROOF.md`
- `20-root12/`: `INSTANCE.json`, `LICENSE.ProveIt`, `NEGATIVE_CONTROLS.json`, `PDF_QA.json`, `README.md`, `VERIFICATION.json`, `instance_binding.py`, `negative_controls.py`, `report.pdf`, `report.tex`, `verify.py`
- `20-root12/amalgamation/`: `ROOT12_CHECKS.json`, `ROOT12_PROOF.md`, `build_root12.py`, `main_root12_product.json`, `main_root12_sos.json`, `main_root12_system.json`
- `20-root12/amalgamation/dependencies/`: `09_ROOT_AMALGAMATION_PROOF.md`, `FETCH_PROVENANCE.json`, `RATIONAL_AUXILIARY_PELL_LEMMA.md`, `complete84_signed_quotient_absorption.md`, `complete84_signed_quotient_soundness_scout.md`
- `20-root12/arithmetic/`: `INTEGER27_PROOF.md`, `SMALL_WEIGHT_PROOF.md`, `build_integer27.py`, `build_smallweight.py`, `integer27_product136.json`, `integer27_product136_smallweight.json`, `integer27_sos141.json`, `integer27_sos141_smallweight.json`, `integer27_system130.json`, `integer27_system130_smallweight.json`, `integer27_verification.json`, `polynomial13_84_smallweight.json`, `smallweight_verification.json`, `sos13_89_smallweight.json`, `system13_78_smallweight.json`
- `20-root12/arithmetic/sources/09-combined13/arithmetic/`: `build_candidates.py`, `polynomial13_84.json`, `sos13_89.json`, `system13_78.json`
- `20-root12/arithmetic/sources/09-combined13/proofs/`: `INDEPENDENT_ROOT13_AUDIT.md`, `ROOT_AMALGAMATION_PROOF.md`
- `20-root12/arithmetic/sources/09-combined13/upstream/`: `06_k215_constants.json`
- `20-root12/arithmetic/sources/12-gap-norm14/arithmetic/`: `baseline67.json`, `build_improved.py`, `ordinary_blank_system60.json`
- `20-root12/arithmetic/sources/12-gap-norm14/proofs/`: `GAP_AUXILIARY_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `ROOT_ELIMINATION_PROOF.md`
- `20-root12/arithmetic/sources/14-integer29/proofs/`: `independent_signed_review.md`, `signed_domain_proof.md`
- `20-root12/coefficients/`: `COEFFICIENTS.json`, `COEFFICIENT_PROOF.md`, `README.txt`, `audit_compact.py`, `build_coefficients.py`, `independent_audit.json`, `independent_count.json`, `independent_count.py`, `load_coefficients.py`, `tiles4094.json`, `verification.json`
- `20-root12/coefficients/expanded/`: `K.bin`, `MANIFEST.json`, `MC.bin`, `MF_source.bin`, `README.txt`, `beta.bin`
- `20-root12/coefficients/sources/`: `k215_transitions.json`
- `20-root12/coefficients/sources/t4-bridge/`: `BRIDGE_AUDIT.md`
- `20-root12/coefficients/sources/t4-bridge/sources/`: `k215_audit_notes.md`, `proof_dependencies.json`
- `20-root12/domains/`: `DOMAIN_CHECKS.json`, `DOMAIN_REDUCTION_PROOF.md`, `LICENSE.ProveIt`, `ORIGINAL_COEFFICIENTS.json`, `README.txt`, `TRADEOFF_CHECKS.json`, `build_domains.py`, `build_tradeoffs.py`, `integer34_degree16.json`, `integer35_degree12.json`, `integer37_degree10.json`, `integer39_degree8.json`, `integer45_degree6.json`, `integer46_octic.json`, `integer54_quartic.json`, `sparse_poly.py`
- `20-root12/domains/sources/12-gap-norm14/proofs/`: `quartic32_proof.md`
- `20-root12/domains/sources/12-gap-norm14/quadratic/`: `build_quartic32.py`, `quartic32.json`
- `20-root12/domains/sources/14-integer29/data/`: `blank_ordinary_system61.json`
- `20-root12/domains/sources/14-integer29/dependencies/`: `blank_helical_proof.md`, `fixed_blank_67_proof.md`
- `20-root12/domains/sources/14-integer29/proofs/`: `independent_signed_review.md`, `signed_domain_proof.md`
- `20-root12/domains/sources/14-integer29/src/`: `build_integer29.py`
- `20-root12/domains/sources/14-integer29/vendor/blank67/`: `blank_helical.py`, `compiler_constants.py`, `k215_transitions.json`
- `20-root12/domains/sources/15-release/evidence/diophantine_zfc_round2/integers/`: `SIGNED_DOMAIN_PROOF.md`
- `20-root12/domains/sources/15-release/evidence/diophantine_zfc_round2/quadratic/`: `LOW_DEGREE_PROOF.md`, `ordinary_octic20.json`, `start_only_sextic25.json`
- `20-root12/domains/sources/15-release/`: `final_forms.json`
- `20-root12/domains/sources/`: `complete75_asymmetric_scale_tradeoffs.md`, `pell_kernel_half_binomial42.md`
- `20-root12/review/`: `LOW_DEGREE_INDEPENDENT_CHECKS.json`, `RATIONAL_AUXILIARY_PELL_LEMMA.md`, `ROOT12_INDEPENDENT_CHECKS.json`, `SMALLWEIGHT_INDEPENDENT_CHECKS.json`, `check_low_degree_independent.py`, `check_root12_independent.py`, `check_smallweight_independent.py`
- `21-norm12/`: `COEFFICIENT_BINDING.json`, `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_MANIFEST.json`, `report.pdf`, `report.tex`, `verify.py`
- `21-norm12/arithmetic/`: `build_norm12.py`, `build_norm12_lower_degree.py`, `norm12_checks.json`, `norm12_lower_degree_checks.json`, `norm12_product.json`, `norm12_product_integer26.json`, `norm12_product_lower_degree.json`, `norm12_sos.json`, `norm12_sos_integer26.json`, `norm12_sos_lower_degree.json`, `norm12_system.json`, `norm12_system_integer26.json`, `norm12_system_lower_degree.json`
- `21-norm12/coefficients/`: `COEFFICIENTS.json`, `README.md`, `REDUCED_T4_PROOF.md`, `check_reduced.py`, `check_t4.py`, `explore_t4.py`, `reduced_t4_receipt.json`, `reduced_t4_windows.json`
- `21-norm12/coefficients/licenses/`: `LICENSE.ProveIt`
- `21-norm12/coefficients/sources/`: `k215_transitions.json`
- `21-norm12/proofs/`: `COEFFICIENT_ADAPTER_REVIEW.md`, `INTEGER26_PROOF.md`, `NORM12_INDEPENDENT_AUDIT.md`, `NORM12_LOWER_DEGREE.md`, `NORM12_PROOF.md`, `REDUCED_T4_PROOF.md`
- `21-norm12/upstream/`: `BLANK_HELICAL_PROOF.md`, `FIXED_BLANK_67_PROOF.md`, `K215_AUDIT_NOTES.md`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `ORDINARY_BLANK_PROOF.md`, `PELL_LEMMA_AUDIT.md`, `PRODUCT67.json`, `REPOSITORY_COMPARISON.md`, `ROOT_AMALGAMATION_13.md`, `SIGNED_DOMAIN_29.md`, `SIGNED_DOMAIN_29_REVIEW.md`, `T4_BRIDGE_AUDIT.md`, `T4_CONSTANTS.json`
- `21-norm12/verification/`: `INDEPENDENT_CIRCUIT_AUDIT.json`, `PACKAGE_QA.json`, `REPRODUCTION.json`, `audit_norm12.py`
- `22-monic12/`: `MANIFEST.sha256`, `Makefile`, `README.md`, `SOURCE_PROVENANCE.json`, `con_zfc_synthesis.pdf`, `con_zfc_synthesis.tex`
- `22-monic12/code/`: `build_integer26.py`, `build_mergers.py`, `build_retained59.py`, `check_bundle.py`, `check_strict_independent.py`, `coefficient_recipe.py`, `reproduce.py`, `sparse_polynomial.py`, `strict_compiler.py`
- `22-monic12/data/`: `COEFFICIENT_BINDING.json`, `REPRODUCTION.json`, `audit_integer26.json`, `bundle_checks.json`, `coefficient_residues.json`, `integer26_product.json`, `integer26_system.json`, `k215_transitions.json`, `merger12_product.json`, `merger12_system.json`, `merger13_product.json`, `merger13_system.json`, `merger_checks.json`, `pdf_build.json`, `retained16_system59.json`, `retained16_system60.json`, `retained59_checks.json`, `strict_compiler_checks.json`, `strict_independent_checks.json`, `strict_windows.json`
- `22-monic12/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE.md`, `NOTICE_K215.md`
- `22-monic12/proofs/`: `FINAL_TEX_AUDIT.md`, `INDEPENDENT_TWELVE_REVIEW.md`, `RETAINED59_PROOF.md`, `STRICT_COMPILER_REVIEW.md`, `integer26_proof.md`, `merger_proof.md`, `report_transcription_audit.md`
- `22-monic12/reference/`: `blank_helical_proof.md`, `comparison_at_pin.md`, `fixed_blank_67_proof.md`, `ordinary_signed_proof.md`, `pell_lemma_audit.md`, `retained_low_degree_proof.md`, `signed_domain_proof.md`, `t4_compiler_proof.md`, `t4_windows.json`, `weighted_root_proof.md`
- `23-separating12/`: `COEFFICIENT_BINDING.json`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_MANIFEST.json`, `comparison.csv`, `report.pdf`, `report.tex`, `reproduce.py`
- `23-separating12/code/`: `audit_integer26.py`, `build_integer26.py`, `build_integer27.py`, `build_twelve.py`
- `23-separating12/code/inputs/`: `blank_normalized_integer29_poly119.json`, `blank_normalized_integer29_poly120.json`, `blank_ordinary_integer29_poly121.json`, `blank_ordinary_integer29_sos130.json`, `blank_ordinary_integer29_system113.json`, `ordinary_blank_sos77.json`, `ordinary_blank_system60.json`
- `23-separating12/coefficients/`: `LICENSE.ProveIt`, `REFINED_COMPILER_PROOF.md`, `T5263_CONSTANTS.json`, `compiler5263.py`, `compiler5263_section.tex`, `k215_transitions.json`, `verification5263.json`, `windows5263.json`
- `23-separating12/data/integer26/`: `polynomial26.json`, `residual_system26.json`, `sos26.json`, `system26.json`, `verification26.json`
- `23-separating12/data/`: `integer26_independent_checks.json`, `polynomial12.json`, `residual_system12.json`, `sos12.json`, `system12.json`, `verification12.json`
- `23-separating12/data/integer27/`: `normalized27_poly114.json`, `normalized27_poly115.json`, `ordinary27_poly116.json`, `ordinary27_sos124.json`, `ordinary27_system107.json`, `verification.json`
- `23-separating12/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`
- `23-separating12/proofs/`: `INDEPENDENT_COEFFICIENT_AUDIT.md`, `INDEPENDENT_INTEGER26_AUDIT.md`, `INDEPENDENT_TWELVE_AUDIT.md`, `INDEPENDENT_TWELVE_AUDIT_CIRCUIT.md`, `INDEPENDENT_TWELVE_AUDIT_COMPILER.md`, `INTEGER26_PROOF.md`, `ODD_SCALE_27_PROOF.md`, `TWELVE_VARIABLE_PROOF.md`
- `23-separating12/sections/`: `coefficients.tex`, `integer27.tex`, `logic_verification.tex`, `twelve.tex`
- `23-separating12/upstream/`: `KEndpoint215.lean`, `NineMain.lean`, `T4_bridge_audit.md`, `T4_constants.json`, `baseline_p67.json`, `baseline_quartic32.json`, `blank_helical_proof.md`, `catalogue_README.md`, `k215_audit_notes.md`, `normalized_blank_proof.md`, `ordinary_strong_proof.md`, `pell_interface_lemmas.md`, `pell_lemma_audit.md`, `previous_low_degree_proof.md`, `previous_root13_proof.md`, `signed_domain_29.md`, `signed_domain_core.md`, `signed_quotient_absorption.md`, `signed_quotient_soundness.md`
- `23-separating12/verification/`: `PDF_QA.json`, `REPRODUCTION.json`
- top level: `README.md` (this file), `PLACEMENT.md`
