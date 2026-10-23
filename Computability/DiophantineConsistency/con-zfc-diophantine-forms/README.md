# Con(ZFC) in Diophantine form

This collection lives under `Computability/DiophantineConsistency`. It was
moved there on 23 October 2026 (`ea8ae71167`, at Vladimir's request) from
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
Paths in pinned source ledgers and historical Git commands still refer to the
locations in those earlier commits. The delivered packages keep their
original contents. See the [active research](../README.md) for new Lean
proofs and the current status; this README covers only the delivered
manuscripts.

**Explicit polynomials with fixed integer coefficients whose unsolvability
ZFC proves equivalent to Con(ZFC). Waves 5 and 6 are both in the tree: ten
unrestricted integers at degree 237,520,456 (via Sun's reduction), nine
positive unknowns at degree about 1.3·10^8, eleven positive unknowns, and
twelve at degree 901.**

The report holds fifteen AI-assisted research packages:

- **Wave 5**, sources 31–37: batch 221 (arrival `b7f8b75b5b`, placed in
  `952c1fab49`), dated 22–23 October 2026 and pinned to `8c6eec9d19`.
- **Wave 6**, sources 38–45: batch 222 (arrival `29ca562f8f`, "Con(ZFC) in
  Diophantine form (wave-6)", placed in `124c07c0b7`), dated 23 October 2026
  and pinned to `22e75dd6b8`. At that pin the report, with wave 5's audited
  README, was still under the old path.

**Wave 5 is kept.** By Vladimir's direction (23 October 2026), wave 6 is
placed beside wave 5 rather than replacing it. Wave-6 packages cite wave-5
packages by their numbers 31–37; no wave-6 package cites another.

## Earlier waves

Waves 1–4 were each superseded by the next wave and removed from the tree.
They remain in history:

| Wave | Batch | Arrival (archives) | Directories in every commit from … to … | Audited README |
|---|---|---|---|---|
| 1 | 217 | `2fd49a1a9d` | `084e120830` … `8a4b00b5bf^` | `f3af223ef7` |
| 2 | 218 | `7be2780f26` | `8a4b00b5bf` … `da064316ea^` | `5b0c9ae9fd` |
| 3 | 219 | `cbf94cb552` | `da064316ea` … `604b1416b5^` | `a477d0fc8b` |
| 4 | 220 | `375cc6e3d7` | `604b1416b5` … `952c1fab49^` | `52f475c7a7` |
| 5 | 221 | `b7f8b75b5b` | `952c1fab49` … (kept) | `22e75dd6b8` |
| 6 | 222 | `29ca562f8f` | `124c07c0b7` … | this file |

Until `ea8ae71167`, every one of these READMEs lived at
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/README.md`.
To read one, use for example
`git show 52f475c7a7:SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/README.md`.
Results that later waves did not reproduce are listed in those READMEs, and
for wave 4 in the wave-5 section below.

## How this report was made

The packages overlap, so they are **placed, not written**
([docs/incoming/README.md](../../../docs/incoming/README.md), section 2):

- each package keeps its delivered layout and PDF in its numbered directory,
  with the wrapper removed;
- this README is the reconciliation note;
- no delivered file was edited, no PDF was built, and no delivered program
  was run at intake.

Facts are the packages' own, from read-only intake dossiers. Their scripts
also evaluated delivered circuits modulo large primes, with the actual fixed
values where available, to tell polynomials apart. Agreement at random points
is strong evidence of identity, not proof; disagreement proves the
polynomials differ.

[`PLACEMENT.md`](PLACEMENT.md) is the recovery map for both waves: the
batch-221 record, then the appended batch-222 record.

| Wave | Archive members | Staged | Omitted copies | Ignored |
|---|---:|---:|---:|---:|
| 5 | 1,197 | 1,129 | 46 | 22 |
| 6 | 1,149 | 773 | 371 | 5 |

Omitted copies are byte-identical (up to line ends) to repository files.
Most of wave 6's are copies of wave-5 files of this report, which stay in the
tree. Ignored members are checksum ledgers and logs, excluded by the root
`.gitignore`.

## The common theorem

Each package defines polynomials or small systems with four **fixed integer
coefficient ports**:

- Bm1 = B − 1;
- Kconstant = D_C + B·D_R;
- MC;
- the **shifted** MF = (native high mask) + B − 1.

The ports are determined by a finite recipe from the literal 215-state
machine
[`candidate-k215/k215.tm`](../../BusyBeaver/Research/ZFC/candidate-k215/k215.tm).
Each package proves, by ordinary mathematics formalizable in ZFC, that

> ZFC ⊢ (no solution in the stated domain) ↔ Con(ZFC).

The route:

1. The blank run of K215 halts iff ZFC has a finite refutation.
2. A local tile language of that run is compiled by the repository's
   native-window/Pell compiler
   ([`native-stream-queue/`](../../HilbertTenthProblem/Papers/research-wip/native-stream-queue/README.md)),
   with its input interface removed.
3. The **11- and 12-positive forms** are direct Pell constructions on the
   compiler source. They merge roots, separate norms and absorb indices,
   with no reduction to a quartic.
4. The **lowest-variable forms** reduce a fixed parent: wave-4 30's
   31-unknown system of 22 quadratic residuals or its quartic sum of
   squares, in coordinates such as 31's 60-operation system (z_old = z + 1).
   There are two reductions:
   - the **Matiyasevich–Jones** nine-variable reduction, for the 9ℕ and
     9-positive forms and the signed 13–17ℤ forms;
   - **Sun's** ten-integer reduction, for every 10ℤ form.

   The exception is wave-5 32's 15ℤ and 16ℤ forms, which use ν = 32 and
   package 29's T4 quartic32.

Wave 6's main new idea is to replace wave 5's exponentially spaced digit
positions 5^j by a finite additive code. The B₂ (Sidon) packages 38, 39,
40, 43 and 45 code the 22 quadratic residuals directly. The B₄
(Bose–Chowla) packages 41, 42 and 44 keep the quartic sum of squares but
place it on a B₄ set. Both cut the degree of the low-variable forms by many
orders of magnitude.

## Combined frontier, waves 5 and 6 (intake findings)

Numbers are the packages' own; **none was re-derived at intake.** "u / e / d /
o" means unknowns / equations / degree / operations. Operations count every
binary +, −, × including multiplication by fixed numerals; reuse and system
comparisons are free. Unknowns are strictly positive unless marked ℤ
(unrestricted integers) or ℕ (naturals).

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Fewest unrestricted integers (Sun's reduction) | **10ℤ at degree 237,520,456**, in 782 ops (40) or 809 (43). They are the same polynomial up to one fixed constant, the source base β_source (40's 2^2140030, 43's 2^2134940); with 43's value, 40's cheaper circuit evaluates 43's polynomial | 40, 43 | 40 |
| 10ℤ, fewest operations | **773 ops** at degree 449,607,016 (38, on its own tuple) | 38 | 38 |
| 10ℤ, other forms | 39: 267,823,432 / 786 (one circuit on two tuples). 45: 237,526,776 / 936. 41: 69,554,088,184 / 1333, the same polynomial as 44's 1407-op `sun_b4`, so 41 is a cheaper evaluator of it. 42: 107,286,763,576 / 2204. Wave-5 31: about 5.9·10^26 / 1442 | — | — |
| Fewest integers without Sun's 2026 reduction | **13ℤ** at degree 226,334,238,192, 1409 ops; and **14ℤ** at 226,295,141,096 / 1420, which dominates every wave-5 14–16ℤ form on degree and operations | 44 | 44 |
| Nine unknowns | **9 positive at degree 129,875,980, 788 ops** (791 over ℕ). Also 166,177,600 at 864 positive / 868 ℕ (38), and 23,321,536,264 / 1378 (44). All three beat wave 5's and wave 4's nine-variable forms on both measures | 45; 38; 44 | 45 |
| Eleven positive unknowns | **degree 1154, 123 ops**; two-equation system (degrees 2, 1152) at 119, shifted 118; translated product 1140 / 129. The first eleven-positive form; see the tension below | 38 only | 38 |
| Twelve positive, lowest degree | **901 / 112** (system 892 / 107, shifted 106) and 905 / 110 (shifted system 104) (44). Also 938 / 122 (system 929 / 117) (41) and 941 / 121 (system 932 / 116; alternatives 945 / 119, 949 / 116, 961 / 112) (45). All beat wave 5's 1022 | 44; 41; 45 | 44 |
| Twelve positive, fewest operations | unchanged: **108** (wave-5 31, 32, 33, 35); system **102** (31, shifted) | wave 5 | 31 |
| 31-unknown positive quartic | unchanged: system 60, SOS 125 (31) | wave 5 | 31 |
| Integer quartic | unchanged: 50ℤ (34, 37) | wave 5 | 34 |
| 24ℤ at moderate degree | unchanged: 37's 1936 / 161 | wave 5 | 37 |
| Fewest operations | **67** (P₆₇), and the 59-op 16 / 7 / 24 system, unchanged. 42 and 44 rebind both to their new tuples | — | (wave 1) |
| Smallest coefficients binding an equation | **B = 2^590069**, 295,388 raw bytes, largest port 592,884 bits. It binds 39's compact 10ℤ instance and 44's P₆₇ and 59-op system, with identical payload bytes. Next come 38's 2^678139 (339,476 bytes) and 42's 2^683195 (342,269 bytes). 40's research candidate 2^690547 binds no equation | 39, 44 | 39 |

Wave 5's own frontier, as placed, is in the wave-5 section below. The
combined table above supersedes it on the criteria wave 6 improves.

## Wave 6 (sources 38–45)

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`38-batching11/`](38-batching11/) | `con-zfc-quadratic-batching-2026-10-23.zip` | *Quadratic batching, index absorption, and smaller consistency equations* | **11 / 1 / 1154 / 123** (system 119, shifted 118; translated 1140 / 129); **9ℕ / 1 / 166,177,600 / 868** (864 positive); 10ℤ / 1 / 449,607,016 / **773**; new tuple B = 2^678139 |
| [`39-direct10/`](39-direct10/) | `ConZFC_Direct_Quadratic10_2026-10-23.zip` | *Direct quadratic coding for ZFC consistency* | 10ℤ / 1 / 267,823,432 / 786 on 31's tuple, and the same circuit on a compact tuple B = 2^590069 |
| [`40-packing10/`](40-packing10/) | `ConZFC_Quadratic_Packing_2026-10-23.zip` | *Direct quadratic packing for a ten-integer consistency equation* | **10ℤ / 1 / 237,520,456 / 782** on 31's tuple; an unfinished research-candidate tuple B = 2^690547 binding no equation |
| [`41-bose-chowla/`](41-bose-chowla/) | `ConZFC_BoseChowla_2026-10-23.zip` | *Finite additive coding for an explicit Con(ZFC) equation* (README title: 31's) | 10ℤ / 1 / 69,554,088,184 / 1333 (literal Sun finalizer: 1.32·10^12 / 1383); 12 / 1 / 938 / 122, system 929 / 117 |
| [`42-additive-b4/`](42-additive-b4/) | `ConZFC_Additive_Coding_2026-10-23.zip` | *Additive coding and smaller coefficients for Diophantine consistency equations* | 10ℤ / 1 / 107,286,763,576 / 2204 (comparison instance on 31's tuple; recommended composed instance on a new tuple B = 2^683195); P₆₇ and the 59-op system rebound |
| [`43-sidon10/`](43-sidon10/) | `con-zfc-b2-2026-10-23.zip` | *Direct quadratic block coding for Con(ZFC)* (README: *A smaller ten-integer Diophantine equation…*) | 10ℤ / 1 / 237,520,456 / 809 on 31's tuple |
| [`44-b4-sparse/`](44-b4-sparse/) | `ZFC_Diophantine_B4_Sparse_Encodings_2026-10-23.zip` | *Sparse carry encodings for the consistency of ZFC* | 10ℤ / 1 / 69,554,088,184 / 1407; 9 positive / 1 / 23,321,536,264 / 1378 (1383 ℕ); **13ℤ / 1 / 226,334,238,192 / 1409** and 14ℤ / 226,295,141,096 / 1420 without Sun's 2026 reduction; **12 / 1 / 901 / 112** (shifted system 892 / 106), 905 / 110 (shifted system 104); native tuple B = 2^590069 binding P₆₇ and the 59-op system |
| [`45-multioutput/`](45-multioutput/) | `con-zfc-multioutput-22e75dd6b8.zip` | *Simultaneous quadratic coding for ZFC consistency* | **9 positive / 1 / 129,875,980 / 788** (791 ℕ); 10ℤ / 1 / 237,526,776 / 936; 12 / 1 / 941 / 121 (system 932 / 116; alternatives 945 / 119, 949 / 116, 961 / 112) |

Directory numbers follow the archives' arrival (file-time) order. Several
packages suggest other directory names: 38, 40 and 41 each suggest slot 38,
and 43 suggests `38-b2-blocks`. 40's archive wrapper was itself named
`38-quadratic-packing`. Each directory's `README.md` is its entry point; the
article is `report.pdf` (`report/report.pdf` in 45).

### Codes and parents

| Dir | Code | Parent |
|---|---|---|
| 38, 40, 43 | the same 32-element Sidon set (maximum 799); 38's target stride is 3197, 40's and 43's 1599 | 22 quadratic residuals |
| 39 | Sidon set, maximum 901 | 22 quadratic residuals |
| 45 | 43's Sidon set, targets 1599j (one above 43's) | 31's 60-op quadratic system (`quartic31_system60.json`, z_old = z + 1) |
| 41, 44 | the same Bose–Chowla B₄ set (maximum 610,895), an affine image of 42's code | 31's quartic sum of squares |
| 42 | a B₄ code with T = 942,302, plus nonzero edge words in the compiler | 31's quartic sum of squares |

### Coefficient recipes: use one whole tuple

| Dir | Tuple | Materialized | Notes |
|---|---|---|---|
| 38 | new: B = 2^678139 (ρ = 2^77, L = 8807, padding prime 56611) | 339,476 raw bytes (gzip 8,851); κ and β_Sun materialized | bytes match no other package |
| 39 | 31's tuple (principal); compact B = 2^590069 (ρ = 2^67, prime 581197) | compact: 295,388 raw bytes | compact bytes identical to 44's native tuple |
| 40 | 31's tuple; research candidate B = 2^690547 (346,098 bytes) | 31's (copies omitted at intake); source base β_source = 2^2140030 | the candidate binds no equation |
| 41 | 31's tuple, β_Sun = 2^4269882 | copies omitted at intake | 79 fixed leaves |
| 42 | new: B = 2^683195 (ρ = 2^107, L = 6385, prime 135257) for the composed instance; 31's for the comparison instance | 342,269 raw bytes; β_S = 2^2743514 | the comparison and composed instances are one DAG on two tuples |
| 43 | 31's tuple | β_source = 2^2134940 as a recipe only | 16 recipe leaves |
| 44 | 31's tuple for the low-variable forms; native B = 2^590069 for P₆₇ and the 59-op system | native: gzip, 295,388 raw bytes | "Never splice" |
| 45 | 31's tuple | all 17 leaves of each nine/ten form materialized (3,464,120 raw bytes each) | |

Every package binds its four ports as one tuple and forbids splicing.

### Tensions, not adjudicated at intake

- **The eleven-positive form.** Several packages explicitly declined an
  eleven-positive form:
  - earlier: wave-4 24 (no identity forcing gcd(E, H) = 1), 36 and 37;
  - in this wave, 42 (`report.tex:428-437`), which names the gcd(E, H)
    obstacle and the proof-order problem that X = 2^R cannot be used
    before the packed index is recovered.

  38's argument (`38-batching11/sections/section_eleven.tex`):
  - it deletes h and N_k and keeps the weaker divisibility
    E | H(k − R − 1);
  - it recovers p = R first, which addresses 42's proof-order point;
  - it uses the modulus μ = E / gcd(E, H) > R.

  38 cites none of these remarks, and its review is a same-session AI
  review (`eleven/INDEPENDENT_REVIEW.md`). It is the result most in need of
  independent checking.
- **The square base (from wave 5).** 44's `signed_audit/COFINAL_BASE_AUDIT.md`
  says 34's and 37's square-base reductions are sound, and that 33's caution
  is correct only for a different proposal. It still argues from the proof
  lines of `Jones1982.USys_of_mem`, not from its statement. 44's own new
  front end avoids the step.
- **Sun dependence.** Every 10ℤ form depends on Sun's 2026 preprint
  (arXiv:2609.01594), as wave-5 31 did. The 9ℕ, 9-positive, 11- and
  12-positive forms, and 44's 13ℤ and 14ℤ forms, do not.
- **Smallest-tuple claims.** 38, 39, 42 and 44 each present a smaller tuple
  without knowing of each other. 39's compact tuple and 44's native tuple are
  byte-identical.
- **Inside packages.**
  - 42's README recommends the composed instance, while its Theorem 1.1
    states the comparison instance.
  - 45's two statements on its shift are consistent. One calls the zero sets
    bijective given the compiler bounds (`report/report.tex:202-204`); the
    other says the shift is not a bijection on all positive witnesses
    (`:429`).
  - 45's "83" and "84" source pins are also consistent: 83 initial-review
    checks plus construction pins.
- **No package calls wave 5 or its README wrong.**
  - 45 compares its twelve-positive system with 34's 1013 / 120 system. That
    system is real (`34-integer14/positive/SHIFTED12_PROOF.md:14`), and the
    wave-5 text below now lists it.
  - 41 cites the same system.

### Delivery discrepancies (wave 6)

- **Drivers fail in place.** Every wave-6 driver reads files omitted at
  intake or ignored ledgers. Rerun from the arrival archives, as
  `PLACEMENT.md` explains.

  | Dir | Driver | Reads |
  |---|---|---|
  | 38 | `reproduce.py` | contrary to its README |
  | 39 | `reproduce.py` | |
  | 40 | `code/verify.py` | |
  | 41 | `reproduce.py` | contrary to its README; NumPy for the positive checker |
  | 42 | `reproduce.py` and `package_release.py --check` | |
  | 43 | `reproduce.py` | contrary to its README |
  | 44 | `verify.py` | `SHA256SUMS.json` first |
  | 45 | `verify_release.py` | exact file set; SymPy and NumPy |

- **Licence and attribution.**
  - Notices of AI assistance:
    - 38: "no independent human review is asserted".
    - 39: "Prepared with AI assistance".
    - 40, 41, 44: OpenAI, "not external human endorsements". 41 names
      ChatGPT in its report.
    - 42: "no assertion of human authorship".
    - 43: ChatGPT; reviews by "separate AI work streams".
    - 45: "Human mathematical review is required".
  - 42 ships no licence file for its new material and says only "No new
    license restriction". The others ship MIT-0.
  - Every package ships the K215 machine notices (`LICENSE.Wade`,
    `NOTICE-K215`).
  - 44 calls wave-5 37 "the preceding delivery in this conversation".
- **Bundled post-pin files.** 45 bundles byte copies of
  `Computability/DiophantineConsistency/README.md` and `STATUS.md`, and 44
  bundles `STATUS.md` only. Both copies are as of `8747904f8b`, the commit
  after their pin that started the active Lean research; 45 calls it the
  "postscript". No package uses the active Lean work.
- **Retained intermediates.**
  - 38: an earlier review copy, `review/ELEVEN_INDEPENDENT_REVIEW.md`.
  - 40: the unfinished `research_candidate/`.
  - 42: dominated finalizer variants and `review/UNSUCCESSFUL_REDUCTIONS.md`.
  - 45: two nine-variable degree-certificate DAGs (803 and 806 ops) and the
    `short/` dead ends.

### Further questions (wave 6)

1. **Smaller codes.** Smaller or support-aware Sidon and B₄ sets, joint span
   and cost optimization, and support-aware targets (38, 39, 40, 41, 42, 43,
   45).
   Each unit drop in the Sidon maximum lowers 40's degree by 297,088.
2. **Formalize.** The extraction, carry decoder, signed bootstrap and
   reordered Pell-index recovery (38); the source interface (43, 45); which
   lemma to formalize first (42).
3. **Fewer unknowns.**
   - Eight naturals and nine unrestricted integers remain unsettled (38).
   - Going below ten integers needs other ideas (41).
   - B₄ coding for the nine-variable Jones route (asked by 42 and 43) is
     already delivered by 44. 38's and 45's B₂ nine-variable forms beat it.
4. **A smaller parent.** A smaller quartic or source system (39, 42, 43). 44
   found no validated thirty-variable quartic.
5. **Coefficients.** Rebinding native improvements (39), transporting 36's
   tuple (45) and finishing 40's research candidate (40).

## Wave 5 (sources 31–37)

Wave 5 is described as placed, with its frontier at that time. The
combined frontier above supersedes it where wave 6 improves on it.

### Supersession of wave 4

All seven wave-5 packages bundle a copy of the audited wave-4 README:

| Package | Copy |
|---|---|
| 31 | `sources/COLLECTION_AT_PIN.md` |
| 32 | `references/COMPARISON_AT_PIN.md` |
| 33 | `upstream/reviewed_README.md` |
| 34 | `review/README.md` |
| 35 | `sources/catalogue/README.md` |
| 36 | `evidence/COMPARISON_AT_PIN.md` |
| 37 | `sources/README.md` |

Several packages also bundle wave-4 circuits as reference material. These
copies stay bound to their original wave-4 tuples, and they describe a
superseded wave.

**Wave-4 results that wave 5 does not reproduce or rebind** (an intake
comparison by blob matching against the wave-4 tree):

| Wave-4 result | Byte copy in the wave-5 tree |
|---|---|
| 30's 25ℤ / 920 / 131 and 26ℤ / 214 / 123 forms (system 128 / 117) | `37-wave5/lowdegree/upstream/integers/` |
| 24's 24ℤ / 1936 / 167 and 26's 24ℤ / 2432 / 163 | `34-integer14/review/24-integer24/`, `34-integer14/review/26-ratio12/` |
| 27's 24ℤ / 1936 / 168 and 30's 24ℤ / 2240 / 165 | none (history only) |
| 27's nine-positive form at 1537 ops (new majorant) | `34-integer14/review/27-wave4/nine/generated/` |
| 27's 1480-op nine-positive form of 18's circuit and its literal-weight variants | none (history only) |
| 24's 13-unknown forms 319 / 89 and 288 / 81 | none (history only) |
| the 42ℤ sextic and 36ℤ octic (27, 29) | none (history only) |
| 27's 59-op systems of degree 12, 10, 8, 6 (17–20 unknowns) | none (history only) |
| the 16 / 7 / 22 / 60 system (27, 30) | none (history only) |

The byte copies of 24's, 26's and 27's circuits are bound to coefficient
tuples whose payloads are not in the tree, so in practice they too are
usable only from history. To read the results that are in history only,
use the wave-4 README and
directories at `52f475c7a7`, e.g.
`git show 52f475c7a7:SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/README.md`.
Earlier waves' lost results
are listed in their own READMEs (see the wave table).

Some earlier results remain unbeaten on their own measures:

- the 67-operation equation P₆₇ (wave 1), for fewest operations;
- the 59-operation 16 / 7 / 24 system;
- wave-2 Q₅₆ (15 / 1 / 56 / 74) and the 33ℤ / 1 / 159 / 134 polynomial;
- the history-only items above: 27's low-degree 59-operation systems, 24's
  13-unknown forms, and 27's nine-positive forms at 1480 operations
  (majorant) and 1473 (literal weights), which still have fewer
  operations than any wave-5 nine-unknown form.

36 ships P₆₇ and the 59-operation system rebound to its coefficients, and
31 bundles the 59-operation system.

### The seven wave-5 packages

Numbers are the packages' own; **none was re-derived at intake.** "u / e / d
/ o" means unknowns / equations / degree / operations, with L = 5^32.
Operations count every binary +, −, × including multiplication by fixed
numerals; reuse and system comparisons are free. Unknowns are strictly
positive unless marked ℤ (unrestricted integers) or ℕ (naturals).

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`31-sun10/`](31-sun10/) | `con_zfc_synthesis.zip` | *Smaller explicit Diophantine forms for Con(ZFC)* | **10ℤ / 1 / 126496·5^31 + 27064 / 1442** (Sun's reduction instantiated); 16ℤ / 1 / 813056·L + 10016 / 1617; 31-quartic system 22 / 2 / **60**, SOS 125; 12 / 1 / 1081 / 108, shifted system **102** |
| [`32-integer15/`](32-integer15/) | `con_zfc_fifteen_integer_synthesis_2026-10-22.zip` | *Fifteen integer unknowns and smaller coefficient tuples…* | 15ℤ / 1 / 813056·5^33 + 4184 / 1541; 16ℤ / 1 / 406528·5^33 + 10008 / 1550 (both on the T4 tuple); 12 / 1 / 1081 / 108, systems 104 and 103 |
| [`33-signed16/`](33-signed16/) | `ConZFC_Signed16_Synthesis_2026-10-22.zip` | *Sixteen integer unknowns for an explicit consistency equation* | 16ℤ / 1 / 406528·L + 10008 / 1590; 31-quartic system 61, SOS 126; 12 / 1 / 1081 / 108 (systems 104, 103); optional tuple B = 2^1012625 binding no equation |
| [`34-integer14/`](34-integer14/) | `con-zfc-fourteen-integer-8c6eec9d19.zip` | *Smaller Diophantine forms for ZFC consistency* | **14ℤ / 1 / 813056·L + 2152 / 1586**; 15ℤ / 1 / 406528·L + 2528 / 1594; **9ℕ / 9 positive at 92324·L + 296**, 1559 / 1554 ops; **12 / 1 / 1022 / 124**, 1023 / 119, 1025 / 116, 1033 / 114, 1041 / 111, 1081 / 110 (systems down to 1013 / 120, 1014 / 115, 1016 / 112, 1024 / 110); 50ℤ quartic (29 residuals) |
| [`35-cancel12/`](35-cancel12/) | `con-zfc-synthesis-2026-10-22.zip` | *Smaller explicit Diophantine forms of ZFC consistency* | 16ℤ / 1 / 813056·L + 10024 / 1865; 17ℤ / 1 / 406528·L + 27512 / 1874; 12 / 1 / 1065 / 118 (systems 114, 113); 12 / 1 / 1081 / 108 (systems 104, 103); 31-quartic system 62, SOS 127 |
| [`36-small-tuple/`](36-small-tuple/) | `con-zfc-synthesis-2026-10-22 (1).zip` | *Smaller Diophantine presentations of ZFC consistency* | **B = 2^1012115**, materialized (506,664 raw bytes); 12 / 1 / 1081 / 109 and 1069 / 120 (systems 104 / 115, shifted 103 / 114); 30's nine-variable polynomial in 1587 / 1582 ops; P₆₇ and the 59-op system rebound |
| [`37-wave5/`](37-wave5/) | `ZFC_Diophantine_Fourteen_Integers_2026-10-23.zip` | *Fourteen integer unknowns and smaller separating norms for the consistency of ZFC* | **14ℤ / 1 / 813056·L + 2752 / 1524**; 16ℤ / 1 / 406528·L + 10008 / **1537**; **9 positive / 92324·L + 296 / 1500** (1505 over ℕ) and 9 positive / 93264·L + 288 / 1498 (1503 over ℕ); 12-positive products of degree 1061, 1065, 1069, 1081 (120, 119, 117, 109 ops), systems 1052 / 114 and 1072 / 103; 24ℤ / 1 / 1936 / 161 (system 156); 50ℤ quartic (system 111, SOS 197) |

Directory numbers follow the archives' arrival (file-time) order. Each
directory's `README.md` is its entry point. The articles are `report.pdf` in
31, 32, 33, 35, 36 and 37, and `report/synthesis_report.pdf` in 34.

### Wave-5 frontier, as placed

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Fewest unrestricted integers | **10ℤ**: degree 126496·5^31 + 27064 (about 5.9·10^26), 1,442 ops; instantiates Sun's 2026 ten-integer reduction (preprint arXiv:2609.01594v2, cited, not reproduced, not checked at intake) on 30's quartic | 31 only | 31 |
| Fewest unrestricted integers, Jones route | **14ℤ**: 37 (813056·L + 2752, 1524 ops) beats 34 (813056·L + 2152 at 1586 ops) on operations, and 34 beats 37 on degree; different polynomials | 34, 37 | 34 |
| 15ℤ and 16ℤ | 15ℤ: 37 (813056·L + 4184 / 1530), 34 (406528·L + 2528 / 1594), 32 (813056·5^33 + 4184 / 1541, ν = 32, T4 tuple). 16ℤ: 31, 32, 33, 35 and 37, all different polynomials (33's and 37's share the degree 406528·L + 10008 but differ in their parent-quartic records, checked by the audit); fewest ops 37 (1537) | 37, 34, 32; 31, 32, 33, 35, 37 | 34 for 15ℤ; 31 for 16ℤ, 37 for operations |
| Nine unknowns | **degree 92324·L + 296**, 9 positive at 1500 ops (37) or 1554 (34), over ℕ 1505 / 1559: different polynomials (different templates and tuples, checked by the audit). 37 also has degree 93264·L + 288 at 1498 positive / 1503 ℕ. Wave-4 27's history-only 1480 / 1473 still have fewer operations | 34, 37 | 34 |
| Twelve positive, lowest degree | **1022** at 124 ops, then 1023 / 119, 1025 / 116, 1033 / 114, 1041 / 111; systems 1013 / 120, 1014 / 115, 1016 / 112, 1024 / 110 (all 34). 34's 1025 / 116 product and 1016 / 112 system dominate 37's 1061 / 120 (system 1052 / 114) and 35's and 37's 1065 forms (the same template on different tuples) | 34 | 34 |
| Twelve positive, fewest operations | **108** (31, 32, 33, 35): all are 30's degree-1081 polynomial evaluated more cheaply. 31's, 32's and 35's are the same fixed polynomial (identical tuples), and 33's is 30's own fixed polynomial. Systems: **102** (31, shifted) | 31, 32, 33, 35 | 31 |
| 31-unknown positive quartic | system **60** ops, SOS 125 (31); 61 / 126 (33); 62 / 127 (35), each 30's quartic under affine coordinate changes | 31, 33, 35 | 31 |
| Integer quartic | **50ℤ** (34, 37: they differ in one of 29 residuals, checked by the audit) | 34, 37 | 34 |
| 24ℤ at moderate degree | 37's 1936 / 161 (system 156), a different polynomial from wave-4 24's and 27's 1936 forms (smaller ratio weight) | 37 | 37 |
| Fewest operations | **67** (P₆₇), unchanged; the 59-op 16 / 7 / 24 system unchanged | — | (wave 1) |
| Smallest coefficients binding an equation | **B = 2^1012115** (36, 506,664 raw bytes, largest port 1,016,946 bits). 33's optional 2^1012625 binds none but has fewer raw bytes (506,644) and a smaller largest port (1,015,251 bits), so "smallest" depends on the measure. 2^1064921 (31, 32, 35: one identical tuple; 34 shares only β) | 36 | 36 |

### Wave-5 coefficient recipes

| Dir | B | Materialized | Notes |
|---|---|---|---|
| 31 | 2^1064921 (ρ = 2^121, cell 8801, padding prime 2341) | raw and gzip, 533,099 raw bytes; Jones index z = 2^4269855 for its 16ℤ form | the same bytes as 32's and 35's tuple |
| 32 | 2^1064921 (31's tuple) for the positive forms; T4 (2^(5^18), not expanded) for the integer forms | gzip | "no unverified claim that the new tuple has been substituted" into the Jones forms |
| 33 | 30's 2^(5^10) for its equations; optional 2^1012625 | gzip | optional tuple binds no delivered equation |
| 34 | 2^1064921 with 31's β but different K, MC, MF | raw and gzip, 532,479 raw bytes; z = 2^4259933 and 78 fixed leaves | a different tuple from 31's |
| 35 | 2^1064921 (31's tuple) | raw and gzip; z = 2^4269855 | identical bytes to 31's |
| 36 | **2^1012115** (ρ = 2^115, padding prime 3433) | gzip, 506,664 raw bytes; new Jones index z = 2^4058127 (507,266 raw bytes) | replaces earlier tuples as a whole |
| 37 | 30's 2^(5^10) | raw and gzip; z = 2^45933757 (`nine/generated/z_index.bin`, identical to wave-4 30's) | calls 25's and 27's 2^(5^9) tuples "valid competing" choices |

- Every package binds its four ports as one tuple and forbids splicing.
- Jones forms need a fresh index on any rebinding (36).
- The dossiers' read-only checks confirm the stated hashes and byte sizes
  of the materialized payloads. They do not check the compiler theorem the
  bytes instantiate.

### Wave-5 tensions

- **The square base.** 33 says replacing the base slack by a square "is not
  justified" (`report.tex:763-767`). Other forms use a square or cofinal
  base leaf, justified by inspecting the Lean proof of
  `Jones1982.USys_of_mem` (34's open question 2 notes the dependence):
  - 31's 16ℤ form (`kappa_index`);
  - 32's 15ℤ form (`b_floor`);
  - 34's 14ℤ form (`b_floor_odd`);
  - 35's 16ℤ form (`b_scale`);
  - 37's 14ℤ and 15ℤ forms (`base_scale`).

  32's, 33's and 37's 16ℤ forms and 34's 15ℤ form use the ordinary Jones
  index, so they do not depend on the contested step. That includes the
  16ℤ form with the fewest operations (37's, 1537).
- **Smallest-tuple claims.** 31, 32, 33, 35 and 36 each present their tuple
  as smaller than the pin's, without knowing of each other. 36's binds an
  equation and has the smallest B; 33's optional tuple, which binds nothing,
  has fewer bytes.
- **Like-for-like system counts.** 36 compares old *unshifted* systems
  (107, 118 ops) with its new *shifted* ones (103, 114) (`report.tex:117-119`;
  its README shows 107 → 103). Like for like, the new counts are 104 and
  115.
- **Corrections of wave 4.** 34 says wave-4 30's `positive/README.md` wrongly
  points to a nonexistent `coefficients/` folder; the wave-4 README already
  recorded this. 37 says wave-4 27's "same paper18 polynomial" is a template
  identity only, as the wave-4 README says, and qualifies the README's
  remark on 27's adapter (27's coefficient proof argues it). No package
  calls a wave-4 result or the wave-4 README wrong.

### Wave-5 delivery discrepancies

These are disclosed here and were not fixed in the delivered files.

- **Drivers.** These drivers read files omitted at intake (`k215.tm`, Lean
  sources, `KEndpoint215.lean`) or ignored ledgers, and fail in place:

  | Dir | Driver |
  |---|---|
  | 31 | `verify_all.py` |
  | 32 | `verify_all.py` |
  | 33 | `reproduce.py`, including its default run (stage 4 hashes the omitted sources) |
  | 34 | `verify_release.py` (exact manifest; needs SymPy and NumPy) |
  | 35 | `reproduce.py` |
  | 37 | `verify.py` (needs NumPy and SymPy) |

  From reading the code (not running it), only 36's `verify.py` reads no
  omitted file. Rerun from the arrival commit, as
  `PLACEMENT.md` explains.
- **Licence and attribution.**
  - Notices of AI assistance:

    | Package | Notice |
    |---|---|
    | 31 | AI assistance (one line) |
    | 32 | OpenAI, no human review |
    | 33 | "Prepared with AI assistance"; "remain open to human review" |
    | 34 | OpenAI; "not external human endorsements" |
    | 35 | OpenAI, disclaiming human authorship |
    | 36 | AI-assisted, unnamed |
    | 37 | OpenAI; "No external human review" |

  - 33 states **no licence for its new material**.
  - Every package ships a K215 machine notice. 37 says it fixes wave-4
    27's omission of one.
  - 34 calls wave-4 30 "our preceding construction". 37 calls wave-4 27
    "the previous delivery".
- **Inside the packages.**
  - 31's `quartic31_sos125.json` carries `exact_degree: 4` together with
    the system's `exact_maximum_degree: 2`, equation count and
    comparisons.
  - 33's own earlier 1617-op circuit is superseded.
  - 34's `audit/SUN_SCOPE_NOTE.md` still speaks of a "new 16-variable
    construction".
  - 36's system comparison mixes shifted and unshifted counts (above).
  - 37 lists no open questions.
- **Retained intermediates.**
  - 31's comparison variants and its inactive reference instance.
  - 34's dominated `nine31_structured*` and undelivered
    `coefficients/exploration/`. Its superseded 16 / 17-variable forms are
    mentioned in prose only.
  - 36's folded nine-variable copies and an exploratory moment method.
  - 37's signed15 (813056·L + 4184 / 1530), which 37 calls dominated
    although it beats 32's and 34's 15ℤ forms on operations.
- **Bundled copies.** Some bundled Lean files differ from the repository's
  only by a trailing blank line, so they were kept: 32's, including
  `compiler/upstream/KEndpoint215.lean`; 34's `audit/ProductPell.lean.txt`
  and `audit/Ratio.lean.txt`; and 37's `review/upstream/Ratio.lean`.

### Wave-5 further questions

These are the open problems the packages list, merged and credited:

1. **Formalize.** Sun's Lucas and interpolation theorems and the
   ten-integer adapter (31). The cofinal radix via `USys_of_mem` and the
   Pell-orbit lemma (32). The adapter and finalizers (35). The new lemmas
   generally (33, 34).
2. **Fewer unknowns.**
   - Below ten integers is a separate problem (31).
   - Instantiate Sun's route on the other packages' tuples (32, 33, 34,
     35).
   - Rebuild the Jones index at ν = 31 (32).
   - Remove more signed guards (35).
3. **Smaller circuits** (31, 32), better finalizers and majorants (33,
   34), and smaller tile languages and coefficient geometry (32, 34, 36).
4. **A smaller parent quartic.** It would lower every Jones and Sun degree
   (33, 34, 36). A new encoding of the first-index congruence (36).
5. **Justify the square base from the statement of `USys_of_mem`**, not its
   proof (34's open question 2; see the tension above).

Each package's full list is in its own article, for example
`33-signed16/report.tex` (from line 762), `34-integer14/report/synthesis_report.md`
(lines 1490-1503) and `32-integer15/report.tex` (from line 551).

## What is not claimed

The packages say, in their own words (exceptions noted):

- **No new formal result.**
  - New reductions are ordinary proofs with finite audits.
  - There is no Lean or Rocq end-to-end certificate and no fresh endpoint
    build.
  - Sun's reduction is not formalized anywhere in the repository (checked at
    intake: nothing in `Computability/HilbertTenthProblem`).
  - No package uses the active Lean research in
    `Computability/DiophantineConsistency/Lean/`, which postdates the pins.
- **No new general theorem.**
  - The ten-integer reduction is attributed to Sun. 31 "does not claim a new
    general ten-unknowns theorem".
  - Wave-6 packages cite Sun's 2026 preprint as a dependency, not as their
    own result. 42 calls it "a preprint dependency".
  - 38 says its nine-variable form "does not extend the result to nine
    unrestricted integers". 44 makes no sub-ten-integer or sub-nine-natural
    claim.
  - 31's review is not an independent audit of Sun's Lucas theorems.
  - 31 warns that ten integers "should not be compared … as if the domains
    were identical".
- **No consistency proof.** The theorems are equivalences, and every
  package disclaims a consistency proof; most also say they decide neither
  side. Several add that a two-sided independence claim needs an extra
  hypothesis: wave-5 32, 33, 36 and wave-6 41, 43, 45.
- **Domains.** Positive and nine-variable equations must not be read over ℤ;
  the domains of different forms are not interchangeable.
- **No optimality.** No global minimum is claimed, and nothing below 67
  operations is claimed. No form below nine unknowns or ten unrestricted
  integers is claimed.

## Relation to the formal developments

- **Machine endpoint.** The packages rest on the ordinary K215 calibration
  that `KEndpoint215.blank_halts_iff_zfc_refutation`
  (`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`, present
  at `HEAD`, not rebuilt) mirrors. The ZFC-provability claim does not go
  through Lean's soundness.
- **Jones.** The Jones-route forms build on the parametric Lean development
  of `Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/`. The
  packages use these lemmas:
  - `Jones1982.Nine.ratio_complete` and `Jones1982.Nine.ratio_sound`;
  - `Jones1982.Nine.reduced_of_mem` and `Jones1982.USys_of_mem`;
  - `Jones1982.exists_B25core`;
  - in 38, also `Jones1982.lemma_2_16`.

  Which lemmas each wave uses:
  - Wave 5's nine-variable forms apply `Jones1982.Nine.wset_iff_nine`
    (for example 37 at ν = 31).
  - Wave-6 38, 44 and 45 use the ratio lemmas directly instead. Their
    additive codes replace the 5^ν packing that `wset_iff_nine` hard-wires
    (`NineMain.lean:46-60`).
  - 38 and 44 also use `Jones1982.lemma_2_16`.
  - No package uses `Jones1982.nine_unknowns`, which fixes ν = 58.

  The new codes, decoders, finalizers, majorants and Pell-index arguments
  are unformalized. Several arguments rest on the structure of Lean proofs
  rather than their statements, for example the square base via
  `Jones1982.USys_of_mem`.
- **Sun.** Every 10ℤ form depends on Sun's 2026 preprint and his 2021 paper.
  31 cites Proposition 2.1, Theorems 3.1 and 4.1, Propositions 6.1–6.2 and
  §7 of the preprint. These are external, unformalized and were not checked
  at intake.
- **Active research.** `Computability/DiophantineConsistency` (outside this
  directory) holds checked Lean work on a Diophantine consistency equation;
  see its [README](../README.md) and STATUS. This report's packages are not
  part of that formal development.
- **Nothing in this report is formalized.**

## Licence and provenance

Every package was prepared for ProveIt and reuses MIT-0 repository material;
see the licence notes in each wave's section. Every licence, notice and
attribution file the packages ship is kept in place.

| Wave | Pin | Arrival | Placement |
|---|---|---|---|
| 5 | `8c6eec9d19ef80538c8e61ff6e0180040583446a` | `b7f8b75b5b` | `952c1fab49` |
| 6 | `22e75dd6b87b1b199bb08c778d7cf075ae5aae08` | `29ca562f8f` | `124c07c0b7` |

## Files

Every staged file, grouped by source directory (generated from the tree):

- `31-sun10/`: `INSTANCE_BINDINGS.json`, `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `report.pdf`, `report.tex`, `verify_all.py`
- `31-sun10/coefficients/`: `BUILD_RECEIPT.json`, `COEFFICIENT_BINDING.json`, `COEFFICIENT_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_coefficients.py`, `coefficient_section.tex`
- `31-sun10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `31-sun10/coefficients/payloads/`: `K.bin`, `K.bin.gz`, `MC.bin`, `MC.bin.gz`, `MF_source.bin`, `MF_source.bin.gz`, `beta.bin`, `beta.bin.gz`
- `31-sun10/coefficients/upstream/`: `24-coefficients.tex`, `25-COEFFICIENT_PROOF.md`, `27-COEFFICIENT_PROOF.md`, `k215_transitions.json`, `wang943_tiles.json`
- `31-sun10/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `31-sun10/positive12/`: `CHECKS.json`, `COEFFICIENT_BINDING.json`, `COEFFICIENT_INDEPENDENT_AUDIT.md`, `COEFFICIENT_INDEPENDENT_CHECKS.json`, `README.md`, `REFACTORED12_PROOF.md`, `SIGNED16_INDEPENDENT_AUDIT.md`, `SOURCE_PINS.json`, `audit_coefficients_independent.py`, `build_refactored12.py`, `check_refactored12.py`
- `31-sun10/positive12/generated/`: `product108.json`, `shifted_system102.json`, `system103.json`
- `31-sun10/positive12/upstream/`: `25-hybrid12README.md`, `26-ratio12README.md`, `COMPACT12_PROOF.md`, `POSITIVE12_PROOF.md`, `RATIO12_PROOF.md`, `README.md`, `build_positive.py`, `check_positive.py`, `con_zfc_synthesis.tex`, `positive12_system.json`
- `31-sun10/quartic31/`: `INSTANCE.json`, `QUARTIC60_CHECKS.json`, `QUARTIC60_PROOF.md`, `README.md`, `SIGNED16_LITERAL_AUDIT.json`, `SIGNED16_REVIEW.md`, `SOURCE_PINS.json`, `audit_signed16_independent.py`, `build_quartic60.py`, `quartic31_sos125.json`, `quartic31_sparse.json`, `quartic31_system60.json`
- `31-sun10/quartic31/upstream/27-wave4/operations/`: `PROOF.md`
- `31-sun10/quartic31/upstream/27-wave4/operations/upstream/`: `RETAINED59_PROOF.md`, `build_retained59.py`, `retained16_system59.json`
- `31-sun10/quartic31/upstream/28-compact-norms/vendor/inherited/`: `FIXED_BLANK_67_PROOF.md`, `PELL_LEMMA_AUDIT.md`
- `31-sun10/quartic31/upstream/30-quartic31/arithmetic/`: `QUARTIC31_PROOF.md`, `build_arithmetic.py`
- `31-sun10/quartic31/upstream/`: `PRODUCT67.json`, `quartic31.json`, `quartic31_circuit.json`, `quartic31_system.json`
- `31-sun10/sections/`: `coefficients.tex`, `low_degree.tex`, `overview.tex`, `parent.tex`, `reproduction.tex`, `signed16.tex`
- `31-sun10/signed10/`: `INDEPENDENT_AUDIT.json`, `INDEPENDENT_AUDIT.md`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `NOTICE.md`, `README.md`, `SIGNED10_PROOF.md`, `SIGNED10_SECTION.tex`, `SOURCES.json`, `audit_signed10_independent.py`, `build_signed10.py`, `circuit.py`, `verify_signed10.py`
- `31-sun10/signed10/data/`: `INSTANCE.json`, `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`, `beta_sun.bin.gz`, `coefficients_binding.json`, `constants.json`, `index_bound.json`, `parent_quartic31.json`
- `31-sun10/signed10/generated/`: `VERIFICATION.json`, `coefficient_aliases.json`, `norm3_polynomial.json`, `norm4_polynomial.json`, `signed10.json`, `signed10_h3quintic.json`, `signed10_h4quintic.json`, `signed10_sun6.json`, `signed10_universal_weights.json`
- `31-sun10/signed16/`: `README.md`, `build_signed16.py`, `circuit.py`, `verify_signed16.py`
- `31-sun10/signed16/data/`: `INSTANCE.json`, `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `Z_MATERIALIZATION.json`, `beta.bin.gz`, `coefficients_binding.json`, `constants.json`, `index_bound.json`, `parent_quartic31.json`, `z_index.bin.gz`
- `31-sun10/signed16/data/reference_instance/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`, `coefficients_binding.json`, `constants_upstream.json`, `index_bound.json`
- `31-sun10/signed16/generated/`: `VERIFICATION.json`, `coefficient_aliases.json`, `signed16.json`
- `31-sun10/sources/`: `BLANK_HELICAL_PROOF.md`, `COLLECTION_AT_PIN.md`, `DIGIT_CIRCUIT_SOURCE_PROOF.md`, `FIXED_BLANK_67_PROOF.md`, `NINE31_SOURCE_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `PELL_LEMMA_AUDIT.md`, `QUARTIC31_SOURCE_PROOF.md`, `SIGNED17_SOURCE_PROOF.md`
- `31-sun10/verification/`: `PDF_QA.json`, `PORTABILITY.json`, `SUMMARY.json`
- `32-integer15/`: `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `RESULTS.json`, `metrics.tex`, `report.pdf`, `report.tex`, `verify_all.py`
- `32-integer15/compiler/`: `BUILD_RECEIPT.json`, `COEFFICIENT_PROOF.md`, `INDEPENDENT_RECEIPT.json`, `NOTICE.md`, `SOURCE_LEDGER.json`, `audit_independent.py`, `build_coefficients.py`
- `32-integer15/compiler/coefficients/`: `COEFFICIENT_BINDING.json`, `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `32-integer15/compiler/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `32-integer15/compiler/upstream/`: `COEFFICIENT_PROOF.md`, `KEndpoint215.lean`, `coefficients.tex`, `fixed_factor_padding.tex`, `mixed125_adapter.md`, `mixed125_full_interface.md`, `mixed125_interface_review.md`, `wang943_language.md`, `wang943_tiles.json`
- `32-integer15/evidence/`: `CLEAN_COPY_REBUILD.json`, `PDF_QA.json`, `VERIFICATION.json`, `compiler_audit_independent.log.txt`, `compiler_build_coefficients.log.txt`, `integer15_build_signed15.log.txt`, `integer15_check_new_lemmas.log.txt`, `integer16_build_signed16.log.txt`, `positive_optimize_positive.log.txt`, `positive_review_signed_reductions.log.txt`
- `32-integer15/integer15/`: `COEFFICIENT_BINDING.json`, `LICENSE`, `NEW_LEMMA_CHECKS.json`, `NOTICE.md`, `README.md`, `SIGNED15_16_PROOF.md`, `SOURCE_ADDITIONS.json`, `SOURCE_PINS.json`, `build_signed15.py`, `check_new_lemmas.py`, `optimized_source.py`
- `32-integer15/integer15/generated/`: `signed15.json`, `signed15_checks.json`
- `32-integer15/integer15/inherited/`: `SIGNED17_PROOF.md`, `build_improved27.py`
- `32-integer15/integer15/source_review/`: `Master3.lean`, `NineRatio.lean`, `NineReduce.lean`
- `32-integer15/integer15/upstream/`: `COEFFICIENT_BINDINGS.json`, `LICENSE`, `NOTICE.md`
- `32-integer15/integer15/upstream/base/`: `quartic32.upstream.json`
- `32-integer15/integer15/upstream/code/`: `fixed_coefficients.py`
- `32-integer15/integer15/upstream/coefficients/`: `T4_CONSTANTS.upstream.json`, `t4_windows.json`
- `32-integer15/integer15/upstream/nine/generated/`: `constants.json`, `index_bound_s.json`
- `32-integer15/integer15/upstream/nine/`: `nine_compressor.py`, `nine_section.tex`, `verify_fixed_instance.py`
- `32-integer15/integer15/upstream/upstream/licenses/`: `LICENSE.ProveIt`
- `32-integer15/integer15/upstream/upstream/machine/`: `NOTICE.md`
- `32-integer15/integer15/upstream/upstream/machine/licenses/`: `LICENSE.Wade`
- `32-integer15/integer15/upstream/upstream/t4/bridge/`: `BRIDGE_AUDIT.md`
- `32-integer15/integer15/upstream/upstream/t4/bridge/sources/`: `blank_helical.py`, `compiler_constants.py`, `k215_transitions.json`
- `32-integer15/integer16/`: `COEFFICIENT_BINDING.json`, `LICENSE`, `NEW_LEMMA_CHECKS.json`, `NOTICE.md`, `README.md`, `SIGNED15_16_PROOF.md`, `SOURCE_ADDITIONS.json`, `SOURCE_PINS.json`, `build_signed16.py`, `check_new_lemmas.py`, `optimized_source.py`
- `32-integer15/integer16/generated/`: `signed16.json`, `signed16_checks.json`
- `32-integer15/integer16/inherited/`: `SIGNED17_PROOF.md`, `build_improved27.py`
- `32-integer15/integer16/upstream/`: `COEFFICIENT_BINDINGS.json`, `LICENSE`, `NOTICE.md`
- `32-integer15/integer16/upstream/base/`: `quartic32.upstream.json`
- `32-integer15/integer16/upstream/code/`: `fixed_coefficients.py`
- `32-integer15/integer16/upstream/coefficients/`: `T4_CONSTANTS.upstream.json`, `t4_windows.json`
- `32-integer15/integer16/upstream/nine/generated/`: `constants.json`, `index_bound_s.json`
- `32-integer15/integer16/upstream/nine/`: `nine_compressor.py`, `nine_section.tex`, `verify_fixed_instance.py`
- `32-integer15/integer16/upstream/upstream/licenses/`: `LICENSE.ProveIt`
- `32-integer15/integer16/upstream/upstream/machine/`: `NOTICE.md`
- `32-integer15/integer16/upstream/upstream/machine/licenses/`: `LICENSE.Wade`
- `32-integer15/integer16/upstream/upstream/t4/bridge/`: `BRIDGE_AUDIT.md`
- `32-integer15/integer16/upstream/upstream/t4/bridge/sources/`: `blank_helical.py`, `compiler_constants.py`, `k215_transitions.json`
- `32-integer15/positive/`: `INDEPENDENT_SIGNED_REVIEW.md`, `OPTIMIZATION_CHECKS.json`, `OPTIMIZATION_PROOF.md`, `SIGNED_REVIEW_CHECKS.json`, `optimize_positive.py`, `positive12_product108.json`, `positive12_shifted_system103.json`, `positive12_system104.json`, `review_signed_reductions.py`
- `32-integer15/positive/upstream/`: `POSITIVE12_PROOF.md`, `PRODUCT67.json`, `QUARTIC31_PROOF.md`, `build_positive.py.inert`, `positive12_product.json`, `positive12_system.json`, `quartic31_system.json`
- `32-integer15/positive/upstream/review_sources/`: `Master3.lean`, `NineRatio.lean`, `NineReduce.lean`, `Ratio.lean`
- `32-integer15/references/`: `COMPARISON_AT_PIN.md`, `Master2.lean`, `Master3.lean`, `NineRatio.lean`, `NineReduce.lean`, `Ratio.lean`, `Theorem1.lean`
- `33-signed16/`: `INTEGRATION.md`, `Makefile`, `README.md`, `RELEASE_SHA256.json`, `SOURCE_MANIFEST.json`, `report.pdf`, `report.tex`, `reproduce.py`
- `33-signed16/code/`: `build_signed16.py`, `prepare_index.py`, `verify_signed16.py`
- `33-signed16/coefficients_small/`: `COEFFICIENT_BINDING.json`, `EXTERNAL_REVIEW.md`, `EXTERNAL_REVIEW_CHECKS.json`, `INDEPENDENT_CHECKS.json`, `MANIFEST.json`, `PROOF.md`, `README.md`, `SCALARS.json`, `SOURCE_HASHES.json`, `audit_external_review.py`, `audit_independent.py`, `build.py`, `section.tex`
- `33-signed16/coefficients_small/payloads/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `33-signed16/coefficients_small/source/`: `LICENSE.ProveIt`, `k215_transitions.json`, `wang943_tiles.json`
- `33-signed16/data/`: `coefficients31.json`, `index_bound31.json`, `signed16.json`
- `33-signed16/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `33-signed16/positive12/`: `COEFFICIENT_BINDING.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build_and_verify.py`, `positive12_product108.json`, `positive12_shifted_system103.json`, `positive12_system104.json`
- `33-signed16/positive12/upstream/`: `COEFFICIENT_BINDING.json`, `POSITIVE12_PROOF.md`, `positive12_product.json`
- `33-signed16/quartic31/`: `CHECKS.json`, `PROOF.md`, `README.md`, `build_and_verify.py`, `polynomials.json`, `quartic126.json`, `system61.json`
- `33-signed16/quartic31/upstream/`: `COEFFICIENT_BINDING.pinned.json`, `LICENSE.ProveIt`, `QUARTIC31_PROOF.pinned.md`, `RETAINED59_PROOF.pinned.md`, `quartic31.pinned.json`
- `33-signed16/upstream/`: `blank_helical_proof.md`, `coding_blocks_source.py`, `compact_constants.json`, `compact_nine_proof.md`, `fixed_blank67_proof.md`, `index_bound.json`, `nine_generic31.json`, `norm_source_notice.md`, `ordinary_blank_proof.md`, `pell_lemma_audit.md`, `prepare_coefficients.py`, `quartic31.json`, `quartic31_proof.md`, `reviewed_README.md`, `signed17_proof.md`
- `33-signed16/upstream/compiler/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `WANG943_INDEPENDENT_AUDIT.md`, `beta.bin.gz`, `binding.json`, `build_wang943.py`, `build_wang943_compact.py`, `materialize_wang943_compact.py`, `wang943_compact_layout.json`, `wang943_tiles.json`
- `33-signed16/verification/`: `HORNER_PRIORITY_REVIEW.json`, `PDF_QA.json`, `PORTABLE_REPRODUCTION.json`, `SIGNED16_INDEPENDENT_REVIEW.md`, `reproduction.json`, `signed16_build.json`, `signed16_independent.json`
- `34-integer14/`: `CHECK_PLAN.json`, `COEFFICIENT_BINDING.json`, `LICENSE`, `NOTICE.md`, `PORTABILITY_TRANSFORMS.json`, `README.md`, `RELEASE_MANIFEST.json`, `requirements.txt`, `verify_release.py`
- `34-integer14/audit/`: `COEFFICIENT_DECODER_REPLAY.json`, `COEFFICIENT_SEMANTIC_REVIEW.md`, `COFINAL_RADIX_REVIEW.md`, `FINAL_CIRCUIT_CHECKS.json`, `FINAL_NINE_AND_SIGNED_REVIEW.md`, `LINEAR_PREFIX_SQUARE_STACK.md`, `NEW_LEMMA_CHECKS.json`, `NINE_FINALIZER_INDEPENDENT_CHECKS.json`, `POSITIVE12_REVIEW.md`, `POSITIVE_INDEPENDENT_CHECKS.json`, `ProductPell.lean.txt`, `QUARTIC50_INDEPENDENT_CHECKS.json`, `RELEASE_NEGATIVE_CONTROLS.json`, `Ratio.lean.txt`, `SIGNED_H_CHECKS.json`, `SIGNED_H_PRODUCT_PELL.md`, `SUN_SCOPE_NOTE.md`, `check_final_circuits.py`, `check_new_lemmas.py`, `check_nine_finalizer_independent.py`, `check_positive_independent.py`, `check_quartic50_independent.py`, `check_signed_h.py`, `upstream28-nine.tex`, `upstream29-signed17.md`
- `34-integer14/coefficients/`: `BUILD_CHECKS.json`, `COEFFICIENT_PROOF.md`, `INDEPENDENT_CHECKS.json`, `README.md`, `REPLAY_CHECKS.json`, `SOURCE_LEDGER.json`, `build_coefficients.py`, `verify_independent.py`, `wang943_tiles.json`
- `34-integer14/coefficients/exploration/`: `UNPROMOTED.md`, `variable_width.py`
- `34-integer14/coefficients/payloads/`: `COEFFICIENT_BINDING.json`, `K.bin`, `K.bin.gz`, `MC.bin`, `MC.bin.gz`, `MF_source.bin`, `MF_source.bin.gz`, `beta.bin`, `beta.bin.gz`
- `34-integer14/coefficients/sources/`: `24_report.tex`, `25-hybrid12_COEFFICIENT_BINDING.json`, `25-hybrid12_PROOF.md`, `25-hybrid12_build_coefficients.py.inert`, `26-ratio12_PARITY_COEFFICIENT_PROOF.md`, `27-wave4_COEFFICIENT_BINDING.json`, `27-wave4_COEFFICIENT_PROOF.md`, `27-wave4_build_mixed.py.inert`, `WANG943_COMPACT_LAYOUT.md`, `WANG943_LANGUAGE_AND_COMPILER.md`
- `34-integer14/integers/`: `INDEX_CONSTANTS.json`, `README.md`, `SIGNED_BINDING.json`, `SIGNED_BUILD_LEDGER.json`, `SIGNED_CHECKS.json`, `SIGNED_FAMILY_PROOF.md`, `SOURCE_LEDGER.json`, `build_signed_forms.py`, `check_signed_forms.py`, `circuit_support.py`, `signed14.json`, `signed15_linear.json`, `source_core31.json`
- `34-integer14/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `34-integer14/low_degree/`: `CHECKS.json`, `QUARTIC50_PROOF.md`, `SOURCE_LEDGER.json`, `build_quartic50.py`, `quartic50.json`
- `34-integer14/low_degree/upstream/`: `ODD_SCALE_LIFTS_PROOF.md`, `integer51_degree4_odd_scale.json`
- `34-integer14/nine/`: `ACTUAL_INDEX_CHECKS.json`, `BUILD_LEDGER.json`, `CHECK_RESULTS.json`, `DEGREE_CERTIFICATE.json`, `DELIVERY_FILES.json`, `FIXED_LEAF_PAYLOADS.json`, `HORNER_SEARCH.json`, `INDEX_BOUND.json`, `INDEX_CONSTANTS.json`, `PORTABILITY_TRANSFORMS.json`, `QUARTIC31_PROOF.md`, `README.md`, `SIGNED_QUADRATIC_NINE_PROOF.md`, `SOURCE_LEDGER.json`, `STANDALONE_REPLAY.json`, `base31.json`, `bind_index.py`, `build_signed_nine.py`, `check_actual_index.py`, `check_degree.py`, `check_signed_nine.py`, `circuit_support.py`, `materialize_fixed_leaves.py`, `nine31_signed_quadratic.json`, `nine31_signed_quadratic_positive.json`, `nine31_structured.json`, `nine31_structured_positive.json`, `quartic31.json`, `quartic_coefficients.json`, `z_index.bin`, `z_index.bin.gz`
- `34-integer14/nine/fixed_leaf_payloads/`: `c0000.magnitude.bin.gz`, `c0016.magnitude.bin.gz`, `c0029.magnitude.bin.gz`, `c0030.magnitude.bin.gz`, `c0031.magnitude.bin.gz`, `c0049.magnitude.bin.gz`, `c0062.magnitude.bin.gz`, `c0064.magnitude.bin.gz`, `c0095.magnitude.bin.gz`, `c0096.magnitude.bin.gz`, `c0097.magnitude.bin.gz`, `c0099.magnitude.bin.gz`, `c0101.magnitude.bin.gz`, `c0189.magnitude.bin.gz`, `c0190.magnitude.bin.gz`, `c0191.magnitude.bin.gz`, `c0202.magnitude.bin.gz`, `c0205.magnitude.bin.gz`, `c0207.magnitude.bin.gz`, `c0212.magnitude.bin.gz`, `c0261.magnitude.bin.gz`, `c0262.magnitude.bin.gz`, `c0263.magnitude.bin.gz`, `c0264.magnitude.bin.gz`, `c0266.magnitude.bin.gz`, `c0272.magnitude.bin.gz`, `c0273.magnitude.bin.gz`, `c0279.magnitude.bin.gz`, `c0281.magnitude.bin.gz`, `c0284.magnitude.bin.gz`, `c0286.magnitude.bin.gz`, `c0287.magnitude.bin.gz`, `c0288.magnitude.bin.gz`, `c0293.magnitude.bin.gz`, `c0295.magnitude.bin.gz`, `c0298.magnitude.bin.gz`, `c0302.magnitude.bin.gz`, `c0306.magnitude.bin.gz`, `c0308.magnitude.bin.gz`, `c0309.magnitude.bin.gz`, `c0313.magnitude.bin.gz`, `c0315.magnitude.bin.gz`, `c0321.magnitude.bin.gz`, `c0323.magnitude.bin.gz`, `c0324.magnitude.bin.gz`, `c0325.magnitude.bin.gz`, `c0327.magnitude.bin.gz`, `c0329.magnitude.bin.gz`, `c0331.magnitude.bin.gz`, `c0333.magnitude.bin.gz`, `c0336.magnitude.bin.gz`, `c0341.magnitude.bin.gz`, `c0345.magnitude.bin.gz`, `c0346.magnitude.bin.gz`, `c0348.magnitude.bin.gz`, `c0349.magnitude.bin.gz`, `c0353.magnitude.bin.gz`, `c0355.magnitude.bin.gz`, `c0357.magnitude.bin.gz`, `c0359.magnitude.bin.gz`, `c0362.magnitude.bin.gz`, `c0365.magnitude.bin.gz`, `c0369.magnitude.bin.gz`, `c0373.magnitude.bin.gz`, `c0376.magnitude.bin.gz`, `c0377.magnitude.bin.gz`, `c0378.magnitude.bin.gz`, `c0380.magnitude.bin.gz`, `c0381.magnitude.bin.gz`, `c0384.magnitude.bin.gz`, `c0388.magnitude.bin.gz`, `c0393.magnitude.bin.gz`, `c0394.magnitude.bin.gz`, `c0395.magnitude.bin.gz`, `c0397.magnitude.bin.gz`, `c0398.magnitude.bin.gz`, `c0399.magnitude.bin.gz`, `c0401.magnitude.bin.gz`
- `34-integer14/nine/upstream/`: `27-wave4__nine__IMPROVEMENT_PROOF.md.txt`, `27-wave4__nine__build_improved.py.txt`, `28-compact-norms__code__nine_structured.py.txt`, `28-compact-norms__sections__nine.tex.txt`, `parent_constants.round4.json`, `quartic31.round4.json`
- `34-integer14/positive/`: `CHECKS.json`, `FACTOR_DEGREES.json`, `README.txt`, `SHIFTED12_PROOF.md`, `SOURCE_LEDGER.json`, `build_shifted.py`, `check_factor_degrees.py`, `check_shifted.py`, `positive12_shift_ac2_product.json`, `positive12_shift_ac2_system.json`, `positive12_shift_ac_product.json`, `positive12_shift_ac_system.json`, `positive12_shift_b_product.json`, `positive12_shift_b_system.json`, `positive12_shift_base_product.json`, `positive12_shift_base_system.json`, `positive12_shift_half_aux_product.json`, `positive12_shift_half_aux_system.json`, `positive12_shift_half_product.json`, `positive12_shift_half_system.json`
- `34-integer14/positive/upstream/`: `COEFFICIENT_BINDING.upstream.json`, `INHERITED_POSITIVE12_PROOF.md`, `code_build_optimized_1069.py.inert`, `sections_positive.tex`
- `34-integer14/report/`: `MAIN.md`, `REPORT_CONFIG.json`, `build_report.py`, `code_breaks.lua`, `header.tex`, `synthesis_report.md`, `synthesis_report.pdf`, `synthesis_report.tex`
- `34-integer14/review/24-integer24/`: `README.md`
- `34-integer14/review/24-integer24/circuits/`: `optimized_tightest_separating12_product.json`, `signed_separating_saturated24_product.json`
- `34-integer14/review/24-integer24/sections/`: `integer.tex`, `positive.tex`
- `34-integer14/review/25-hybrid12/`: `README.md`, `RESULTS.json`
- `34-integer14/review/25-hybrid12/arithmetic/`: `hybrid12_square_unweighted_product.json`
- `34-integer14/review/25-hybrid12/coefficients/`: `README.md`
- `34-integer14/review/25-hybrid12/proofs/`: `HYBRID12_PROOF.md`
- `34-integer14/review/26-ratio12/`: `README.md`, `RESULTS.json`
- `34-integer14/review/26-ratio12/arithmetic/`: `integer24_product.json`, `ratio12_product.json`
- `34-integer14/review/26-ratio12/coefficients/`: `README.md`
- `34-integer14/review/26-ratio12/proofs/`: `RATIO12_PROOF.md`
- `34-integer14/review/26-ratio12/references/`: `README.md`
- `34-integer14/review/27-wave4/`: `README.md`
- `34-integer14/review/27-wave4/integers/`: `README.md`
- `34-integer14/review/27-wave4/nine/`: `IMPROVEMENT_PROOF.md`, `README.md`
- `34-integer14/review/27-wave4/nine/generated/`: `nine_natural-majorant_specialized_positive_dag.json`
- `34-integer14/review/27-wave4/norms/`: `README.md`, `two_weight_norm12_product.json`
- `34-integer14/review/28-compact-norms/`: `README.md`, `report.tex`
- `34-integer14/review/28-compact-norms/circuits/`: `compact12_product.json`
- `34-integer14/review/29-simpler-forms/`: `README.md`
- `34-integer14/review/29-simpler-forms/norm12/`: `SHIFTED_NORM12_PROOF.md`, `shifted_norm12_product.json`
- `34-integer14/review/29-simpler-forms/signed17/`: `README.md`, `SIGNED17_PROOF.md`
- `34-integer14/review/29-simpler-forms/signed17/generated/`: `signed17.json`
- `34-integer14/review/30-quartic31/`: `README.md`
- `34-integer14/review/30-quartic31/integers/`: `README.md`
- `34-integer14/review/30-quartic31/nine/`: `README.md`
- `34-integer14/review/30-quartic31/positive/`: `README.md`
- `34-integer14/review/`: `ATTRIBUTION_SOURCE_MAP.json`, `COMPARISON_REVIEW.md`, `COUNT_AUDIT.json`, `PLACEMENT.md`, `README.md`, `SOURCE_LEDGER.json`, `TREE.json`, `audit_counts.py`
- `35-cancel12/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `RESULTS.json`, `report.pdf`, `report.tex`, `reproduce.py`
- `35-cancel12/coefficients/`: `CHECKS.json`, `COEFFICIENT_BINDING.json`, `K.bin`, `K.bin.gz`, `MC.bin`, `MC.bin.gz`, `MF_source.bin`, `MF_source.bin.gz`, `README.md`, `beta.bin`, `beta.bin.gz`, `build_coefficients.py`, `wang943_tiles.json`
- `35-cancel12/coefficients/upstream/`: `wang943_tiles.json`
- `35-cancel12/integers/`: `README.md`, `SOURCE_PINS.json`, `build_signed.py`, `signed_section.tex`
- `35-cancel12/integers/generated/`: `INDEX_BOUND_CERTIFICATE.json`, `INDEX_CONSTANTS.json`, `signed16.json`, `signed16_checks.json`, `signed17.json`, `signed17_checks.json`
- `35-cancel12/integers/upstream/27-wave4/nine/source/proofs/`: `independent_review.md`
- `35-cancel12/integers/upstream/29-simpler-forms/signed17/`: `SIGNED17_PROOF.md`, `build_signed17.py`
- `35-cancel12/integers/upstream/29-simpler-forms/signed17/upstream/nine/`: `nine_section.tex`
- `35-cancel12/integers/upstream/30-quartic31/arithmetic/`: `quartic31.json`
- `35-cancel12/integers/upstream/30-quartic31/integers/`: `SIGNED_ODD_SCALE_FAMILY_PROOF.md`
- `35-cancel12/integers/upstream/30-quartic31/nine/`: `COMPACT_NINE_PROOF.md`, `build_compact_nine.py`
- `35-cancel12/integers/upstream/30-quartic31/nine/nu31/`: `COMPACT_COEFFICIENT_BINDING.json`, `COMPACT_CONSTANTS.json`, `nine_compact_magnitude_tight.json`
- `35-cancel12/integers/upstream/30-quartic31/review/18-jones9/proofs/`: `nine_source_audit.md`
- `35-cancel12/integers/upstream/30-quartic31/review/`: `optimize_nine_circuit.py`
- `35-cancel12/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `35-cancel12/positive/`: `CHECK_RESULTS.json`, `README.md`, `build_new.py`, `cancellation1065_product.json`, `cancellation1065_shifted_system.json`, `cancellation1065_system.json`, `check_new.py`, `economical_product.json`, `economical_shifted_system.json`, `economical_system.json`
- `35-cancel12/quartic/`: `QUARTIC31_62_AUDIT.json`, `QUARTIC31_62_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_quartic31_62.py`, `quartic31_sos127.json`, `quartic31_system62.json`
- `35-cancel12/quartic/upstream/`: `QUARTIC31_PROOF.upstream.md`, `RETAINED59_PROOF.upstream.md`, `quartic31.json`
- `35-cancel12/reviews/`: `COEFFICIENTS_INDEPENDENT_AUDIT.json`, `COEFFICIENTS_INDEPENDENT_REVIEW.md`, `POSITIVE1065_INDEPENDENT_REVIEW.md`, `SIGNED16_INDEPENDENT_REVIEW.json`, `SIGNED16_INDEPENDENT_REVIEW.md`, `audit_coefficients_independent.py`, `audit_signed16.py`
- `35-cancel12/sections/`: `coefficients.tex`, `positive.tex`, `quartic.tex`, `signed.tex`, `verification.tex`
- `35-cancel12/sources/`: `SOURCE_MAP.json`
- `35-cancel12/sources/catalogue/24-integer24/`: `README.md`
- `35-cancel12/sources/catalogue/24-integer24/code/`: `build_coefficients.py`, `build_optimized_1069.py`
- `35-cancel12/sources/catalogue/24-integer24/sections/`: `coefficients.tex`, `positive.tex`
- `35-cancel12/sources/catalogue/25-hybrid12/`: `LICENSE`, `NOTICE.md`, `README.md`
- `35-cancel12/sources/catalogue/25-hybrid12/coefficients/`: `COEFFICIENT_BINDING.json`, `PROOF.md`, `build_coefficients.py`, `wang943_tiles.json`
- `35-cancel12/sources/catalogue/25-hybrid12/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `35-cancel12/sources/catalogue/25-hybrid12/proofs/`: `HYBRID12_PROOF.md`
- `35-cancel12/sources/catalogue/25-hybrid12/upstream/`: `09_ROOT_AMALGAMATION_PROOF.md`, `BLANK_HELICAL_PROOF.md`, `FIXED_BLANK_67_PROOF.md`, `NORM12_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `RETAINED59_PROOF.md`, `ROOT12_PROOF.md`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `complete84_signed_quotient_absorption.md`, `complete84_signed_quotient_soundness_scout.md`
- `35-cancel12/sources/catalogue/26-ratio12/`: `README.md`
- `35-cancel12/sources/catalogue/26-ratio12/arithmetic/`: `build_ratio12.py`
- `35-cancel12/sources/catalogue/26-ratio12/proofs/`: `RATIO12_PROOF.md`
- `35-cancel12/sources/catalogue/27-wave4/`: `README.md`
- `35-cancel12/sources/catalogue/27-wave4/coefficients/`: `COEFFICIENT_PROOF.md`, `audit_independent.py`, `build_mixed.py`
- `35-cancel12/sources/catalogue/27-wave4/coefficients/sources/`: `k215_transitions.json`
- `35-cancel12/sources/catalogue/27-wave4/coefficients/upstream/compiler/`: `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`
- `35-cancel12/sources/catalogue/27-wave4/operations/`: `PROOF.md`, `build_operations.py`
- `35-cancel12/sources/catalogue/27-wave4/operations/upstream/`: `RETAINED59_PROOF.md`, `retained16_system59.json`
- `35-cancel12/sources/catalogue/28-compact-norms/`: `README.md`
- `35-cancel12/sources/catalogue/28-compact-norms/proofs/`: `COMPACT12_PROOF.md`
- `35-cancel12/sources/catalogue/28-compact-norms/vendor/inherited/`: `FIXED_BLANK_67_PROOF.md`
- `35-cancel12/sources/catalogue/29-simpler-forms/`: `README.md`
- `35-cancel12/sources/catalogue/30-quartic31/`: `README.md`
- `35-cancel12/sources/catalogue/30-quartic31/arithmetic/`: `LOW_OPERATION_REPORT.md`, `QUARTIC31_PROOF.md`, `build_arithmetic.py`, `quartic31.json`, `quartic31_system.json`
- `35-cancel12/sources/catalogue/30-quartic31/positive/`: `POSITIVE12_PROOF.md`, `build_positive.py`
- `35-cancel12/sources/catalogue/`: `README.md`
- `35-cancel12/verification/`: `CLEAN_EXTRACTION.json`, `PDF_BUILD.json`, `REPRODUCE.json`
- `36-small-tuple/`: `Makefile`, `NOTICE.md`, `README.md`, `closing_sections.tex`, `nine_section.tex`, `report.pdf`, `report.tex`, `reproduce.py`, `verify.py`
- `36-small-tuple/baseline/`: `build_baselines.py`, `product67.json`, `retained16_system59.json`
- `36-small-tuple/baseline/upstream/`: `product67.original.json`, `retained16_system59.original.json`
- `36-small-tuple/coefficients/`: `COEFFICIENT_BINDING.json`, `INDEPENDENT_AUDIT.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCES.json`, `audit_coefficients.py`, `build_coefficients.py`, `k215_transitions.json`, `wang943_tiles.json`
- `36-small-tuple/coefficients/coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `36-small-tuple/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `36-small-tuple/coefficients/source_proofs/`: `BLANK_HELICAL_PROOF.md`, `COEFFICIENT_TRANSFER.md`, `FIXED_BLANK_67_PROOF.md`, `ODD_SCALE_27_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `SIGNED_DOMAIN_29.md`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `package24_prime_padding.tex`, `package25_mixed_clauses.md`, `package27_complete_transfer.md`
- `36-small-tuple/evidence/`: `COMPARISON_AT_PIN.md`, `INDEPENDENT_REVIEW.md`, `PDF_QA.json`, `RELOCATION_CHECK.json`, `UPSTREAM_PROVENANCE.json`, `VERIFICATION.json`
- `36-small-tuple/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `36-small-tuple/nine/`: `NINE_PROOF.md`, `README.md`, `SOURCE_MANIFEST.json`, `circuit_tools.py`, `coefficient_aliases.json`, `nine31_folded_checks.json`, `nine31_folded_natural.json`, `nine31_folded_positive.json`, `optimize_combined.py`, `rebind_compact.py`
- `36-small-tuple/nine/compact/`: `CONSTANTS.json`, `INDEX_BOUND_CERTIFICATE.json`, `REBOUND_CHECKS.json`, `nine31_natural.json`, `nine31_positive.json`, `z_index.bin.gz`
- `36-small-tuple/nine/source/`: `COMPACT_CONSTANTS.json`, `COMPACT_NINE_PROOF.md`, `LICENSE.ProveIt`, `UPSTREAM_COEFFICIENT_BINDING.json`, `nine_compact_magnitude_tight.json`, `quartic31.json`
- `36-small-tuple/nine/source/coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `36-small-tuple/positive/`: `CHECK_RESULTS.json`, `METRICS.json`, `REFINEMENT_PROOF.md`, `SOURCE_PINS.json`, `build_positive_refinements.py`, `check_positive_refinements.py`
- `36-small-tuple/positive/circuits/`: `short109_product.json`, `short109_shifted_system.json`, `short109_system.json`, `tight120_product.json`, `tight120_shifted_system.json`, `tight120_system.json`
- `36-small-tuple/positive/upstream/`: `LICENSE.ProveIt`, `NOTICE.original30.txt`, `POSITIVE12_PROOF.original30.md`, `TRANSPORT_SHIFT_PROOF.original29.md`, `ordinary_blank_proof.md`, `positive.original24.tex`, `positive12_product.original24.json`, `positive12_product.original30.json`
- `36-small-tuple/proofs/`: `INHERITED_ORDINARY_PROOF.md`, `INHERITED_P67_PROOF.md`, `INHERITED_PELL_AUDIT.md`, `INHERITED_RETAINED59_PROOF.md`
- `37-wave5/`: `INSTANCE.json`, `LICENSE`, `NEGATIVE_CONTROLS.json`, `NOTICE.md`, `PDF_QA.json`, `README.md`, `VERIFICATION.json`, `negative_controls.py`, `report.pdf`, `report.tex`, `verify.py`
- `37-wave5/coefficients/`: `COEFFICIENT_TRANSFER.md`, `COMPACT_COEFFICIENT_BINDING.json`, `REBUILD_CHECKS.json`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `WANG943_INDEPENDENT_AUDIT.md`, `k215_transitions.json`, `rebuild.py`, `wang943_tiles.json`
- `37-wave5/coefficients/coefficients_compact/`: `K.bin`, `K.bin.gz`, `MC.bin`, `MC.bin.gz`, `MF_source.bin`, `MF_source.bin.gz`, `beta.bin`, `beta.bin.gz`
- `37-wave5/licenses/`: `LICENSE`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE-source28.md`
- `37-wave5/lowdegree/`: `BUILD_RESULTS.json`, `CHECKS.json`, `PROOF.md`, `README.md`, `SOURCE_PROVENANCE.json`, `build.py`, `check.py`, `integer24_ratio_product.json`, `integer24_ratio_sos.json`, `integer24_ratio_system.json`, `integer50_quartic.json`, `integer50_quartic_expanded.json`, `integer50_quartic_system.json`, `section.tex`
- `37-wave5/lowdegree/upstream/`: `COEFFICIENT_BINDING.json`
- `37-wave5/lowdegree/upstream/arithmetic/`: `QUARTIC31_PROOF.md`, `SOURCE_LEDGER.json`, `build_arithmetic.py`, `quartic31.json`, `quartic31_system.json`
- `37-wave5/lowdegree/upstream/compiler/`: `COMPACT_COEFFICIENT_BINDING.json`
- `37-wave5/lowdegree/upstream/integers/`: `COEFFICIENT_BINDINGS.json`, `COEFFICIENT_TRANSFER.md`, `SIGNED_ODD_SCALE_FAMILY_PROOF.md`, `build_odd_scale_family.py`, `integer25_small_weight131_degree920.json`, `integer26_ordinary_two_root123_degree214.json`, `integer26_system117_degree128.json`
- `37-wave5/lowdegree/upstream/positive/`: `POSITIVE12_PROOF.md`, `positive12_product.json`
- `37-wave5/lowdegree/upstream/source27/`: `COEFFICIENT_BINDING.json`, `INTEGER24_PROOF.md`, `INTEGER24_RATIO_WEIGHT_PROOF.md`, `LOW_DEGREE_PROOF.md`, `integer51_degree4.json`
- `37-wave5/lowdegree/upstream/source27/sources/23-separating12/proofs/`: `ODD_SCALE_27_PROOF.md`
- `37-wave5/nine/`: `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_nine.py`, `section.tex`, `verify_nine.py`
- `37-wave5/nine/generated/`: `COEFFICIENT_ALIASES.json`, `DEGREE_CERTIFICATE.json`, `VALIDATION.json`, `Z_MATERIALIZATION.json`, `ledger.json`, `nine_sharp_degree_certificate.json`, `nine_sharp_natural.json`, `nine_sharp_positive.json`, `nine_structured_natural.json`, `nine_structured_positive.json`, `z_index.bin`, `z_index.bin.gz`
- `37-wave5/nine/source/27-wave4/nine/`: `IMPROVEMENT_PROOF.md`, `build_improved.py`
- `37-wave5/nine/source/28-compact-norms/`: `LICENSE`, `NOTICE.md`
- `37-wave5/nine/source/28-compact-norms/code/`: `nine_structured.py`
- `37-wave5/nine/source/28-compact-norms/sections/`: `nine.tex`
- `37-wave5/nine/source/30-quartic31/arithmetic/`: `QUARTIC31_PROOF.md`, `quartic31.json`
- `37-wave5/nine/source/30-quartic31/compiler/`: `COMPACT_COEFFICIENT_BINDING.json`
- `37-wave5/nine/source/30-quartic31/licenses/`: `LICENSE.ProveIt`, `NOTICE.txt`
- `37-wave5/nine/source/30-quartic31/nine/`: `COMPACT_NINE_PROOF.md`, `build_compact_nine.py`, `prepare_coefficients.py`, `rebuild_nu31.py`
- `37-wave5/nine/source/30-quartic31/nine/nu31/`: `COMPACT_CONSTANTS.json`, `INDEX_BOUND_CERTIFICATE.json`
- `37-wave5/positive/`: `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`, `COEFFICIENT_BINDING.json`, `PROOF.md`, `README.md`, `SOURCE_PROVENANCE.json`, `build_positive.py`, `check_positive.py`, `mid_full_product.json`, `mid_full_shifted_system.json`, `mid_full_sos.json`, `mid_full_system.json`, `mid_half_product.json`, `mid_half_shifted_system.json`, `mid_half_sos.json`, `mid_half_system.json`, `section.tex`, `shift_half_product.json`, `shift_half_shifted_system.json`, `shift_half_sos.json`, `shift_half_system.json`, `short_plain_product.json`, `short_plain_shifted_system.json`, `short_plain_sos.json`, `short_plain_system.json`, `tight_full_product.json`, `tight_full_shifted_system.json`, `tight_full_sos.json`, `tight_full_system.json`, `tight_half_product.json`, `tight_half_shifted_system.json`, `tight_half_sos.json`, `tight_half_system.json`
- `37-wave5/positive/upstream/`: `24-integer24__circuits__optimized_tight_separating12_product.json`, `24-integer24__circuits__optimized_tightest_separating12_product.json`, `24-integer24__code__build_optimized_1069.py`, `24-integer24__code__build_optimized_1073.py`, `24-integer24__code__build_optimized_1081.py`, `24-integer24__sections__positive.tex`, `25-hybrid12__proofs__HYBRID12_PROOF.md`, `26-ratio12__proofs__RATIO12_PROOF.md`, `28-compact-norms__proofs__COMPACT12_PROOF.md`, `30-POSITIVE12_PROOF.md`, `30-quartic31__integers__COEFFICIENT_TRANSFER.md`, `30-quartic31__positive__COEFFICIENT_BINDING.json`, `30-quartic31__positive__build_positive.py`, `30-quartic31__positive__positive12_product.json`
- `37-wave5/review/`: `FINAL_REVIEW_SUMMARY.md`, `LITERAL_STRUCTURE_CHECKS.json`, `POSITIVE_AND_INTEGER_NORM_REVIEW.md`, `SIGNED14_15_INDEPENDENT_REVIEW.md`, `SIGNED16_INDEPENDENT_REVIEW.md`, `check_literal_structure.py`
- `37-wave5/review/upstream/`: `27-wave4__coefficients__COEFFICIENT_PROOF.md`, `27-wave4__nine__IMPROVEMENT_PROOF.md`, `29-simpler-forms__signed17__SIGNED17_PROOF.md`, `30-quartic31__arithmetic__QUARTIC31_PROOF.md`, `30-quartic31__integers__COEFFICIENT_TRANSFER.md`, `30-quartic31__nine__COMPACT_NINE_PROOF.md`, `30-quartic31__positive__POSITIVE12_PROOF.md`, `PLACEMENT.md`, `Ratio.lean`
- `37-wave5/root/`: `COMPLETED_SQUARE_CHECKS.json`, `NINE_TELESCOPING_CHECKS.json`, `PELL_ORBIT_CHECKS.json`, `check_completed_square_bounds.py`, `check_nine_telescoping.py`, `check_pell_orbits.py`
- `37-wave5/signed/`: `FIXED_RECIPES.json`, `LICENSE`, `NOTICE.md`, `README.md`, `SIGNED_PROOF.md`, `SOURCE_PINS.json`, `build_signed.py`, `check_signed.py`, `fast_jones_base.py`, `section.tex`
- `37-wave5/signed/generated/`: `CHECKS.json`, `COEFFICIENT_ALIASES.json`, `LEDGER.json`, `signed14.json`, `signed15.json`, `signed16.json`
- `37-wave5/signed/upstream/`: `29-simpler-forms__signed17__SIGNED17_PROOF.md`, `29-simpler-forms__signed17__build_signed17.py`, `30-quartic31__arithmetic__QUARTIC31_PROOF.md`, `30-quartic31__nine__COMPACT_NINE_PROOF.md`, `30-quartic31__nine__build_compact_nine.py`, `30-quartic31__nine__rebuild_nu31.py`, `COMPACT_COEFFICIENT_BINDING.json`, `COMPACT_CONSTANTS.json`, `INDEX_BOUND_CERTIFICATE.json`, `LICENSE.ProveIt`, `LICENSE.source29`, `NOTICE.source29.md`, `NOTICE.source30.txt`, `quartic31.json`
- `37-wave5/sources/24-integer24/`: `README.md`
- `37-wave5/sources/25-hybrid12/`: `README.md`
- `37-wave5/sources/`: `PLACEMENT.md`, `README.md`
- `38-batching11/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `VERIFICATION.json`, `report.pdf`, `report.tex`, `reproduce.py`
- `38-batching11/compiler/`: `COEFFICIENT_BINDING.json`, `INDEPENDENT_AUDIT.json`, `PROOF.md`, `SOURCE_PINS.json`, `audit_complemented.py`, `build_complemented.py`
- `38-batching11/compiler/coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `38-batching11/compiler/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `38-batching11/eleven/`: `ELEVEN_POSITIVE_PROOF.md`, `INDEPENDENT_REVIEW.md`, `OPTIONAL_TRANSLATION_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_eleven.py`, `build_eleven_translated.py`, `check_eleven.py`, `check_eleven_translated.py`
- `38-batching11/eleven/generated/`: `CHECK_RESULTS.json`, `TRANSLATED_CHECK_RESULTS.json`, `absorbed_index_eleven_product.json`, `absorbed_index_eleven_shifted_system.json`, `absorbed_index_eleven_system.json`, `absorbed_index_eleven_translated_product.json`, `absorbed_index_eleven_translated_shifted_system.json`, `absorbed_index_eleven_translated_system.json`
- `38-batching11/eleven/source_proofs/`: `LICENSE.source35`, `NOTICE.source35.md`
- `38-batching11/nine/`: `COEFFICIENT_BINDING.json`, `INDEPENDENT_BOOTSTRAP_REVIEW.md`, `README.md`, `bind_coefficients.py`, `build_nine.py`, `kappa.bin.gz`, `source_data.json`, `verify_nine.py`, `weights.json`
- `38-batching11/nine/generated/`: `DEGREE_CERTIFICATE.json`, `VERIFICATION.json`, `nine_degree_certificate.json`, `nine_natural.json`, `nine_positive.json`
- `38-batching11/provenance/`: `NOTICE.K215.md`, `SOURCE_PROVENANCE.json`
- `38-batching11/review/`: `ELEVEN_INDEPENDENT_REVIEW.md`, `PDF_QA.json`
- `38-batching11/sections/`: `section_compiler.tex`, `section_eleven.tex`, `section_eleven_optional.tex`, `section_nine.tex`, `section_overview.tex`, `section_sun.tex`, `section_verification.tex`
- `38-batching11/signed10/`: `NOTICE.md`, `PROOF.md`, `README.md`, `build.py`, `circuit.py`, `verify.py`, `weights.json`
- `38-batching11/signed10/data/`: `INSTANCE.json`, `beta_sun.bin.gz`, `constants_b2.json`
- `38-batching11/signed10/generated/`: `VERIFICATION.json`, `coefficient_aliases.json`, `signed10_b2.json`
- `38-batching11/signed10/inherited/`: `LICENSE.source31`, `NOTICE.source31.md`, `README.md`, `SOURCE_PINS.json`
- `39-direct10/`: `DIRECT_QUADRATIC_PROOF.md`, `INTEGRATION.md`, `LICENSE`, `MANIFEST.sha256`, `Makefile`, `PROVENANCE.json`, `README.md`, `report.pdf`, `report.tex`, `reproduce.py`
- `39-direct10/code/`: `build_direct10.py`, `finalizer_tools.py`, `verify_direct10.py`
- `39-direct10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `39-direct10/data/`: `INSTANCE.json`, `UPSTREAM_FILES.json`, `beta_source.bin.gz`, `weights.json`
- `39-direct10/generated/`: `direct10.json`, `source_certificate.json`
- `39-direct10/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`, `package31-LICENSE`, `package31-NOTICE.md`
- `39-direct10/optional_compact/`: `DIRECT_QUADRATIC_PROOF.md`, `LICENSE`, `README.md`, `reproduce.py`
- `39-direct10/optional_compact/code/`: `build_direct10.py`, `finalizer_tools.py`, `verify_direct10.py`
- `39-direct10/optional_compact/coefficients/`: `COEFFICIENT_BINDING.json`, `INDEPENDENT_AUDIT.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `audit_coefficients.py`, `build_coefficients.py`
- `39-direct10/optional_compact/coefficients/coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `39-direct10/optional_compact/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `39-direct10/optional_compact/data/`: `COMPACT_COEFFICIENT_FILES.json`, `INSTANCE.json`, `UPSTREAM_FILES.json`, `beta_source.bin.gz`, `native_coefficients_binding.json`, `weights.json`
- `39-direct10/optional_compact/generated/`: `direct10_compact.json`, `source_certificate.json`
- `39-direct10/optional_compact/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`, `package31-LICENSE`, `package31-NOTICE.md`
- `39-direct10/optional_compact/upstream/`: `signed10_NOTICE.md`
- `39-direct10/optional_compact/verification/`: `DIRECT10_COMPACT_INDEPENDENT_AUDIT.json`, `INDEPENDENT_REVIEW.md`, `INTEGRATION.json`, `RESULTS.json`, `audit_independent.py`, `build.json`, `coefficients_independent_audit.json`, `coefficients_rebuild.json`, `independent_stdout.json`, `verify_stdout.json`
- `39-direct10/review/`: `COMPARISON_AT_PIN.md`
- `39-direct10/upstream/`: `signed10_NOTICE.md`
- `39-direct10/verification/`: `DELIVERY_VALIDATION.json`, `DIRECT10_INDEPENDENT_AUDIT.json`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `RESULTS.json`, `audit_independent.py`, `build.json`, `compact_reproduction.txt`, `independent_stdout.json`, `verify_stdout.json`
- `40-packing10/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCES.json`, `report.pdf`, `report.tex`
- `40-packing10/certificates/`: `binding.json`, `coefficient_bound.json`, `degree.json`, `full_circuit.json`, `metrics.json`, `norm_identity.json`, `parent_packing.json`, `toy_controls.json`, `verification.json`
- `40-packing10/code/`: `audit_full_circuit.py`, `audit_parent_packing.py`, `build.py`, `check_multitarget_toy.py`, `verify.py`
- `40-packing10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `40-packing10/data/`: `beta_source.bin.gz`, `coefficient_recipes.json`, `polynomial.json`, `weights.json`
- `40-packing10/research_candidate/`: `FACTORIZED_RECEIVERS.md`, `SHA256.json`, `UPSTREAM_COEFFICIENT_NOTICE.md`, `UPSTREAM_LICENSE`, `build_factorized.py`, `build_receipt.json`, `factorized_results.json`, `independent_local_audit.py`, `local_audit_receipt.json`
- `40-packing10/research_candidate/experimental_coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `40-packing10/research_candidate/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `40-packing10/upstream/`: `COMPARISON_AT_PIN.md`, `EXACT_DEGREE_AUDIT.md`, `FINALIZER_REVIEW.md`, `LICENSE`, `MULTITARGET_AUDIT.md`, `parent_sparse.json`
- `41-bose-chowla/`: `LICENSE`, `MANIFEST.json`, `Makefile`, `NOTICE.md`, `README.md`, `report.pdf`, `report.tex`, `reproduce.py`
- `41-bose-chowla/code/`: `build_equation.py`, `check_circuit_independent.py`, `check_coefficients.py`, `check_equation.py`, `shared_powers.py`, `weights.py`
- `41-bose-chowla/data/`: `INSTANCE.json`, `weights_certificate.json`
- `41-bose-chowla/generated/`: `CIRCUIT_AUDIT.json`, `COEFFICIENT_REPLAY.json`, `PORTABILITY_CHECK.txt`, `VERIFICATION.json`, `equation10.json`, `equation10_sun_finalizer.json`, `metrics.json`
- `41-bose-chowla/positive/`: `CHECK_RESULTS.json`, `COEFFICIENT_BINDING.json`, `POSITIVE_PROOF.md`, `build_majorant.py`, `check_majorant.py`, `positive12_majorant_product.json`, `positive12_majorant_system.json`, `section.tex`
- `41-bose-chowla/proofs/`: `ARBITRARY_WEIGHTS_AUDIT.md`, `B4_CODING_PROOF.md`, `POSITIVE_AUDIT.md`
- `41-bose-chowla/upstream/`: `SOURCE31_MANIFEST.json`
- `41-bose-chowla/upstream/dependencies/`: `DEPENDENCIES_MANIFEST.json`, `README.md`
- `41-bose-chowla/upstream/source31/`: `LICENSE`, `NOTICE.md`
- `41-bose-chowla/upstream/source31/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `42-additive-b4/`: `MANIFEST.json`, `Makefile`, `NOTICE.md`, `PDF_QA.json`, `README.md`, `REPRODUCTION.json`, `RESULTS.json`, `SOURCE_LEDGER.json`, `package_release.py`, `report.pdf`, `report.tex`, `reproduce.py`
- `42-additive-b4/coefficient_backend/`: `ATTRIBUTION.md`, `COEFFICIENT_BINDING.json`, `FILE_MANIFEST.json`, `INDEPENDENT_REVIEW.md`, `NONZERO_COEFFICIENTS_INDEPENDENT_AUDIT.json`, `PROOF.md`, `README.md`, `audit_coefficients.py`, `build_coefficients.py`, `k215_transitions.json`, `verify_equations.py`
- `42-additive-b4/coefficient_backend/coefficients/`: `K.bin`, `K.bin.gz`, `MC.bin`, `MC.bin.gz`, `MF_source.bin`, `MF_source.bin.gz`, `beta.bin`, `beta.bin.gz`
- `42-additive-b4/coefficient_backend/equations/`: `SOURCE_PINS.json`, `VERIFICATION.json`, `product67_nonzero683195.json`, `retained16_system59_nonzero683195.json`
- `42-additive-b4/coefficient_backend/equations/upstream/`: `product67.json`, `retained16_system59.json`
- `42-additive-b4/coefficient_backend/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `42-additive-b4/coefficient_backend/proofs/`: `INHERITED_RETAINED59_PROOF.md`
- `42-additive-b4/coefficient_backend/source_proofs/`: `BLANK_HELICAL_PROOF.md`, `COEFFICIENT_TRANSFER.md`, `WANG943_COEFFICIENTS.md`, `WANG943_COMPACT_LAYOUT.md`, `package36_PROOF.md`
- `42-additive-b4/review/`: `B4_INDEPENDENT_AUDIT.json`, `B4_INDEPENDENT_REVIEW.md`, `COMPOSED_B4_INDEPENDENT_AUDIT.json`, `COMPOSED_B4_INDEPENDENT_REVIEW.md`, `COMPOSED_BINDING_INDEPENDENT_AUDIT.json`, `UNSUCCESSFUL_REDUCTIONS.md`, `audit_b4_independent.py`, `audit_composed_binding.py`
- `42-additive-b4/sections/`: `coefficient_refinement.tex`, `composed_variant.tex`, `source_b4.tex`
- `42-additive-b4/sources/31-sun10/coefficients/`: `COEFFICIENT_PROOF.md`
- `42-additive-b4/sources/31-sun10/quartic31/`: `QUARTIC60_PROOF.md`
- `42-additive-b4/sources/31-sun10/signed10/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`
- `42-additive-b4/sources/31-sun10/sources/`: `PELL_LEMMA_AUDIT.md`
- `42-additive-b4/sources/`: `COLLECTION_README.md`, `README.md`
- `42-additive-b4/ten_integer/`: `LICENSE.upstream31`, `NOTICE.md`, `NOTICE.upstream31.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `b4_code.py`, `bose_chowla32.json`, `build_b4_sun10.py`, `circuit.py`, `upstream_NOTICE.md`, `upstream_SIGNED10_PROOF.md`, `upstream_verify_signed10.py`, `verify_b4_sun10.py`
- `42-additive-b4/ten_integer/data/`: `INSTANCE.json`, `constants.json`
- `42-additive-b4/ten_integer/generated/`: `CLEAN_REBUILD.json`, `VERIFICATION.json`, `b4_signed10.json`, `b4_signed10_h3quintic.json`, `b4_signed10_h4quintic.json`, `b4_signed10_sun6.json`, `b4_signed10_universal_weights.json`
- `42-additive-b4/ten_integer/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `42-additive-b4/ten_integer_composed/`: `COMPOSITION_BINDING.json`, `LICENSE.upstream31`, `NOTICE.md`, `NOTICE.upstream31.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `b4_code.py`, `bose_chowla32.json`, `build_b4_sun10.py`, `circuit.py`, `regenerate_binding.py`, `verify_b4_sun10.py`
- `42-additive-b4/ten_integer_composed/data/`: `INSTANCE.json`, `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`, `beta_sun.bin.gz`, `coefficients_binding.json`, `constants.json`, `index_bound.json`
- `42-additive-b4/ten_integer_composed/generated/`: `CLEAN_REBUILD.json`, `VERIFICATION.json`, `b4_signed10.json`
- `42-additive-b4/ten_integer_composed/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `42-additive-b4/ten_integer_composed/source_proofs/`: `FETCH_PINS.json`, `PELL_LEMMA_AUDIT.md`
- `43-sidon10/`: `INSTANCE.json`, `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `build.py`, `circuit.py`, `evaluate.py`, `report.pdf`, `report.tex`, `reproduce.py`
- `43-sidon10/checks/`: `audit.py`, `sidon_and_toys.py`, `source_interface.py`
- `43-sidon10/data/`: `coefficients_binding.json`
- `43-sidon10/generated/`: `BUILD_RECEIPT.json`, `INDEPENDENT_AUDIT.json`, `METRICS.json`, `REPRODUCTION.json`, `SIDON_AND_TOYS_AUDIT.json`, `SOURCE_INTERFACE_AUDIT.json`, `signed10_b2.json`, `source_records.json`
- `43-sidon10/proof-notes/`: `FURTHER_REDUCTIONS.md`, `INDEPENDENT_REVIEW.md`, `MULTI_RESIDUAL_SOURCE.md`, `SOURCE_REVIEW.md`
- `43-sidon10/vendor/`: `PARENT_REBUILD_RECEIPT.json`, `README.md`, `REBUILD_RECEIPT.json`, `SOURCES.json`, `rebuild_coefficients.py`
- `43-sidon10/vendor/machine/`: `NOTICE.md`
- `43-sidon10/vendor/machine/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `SOURCE_PINS.json`
- `43-sidon10/vendor/package18/`: `LICENSE`, `NOTICE.md`, `report.tex`
- `43-sidon10/vendor/package31/`: `LICENSE`, `NOTICE.md`
- `43-sidon10/vendor/package31/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `43-sidon10/vendor/package31/signed10/`: `NOTICE.md`
- `43-sidon10/vendor/quartic31-source/upstream/`: `RETAINED59_PROOF.pinned.md`, `retained16_system59.pinned.json`
- `43-sidon10/verification/`: `sidon_and_toys.json`
- `44-b4-sparse/`: `DEPENDENCY_MAP.json`, `LICENSE`, `NOTICE.md`, `PLACEMENT.md`, `README.md`, `REBUILD_FILES.json`, `REPLAY_SUMMARY.json`, `build_report.sh`, `negative_controls.py`, `report.pdf`, `report.tex`, `requirements.txt`, `results.tex`, `validation.tex`, `verify.py`
- `44-b4-sparse/native/`: `COEFFICIENT_BINDING.json`, `INDEPENDENT_AUDIT.json`, `NOTICE-upstream.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `audit_coefficients.py`, `build_coefficients.py`, `native_report.pdf`, `native_report.tex`, `native_section.tex`, `product67.json`, `retained16_system59.json`
- `44-b4-sparse/native/coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `44-b4-sparse/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `44-b4-sparse/nine/`: `NINE_B4_PROOF.md`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `b4_support.py`, `build_nine_b4.py`, `section.tex`, `standalone.tex`, `verify_nine_b4.py`
- `44-b4-sparse/nine/generated/`: `VALIDATION.json`, `natural_DEGREE_CERTIFICATE.json`, `nine_b4_natural.json`, `nine_b4_natural_certificate.json`, `nine_b4_positive.json`, `nine_b4_positive_certificate.json`, `positive_DEGREE_CERTIFICATE.json`
- `44-b4-sparse/positive/`: `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`, `COEFFICIENT_BINDING.json`, `INDEPENDENT_REVIEW.md`, `PROOF.md`, `README.md`, `RECIPE_SOURCE_PINS.json`, `SELECTED_TUPLE_SOURCE_PINS.json`, `SOURCE_PINS.json`, `build_positive.py`, `check_positive.py`, `full_product.json`, `full_shifted_system.json`, `full_sos.json`, `full_system.json`, `report.pdf`, `report.tex`, `section.tex`, `short_product.json`, `short_shifted_system.json`, `short_sos.json`, `short_system.json`
- `44-b4-sparse/positive/upstream/`: `26-ratio12__proofs__RATIO12_PROOF.md`, `34-integer14__positive__SHIFTED12_PROOF.md`, `37-wave5__positive__PROOF.md`, `COEFFICIENT_BINDING.json.inert`, `build_positive.py.inert`, `check_positive.py.inert`, `wang943_compact_materialization_receipt.json`
- `44-b4-sparse/quartic/`: `ELIMINATION_AUDIT.json`, `POSITIVE_M1_INDEPENDENT_REVIEW.md`, `REVIEW.md`, `SOURCE_PINS.json`, `SUN_B4_INDEPENDENT_CHECKS.json`, `SUN_B4_INDEPENDENT_REVIEW.md`, `audit_eliminations.py`, `check_sun_b4_independent.py`, `source_tree_records.json`
- `44-b4-sparse/review/`: `FORMAL_STATUS_POST_PIN.md`, `README.md`, `SOURCE_MAP.json`
- `44-b4-sparse/root_checks/`: `INDEPENDENT_RELEASE_CHECKS.json`, `INDEPENDENT_RELEASE_REVIEW.md`, `bose_chowla.py`, `bose_chowla_31.json`, `bose_chowla_31_optimized.json`, `check_complement_clause.py`, `check_dag_structure.py`, `check_norm_and_guard.py`, `check_sparse_digit.py`, `complement_clause_checks.json`, `dag_structure_checks.json`, `independent_release_checks.py`, `norm_guard_checks.json`, `optimize_bose.py`, `sparse_digit_checks.json`
- `44-b4-sparse/signed_audit/`: `COFINAL_BASE_AUDIT.md`, `FIXED_POLYNOMIAL_CARRY_PROOF.md`, `README.md`, `SIGNED13_B4_CHECKS.json`, `SIGNED14_B4_CHECKS.json`, `SIGNED_B4_PROOF.md`, `SOURCE_PINS.json`, `THIRTEEN_GUARD_PROOF.md`, `b4_support.py`, `build_signed_b4.py`, `check_signed_b4.py`, `section.tex`
- `44-b4-sparse/signed_audit/generated/`: `DEGREE_CERTIFICATE_13.json`, `DEGREE_CERTIFICATE_14.json`, `LEDGER.json`, `signed13_b4.json`, `signed14_b4.json`
- `44-b4-sparse/sun/`: `B4_CERTIFICATE.json`, `B4_OPTIMIZED.json`, `INSTANCE.json`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `SUN_B4_PROOF.pdf`, `SUN_B4_PROOF.tex`, `SUN_B4_VERIFICATION.json`, `bose_chowla.py`, `build_sun_b4.py`, `section.tex`, `verify_sun_b4.py`
- `44-b4-sparse/sun/generated/`: `sun_b4.json`
- `44-b4-sparse/sun/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `44-b4-sparse/sun/sources/`: `NOTICE.md`
- `45-multioutput/`: `LICENSE-NEW-MATERIAL.txt`, `NOTICE.md`, `README.md`, `RELEASE_HASHES.json`, `verify_release.py`
- `45-multioutput/audit/`: `COMPLETE_EQUIVALENCE_REVIEW.md`, `COMPLETE_FORMULA_REPLAY.json`, `DEGREE_AUDIT.json`, `FIXED_BINDINGS_AUDIT.json`, `NEGATIVE_CONTROLS.json`, `RELEASE_QA.json`, `check_complete_equations.py`, `check_degree_certificates.py`, `check_fixed_bindings.py`
- `45-multioutput/nine/`: `MULTITARGET_INSTANCE.json`, `MULTITARGET_NINE_PROOF.md`, `README.md`, `build_multitarget_nine.py`, `circuit.py`, `materialize_fixed_coefficients.py`, `verify_multitarget_nine.py`
- `45-multioutput/nine/generated/`: `VERIFICATION.json`, `multitarget_nine_natural.json`, `multitarget_nine_natural_degree_certificate.json`, `multitarget_nine_positive.json`, `multitarget_nine_positive_degree_certificate.json`
- `45-multioutput/nine/generated/fixed/`: `a000.bin.gz`, `a001.bin.gz`, `a003.bin.gz`, `a004.bin.gz`, `a005.bin.gz`, `a006.bin.gz`, `a007.bin.gz`, `a017.bin.gz`, `a018.bin.gz`, `a019.bin.gz`, `a020.bin.gz`, `a021.bin.gz`, `a022.bin.gz`, `a023.bin.gz`, `a024.bin.gz`, `a025.bin.gz`, `base_floor.bin.gz`
- `45-multioutput/nine/upstream/`: `Index.lean`, `Master1.lean`, `PROOF.md`, `PackingBounds_copy.lean`, `Packing_copy.lean`, `Section4.lean`, `Theorem2.lean`, `build_nine.py`
- `45-multioutput/nine/upstream/generated/`: `nine_sharp_degree_certificate.json`, `nine_sharp_positive.json`
- `45-multioutput/positive/`: `CHECKS.json`, `COEFFICIENT_BINDING.json`, `COEFFICIENT_CHECKS.json`, `DEGREE_DIAGNOSTICS.json`, `README.txt`, `SOURCE_PINS.json`, `WEIGHT10_PROOF.md`, `build_new_weight.py`, `check_bound_instance.py`, `check_weight_degrees.py`, `check_weight_identity.py`, `positive12_weight10_ac2_aux_product.json`, `positive12_weight10_ac2_aux_system.json`, `positive12_weight10_ac_aux_product.json`, `positive12_weight10_ac_aux_system.json`, `positive12_weight10_b_aux_product.json`, `positive12_weight10_b_aux_system.json`, `positive12_weight10_b_product.json`, `positive12_weight10_b_system.json`, `positive12_weight10_base_product.json`, `positive12_weight10_base_system.json`, `positive12_weight10_half_aux_product.json`, `positive12_weight10_half_aux_system.json`
- `45-multioutput/quartic/`: `B2_CERTIFICATE.json`, `QUADRATIC_MULTI_TARGET_PROOF.md`, `QUADRATIC_REPLAY.json`, `QUADRATIC_TARGETS.json`, `build_b2.py`, `build_quadratic_targets.py`, `verify_quadratic_targets.py`
- `45-multioutput/report/`: `build.sh`, `metrics.tex`, `report.pdf`, `report.tex`
- `45-multioutput/review/`: `CATALOGUE_AT_PIN.md`, `MULTI_OUTPUT_SOURCE_REVIEW.md`, `README_POST_PIN.md`, `SOURCE_PINS.json`, `STATUS_POST_PIN.md`
- `45-multioutput/review/sources/31-sun10/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/review/sources/31-sun10/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `45-multioutput/review/sources/31-sun10/signed10/`: `NOTICE.md`
- `45-multioutput/review/sources/32-integer15/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/review/sources/32-integer15/compiler/`: `NOTICE.md`
- `45-multioutput/review/sources/32-integer15/integer15/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/review/sources/32-integer15/integer16/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/review/sources/33-signed16/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `45-multioutput/review/sources/33-signed16/upstream/`: `norm_source_notice.md`
- `45-multioutput/review/sources/34-integer14/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/review/sources/34-integer14/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `45-multioutput/review/sources/34-integer14/review/`: `ATTRIBUTION_SOURCE_MAP.json`
- `45-multioutput/review/sources/35-cancel12/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/review/sources/35-cancel12/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `45-multioutput/review/sources/36-small-tuple/`: `NOTICE.md`
- `45-multioutput/review/sources/36-small-tuple/coefficients/`: `NOTICE.md`
- `45-multioutput/review/sources/36-small-tuple/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `45-multioutput/review/sources/37-wave5/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/review/sources/37-wave5/licenses/`: `LICENSE`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE-source28.md`
- `45-multioutput/review/sources/37-wave5/signed/`: `LICENSE`, `NOTICE.md`
- `45-multioutput/short/`: `POSITIVE_WEIGHT_REVIEW.md`, `POSITIVE_WEIGHT_REVIEW_CHECK.json`, `SEARCH_AUDIT.md`, `check_positive_weight_review.py`, `check_short_audit.py`
- `45-multioutput/short/upstream/`: `INHERITED_RETAINED59_PROOF.md`, `product67.json`, `retained16_system59.json`
- `45-multioutput/sun/`: `MULTITARGET_INSTANCE.json`, `MULTITARGET_SOURCE_PROOF.md`, `README.md`, `build_multitarget_sun.py`, `build_weighted_sun.py`, `materialize_multitarget.py`, `verify_multitarget_sun.py`
- `45-multioutput/sun/data/fixed/`: `beta_sun.bin.gz`, `q0000.bin.gz`, `q0001.bin.gz`, `q0002.bin.gz`, `q0003.bin.gz`, `q0004.bin.gz`, `q0005.bin.gz`, `q0006.bin.gz`, `q0007.bin.gz`, `q0008.bin.gz`, `q0009.bin.gz`, `q0010.bin.gz`, `q0011.bin.gz`, `q0012.bin.gz`, `q0013.bin.gz`, `q0014.bin.gz`, `q0015.bin.gz`
- `45-multioutput/sun/generated/`: `MULTITARGET_VERIFICATION.json`, `multitarget_sun10.json`, `quadratic_coefficients.json`
- `45-multioutput/sun/upstream/`: `LICENSE`, `NOTICE.md`, `SIGNED10_PROOF.md`, `build_signed10.py`
- `45-multioutput/sun/upstream/signed10/data/`: `INSTANCE.json`, `K.bin.gz.json`, `MC.bin.gz.json`, `MF_source.bin.gz.json`, `beta.bin.gz.json`, `constants.json`, `index_bound.json`, `parent_quartic31.json`
- `45-multioutput/sun/upstream/signed10/generated/`: `signed10.json`
- `45-multioutput/weights/`: `MULTI_OUTPUT_EXTRACTION_PROOF.md`
- top level: `README.md` (this file), `PLACEMENT.md`
