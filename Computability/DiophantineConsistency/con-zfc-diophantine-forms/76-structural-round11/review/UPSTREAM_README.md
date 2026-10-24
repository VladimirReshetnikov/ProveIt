# Con(ZFC) in Diophantine form

This collection lives under `Computability/DiophantineConsistency`. It was
moved there on 23 October 2026 (`ea8ae71167`, at Vladimir's request) from
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
Paths in pinned source ledgers and historical Git commands still refer to the
locations in those earlier commits. The delivered packages keep their
original contents. See the [active research](../README.md) for new Lean
proofs and the current status; this README covers only the delivered
manuscripts.

The active research's proposal reviews record independent release replays,
circuit counts, proof assessments and its next formalization target:

- After wave 7, [PROPOSAL_REVIEW.md](../PROPOSAL_REVIEW.md) selected package
  52's 548-operation nine-positive form.
- After wave 8, [PROPOSAL_REVIEW_WAVE8.md](../PROPOSAL_REVIEW_WAVE8.md)
  (`94d84e5c1b`) moved to 59's 473-operation form.
- After wave 9, [PROPOSAL_REVIEW_WAVE9.md](../PROPOSAL_REVIEW_WAVE9.md)
  (`bdd86761ba`) adopted 66's 444-operation H2082 form. It sealed a local
  443-operation instance on 54's smaller tuple, and kept 65's and 67's
  lower-degree forms.
- After wave 10, [PROPOSAL_REVIEW_WAVE10.md](../PROPOSAL_REVIEW_WAVE10.md)
  (`1affa014c2`) keeps the 443-operation target. It records 71's lower-degree
  nine-positive form, 69's and 71's 38-integer quartics and 70's
  eleven-positive form as alternative targets.

The delivered packages remain unchanged.

**Explicit polynomials with fixed integer coefficients whose unsolvability
ZFC proves equivalent to Con(ZFC). Waves 5–10 are all in the tree. The stated
frontier is now:**

- **nine positive unknowns** in 444 operations at degree 1,845,940 (66), or at
  degree 1,379,730 in 478 operations (71);
- **ten unrestricted integers** at degree 1,576,864 in 481 operations (68),
  the fewest operations and the lowest degree at once, via Sun's reduction;
- **thirteen unrestricted integers without Sun's reduction** at degree
  10,461,744 (67, unchanged);
- **eleven positive unknowns** at degree 325 in 113 operations (70), down
  from 954;
- **twelve positive unknowns** at degree 82 (69), or in 89 operations (57's
  258 form);
- **thirteen positive unknowns** at degree 28 (72), or in 83 operations at
  degree 114 (62);
- **fourteen positive unknowns** at degree 24 (72), or in 79 operations at
  degree 52 (55, 59);
- **fifteen positive unknowns** at degree 24 in 88 operations (66), and in
  66 operations (51's P66, degree 157), both unchanged;
- **a quartic in 38 unrestricted integers**, a sextic in 32 and an octic in
  27 (69 and 71, independently), and a degree-16 form in 26 (68);
- **the smallest native tuple binding an equation**, B = 2^429959 (54,
  unchanged).

The report holds forty-five research packages; all but 60, 66 and 68 state
AI assistance.

- **Wave 5**, sources 31–37: batch 221 (arrival `b7f8b75b5b`, placed in
  `952c1fab49`), pinned to `8c6eec9d19`.
- **Wave 6**, sources 38–45: batch 222 (arrival `29ca562f8f`, placed in
  `124c07c0b7`), pinned to `22e75dd6b8`.
- **Wave 7**, sources 46–53: batch 223 (arrival `4b4349064a`, "Con(ZFC) in
  Diophantine form (wave-7)", placed in `6d375f2d2d`), all dated
  23 October 2026 and pinned to `124c07c0b7`. That pin is the wave-6
  placement commit, when this README still described wave 5 only.
- **Wave 8**, sources 54–59: batch 224 (arrival `7331974b69`, "Con(ZFC) in
  Diophantine form (wave-8)", placed in `beb0192cb8`), all dated
  23 October 2026. 54–57 and 59 are pinned to the wave-7 arrival
  `4b4349064a`, 58 to the wave-7 placement `6d375f2d2d`.
- **Wave 9**, sources 60–67: batch 225 (arrival `0c6be9a074`, "Con(ZFC) in
  Diophantine form (wave-9)", placed in `a2cd79b912`), all dated
  23 October 2026 and pinned to the wave-8 placement `beb0192cb8`.
- **Wave 10**, sources 68–75: batch 226 (arrival `9513bd88ce`, "Con(ZFC) in
  Diophantine form (wave-10)", placed in `d79b41884d`), all dated
  23 October 2026. They are pinned to the wave-9 placement `a2cd79b912` or
  to the later merge `9cca523d9f`, which preceded the wave-9 README.

**Earlier waves are kept.** By Vladimir's direction, waves 6–10 are each
placed beside the earlier waves rather than replacing them. Wave-7 packages
cite wave-5 and wave-6 packages by number; no wave-7 package cites another.
In wave 8, only 59 cites a sibling: it reviews and builds on 56 and 57,
which reached it during packaging. No wave-9 or wave-10 package cites a
sibling of its own wave.

## Any encoding is welcome

By Vladimir's direction (23 October 2026), a proposal **need not** be built
from the following, and is free to explore other encodings:
- an encoding of the Turing machine K215
  ([`candidate-k215/k215.tm`](../../BusyBeaver/Research/ZFC/candidate-k215/k215.tm));
- Jones's universal Diophantine equation or its nine-variable reduction;
- Sun's ten-integer reduction;
- the native-window/Pell compiler.

The only requirement is the theorem itself:
- an explicit polynomial (or small system) with fixed integer coefficients;
- a stated domain;
- an ordinary proof, formalizable in ZFC, that ZFC proves "no solution" ↔
  Con(ZFC).

A route of its own must state and prove its own calibration, as carefully as
the K215 endpoint does here.

Every finished equation so far encodes the K215 blank run through the
native compiler, and most also use Jones's reduction or Sun's;
[The common theorem](#the-common-theorem) below describes that route. That
is a fact about the existing packages, not a rule. Part of the route has
checked infrastructure here: the K215 endpoint in Lean and Rocq, and the
Lean development of Jones's reduction. The compiler and the Diophantine
bridge are not formalized.

Other routes in the repository:
- **Explored by packages.** Wave 9's 60, 66 and 67 and wave 10's 68 and 75
  discuss or build pieces of routes past K215 and Jones (see the wave-9 and
  wave-10 sections below). None has yet produced a finished equation.
- **In the active research.** It records its own alternatives in
  [ALTERNATIVE_ENCODINGS.md](../ALTERNATIVE_ENCODINGS.md). These include a
  Lean-checked direct quartic for syntactic ZFC refutability that skips the
  Jones compression (`DirectQuarticZFC.noNaturalZero_iff_conZFC`, at
  `da269a4f57`). Its variable and operation counts are not yet measured,
  and the theorem is external: its derivation inside ZFC remains open.

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
| 6 | 222 | `29ca562f8f` | `124c07c0b7` … (kept) | `6ed62e4cd5` |
| 7 | 223 | `4b4349064a` | `6d375f2d2d` … (kept) | `8e5fa20d8f` |
| 8 | 224 | `7331974b69` | `beb0192cb8` … (kept) | `46988b7869` |
| 9 | 225 | `0c6be9a074` | `a2cd79b912` … (kept) | `f55088fc27` |
| 10 | 226 | `9513bd88ce` | `d79b41884d` … | this file |

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

[`PLACEMENT.md`](PLACEMENT.md) is the recovery map for all six waves: the
batch-221 record, then the appended batch-222 to batch-226 records.

| Wave | Archive members | Staged | Omitted copies | Ignored |
|---|---:|---:|---:|---:|
| 5 | 1,197 | 1,129 | 46 | 22 |
| 6 | 1,149 | 773 | 371 | 5 |
| 7 | 1,571 | 1,043 | 524 | 4 |
| 8 | 1,736 | 974 | 759 | 3 |
| 9 | 1,829 | 1,030 | 766 | 33 |
| 10 | 1,192 | 703 | 440 | 49 |

Omitted copies are byte-identical (up to line ends) to repository files.
Most of the later waves' are copies of earlier-wave files of this
report, which stay in the tree. Copies within one wave are kept: 59's copies
of 56's and 57's files are staged twice. 75's bundled copies of the eight
wave-9 ZIPs are omitted and mapped to their arrival commit `0c6be9a074`.
Wave 10 also ships ignored TeX build artifacts. Ignored members are checksum ledgers and logs, excluded by the root
`.gitignore`.

## The common theorem

This is the route the packages so far have taken; it is not required (see
above). Each finished equation defines polynomials or small systems with four
**fixed integer coefficient ports**:

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

Wave 7 refines this coding. Its packages make the code **support-aware**
or **selective**: positions and targets are chosen for the monomials
that actually occur in the parent, rather than for a full Sidon set.

- These parents have 62 monomials in the raw coordinates and 71 in the
  shifted ones.
- The new weights of 46–50, 52 and 53 have maxima of 174–239, against 799
  before; 51 keeps 40's 799-maximum Sidon set and makes only its targets
  sparse.
- The packages also change the arithmetic finalizers. They use new
  majorants, midpoint and lean carriers, absorption modulo Y, and
  reparameterized short circuits.

Wave 8 keeps the selective codes and changes what is packed and how the
norms are separated:

- **Degree separation** (57, 59). The source is packed as
  A₂·y² + A₁·y + A₀ in one word, so collisions between different degrees are
  harmless. 57 reduces it to 94 records (weight maximum 108), 59 to 89.
- **A free Pell coordinate** (56). The derived coordinate C becomes a free
  unknown, and the leading carry block is removed. 59's nine-positive form
  combines this with 59's own source.
- **Congruence separation** (55). The radicands lie in different residue
  classes, so a quartic two-root norm replaces separating weights.
- **Calibrated carry thresholds** (54), on wave-7 46's 2^429959 tuple, which
  46 itself had bound to no equation.
- **Integral roots** (58). A monic square equation forces q³ | Y, so Y can be
  supplied directly. This gives degree 24 at fifteen positive unknowns.
- **An ordinary-root merger** (59) for twelve positive unknowns, and a
  coprime guard for thirteen unrestricted integers.

Wave 9 works mostly on signs, guards and carriers:

- **Sign recovery and product guards** (62, 63, 64, 67). One guard on a product
  replaces two separate sign guards; this gives the 42ℤ quartic that all
  three found.
- **Congruence and integral carriers** (61, 64, 65, 67). Divisibility forced by
  a square equation recovers scales and quotients, for low degree at 12–14
  positive unknowns.
- **Shared coefficient positions** (65) and **positive gap coordinates** (60, 66) lower
  the source height of the nine-variable forms; **higher majorants** (63,
  66, 67) lower their degree below the common formula.
- **Direct proof certificates** (66) and a **review of non-K215 routes**
  (67); see the wave-9 section.

Wave 10 works mostly on guards and roots:

- **One quadratic-form guard** (68, 69, 71) replaces two sign guards. It
  gives 69's and 71's 38ℤ quartic, 32ℤ sextic and 27ℤ octic, and 68's 28ℤ
  octic and 26ℤ degree-16 form.
- **Residue orientation and root transfer** (70) delete a positivity witness
  and move a Pell root into an existing gap, for eleven and twelve positive
  unknowns.
- **Rational Pell descent** (69) recovers integrality after a norm merger,
  for twelve positive unknowns at degree 82.
- **Adaptive carrier moduli and centred norms** (71, 73, 74) and a
  **signed-power bootstrap** (75).
- **Composed sources and finalizers**: 71's nine-positive form, and 68's
  ten-integer form with a strengthened Lucas-index lemma.

## Combined frontier, waves 5–10 (intake findings)

Numbers are the packages' own. At intake, four read-only dossiers recounted
every operation count and measured the degrees of the headline circuits; all
checked figures agree with the claims. The mathematics was not re-derived,
and every dominance statement assumes the competing proofs are correct.

- "u / e / d / o" means unknowns / equations / degree / operations; pairs
  are degree / operations.
- Operations count every binary +, −, × including multiplication by fixed
  numerals; reuse and system comparisons are free. Fixed leaves are free,
  so a constant folded into a leaf costs nothing. Packages differ in what
  they fold:
  - 66 stores a threshold power as a leaf (otherwise 495 and 499 operations,
    not 490 and 494);
  - the ten-integer circuits of 65 (525) and 67 (519, 520, 522) contain 7
    gates on constants only;
  - 68's ten-integer form (481) would cost 486 if the five gates building
    its threshold were charged;
  - 72's 98 and 101 leave six derived constants as leaves; computing them
    takes 7 operations.
- Unknowns are strictly positive unless marked ℤ (unrestricted integers)
  or ℕ (naturals). Natural-coordinate companions have separate counts:
  - in wave 7, package 52 adds three operations, 47 adds four, and 53's
    calibrated form adds six;
  - in wave 8, 54 adds three, 57 two, 55 six, 56 seven (nine for its
    reference form), 59 seven (four for its initial form), and 58's
    natural translation fifteen;
  - in wave 9, every nine-positive form adds seven, and 63's fourteen-positive
    form adds fourteen;
  - in wave 10, 71's nine-positive form adds seven and 74's twelve-positive
    product adds twelve.

  The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package. Within one wave, the
lower directory number counts as earlier.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Nine positive, fewest operations | unchanged: **444** at degree 1,845,940 (ℕ: 451) | 66 | 66 |
| Nine positive, lowest degree | **1,379,730 / 478** (ℕ: 485). It combines 65's source, 63's majorant and 62's power rewrite | 71 | 71 |
| Nine positive, Pareto frontier | 1,845,940 / 444, 1,834,516 / 449, 1,825,540 / 451 (66); 1,738,228 / 457, 1,675,396 / 458 (65); 1,663,788 / 475 (67); 1,520,178 / 476 (66); 1,379,730 / 478 (71). Newly dominated by 71: 66's 481 and 483 and 67's 487 | 65, 66, 67, 71 | — |
| 10ℤ (Sun's reduction) | **1,576,864 / 481**, the lowest degree and the fewest operations at once. It dominates every earlier 10ℤ form, including 66's 490 and 494 and 67's 519 | 68 | 68 |
| Fewest integers without Sun's 2026 reduction | unchanged: **13ℤ**, 10,461,744 / 519 (67) and 11,543,632 / 518 (59) | 67; 59 | — |
| Eleven positive | **325 / 113** (system 110), dominating 52's 954 / 113 | 70 | 70 |
| Twelve positive, Pareto frontier | **82 / 102** (69); 110 / 100 and the sum of squares 164 / 99 (74); 57's 242 / 94 and **258 / 89**. Dominated: 70's 84 / 103, 71's 110 / 102, 73's 110 / 105 and 164 / 104, 75's 114 / 105, and 61's forms | 69; 74; 57 | — |
| Thirteen positive, Pareto frontier | **28 / 98** (72); 30 / 92 (73; 74 has the same polynomial in 93); **114 / 83** (62). Dominated: 70's and 75's 30 / 94 (one polynomial) and 61's 34 / 93 | 72; 73; 62 | — |
| Fourteen positive, Pareto frontier | **24 / 101** (72); 65's 26 / 92; 64's 30 / 83; 55's and 59's **52 / 79** | 72; 65; 64; 55 | — |
| Fifteen positive | unchanged: 66 ops (51's P66, degree 157); lowest degree 24 / 88 (66); Pareto frontier as after wave 9 | 51; 66 | — |
| Integer quartic | **38ℤ**, two different polynomials (25 residuals each) | 69; 71 | 69 |
| Integer sextic | **32ℤ**, two different polynomials (19 residuals each). The four 34ℤ sextics of 70, 72, 73 and 75 are dominated | 69; 71 | 69 |
| Integer octic | **27ℤ**, two different polynomials (14 residuals each). 68's 28ℤ and 70's 29ℤ are dominated | 69; 71 | 69 |
| Integer, degree 16 | 26ℤ, 13 residuals | 68 | 68 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125; 24ℤ at 1936 / 161. From wave 2 (history only, see the wave-2 README `5b0c9ae9fd`): 15's positive-domain sextic in 25 and octic in 20 unknowns, which still dominate 75's 26- and 21-unknown versions | waves 2, 5, 6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^429959** (54). 69's and 71's integer forms use six coefficient payloads (881,696 and 615,883 raw bytes) instead of four; 73's sextic is the first integer form bound to the 2^590069 tuple | 54 | 54 |

## Wave 10 (sources 68–75)

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`68-joint-positivity/`](68-joint-positivity/) | `ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.zip` | *Joint positivity, free Lucas coordinates, and commutative proof certificates* (README) | **10ℤ / 1 / 1,576,864 / 481** (31's tuple); 28ℤ octic (14 residuals) and **26ℤ degree-16** form (13 residuals); `direct/`, `alternative/` and `disjointness/` proof-certificate work (see below) |
| [`69-cones-pell/`](69-cones-pell/) | `con-zfc-cones-pell-2026-10-23.zip` | *Weighted cones and rational Pell descent* | **38ℤ quartic**, **32ℤ sextic**, **27ℤ octic** (six payloads, 881,696 bytes); **12 / 1 / 82 / 102** (2^590069 tuple) |
| [`70-residue-orientation/`](70-residue-orientation/) | `con-zfc-residue-orientation-root-transfer-2026-10-23.zip` | *Residue orientation and root transfer* | **11 / 1 / 325 / 113** (system 110); 12 / 1 / 84 / 103; 13 / 1 / 30 / 94; 40ℤ quartic (direct and alternate), 34ℤ sextic, 29ℤ octic (34's tuple) |
| [`71-determinant-guards/`](71-determinant-guards/) | `con_zfc_calibrated_determinant_guards_2026-10-23.zip` | *Calibrated determinant guards for Diophantine ZFC consistency* | **38ℤ quartic**, **32ℤ sextic**, **27ℤ octic** (six payloads, 615,883 bytes); 12 / 1 / 110 / 102; **9 positive / 1,379,730 / 478** (ℕ 485) |
| [`72-congruence-sextic/`](72-congruence-sextic/) | `con_zfc_congruence_and_sextic_2026-10-23.zip` | *Congruence Carriers and a Sextic Reduction for Diophantine Consistency* (README: *Three explicit equations for Diophantine ZFC consistency*) | **13 / 1 / 28 / 98** (system 91); **14 / 1 / 24 / 101** (system 92); 34ℤ sextic (34's tuple); positive forms on 2^590069 |
| [`73-guard-reanchoring/`](73-guard-reanchoring/) | `con_zfc_guard_reanchoring.zip` | *Reanchored sign constraints and adaptive Pell carriers* | 34ℤ sextic, on 2^590069 (recommended) and on 34's tuple; **13 / 1 / 30 / 92** (system 85); 12 / 1 / 110 / 105 and SOS 164 / 104 |
| [`74-centered-pell-gaps/`](74-centered-pell-gaps/) | `con-zfc-centered-pell-gaps-2026-10-23.zip` | *Centered Pell gaps and adaptive congruence moduli* | **12 / 1 / 110 / 100** and **SOS 164 / 99** (ℕ product 112; 36ℤ translation 220 / 184); 13 / 1 / 30 / 93 |
| [`75-signed-bootstrap/`](75-signed-bootstrap/) | `ZFC_Diophantine_Signed_Bootstrap_2026-10-23.zip` | *Signed-power bootstrap and alternative certificate interfaces* (README) | 34ℤ sextic (19 residuals); 13 / 1 / 30 / 94; 12 / 1 / 114 / 105; `certificates/` and `direct/` interface work (see below); bundles the eight wave-9 ZIPs |

Directory numbers: 68–73 carry zeroed file times and follow archive-name
order; 74 and 75 follow their file times. 71's archive wraps a directory
named `con_zfc_calibrated_cones`. Each directory's `README.md` is its entry
point.

### Encodings beyond K215 and Jones

Every finished wave-10 equation still calibrates through the K215 blank run
and the native compiler. Jones's reduction is used only by 71's
nine-positive form, and Sun's only by 68's ten-integer form; every other
wave-10 equation uses neither. Two packages work on other routes:

- **68's `direct/`.** It checks proofs in the repository's numerical
  calculus C222, through unordered "flow" certificates with pairwise
  coprime weights and a single accumulator.
  - Finished: the local step, with 23 witnesses at degree 50.
  - Uncompiled: the global constructor, `SharedAffineProductEquation.lean`.
    It defines objects but proves no theorem, and its final polynomial is
    neither produced nor counted.
- **68's `alternative/`.** Local versions of 66's one-stack step, with 17
  witnesses (degree 52, or 50 in a rule-checking variant). These are local
  relations only.
- **68's `disjointness/`.** A standalone three-Pell test for S AND T = 0 (bitwise
  disjointness), with 12 or 13 witnesses at degree 504 or 368. It is not
  integrated: the guard forcing a power-of-two base is missing. 68 credits
  the three-Pell method to Jones, Sato, Wada and Wiens (1976).
- **75's `certificates/`.** An inert-prime CRT closure for bounded universal
  quantifiers, aimed at 66's direct proof-checker step. The theorem is
  proved, but its factorial, binomial and power steps are not expanded into
  polynomials, nothing is instantiated or counted, and no calibration is
  named. The dossier calls it a variant of the classical
  Matiyasevich–Robinson construction; 75 does not compare it with the
  literature.
- **75's `direct/`.** A fixed-input boundary: a small universal machine
  with an input word would replace K215's tile alphabet.
  - Proved on paper: a one-equation boundary lemma, a zero-cost
    substitution (for unrestricted-integer sources), a constant-size
    initializer, and a conditional bound of at most 130 tiles.
  - Missing: the machine table, the K215-to-input translator, the input
    word and the regenerated coefficients.
- **Notes elsewhere.** 72 records a square-carrier lemma and why it cannot
  remove 64's sign guards. 73 proves a lemma on encoding proof syntax
  without a well-formedness check and a Pell power-recovery lemma, and says
  this is "not a completed non-K215 consistency equation".

### Identities and dominance (intake findings)

**How the dossiers checked.** Their own evaluators, not package code,
evaluated circuits modulo 2^127 − 1 with the actual fixed values (and with
random ones). Degrees were measured exactly along random lines or by finite
differences, and the integer forms were expanded with SymPy with the
coefficient ports symbolic. Every measured figure agrees with its claim.

- **One guard idea, three times.** 68, 69 and 71 each replace two sign
  guards by one quadratic-form guard of the shape xy − (s − x − y)². None
  cites the others.
- **69 and 71: same sizes, different polynomials.** Their 38ℤ quartics share
  24 of 25 rows and differ only in the guard row and its fixed numbers. Their
  32ℤ sextics and 27ℤ octics share most rows (11 of 14 for the octics) and
  differ in the guard and in which coordinates are kept. Both packages'
  restoration maps back to the quartic check out exactly.
- **Derived forms.**
  - 70's direct 40ℤ quartic is 64's 41ℤ quartic with X replaced by
    3·X3 − 1 and the row X − 2u² deleted.
  - 68's 28ℤ octic is 62's 30ℤ octic with its two sign guards merged.
  - 68's ten-integer form uses 66's gap source repacked on 65's layout, with
    a strengthened Lucas-index lemma that drops a divisibility hypothesis.
  - 71's nine-positive form is 65's source with 63's majorant and 62's
    power rewrite, which answers wave-9 further question 2.
- **Thirteen positive.** 73's 30 / 92 and 74's 30 / 93 are one polynomial,
  and 73 evaluates it in one operation fewer. 70's and 75's 30 / 94 are one
  other polynomial. 72's 28 / 98 is a third. None of these packages cites
  another.
- **Twelve positive.** All ten wave-9 and wave-10 circuits are pairwise
  different, with no ±1 shift relating any two. Pieces are shared: 74's norm
  residual is 71's, and 71's carrier residual is 75's.
- **The four 34ℤ sextics** of 70, 72, 73 and 75 are four different
  polynomials (368 to 614 terms).

### Tensions, not adjudicated at intake

- **Parallel discoveries.** The triple guard idea; 69 and 71 at identical
  sizes; the 73 / 74 and 70 / 75 thirteen-positive pairs; four 34ℤ sextics.
- **A caution overtaken.** 74's research note says the naive combination of
  62 and 64 does not reach 34 integers, and that deleting the global square
  guard is not justified. Four siblings reach 34 integers anyway, and 75
  deletes exactly that guard with a new proof.
- **Comparisons against stale baselines.**
  - 71 compares its nine-positive form only with 62's 453, though 66's 444
    and 449 were in the tree at its pin.
  - 72 compares its 14-positive form with 60's 89-operation evaluator; 66's
    88-operation evaluator of the same polynomial was already there.
- **Stale README at the pins.** 71 and 73 observe that this README, at
  `9cca523d9f`, still described waves 5–8. That was true; the wave-9
  reconciliation came later.
- **Placement side effects.** 72 reports that 61's `ACTIVE_BINDING.json`
  paths are broken. That is true in the placed tree, because intake omitted
  the payloads as copies; the arrival archives are intact. 72's, 73's and
  75's own binding paths break the same way.
- **An unattributed correction.** 68 calls an "incorrect claimed
  41-quartic-to-29-octic elimination" wrong without naming whose it is.
- **The active review.** 75 notes that, at `bdd86761ba`, the active wave-9
  review called the joint-power rewrite "now checked in Lean" while its
  status file said "in progress". `SplitJointPower59.lean` now exists.
- **No package calls this README wrong**, apart from the stale-pin remarks
  above.

### Delivery discrepancies (wave 10)

- **Drivers fail in place.** Every driver reads files omitted at intake.
  68's and 75's also read their git-ignored `SHA256SUMS.json`, and 75's the
  omitted `incoming/` archives. Rerun from the arrival archives, as
  `PLACEMENT.md` explains.

  | Dir | Driver | Note |
  |---|---|---|
  | 68 | `verify.py` | SymPy; `packing/verify.py` needs ignored logs and writes in place |
  | 69 | `verify.py` | standard library; writes `VERIFICATION.json` in place |
  | 70 | `verify.py` | works in a temporary copy |
  | 71 | `verify_all.py` | writes in place |
  | 72 | `verify_all.py` | standard library; rewrites its polynomial files and receipts in place; runs 44's and 64's builders |
  | 73 | `verify_all.py` | standard library; writes logs and receipts in place; `MANIFEST.sha256` lists 25 ignored logs |
  | 74 | `verify.py` | writes its receipts in place |
  | 75 | `verify.py` | SymPy |

- **Titles.** 69's and 70's PDF metadata titles differ from their TeX titles;
  72's README H1 differs, and its title begins like 61's.
- **Inside packages.**
  - 68's `direct/README.md` names six scripts and two data files, and
    `packing/README.md` names `prepare.py` and `search.cpp`; none is
    shipped. Its `report/free.tex` gives fallback numbers (1,629,856 / 517)
    of an omitted prototype.
  - 69, 71 and others paraphrase the titles of the packages they cite.
  - 72's `PROOF13.md` lists five derived constants where its JSON uses six.
  - 73's coefficient builder would rewrite its payloads in place.
- **Licence and attribution.**
  - 68 ships no root licence for its new material and makes no AI-assistance
    statement of its own; it calls 66 its previous iteration.
  - 75 ships no licence for its new material; its licence files are
    inherited from 64.
  - 73 calls its MIT-0 licence "the repository's MIT license".
  - 72 says it was "prepared with OpenAI ChatGPT"; 74's AI statement covers
    only its reviews.
- **Retained intermediates.** 70's alternate quartic, 73's second sextic
  binding, 74's natural and 36ℤ translations, and 68's prototypes named in
  its report.

### Further questions (wave 10)

1. **Other encodings.**
   - Compile 68's flow-certificate constructor and count its polynomial.
   - Supply the power-of-two base guard that would integrate 68's
     disjointness test.
   - Finish 75's fixed-input boundary (machine table, translator, input
     word) and instantiate its CRT closure.
2. **Combinations (intake observations, untested as proofs).**
   - 70's residue orientation with 69's or 71's guard, for a 37ℤ quartic.
   - 68's guard lemma on the two remaining guards of 69's or 71's 27ℤ octic.
     One dossier built this form and measured 25 unknowns at degree 12; its
     correctness is not proved.
   - 72's elimination with 73's guard change, for a smaller sextic.
3. **Coefficients.** Bind the new integer forms to a four-port compact
   tuple, as 73 does for its sextic.

## Wave 9 (sources 60–67)

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`60-positive-gap/`](60-positive-gap/) | `ConZFC_Positive_Gap_2026-10-23.zip` | *Positive source coordinates for a smaller Diophantine consistency candidate* (README: *Positive source coordinates: a smaller nine-variable candidate*) | 9 positive / 1,797,796 / 465 (ℕ 472), on the 2^590069 tuple and, as the same circuit, on 31's; 15 / 1 / 24 / 89 (58's degree-24 polynomial with z replaced by z + 1) |
| [`61-congruence-carriers/`](61-congruence-carriers/) | `con-zfc-congruence-carriers.zip` | *Congruence carriers for Diophantine consistency equations* (README: *Congruence carriers and a divided Pell norm*) | **13 / 1 / 34 / 93**; **12 / 1 / 118 / 104** and SOS 172 / 103; 37ℤ sextic and 34ℤ octic; positive forms on 2^590069, integer forms on 34's tuple |
| [`62-sign-and-norm/`](62-sign-and-norm/) | `con-zfc-sign-and-norm.zip` | *Sign recovery and centered norms for explicit ZFC consistency equations* | **13 / 1 / 114 / 83**; 42ℤ quartic (27 residuals); **35ℤ sextic**, **30ℤ octic**; 9 positive / 1,834,516 / 453 (ℕ 460); P13 and the nine form on 2^590069, the integer forms on 34's tuple |
| [`63-sign-recovery/`](63-sign-recovery/) | `con-zfc-sign-recovery-2026-10-23.zip` | *Recovering signs and absorbing Pell quotients* | 42ℤ quartic (the same polynomial as 62's); 14 / 1 / 34 / 87 (system 78; ℕ 101); 9 positive / 1,573,266 / 504 (ℕ 511); the quartic and P14 on 34's tuple, F9 on 31's |
| [`64-structural-reductions/`](64-structural-reductions/) | `con-zfc-structural-reductions-2026-10-23.zip` | *Structural reductions for explicit Diophantine consistency equations* | **14 / 1 / 30 / 83**; **41ℤ quartic** (26 residuals), 36ℤ sextic, 31ℤ octic (retained 44ℤ quartic); 9 positive / 1,781,068 / 470 (ℕ 477); P14 on 2^590069, integer forms on 34's tuple, F9 on 31's |
| [`65-shared-taps/`](65-shared-taps/) | `con_zfc_shared_taps_carriers_2026-10-23.zip` | *Shared coefficient positions and integral Pell carriers* | 9 positive / **1,675,396 / 458** and 1,738,228 / 457 (ℕ 465, 464); 10ℤ / 7,428,120 / 525; **14 / 1 / 26 / 92** and 30 / 85; nine and ten on 31's tuple, fourteen on 2^590069 |
| [`66-gap-congruence/`](66-gap-congruence/) | `ConZFC_Gap_Congruence_2026-10-23.zip` | *Smaller consistency equations through degree separation, congruence norms, and direct proof certificates* (README: *Gap coordinates, congruence norms, and direct proof certificates*) | 9 positive: six forms from 1,845,940 / **444** to 1,503,378 / 483; **10ℤ / 3,547,076 / 490** and 3,507,876 / 494; 15-positive 30 / 78, 26 / 87, **24 / 88**; `direct/`, a proof-certificate source avoiding K215 and Jones (see below); nine and ten on 31's tuple, fifteen on 2^590069 |
| [`67-oriented-guards/`](67-oriented-guards/) | `ZFC_Diophantine_Oriented_Guards_2026-10-23.zip` | *Oriented guards and smaller Diophantine consistency equations* | 9 positive: six forms from 1,731,700 / 462 to **1,494,006 / 487**; **10ℤ / 3,327,556 / 519**; **13ℤ / 10,461,744 / 519** without Sun; 14 / 1 / 30 / 87 (system 78, max degree 15); 42ℤ quartic (= 62's), 36ℤ sextic, 32ℤ octic; `alternatives/`, a review of non-K215 routes |

Directory numbers: 60–65 carry zeroed file times and follow archive-name
order; 66 and 67 follow their file times. Each directory's `README.md` is
its entry point.

### Encodings beyond K215 and Jones

Every finished wave-9 equation still calibrates through the K215 blank run
and the native compiler. But several routes avoid other parts of the usual
chain, and two packages explore further:

- **No Jones and no Sun.** These routes use neither:
  - the integer quartics, sextics and octics of 61, 62, 63, 64 and 67;
  - 61's twelve- and thirteen-positive forms and 62's thirteen-positive
    form;
  - the fourteen-positive forms of 63, 64, 65 (`pell/`) and 67;
  - the fifteen-positive forms of 60 and 66.

  Every nine-positive form uses 59's Jones ratio finalizer.
- **66's `direct/`.** A nondeterministic one-stack checker of proofs in the
  repository's numerical calculus C222, rather than a machine run. It avoids
  K215 and Jones at the source level.
  - **Calibration:** `KEndpoint.c222_iff_zf_refutation` and
    `ConstructibleChoice.zf_refutation_iff_zfc_refutation`, both present in
    the repository.
  - **Finished:** a local step quartic with 2 exposed states and 89 natural
    witnesses (91 variables), 85 residuals, 3,108 monomials, degree 4.
  - **Only a proposal:** the global constructor, `OneStackEquation.lean`
    (159 lines, never elaborated, no theorem). Its final unknown count and
    size are unknown.
  - **Not compared:** 66 does not compare it with the active research's
    deterministic C222 enumerator (`NativeGraphEnumerator.lean`, 1,742 step
    witnesses), which also avoids K215 and Jones.
- **67's `alternatives/`.** A review, with no polynomial claimed, of four
  directions:
  - **Direct provability**, after Carl and Moroz: the published
    explicitization is far too large.
  - **Fixed-input universality**, with small universal machines and the
    refuter as initial boundary: called the strongest direction, but it
    lacks an economical finite-input boundary compiler.
  - **The Coq DPRM development via FRACTRAN:** infrastructure, with no
    measured size.
  - **A negative result:** unordered FRACTRAN is a vector-addition system,
    whose reachability is decidable, so it cannot serve as a universal
    refuter.

  No competitive non-K215 endpoint resulted, because no compiler was
  instantiated and measured.
- **The others.** 60's report has a section on a direct proof-checker
  route, without a construction. 63 looked at the active native refutation
  graph and the Coq FRACTRAN route, and 64 at an unnamed alternative;
  neither obtained a smaller equation.

### Identities and dominance (intake findings)

**How the dossiers checked.** Their own evaluators, not package code,
evaluated circuits modulo 2^127 − 1 (and NTT primes) with the actual fixed
values. They recounted every operation count and measured degrees:
- exactly, along random lines, for the small circuits and, by exact
  finite differences or untruncated line restriction, for the nine- and
  ten-variable ones;
- on certificate circuits after checking that each equals its primary, or a
  stated multiple of it (D^16 or D^20 times the primary for 63 and 67).

The integer quartics, sextics and octics were expanded exactly with the
coefficient ports symbolic. Every measured figure agrees with its claim.

- **One quartic, three packages.** The 42ℤ quartics of 62, 63 and 67 are one
  polynomial: the same 27 residuals (67 renames three auxiliaries), on
  byte-identical tuples. Each keeps 25 of 57's 28 residuals, replaces
  w − u² by w − 4u², and merges the two sign guards into one product guard.
  None cites the others. 64's 41ℤ quartic shares 22 of its 26 rows and
  removes one more unknown with X = 2u².
- **Cheaper evaluators of earlier polynomials.** 66's 15-positive 30 / 78
  and 26 / 87 are 58's 30 / 79 and 26 / 88, the same polynomials.
- **Shifted polynomials.** 66's 24 / 88 and 60's 24 / 89 are one polynomial:
  58's 24 / 90 with z replaced by z + 1, so a different polynomial on the
  positive domain.
- **Near twins.** 65's 30 / 85 is 67's 30 / 87 with z replaced by z + 1, so they
  are different polynomials on the positive domain. 64's 30 / 83 differs
  from both: its modulus is Y².
- **Equal degree, different polynomials.** 62's nine-positive form and 66's
  H2068 form both have degree 1,834,516, because both reordered 59's targets
  to height 2068. They differ at random points and use different tuples.
- **Pairwise different:**
  - all 21 nine-positive circuits compared across 59–67, except 62's 453-
    and 467-operation circuits, which are one polynomial;
  - every twelve-, thirteen- and fourteen-positive form;
  - every sextic and octic (64's and 67's 36ℤ sextics share only 10 of 21
    rows).
- **One degree formula.** Every nine-positive form that keeps 59's
  finalizer has degree exactly 816H + 1224W + 5044, where H is the source
  height and W the weight maximum. 63, 66's refined forms and 67's orders
  1–4 go below it with modified majorants.

### Tensions, not adjudicated at intake

- **Parallel discoveries.** The triple 42ℤ quartic; the 65 / 67 fourteen-
  positive twins; 60's and 66's evaluators of the same 24-degree
  polynomial; 62's and 66's identical source height.
- **Corrections to wave 8.** Two corrections of wave-8 work, both minor.
  Earlier waves recorded a few such objections too, such as 34's and 53's.
  - 62, 63, 64 and 67 independently report that 57's quartic proof writes the
    transport row as `(K0+w)C=(z-1)(q-1)+F` and concludes z > 1, while the
    literal row is F + z(q − 1). The dossier calls this an unlabelled shift
    of notation, harmless: z > 0 is what the proof needs, and the circuits
    are unaffected.
  - 66 reports that 54's `REFINED_MAJORANT_PROOF.md` gives a sum of 1719
    where the true sum is 1619. The dossier recomputed 1619; both are below
    the needed 2048. The placed copy still reads 1719.
- **Counting conventions.** See the frontier notes: 66 folds a threshold
  power into a fixed leaf, while 65 and 67 count 7 constant-only gates.
- **Stale README at the pin.** 62, 63 and 64 observe that this README, at
  `beb0192cb8`, still described waves 5–7. That was true; the wave-8
  reconciliation came later.
- **64's P14 ends in a sum of squares minus 1**, as 55's fourteen-positive
  form does, rather than in a sum of squares set to 0.
- **No package calls this README wrong.**

### Delivery discrepancies (wave 9)

- **Drivers fail in place.** Every driver reads files omitted at intake;
  66's and 67's also read their git-ignored `SHA256SUMS.json`. Rerun from the arrival
  archives, as `PLACEMENT.md` explains.

  | Dir | Driver | Note |
  |---|---|---|
  | 60 | `checks/verify_all.py` | writes in place |
  | 61 | `verify_all.py` | writes in place; binding paths inside its integer packets dangle |
  | 62 | `verify_all.py` | writes `verification/REPLAY*.json` and logs in place |
  | 63 | `verify.py` | runs in place; component checks rewrite `VERIFICATION.json` |
  | 64 | `verify_all.py` | writes `certificates/ROOT_CHECKS*.json` in place |
  | 65 | `verify_all.py` | works in a temporary copy |
  | 66 | `verify.py` | SymPy |
  | 67 | `verify.py` | SymPy 1.14.0; refuses `-O` |

- **Degree labels.** The ten-integer JSON of 65, 66 and 67 labels exact degrees
  `degree_upper_bound`, as in wave 8.
- **Titles.** 60, 61, 66 (three different titles), and 63, 64 and 65
  (subtitles only) print titles that differ from their README H1 or PDF
  metadata.
- **Inside packages.**
  - 62's `nine/NOTICE.md` says the independent audit's grouping code "was
    corrected by the component author". Its `RESULTS.json` calls a degree
    bound "matched" that belongs to the certificate circuit, not to the
    453-operation primary.
  - 63's bibliography has no Jones, Matiyasevich or Sun entry, though its
    nine-positive form uses Jones's ratio representation. Its NOTICE says
    "MIT license" for an MIT-0 file.
  - 62's README has the typo "to1,834,516/453".
  - 64's README lists a root `licenses/` directory that does not exist.
  - 63, 64 and 65 paraphrase the titles of the packages they cite. 65 gives
    31's title as this collection's title, "Con(ZFC) in Diophantine form".
  - 66's `ARTIFACT_MAP.md` names a nonexistent `nine/METRICS.json`. Its
    review tells readers to run `check_intake.py` and
    `check_literal_ledgers.py`, which are not shipped, and it gives two
    interaction counts (22,481 and 22,451).
  - 67's top-level `nine/coefficients` binding is the 2^590069 tuple, while
    every nine-variable circuit uses `old_tuple/`, which invites a wrong
    binding. Its README and PDF abstract drop the space before numerals
    ("in42"). It hashes a `sigbovik2020.pdf` that it does not ship.
- **Licence and attribution.**
  - Every package except 66 ships an MIT-0 licence file for its new
    material, and all keep the inherited notices. 65's `sun/` has a NOTICE
    but no LICENSE.
  - 66 ships no root licence for its new material.
  - 60 and 66 make no AI-assistance statement of their own; the others do.
- **Retained intermediates.**
  - 62: the 467-operation Horner form, certificate circuits, a second 42ℤ
    quartic and a copy of 57's quartic.
  - 63: the D^20 certificates and the unshifted P14.
  - 64: the 44ℤ quartic and the certificates.
  - 66 and 67: the dominated nine-positive variants.

### Further questions (wave 9)

1. **Other encodings.**
   - Complete 66's one-stack constructor, and compare it with the active
     deterministic C222 enumerator.
   - An economical finite-input boundary compiler for fixed-input
     universality (67).
2. **Combinations (intake observations, untested).**
   - 65's height-1873 source with 66's or 67's majorants.
   - 64's X = 2u² step with 62's guard exchange, for a smaller sextic or
     octic.
3. **Smaller circuits.**
   - A Diophantine interface for "C(S+T, S) odd", more sign recovery and
     rational-root traps (62).
   - The remaining simplex guards, P14's degree-17 carrier, and F9's
     majorant degrees (63).
   - A joint search over shared positions, a third congruence recovery,
     and fewer gates at degree 26 (65).
4. **Formalize.** 64's adaptive-modulus lemmas, signed packing bounds and
   Mersenne-radix sign lemma; 65's shared-position argument.

### Frontier after wave 9, as placed

Numbers are the packages' own. At intake, four read-only dossiers recounted
every operation count and measured the degrees of the headline circuits; all
checked figures agree with the claims. The mathematics was not re-derived.

- "u / e / d / o" means unknowns / equations / degree / operations; pairs
  are degree / operations.
- Operations count every binary +, −, × including multiplication by fixed
  numerals; reuse and system comparisons are free. Fixed leaves are free,
  so a constant folded into a leaf costs nothing. The packages differ
  slightly here: 66 stores a threshold power as a leaf (otherwise 495 and
  499 operations, not 490 and 494). In the ten-integer circuits of 65 (525)
  and 67 (519, 520, 522), 7 gates act on constants only; 66's have none.
- Unknowns are strictly positive unless marked ℤ (unrestricted integers)
  or ℕ (naturals). Natural-coordinate companions have separate counts:
  - in wave 7, package 52 adds three operations, 47 adds four, and 53's
    calibrated form adds six;
  - in wave 8, 54 adds three, 57 two, 55 six, 56 seven (nine for its
    reference form), 59 seven (four for its initial form), and 58's
    natural translation fifteen;
  - in wave 9, every nine-positive form adds seven, and 63's fourteen-positive
    form adds fourteen.

  The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package. Within one wave, the
lower directory number counts as earlier.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Nine positive, fewest operations | **444** at degree 1,845,940 (ℕ: 451) | 66 | 66 |
| Nine positive, lowest degree | **1,494,006 / 487** | 67 | 67 |
| Nine positive, Pareto frontier | 1,845,940 / 444, 1,834,516 / 449, 1,825,540 / 451 (66); 1,738,228 / 457, 1,675,396 / 458 (65); 1,663,788 / 475 (67); 1,520,178 / 476, 1,510,770 / 481, 1,503,378 / 483 (66); 1,494,006 / 487 (67). Dominated: 60's 1,797,796 / 465, 62's 1,834,516 / 453, 63's 1,573,266 / 504, 64's 1,781,068 / 470, 67's 462, 465, 478 and 482, and every wave-8 form, 59's 473 included | 65, 66, 67 | — |
| Nine positive on a smaller tuple | 60's 1,797,796 / 465 and 62's 1,834,516 / 453, both on 2^590069; 54's 490 (wave 8) on 2^429959 | 60, 62; 54 | — |
| 10ℤ (Sun's reduction), Pareto frontier | **3,547,076 / 490** and **3,507,876 / 494** (66); **3,327,556 / 519** (67). Dominated: 65's 7,428,120 / 525, 67's 520 and 522, and every wave-8 form, 54's 513 included | 66; 67 | — |
| Fewest integers without Sun's 2026 reduction | **13ℤ**: 10,461,744 / 519 (67) and 59's 11,543,632 / 518, a tradeoff | 67; 59 | — |
| Eleven positive | unchanged: **954 / 113** (52) | wave 7 | 52 |
| Twelve positive | **118 / 104** and the sum-of-squares 172 / 103 (61); 57's 242 / 94 and **258 / 89**; 59's three-equation system at 94 operations | 61; 57 | 57 |
| Thirteen positive | **34 / 93** (61) and **114 / 83** (62). 62 dominates 57's 132 / 83 and 59's 126 / 91 | 61; 62 | 61 |
| Fourteen positive | **26 / 92** (65) and **30 / 83** (64), against wave-8 **52 / 79** (55, 59). Dominated: 65's 30 / 85, 67's 30 / 87 and 63's 34 / 87. 67 and 63 also give five-equation systems at 78 operations | 64; 65 | 64 |
| Fifteen positive, fewest operations | unchanged: **66 ops** (51's P66, degree 157) | 51 | 51 |
| Fifteen positive, lowest degree | **24 / 88**: 58's 24 / 90 polynomial with z replaced by z + 1, in 88 operations (66). 60 has the same polynomial in 89 | 66; 60 | 60 |
| Fifteen positive, Pareto frontier | 157 / 66 (51); 125 / 67 (59); 101 / 68 (54); 91 / 69 (59); 80 / 70, 78 / 71 and 64 / 72 (54); 54 / 73 and 46 / 74 (56); 44 / 75 (47); 30 / 78, 26 / 87 and 24 / 88 (66). 66's 30 / 78 and 26 / 87 are 58's 30 / 79 and 26 / 88 polynomials, each evaluated in one operation fewer | 47, 51, 54, 56, 59, 66 | — |
| Integer quartic | **41ℤ** (26 residuals, 388 terms) | 64 | 64 |
| Integer sextic and octic | **35ℤ** sextic (20 residuals) and **30ℤ** octic (15 residuals) | 62 | 62 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125; 24ℤ at 1936 / 161 | waves 5–6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^429959** (54). No wave-9 package uses it; the active research's 443-operation H2082 instance does | 54 | 54 |

The combined frontier near the top of this README supersedes this table
where wave 10 improves on it.

## Wave 8 (sources 54–59)

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`54-calibrated-carry/`](54-calibrated-carry/) | `con-zfc-calibrated-carry-4b4349064a.zip` | *Calibrated carry thresholds and smaller equations for ZFC consistency* (README: *Calibrated carry thresholds for ZFC consistency*) | 9 positive: seven Pareto variants from 9,461,300 / **490** to 4,399,820 / 598 (recommended 4,400,764 / 564); 10ℤ: nine distinct polynomials from 25,838,224 / **513** to 14,696,016 / 558 (recommended 14,699,152 / 554); 15 / 1 / 101 / 68, 80 / 70, 78 / 71, **64 / 72** (recommended), 62 / 73, and 51's P66 rebound; everything on 46's **2^429959** tuple |
| [`55-congruence-norms/`](55-congruence-norms/) | `con_zfc_congruence_norms_2026-10-23.zip` | *Congruence separation and positive-word fusion* | 10ℤ / 1 / 9,152,284 / 586; 9 positive / 5,671,669 / 630 and 6,692,108 / 604; **14 / 1 / 52 / 79**; on 31's tuple |
| [`56-free-coordinate/`](56-free-coordinate/) | `ConZFC_Free_Coordinate_2026-10-23.zip` | *Free Pell coordinates and a smaller nine-variable equation for ZFC consistency* (README: *Free Pell coordinates: a smaller equation for ZFC consistency*) | 9 positive / 4,686,812 / 560 (reference form 562; ℕ 567 and 571); **15 / 1 / 54 / 73** (Q54) and **46 / 74** (Q46); on 31's tuple |
| [`57-separated-degrees/`](57-separated-degrees/) | `ConZFC_Separated_Degrees_2026-10-23.zip` | *Separated degrees and Pell quotients* | **12 / 1 / 242 / 94** and **258 / 89** (intermediate 314 / 91); 13 / 1 / 132 / 83; 9 positive / 2,628,944 / 499; **10ℤ / 1 / 8,317,400 / 544**; **45ℤ quartic**; the 9–13-variable forms on the 2^590069 tuple, the quartic on 34's |
| [`58-integral-root/`](58-integral-root/) | `ConZFC_Integral_Root_2026-10-23.zip` | *Integral-root carriers for Con(ZFC)* | **15 / 1 / 24 / 90**, 26 / 88 and 30 / 79; 12 / 1 / 629 / 114 (system 622 / 109, shifted 108); translations to 15ℕ (24 / 105) and 60ℤ (48 / 210); on the 2^590069 tuple |
| [`59-degree-separated/`](59-degree-separated/) | `ZFC_Diophantine_Degree_Separated_2026-10-23.zip` | *Degree-separated arithmetic encodings and an ordinary-root merger for Con(ZFC)* (README: *Degree-separated encodings and …*) | **9 positive / 1,910,404 / 473** (ℕ 480; initial 2,676,548 / 476); 10ℤ / 8,469,528 / 533; **13ℤ / 11,543,632 / 518** without Sun; 12 / 316 / 102 (system 288 / 95, shifted 94); 13 / 126 / 91; 14 / 52 / 79; 15-positive points from 125 / 67 to 46 / 75; on 31's tuple, except the thirteen-positive form and the three nine-variable comparisons, on 2^590069 |

Directory numbers put 59 last because it reviews and builds on 56 and 57.
59 ships its own `PLACEMENT.md`, suggesting the suffix
`degree-separated-wave8`. Each directory's `README.md` is its entry point.

### Identities and dominance (intake findings)

**How the dossiers checked.** Their own evaluators, not package code,
evaluated circuits modulo 2^127 − 1 with the actual fixed values. They
recounted every operation count and measured degrees in three ways:
- exactly, for circuits up to about degree 1,100;
- by truncated leading-term arithmetic, for the large circuits;
- or on the package's own cancellation-resolved certificate, after checking
  that it equals the primary (for 55's majorant form, D^16 times the
  primary).

Every measured figure agrees with its claim. One gap remains: 54's two
`support2048` nine-positive forms have no certificate, so their degrees
are confirmed only as bounded (about 6.04 million). The independent audit
confirmed 59's nine-variable and 13ℤ degrees exactly.

- **Pairwise different polynomials:**
  - the nine-positive forms of 54–57 and 59;
  - the ten-integer forms of 54, 55, 57 and 59;
  - the twelve-positive forms of 52, 57 (242, 258, 314), 58 and 59;
  - 58's fifteen-positive forms against every other short circuit;
  - 56's Q46 against 59's 46 / 75.
- **The same polynomial:**
  - 59's historical 44 / 76 reference is 49's `offset44`;
  - 59's 13ℤ intermediates `signed_seeded` and `signed` are 53's circuits,
    node for node;
  - 54's 24 ten-integer circuits contain only nine distinct polynomials
    with the actual fixed values (eighteen with random ones).
- **The same circuit on different tuples.** These are different
  polynomials, because the fixed values differ:
  - 59's 101 / 68 and 84 / 70 are 54's 101 / 68 and 54's retained 84 / 70
    comparison, and neither package cites the other;
  - 54's P66 is 51's circuit on 54's tuple.
- **Two fourteen-positive 52 / 79 forms.** 55's and 59's use the same tuple
  and the same residuals, but end differently: 59 squares N_a − 1, while 55
  squares N_a and subtracts 1. Their difference is 2 − 2N_a. Neither package
  cites the other.
- **Dominance within wave 8:**
  - 59's nine-positive form dominates every other;
  - 54's 5,370,068 / 532 dominates both of 55's nine-positive forms;
  - 57 dominates 56's nine-positive form, and 59's and 58's twelve-positive
    ones;
  - 54 and 56 dominate six of 59's nine new short forms: 84 / 70, 80 / 71,
    74 / 72, 60 / 73, 50 / 74 and 46 / 75. 47's 44 / 75 also dominates the
    last of these. 59's 101 / 68 ties 54's, and its new Pareto points are
    125 / 67 and 91 / 69.

### Tensions, not adjudicated at intake

- **Parallel discoveries.**
  - 57 and 59 both present degree separation as new; 59 learned of 57 only
    during packaging.
  - 54 and 59 reach the same short circuits independently.
  - 55 and 59 reach different fourteen-positive forms with the same metrics.
- **59's short frontier is stale.** Its frontier table and
  `short/FRONTIER_COMPARISON.json` do not mention 47's 44 / 75, though 47 is
  among its reviewed inputs. They mark 49's 44 / 76 and its own 46 / 75 as
  undominated. Only `review/LATE_REPLAY_SHORT_COMPARISON.json`, written after
  56 arrived, concedes the point.
- **An under-claimed record.** 54 calls its 215,492-byte tuple "not a new
  record". Against this README's table it is the first equation binding below
  2^590069, though its derived leaves are larger.
- **The active target moved.** The active research chose 52's 548-operation
  form after wave 7. Wave 8 dominates it (54's 490, 59's 473), and the
  active wave-8 review now adopts 59's form.
- **Stale README at the pins.** 55, 56, 57 and 59 observe that this README,
  at their pins, still described wave 6, or still called 67 operations
  unbeaten. That was true at the pins; the wave-7 reconciliation came later.
- **Transcriptions.** 56's baseline review gives 52's twelve-positive
  system as 888 / 102 and its eleven-positive system as 952 / 108,
  dropping "shifted" (here: system 888 / 103, shifted 102; system 109,
  shifted 108). 57's `WAVE7_AUDIT.md` labels both as shifted.
- **58's "improving".** 58's abstract calls its 629 / 114 an improvement on
  52's 897 / 108. It is a degree tradeoff, and within wave 8 it is dominated.
- **No package calls an earlier package or this README wrong.**

### Delivery discrepancies (wave 8)

- **Drivers fail in place.** Every driver reads files omitted at intake,
  and 56's and 59's also read their git-ignored `SHA256SUMS.json`. Rerun
  from the arrival archives, as `PLACEMENT.md` explains.

  | Dir | Driver | Note |
  |---|---|---|
  | 54 | `verify_release.py` | SymPy and NumPy; demands exact file-set equality |
  | 55 | `verify.py` | rewrites `REPRODUCTION.json`; its native check rewrites `VERIFICATION.json` |
  | 56 | `verify_all.py` | `nine/verify.py`, run directly, rewrites `nine/VERIFICATION.json` |
  | 57 | `reproduce.py` | rejects `-O`; writes its outputs in place |
  | 58 | `verify_all.py` | rewrites its circuits and receipts in place |
  | 59 | `verify.py` | NumPy and SymPy; works in a temporary copy |

- **Degree labels.** The ten-integer JSON of 54, 55 and 59 labels exact
  degrees `degree_upper_bound`, as wave-7 52's did. The dossiers measured
  them as exact.
- **Titles.** The PDF metadata titles of 55, 57 and 59 differ from their
  printed `\title`; 56's PDF has none.
- **Inside packages.**
  - 54's reviews name `check_literal_ledgers.py` and
    `check_separated_tuple.py`, and its `positive/README.txt` names
    `check_short*.log` receipts; none is shipped. Its NOTICE says "MIT
    license", while its licence files are MIT-0.
  - 56's `nine/hybrid_section.tex` is inputted nowhere. Its 571-operation
    natural reference form is in `nine/README.md` and `nine/PROOF.md` but
    not in the top-level tables.
  - 57's NOTICE says its upstream programs are not entry points, yet
    `reproduce.py` runs one. Its `RELOCATION_CHECK.json` counts 187 members
    for 191 files. `data/channel_certificate108.json` duplicates
    `channel_certificate.json`. The credit to 50 for U = 4q⁴ is only in
    `low_degree/PROOF.md`.
  - 58's `twelve/upstream/LEAN_PROOF.md` is 52's Y-absorption proof, about
    the "lean carrier", not a Lean proof. Its bibliography paraphrases the
    cited packages' titles.
  - 59's `positive/README.md` says its independent audit uses SymPy; it is
    standard-library only.
- **Licence and attribution.**
  - All six ship MIT-0 licence files for their new material and keep the
    inherited notices.
  - All state AI assistance and call their reviews internal. 59's author line
    reads "OpenAI-assisted research".
  - 54 calls 52 "the prior round-7 package". 59 calls 53 "the preceding
    32-page delivery in this conversation".
- **Active research files.**
  - 54 bundles post-pin copies of the active STATUS, OBJECT_ZFC and
    QUADRATIC_CODING at `d2f19e4d5c`.
  - 57 copies `OBJECT_ZFC.md` and 58 copies `STATUS.md`, both as of the pin.
  - 59 copies this README at `a71325bf18` and the wave-7 `PROPOSAL_REVIEW.md`
    as `review/LATE_*`.
- **Retained intermediates.**
  - 54: eight certificate circuits, fifteen alternative ten-integer layouts,
    three dominated nine-positive forms and two short comparisons.
  - 56: its degree certificates.
  - 57: the 314 / 91 form, the toy checker and the expanded quartic.
  - 58: its certificates and the copies of 47's and 52's prior forms.
  - 59: the nine-variable comparisons, five 13ℤ intermediates, the SOS
    576 / 103 and the 44 / 76 reference.

### Further questions (wave 8)

1. **Formalize.**
   - 56's order: the free-coordinate lemma, the two-block valuation, the
     evaluator certificate, then the compiler.
   - 58's scale-recovery and positive-gap lemmas.
   - The active wave-8 review lists the obligations for 59's form.
2. **Fewer unknowns.**
   - 59's three routes to twelve unrestricted integers.
   - 55's congruence freedom through the Lucas step.
   - 54's thirteenth unguarded coordinate, and an 11/12 coupling. 54 shows
     that naive radical deletion fails.
3. **Smaller circuits.**
   - 54's joint optimization of the source layout, and a lower defect.
   - 55's shorter target code and three-radicand identity.
   - 56's weighted minimum-norm combiner, and an η·ζ > 0 guard, which is
     unproved because the case where both are negative is not excluded.
   - 58's other monic carriers and selective witness elimination.
4. **Coefficients.** A smaller coherent tuple (55). The active wave-8
   review records a feasibility result for moving 59's form to a smaller
   tuple, without a certified circuit.
5. **Lower bounds.** Restricted lower bounds (54).

### Frontier after wave 8, as placed

Numbers are the packages' own. At intake, the dossiers recounted every
operation count and measured the degrees, as described above in this
section;
all checked figures agree with the claims. The mathematics was not
re-derived.

- "u / e / d / o" means unknowns / equations / degree / operations; pairs
  are degree / operations.
- Operations count every binary +, −, × including multiplication by fixed
  numerals; reuse and system comparisons are free.
- Unknowns are strictly positive unless marked ℤ (unrestricted integers)
  or ℕ (naturals). Natural-coordinate companions have separate counts:
  - in wave 7, package 52 adds three operations, 47 adds four, and 53's
    calibrated form adds six;
  - in wave 8, 54 adds three, 57 two, 55 six, 56 seven (nine for its
    reference form), 59 seven (four for its initial form), and 58's
    natural translation fifteen.

  The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Nine positive | **1,910,404 / 473**, the lowest degree and the fewest operations at once (ℕ: 480). It dominates every other nine-positive form, among them 54's 9,461,300 / 490 and 4,399,820 / 598, 57's 2,628,944 / 499, 56's 4,686,812 / 560, 55's 5,671,669 / 630, 59's own initial 2,676,548 / 476, and wave-7 52's 548 and 53's 7,344,328 | 59 | 59 |
| 10ℤ (Sun's reduction), lowest degree | **8,317,400 / 544** | 57 | 57 |
| 10ℤ, fewest operations | **513** at degree 25,838,224, on 46's 2^429959 tuple | 54 | 54 |
| 10ℤ, other Pareto points | 59: 8,469,528 / 533. 54: 25,355,280 / 517 and 24,369,008 / 519. Dominated by 59's 533: 54's recommended 14,699,152 / 554 and 14,696,016 / 558. Dominated by 57 and 59: 55's 9,152,284 / 586. Every wave-7 10ℤ form is dominated too | 59; 54 | — |
| Fewest integers without Sun's 2026 reduction | **13ℤ at 11,543,632 / 518**, beating wave-7 53's 57,866,184 / 759 on both measures | 59 | 59 |
| Eleven positive | unchanged: **954 / 113** (52) | wave 7 | 52 |
| Twelve positive | **242 / 94** and **258 / 89**, two different polynomials | 57 | 57 |
| Twelve positive, other points | 59: 316 / 102. Its three-equation system has residual degrees 2, 26 and 288 in 95 operations, or 94 shifted, the fewest of any twelve-positive system (52's was 103, shifted 102). Dominated: 58's 629 / 114 (system 622 / 109, shifted 108) and wave-7 52's 897 / 108 | 59 | — |
| Thirteen positive | **132 / 83** (57), which dominates the earlier single thirteen-positive equations (wave-4 24's 319 / 89, and 515 / 84 of wave-4 16 and 20); 126 / 91 (59) is a lower-degree tradeoff. The wave-4 systems 288 / 81 (24) and 488 / 78 (16, 20) are counted separately | 57; 59 | 57 |
| Fourteen positive | **52 / 79** in two different polynomials, each dominating wave-7 50's 56 / 79 | 55; 59 | 55 |
| Fifteen positive, fewest operations | unchanged: **66 ops** (51's P66, degree 157) | 51 | 51 |
| Fifteen positive, lowest degree | **24 / 90**; also 26 / 88 and 30 / 79 | 58 | 58 |
| Fifteen positive, Pareto frontier | 157 / 66 (51); 125 / 67 (59); 101 / 68 (54; 59 has the same circuit on another tuple); 91 / 69 (59); 80 / 70, 78 / 71 and 64 / 72 (54); 54 / 73 and 46 / 74 (56); 44 / 75 (47); 30 / 79, 26 / 88 and 24 / 90 (58). P67 (155 / 67) is now dominated by 59's 125 / 67, and wave-2 Q₅₆ (56 / 74) by 56's 46 / 74 | 47, 51, 54, 56, 58, 59 | — |
| Integer quartic | **45ℤ**: the sum of squares of 28 quadratic residuals, 407 expanded terms, below the 50ℤ quartic | 57 | 57 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125; 24ℤ at 1936 / 161 | waves 5–6 | — |
| Smallest coefficients binding an equation | **B = 2^429959** (215,492 bytes), 46's adapter tuple. 54 binds every equation to it, P66 included, but calls the size "not a new record". Its derived fixed leaves are larger: the scale Y_scale alone takes 1.7 MB. Next comes 2^590069 (39 and 44; also 52, 57, 58, and 59's thirteen-positive form and nine-variable comparisons) | 54 | 54 |

**Who knew whom.** Only 59 saw other wave-8 work, 56 and 57, and it
composed 56's free coordinate into its nine-positive form. 54 and 55 did not
know 59. 59 did not know 54 or 58, so its own frontier tables are partly
dominated (see the wave-8 tensions above).

The combined frontier near the top of this README supersedes this table
where wave 9 improves on it.

## Wave 7 (sources 46–53)

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`46-selective/`](46-selective/) | `con-zfc-selective-2026-10-23.zip` | *Selective coefficient extraction for explicit ZFC consistency equations* | 10ℤ / 1 / 35,876,184 / 640; 9 positive / 1 / 19,615,180 / 606; P74 15 / 1 / 68 / 74 (36's tuple); a coefficient adapter B = 2^429959 binding no equation |
| [`47-sparse-support/`](47-sparse-support/) | `ConZFC_Sparse_Support_2026-10-23.zip` | *Sparse support packing for explicit Diophantine consistency equations* | 9 positive / 25,936,016 / 651 and 23,878,392 / 670; 10ℤ / 71,151,176 / 662 and 65,506,504 / 675; 15 / 1 / 44 / 75 and 44 / 76 |
| [`48-majorants/`](48-majorants/) | `con-zfc-support-majorants-2026-10-23.zip` | *Smaller explicit Diophantine equations for ZFC consistency* | 9 positive, six variants from 15,534,796 / 655 to 29,157,244 / 562; 10ℤ / 53,325,896 / 595 and 39,914,856 / 651 |
| [`49-support-pell/`](49-support-pell/) | `con_zfc_sparse_support_2026-10-23.zip` | *Support-aware digit coding and sharper Pell norms: Explicit Diophantine equations for the consistency of ZFC* (README: *…for Con(ZFC)*) | 9 positive / 32,568,568 / 652; 10ℤ / 59,564,744 / 653; 11 / 1 / 990 / 117 and 994 / 115 (systems 988 / 113, 992 / 111, shifted 112, 110: delivered circuits whose operation counts appear only in `eleven/generated/BUILD_RECEIPT.json`); 15 / 1 / 44 / 76 |
| [`50-midpoint11/`](50-midpoint11/) | `ConZFC_Support_Sensitive_2026-10-23.zip` | *Smaller explicit Diophantine equations for ZFC consistency* | **11 / 1 / 954 / 115** (systems 111, shifted 110), full carrier 958 / 116; 9 positive / 30,947,584 / 651; 10ℤ / 56,593,864 / 653; **14 / 1 / 56 / 79** |
| [`51-sparse-arith/`](51-sparse-arith/) | `con_zfc_sparse_arithmetic_2026-10-23.zip` | *Sparse target packing and arithmetic separation for Diophantine consistency* (README: *Sparse packing and arithmetic simplifications for Con(ZFC)*) | 10ℤ / 54,768,104 / 709; 9 positive / 33,332,620 / 682; **P66 15 / 1 / 157 / 66**, P68 113 / 68, P72 80 / 72, P74 68 / 74 (36's tuple) |
| [`52-sparse-pell/`](52-sparse-pell/) | `con-zfc-sparse-pell-124c07c0b7.zip` | *Sparse quadratic coding and shorter Pell finalizers for ZFC consistency* | 9 positive / 10,486,092 / 603, **15,502,748 / 548**, 10,127,484 / 655; 10ℤ / 34,378,296 / 637, **50,822,936 / 582**, 33,202,776 / 689; **11 / 1 / 954 / 113** (system 109, shifted 108); **12 / 1 / 897 / 108** (system 888 / 103, shifted 102); on the 2^590069 tuple |
| [`53-selective-quad/`](53-selective-quad/) | `ZFC_Diophantine_Selective_Quadratic_2026-10-23.zip` | *Selective quadratic encodings and smaller Pell norms for the consistency of ZFC* | **10ℤ / 21,111,400 / 659**; **9 positive / 7,344,328 / 738**, 12,023,320 / 734; **13ℤ / 57,866,184 / 759** without Sun's 2026 reduction (unseeded 71,382,096 / 770); 11 / 958 / 117 and 962 / 115; P72 15 / 1 / 80 / 72 |

Directory numbers follow arrival (file-time) order. Two packages suggest
other names: 48 suggests `46-support-majorants` and 51 `46-sparse-arithmetic`.
53 ships its own `PLACEMENT.md` inside its directory. Each directory's
`README.md` is its entry point.

### Codes, tails and tuples

- **Polynomial identities.** The dossiers evaluated circuits modulo 2^127 − 1
  with the actual fixed values:
  - the 10ℤ circuits of 40, 43, 46, 47 (two), 48 (two) and 49 are pairwise
    different polynomials, and so are the nine-positive circuits of 45, 46,
    47 (two), 48 (six) and 49;
  - the 9- and 10-variable forms of 50–53 differ from all of these by
    degree;
  - wave-6 41's 10ℤ remains the same polynomial as 44's `sun_b4`;
  - the eleven-positive forms of 38, 49, 50, 52 and 53 are pairwise
    different;
  - 52's twelve-positive 897 form differs from 44's.
- **Shared tails.** Where the dossiers compared them, the finalizers are
  shared literally, and the differences lie in the source coding:
  - one Sun finalizer is common to the 10ℤ circuits of 40, 43, 46, 47, 48
    and 49;
  - one Jones tail is common to 45, 46, 47, 49 and 48's "inherited"
    variants.

  51 replaces the Sun norm weights by (1, b, bK), and 52 refactors its
  tails.
- **Shared templates.** 40, 47, 48-uniform, 49 and 50 (W = 190) share the
  ten-integer template deg = 297088W + 147144, where W is the weight
  maximum.
- **Different conventions.** The packages count the parent's monomials as
  62 (raw coordinates, 46) or 71 (shifted, 47–50, 52, 53). The source base
  differs too:
  - 40's 2^2140030 in 46–51;
  - 43's 2^2134940 in 53;
  - 2^1182966 in 52.
- **Tuples.** 46–51 and 53 use 31's tuple, with 36's for the 15-unknown
  short forms of 46 and 51. 52 uses the 2^590069 tuple (bytes identical to
  44's). Fixed leaves are materialized in 48 (16 leaves, 3,331,623 bytes), 51
  and 52; in 46 and 53 they are recipes.

### Tensions, not adjudicated at intake

- **67 → 66 operations.** See the note under "Frontier after wave 7, as
  placed" below.
- **Independent discoveries.** 46–50, 52 and 53 each present support-aware
  or selective isolation as new, and 51 its sparse targets; none cites
  another.
- **Combining 38 and 44.** 49, 50, 52 and 53 each note that 38's index
  absorption and 44's norm cannot simply be juxtaposed. A compatibility
  lemma is needed, because 44's bound Ig − cf > 1 used the old index
  quotient. 53's review calls the unqualified assertion "false". This
  concerns the combination; **no package says 38's own eleven-positive
  proof is wrong.** 38's result still awaits independent review.
- **Stale README at the pin.** 47, 49, 50, 51 and 52 observe that this README,
  at their pin `124c07c0b7`, still described wave 5 only. That was true: the
  wave-6 reconciliation came later, in `613e12db0c`.
- **Missed baselines.**
  - 46's and 51's P74 (68 / 74) do not mention wave-2 Q₅₆ (56 / 74), which
    dominates them.
  - 52 cites two wave-6 details that the wave-6 text below omits: 38's
    translated shifted system 1138 / 124, and the degree 896 of 44's shifted
    104-operation three-equation system.
- **No package calls an earlier package or this README wrong.**

### Delivery discrepancies (wave 7)

- **Drivers fail in place.** Every driver reads files omitted at intake or
  ignored ledgers. Rerun from the arrival archives, as `PLACEMENT.md`
  explains.

  | Dir | Driver | Note |
  |---|---|---|
  | 46 | `verify.py` | |
  | 47 | `verify_release.py` | |
  | 48 | `verify_release.py` | |
  | 49 | `verify_all.py` | NumPy; it also rewrites `audits/ALL_CHECKS.json` |
  | 50 | `verify.py` | NumPy |
  | 51 | `verify_all.py` | |
  | 52 | `verify_release.py` | SymPy and NumPy |
  | 53 | `verify.py` | SymPy and NumPy |

- **Licence and attribution.**
  - Every package states AI assistance, and most add that its reviews are
    not external human review.
  - **47 ships no licence file for its main new material**, which it supplies
    "under its existing project arrangements". The others ship MIT-0.
  - Every package ships the K215 machine notices; in 48 and 52 they are
    inside the bundled copies of earlier packages.
  - 52 calls wave-6 45 "own prior work", and 53 calls wave-6 44 "our
    preceding B4 delivery".
- **Inside packages.**
  - 49 states its systems' operation counts only in a build receipt.
  - 52's METRICS file labels the 10ℤ degrees "upper_bound", while its text
    says they are exact.
  - 51's README speaks of seven polynomials; its report states three
    theorems.
- **Active research files.** The active research in this directory's parent
  predates the wave-7 pin, and some wave-7 packages build on it:
  - **Short forms.** 46, 51 and 53 start their 15-unknown short forms from
    the active research's checked circuits P69, P73 and P75. 46's P74
    equivalence uses the active checked P75 / P69 ↔ P67 result.
  - **At-pin copies.** 46, 47, 48, 50, 51 and 53 bundle copies of active
    files as of the pin (`Lean/DiophantineConsistency/ZFC.lean`,
    short-circuit notes, P75). Most were omitted at intake as copies.
  - **Post-pin snapshots.**
    - 52 bundles one at `2d7766807b`, a merge of active Lean work.
    - 53 bundles one at `59e9d4d22b`. Its STATUS lists the active P76 (76
      operations, degree 64), and 53 notes the active `ExplicitZFC`
      theorems.
  - **Delivered certificates.** None of the packages supplies an end-to-end
    formal certificate for its new construction. Subsequent active stage
    proofs for 52 are tracked in [SELECTIVE_SOURCE52.md](../SELECTIVE_SOURCE52.md).
- **Retained intermediates.**
  - 46's target search;
  - 47's `search/`;
  - 48's T16 adapter and candidate tuple 2^572455 (not delivered);
  - 50's full-carrier variant;
  - 52's dominated 9 / 10 variants;
  - 53's dominated two-block form and the inherited 61-op system.

### Further questions (wave 7)

1. **Formalize.**
   - The selective-extraction and borrow lemmas (46, 53).
   - The U = 4q⁴ lemma (50).
   - The two-block carry lemma (53).
   - The compiler bridge (47, 48, 50).
   - Feeding the sparse interface to the active Jones compiler (52).
2. **Joint optimization.** Optimize weights, targets and parent together
   (46, 47, 48, 51, 52), using equal coefficient vectors (46). Lower bounds
   for the weights (50).
3. **Better finalizers.** A third-order majorant, a signed conditional
   separator and further absorption (52); Pell-remainder separators (51).
4. **Coefficients.** A smaller tuple, but only with a full adapter (46,
   48, 53).
5. **Fewer unknowns.** None of the packages claims anything below nine
   positive, ten unrestricted-integer or eleven positive unknowns at
   moderate degree, and 52 and 53 decline ten positive.

### Frontier after wave 7, as placed

Numbers are the packages' own; **none was re-derived at intake.**

- "u / e / d / o" means unknowns / equations / degree / operations.
- Operations count every binary +, −, × including multiplication by fixed
  numerals; reuse and system comparisons are free.
- Unknowns are strictly positive unless marked ℤ (unrestricted integers)
  or ℕ (naturals). Natural-coordinate companions have separate counts:
  package 52 adds three operations, 47 adds four, and 53's calibrated form
  adds six. The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| 10ℤ (Sun's reduction), lowest degree | **21,111,400 / 659** | 53 | 53 |
| 10ℤ, fewest operations | **582** at degree 50,822,936 | 52 | 52 |
| 10ℤ, other Pareto point | 52: 34,378,296 / 637. Dominated: 52's 33,202,776 / 689 (by 53's 659), 46's 35,876,184 / 640 (by 52's 637) and 48's 53,325,896 / 595 (by 52's 582) | 52 | — |
| Fewest integers without Sun's 2026 reduction | **13ℤ at 57,866,184 / 759**, which beats wave-6 44's 13ℤ and 14ℤ on every measure | 53 | 53 |
| Nine positive, lowest degree | **7,344,328 / 738** | 53 | 53 |
| Nine positive, fewest operations | **548** at degree 15,502,748 | 52 | 52 |
| Nine positive, other Pareto points | 52: 10,127,484 / 655, 10,486,092 / 603. Dominated: 53's 12,023,320 / 734 (by 52's 655), 46's 19,615,180 / 606 and 48's 15,534,796 / 655 (by 52) | 52 | — |
| Eleven positive | **954 / 113**, system 109 (shifted 108) (52). 50's midpoint 954 / 115 (systems 111 / 110) is a different polynomial, dominated by 52's. Also 49's 990 / 117 and 994 / 115, 53's 958 / 117 and 962 / 115, wave-6 38's 1154 / 123 | 52; 50 | 52 |
| Twelve positive | **897 / 108**, three-equation system 888 / 103, shifted 102. It ties the old fewest-operations record (108, system 102) at lower degree than wave-6 44's 901 | 52 | 52 |
| Fourteen positive | 56 / 79 (a new point) | 50 | 50 |
| Fifteen positive, fewest operations | **66 ops** (P66, degree 157, on 36's tuple). See the note below | 51 | 51 |
| Fifteen positive, other points | 51: P68 113 / 68, P72 80 / 72, P74 68 / 74; 53: P72 80 / 72, a different polynomial; 47: 44 / 75; 49: 44 / 76. Wave-2 Q₅₆ (56 / 74) still dominates both 74-op forms (51's and 46's P74) | 47, 49, 51, 53 | — |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125; the 50ℤ quartic; 24ℤ at 1936 / 161 | waves 5–6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^590069** (wave-6 39 and 44; 52 binds its new 9, 10, 11 and 12 forms to it). 46's adapter B = 2^429959 binds no equation | 39, 44 | 39 |

**The 66-operation equation.** 51's P66 is obtained from the old P67 by the
substitution T ↦ fT. It trades two degrees for one operation: degree 157
against P67's 155. P67 (155 / 67) remains the lowest-degree point at 67
operations or fewer.

The same substitution gives 51's P68, P72 and P74 from P69, P73 and P75.
Those are the active research's Lean-checked short circuits in
`Computability/DiophantineConsistency/circuits/`. The dossier and the audit
checked these identities at random points and on 36's tuple. Since the substitution is not invertible over the positive
integers, 51 proves P66's equivalence separately; it says P66 "is not an
identity" with the old polynomial at the same coordinates. 46, 47, 48, 49,
50, 52 and 53 each still call 67 operations unbeaten, without knowing of 51.

The combined frontier near the top of this README supersedes this table
where waves 8–10 improve on it.

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

### Frontier after wave 6, as placed

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

The combined frontier near the top of this README supersedes this table
where waves 7–10 improve on it.

## Wave 5 (sources 31–37)

Wave 5 is described as placed, with its frontier at that time. The
combined frontier above supersedes it where waves 6–10 improve on it.

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
  - The active Lean research in `Computability/DiophantineConsistency/`
    postdates the wave-5 and wave-6 pins, but not the wave-7 to wave-10
    pins.
  - Wave-7 46, 51 and 53 build their short forms on its checked circuits
    P69, P73 and P75.
  - Wave-8 54 cites its later closed executable equation (at
    `d2f19e4d5c`), 56 its `ExplicitZFC` and `NativeZFC` theorems, and 59
    also `PositiveZFC` and the short-circuit theorems. Each says these do
    not certify its new circuits.
  - Wave-9 66's `direct/` calibrates through the existing
    `KEndpoint.c222_iff_zf_refutation` and
    `ConstructibleChoice.zf_refutation_iff_zfc_refutation`; its global
    constructor is an unelaborated Lean sketch with no theorem.
  - Wave-10 68's `direct/` constructor is likewise uncompiled and proves
    no theorem; 75's `certificates/` and `direct/` are proved interface
    lemmas, not equations.
  - No package supplies a new end-to-end formal certificate. Subsequent
    active stage formalization is recorded separately below.
- **No new general theorem.**
  - The ten-integer reduction is attributed to Sun. 31 "does not claim a new
    general ten-unknowns theorem".
  - Wave-6 packages cite Sun's 2026 preprint as a dependency, not as their
    own result. 42 calls it "a preprint dependency".
  - In wave 8, the 10ℤ forms of 54, 55, 57 and 59 depend on it. 59's 13ℤ
    form and every nine-positive form do not.
  - In wave 9, the 10ℤ forms of 65, 66 and 67 depend on it; 67's 13ℤ form
    does not.
  - In wave 10, only 68's ten-integer form depends on it.
  - 38 says its nine-variable form "does not extend the result to nine
    unrestricted integers". 44 makes no sub-ten-integer or sub-nine-natural
    claim.
  - 31's review is not an independent audit of Sun's Lucas theorems.
  - 31 warns that ten integers "should not be compared … as if the domains
    were identical".
- **No consistency proof.** The theorems are equivalences, and every
  package disclaims a consistency proof; most also say they decide neither
  side. Several add that a two-sided independence claim needs an extra
  hypothesis: wave-5 32, 33, 36; wave-6 41, 43, 45; wave-7 48, 52.
- **Domains.** Positive and nine-variable equations must not be read over ℤ;
  the domains of different forms are not interchangeable.
- **No optimality.** No global minimum is claimed. The only claim below 67
  operations is 51's P66 (66 operations, degree 157); no package claims
  fewer. No form below nine unknowns or ten unrestricted integers is
  claimed. 59 lists three routes to twelve unrestricted integers as
  unproved in `signed/NO_TWELVE_VARIABLE_CLAIM.md`; its counterexamples
  there show that two shortcuts in its own 13ℤ proof are invalid.

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
  - Wave-7 packages likewise use the ratio lemmas directly. 51 lists a
    20-file Jones closure, which it did not rebuild.
  - Wave-8 54, 55, 56, 57 and 59 use the ratio lemmas for their
    nine-variable forms. 58 uses no Jones lemma: its 12- and 15-positive
    forms are direct.
  - Every wave-9 nine-positive form keeps 59's Jones ratio finalizer.
    The 12- to 15-positive forms and the integer quartics, sextics and
    octics of wave 9 use no Jones lemma.
  - In wave 10, only 71's nine-positive form uses the Jones ratio
    finalizer.
  - No package uses `Jones1982.nine_unknowns`, which fixes ν = 58.

  These new codes, decoders, finalizers, majorants and Pell-index arguments
  were not formally certified by the delivered packages. Subsequent active
  work now checks 52's literal source, masks, ranges, ratio substitution,
  finalizer and assembled arithmetic source equivalence; see
  [SELECTIVE_SOURCE52.md](../SELECTIVE_SOURCE52.md). Native calibration and
  the internal ZFC equivalence remain open. Several delivered arguments
  rest on the structure of Lean proofs
  rather than their statements, for example:
  - the square base, via `Jones1982.USys_of_mem`;
  - 53's 13ℤ cofinal base, which uses the witness chosen inside the proof
    of `Jones1982.exists_B25core`;
  - 59's 13ℤ argument, which uses lines inside `Ratio.lean` and
    `NineRatio.lean`. Both files still match 59's pinned checksums.
- **Sun.** Every 10ℤ form depends on Sun's 2026 preprint and his 2021 paper.
  31 cites Proposition 2.1, Theorems 3.1 and 4.1, Propositions 6.1–6.2 and
  §7 of the preprint. 55, 57 and 59 cite Propositions 6.1–6.2. These are
  external, unformalized and were not checked at intake.
- **Active research.** `Computability/DiophantineConsistency` (outside this
  directory) holds checked Lean work on a Diophantine consistency equation;
  see its [README](../README.md) and STATUS. This report's packages are not
  part of that formal development.
  - Wave-7 53 notes the active `ExplicitZFC` theorems
    (`noSyntaxZero_iff_conZFC`, `noNaturalZero_iff_conZFC`). It says they do
    not certify its circuits.
  - Wave-7 51 says the active results are "not silently promoted".
  - The active research reviewed wave 8 in
    [PROPOSAL_REVIEW_WAVE8.md](../PROPOSAL_REVIEW_WAVE8.md) (`94d84e5c1b`),
    after replaying all six arrival archives. It adopts 59's 473-operation
    nine-positive form as its target.
  - It reviewed wave 9 in [PROPOSAL_REVIEW_WAVE9.md](../PROPOSAL_REVIEW_WAVE9.md)
    (`bdd86761ba`), replaying all eight archives, and adopts 66's
    444-operation H2082 form, with a local 443-operation instance on 54's
    tuple. Its [ALTERNATIVE_ENCODINGS.md](../ALTERNATIVE_ENCODINGS.md)
    records a Lean-checked direct quartic that skips Jones
    (`DirectQuarticZFC.noNaturalZero_iff_conZFC`, `da269a4f57`).
  - It reviewed wave 10 in [PROPOSAL_REVIEW_WAVE10.md](../PROPOSAL_REVIEW_WAVE10.md)
    (`1affa014c2`), replaying all eight archives. It keeps its
    443-operation nine-positive target and its one-page P69
    presentation, and records the wave-10 records as alternative
    targets.
- **Nothing delivered in this report is formalized.** The active stage
  proofs for 52 live outside this directory.

## Licence and provenance

Every package was prepared for ProveIt and reuses MIT-0 repository material;
see the licence notes in each wave's section. Every licence, notice and
attribution file the packages ship is kept in place.

| Wave | Pin | Arrival | Placement |
|---|---|---|---|
| 5 | `8c6eec9d19ef80538c8e61ff6e0180040583446a` | `b7f8b75b5b` | `952c1fab49` |
| 6 | `22e75dd6b87b1b199bb08c778d7cf075ae5aae08` | `29ca562f8f` | `124c07c0b7` |
| 7 | `124c07c0b77a9e20e84676514d8b1ff78536ea3f` | `4b4349064a` | `6d375f2d2d` |
| 8 | `4b4349064a750ba6347293b55874a7f92abdd0db` (54–57, 59); `6d375f2d2deac0519e659bbce5b48087023c1430` (58) | `7331974b69` | `beb0192cb8` |
| 9 | `beb0192cb8dc36f78c369c080f2adfbc1887a486` | `0c6be9a074` | `a2cd79b912` |
| 10 | `a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49` or `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` | `9513bd88ce` | `d79b41884d` |

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
- `46-selective/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `RESULTS.json`, `SOURCES.json`, `SUPPORT_PROOF.md`, `report.pdf`, `report.tex`, `target_table.tex`, `verify.py`
- `46-selective/assets/`: `pair_sums.png`
- `46-selective/certificates/`: `DOCUMENT_REVIEW.json`, `RELEASE_VERIFICATION.json`, `candidate_independent_audit.json`, `degree.json`, `metrics.json`, `support_verification.json`, `weights175_certificate.json`
- `46-selective/code/`: `audit_candidate.py`, `build.py`, `make_figure.py`, `optimize_targets.py`
- `46-selective/coefficient_adapter/`: `README.md`, `SEPARATED_PROOF.md`, `SOURCES.json`, `UPSTREAM_COEFFICIENT_NOTICE.md`, `UPSTREAM_LICENSE`, `audit_separated.py`, `build_separated.py`, `paper_section.tex`, `separated_audit.json`, `separated_results.json`
- `46-selective/coefficient_adapter/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `46-selective/coefficient_adapter/separated_coefficients/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `46-selective/coefficients/`: `REPRODUCTION.json`, `reconstruct_native.py`
- `46-selective/data/`: `coefficient_recipes.json`, `layout.json`, `polynomial.json`, `raw_recipes.json`
- `46-selective/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE.source31.md`, `NOTICE.source40.md`
- `46-selective/nine/`: `PROOF.md`, `README.md`, `build_nine.py`, `paper_section.tex`, `verify_nine.py`
- `46-selective/nine/data/`: `layout.json`, `raw_recipes.json`
- `46-selective/nine/generated/`: `VERIFICATION.json`, `selective_nine_natural.json`, `selective_nine_natural_degree_certificate.json`, `selective_nine_positive.json`, `selective_nine_positive_degree_certificate.json`
- `46-selective/short/`: `README.md`, `RESULT.md`, `SOURCES.json`, `p74_audit.json`, `p74_norm_minima.json`, `verify_p74.py`
- `46-selective/upstream/`: `ACTIVE_RESEARCH.md`, `ACTIVE_STATUS.md`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE.source31.md`, `NOTICE.source40.md`, `SOURCE_PROVENANCE.json`
- `47-sparse-support/`: `Makefile`, `NOTICE.md`, `README.md`, `RELEASE_HASHES.json`, `RESULTS.json`, `SOURCE_PINS.json`, `verify_release.py`
- `47-sparse-support/construction/`: `INDEPENDENT_MATHEMATICAL_AUDIT.md`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `SPARSE_PROOF.md`, `audit_exported_circuits.py`, `audit_nine_independent.py`, `audit_sparse_source.py`, `build_sparse_nine.py`, `build_sparse_ten.py`, `canonical_gzip.py`, `circuit.py`, `coeff_poly.py`, `fixed_coefficients.json`, `fixed_coefficients10.json`, `independent_export_certificate.json`, `materialize.py`, `materialize_ten.py`, `nine_independent_audit.json`, `source_certificate.json`, `source_independent220.json`, `source_independent239.json`, `targets_sparse220.json`, `targets_sparse239.json`, `verification_optimized_receipt.json`, `verification_receipt.json`, `verify.py`, `verify_source.py`
- `47-sparse-support/construction/coefficients/fixed10/`: `beta_source.bin.gz`, `c001.bin.gz`, `c002.bin.gz`, `c003.bin.gz`, `c004.bin.gz`, `c005.bin.gz`, `c007.bin.gz`, `c008.bin.gz`, `c009.bin.gz`, `c010.bin.gz`, `c011.bin.gz`, `c012.bin.gz`, `c013.bin.gz`
- `47-sparse-support/construction/generated/`: `sparse220_nine_natural.json`, `sparse220_nine_natural_degree_certificate.json`, `sparse220_nine_positive.json`, `sparse220_nine_positive_degree_certificate.json`, `sparse220_ten_integer.json`, `sparse220_ten_integer_degree.json`, `sparse239_nine_natural.json`, `sparse239_nine_natural_degree_certificate.json`, `sparse239_nine_positive.json`, `sparse239_nine_positive_degree_certificate.json`, `sparse239_ten_integer.json`, `sparse239_ten_integer_degree.json`
- `47-sparse-support/construction/licenses/`: `31-sun10__LICENSE`, `31-sun10__NOTICE.md`, `40-packing10__LICENSE`, `40-packing10__NOTICE.md`, `45-multioutput__LICENSE-NEW-MATERIAL.txt`, `45-multioutput__NOTICE.md`, `k215__LICENSE`, `k215__LICENSE.Wade`, `k215__NOTICE-K215.md`
- `47-sparse-support/construction/search/`: `README.md`, `search.cpp`, `search_full.cpp`, `support.txt`, `support_full.txt`, `weights120.json`, `weights_full221.json`
- `47-sparse-support/evidence/31-sun10/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `47-sparse-support/evidence/active/`: `COMPILER.md`, `README.md`, `STATUS.md`
- `47-sparse-support/minima/`: `LICENSE`, `MINIMA_PROOF.txt`, `NOTICE.txt`, `README.txt`, `SOURCE_PINS.json`, `build_minima.py`, `evaluate.py`, `fixed_coefficients.json`, `gap_minima75.json`, `gap_minima76.json`, `gap_system61.json`, `minima_supplement.tex`, `verification_receipt.json`, `verify.py`
- `47-sparse-support/minima/licenses/`: `10-synthesis14__LICENSE`, `12-gap-norm14__LICENSE`, `12-gap-norm14__NOTICE.md`, `31-sun10__LICENSE`, `31-sun10__NOTICE.md`, `k215__LICENSE`, `k215__LICENSE.Wade`, `k215__NOTICE-K215.md`
- `47-sparse-support/minima/upstream/`: `GAP_AUXILIARY_PROOF.md`, `ORDINARY_REDUCTION.md`, `POSITIVE_GAP_SHEARS.md`, `ordinary_gap_sos78.json`
- `47-sparse-support/report/`: `minima_supplement.tex`, `report.pdf`, `report.tex`, `ten_integer_supplement.tex`
- `47-sparse-support/verification/`: `environment.json`, `pdf_review.json`, `reproduction_receipt.json`
- `48-majorants/`: `ADDITIONAL_PROVENANCE.json`, `INTEGRATION.md`, `LICENSE`, `NOTICE.md`, `README.md`, `REFINED_VERIFICATION.json`, `RELEASE_VERIFICATION.json`, `SOURCE_COMPONENT_README.md`, `SOURCE_PROOF.md`, `SOURCE_PROVENANCE.json`, `VERIFICATION.json`, `comparison_table.tex`, `degree_table.tex`, `layout_table.tex`, `metrics.tex`, `refined_tail.tex`, `report.pdf`, `report.tex`, `verify.py`, `verify_refined.py`, `verify_release.py`
- `48-majorants/code/`: `build.py`, `build_refined.py`, `common.py`, `materialize_fixed.py`, `nine_majorant.py`, `nine_refined.py`, `nine_tail.py`, `ten_tail.py`
- `48-majorants/data/`: `coefficient_recipes.json`, `overlap_layout.json`, `weights.json`
- `48-majorants/data/fixed/`: `MANIFEST.json`, `c000.bin.gz`, `c001.bin.gz`, `c002.bin.gz`, `c003.bin.gz`, `c004.bin.gz`, `c007.bin.gz`, `c008.bin.gz`, `c009.bin.gz`, `c010.bin.gz`, `c011.bin.gz`, `c012.bin.gz`, `c013.bin.gz`, `c014.bin.gz`
- `48-majorants/generated/`: `overlap_nine_natural.json`, `overlap_nine_natural_degree_certificate.json`, `overlap_nine_positive.json`, `overlap_nine_positive_degree_certificate.json`, `overlap_ten_integer.json`, `uniform_nine_natural.json`, `uniform_nine_natural_degree_certificate.json`, `uniform_nine_positive.json`, `uniform_nine_positive_degree_certificate.json`, `uniform_ten_integer.json`
- `48-majorants/inherited/31-sun10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `48-majorants/inherited/31-sun10/signed10/`: `NOTICE.md`
- `48-majorants/inherited/40-packing10/`: `LICENSE`
- `48-majorants/inherited/45-multioutput/`: `NOTICE.md`
- `48-majorants/proofs/`: `FOUNDATION_AUDIT.md`, `HIGHER_MAJORANT.md`, `HIGHER_MAJORANT_AUDIT.json`, `MAJORANT2048_INDEPENDENT.json`, `NINE_APPROXIMANT_REVIEW.md`, `NINE_T16_REVIEW.md`, `NINE_T2048_REVIEW.md`, `NINE_WEIGHT_REVIEW.md`, `SUPPORT179_INDEPENDENT.json`, `SUPPORT_OVERLAP_INDEPENDENT.json`, `check_majorant2048_independent.py`, `check_support_independent.py`, `verify_higher_majorant.py`
- `48-majorants/refined/`: `metrics.json`, `overlap_nine_natural_major2048.json`, `overlap_nine_natural_major2048_degree_certificate.json`, `overlap_nine_natural_v8.json`, `overlap_nine_natural_v8_degree_certificate.json`, `overlap_nine_positive_major2048.json`, `overlap_nine_positive_major2048_degree_certificate.json`, `overlap_nine_positive_v8.json`, `overlap_nine_positive_v8_degree_certificate.json`, `uniform_nine_natural_major2048.json`, `uniform_nine_natural_major2048_degree_certificate.json`, `uniform_nine_natural_v8.json`, `uniform_nine_natural_v8_degree_certificate.json`, `uniform_nine_positive_major2048.json`, `uniform_nine_positive_major2048_degree_certificate.json`, `uniform_nine_positive_v8.json`, `uniform_nine_positive_v8_degree_certificate.json`
- `48-majorants/upstream/Computability/DiophantineConsistency/`: `COMPILER.md`, `STATUS.md`
- `49-support-pell/`: `INTEGRATION.md`, `LICENSE`, `Makefile`, `NOTICE.md`, `PACKING_README.md`, `README.md`, `RELEASE_MANIFEST.json`, `SOURCES.json`, `SPARSE_PACKING_PROOF.md`, `SPARSE_PACKING_SECTION.tex`, `materialize.py`, `report.pdf`, `report.tex`, `requirements.txt`, `verify.py`, `verify_all.py`
- `49-support-pell/audits/`: `ALL_CHECKS.json`, `COEFFICIENT_RECONSTRUCTION.json`, `COEFFICIENT_RECONSTRUCTION_OPTIMIZED.json`, `PDF_QA.json`, `eleven_combination_review.md`, `sparse_isolation_review.md`, `verify_coefficients.py`
- `49-support-pell/audits/logs/`: `audits_verify_coefficients_normal.txt`, `audits_verify_coefficients_optimized.txt`, `code_audit_full_circuit_normal.txt`, `code_audit_full_circuit_optimized.txt`, `eleven_verify_eleven_normal.txt`, `eleven_verify_eleven_optimized.txt`, `short_audit_offset44_normal.txt`, `short_audit_offset44_optimized.txt`, `verify_normal.txt`, `verify_optimized.txt`
- `49-support-pell/certificates/`: `degree.json`, `metrics.json`, `sparse_extraction.json`, `ten_independent_audit.json`, `verification_optimized_stdout.json`, `verification_stdout.json`
- `49-support-pell/code/`: `audit_full_circuit.py`, `audit_parent_packing.py`, `build.py`, `parent_arithmetic.py`, `portpoly.py`
- `49-support-pell/coefficients/`: `COEFFICIENT_BINDING.json`, `README.md`, `SOURCE_PINS.json`, `build_coefficients.py`
- `49-support-pell/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `49-support-pell/coefficients/upstream/`: `25-COEFFICIENT_PROOF.md`, `README_PACKAGE31.md`
- `49-support-pell/data/`: `polynomial.json`, `weights.json`
- `49-support-pell/eleven/`: `build_eleven.py`, `verify_eleven.py`
- `49-support-pell/eleven/generated/`: `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`, `eleven_full_product.json`, `eleven_full_shifted_system.json`, `eleven_full_sos.json`, `eleven_full_system.json`, `eleven_short_product.json`, `eleven_short_shifted_system.json`, `eleven_short_sos.json`, `eleven_short_system.json`
- `49-support-pell/fixed/`: `FIXED_LEAVES.json`
- `49-support-pell/fixed/signed10/`: `beta_source.bin.gz`, `c001.bin.gz`, `c002.bin.gz`, `c003.bin.gz`, `c004.bin.gz`, `c005.bin.gz`, `c007.bin.gz`, `c008.bin.gz`, `c009.bin.gz`, `c010.bin.gz`, `c011.bin.gz`, `c012.bin.gz`, `c013.bin.gz`, `c014.bin.gz`
- `49-support-pell/nine/`: `MULTITARGET_NINE_PROOF.md`, `build_multitarget_nine.py`, `circuit.py`, `portpoly.py`, `verify_multitarget_nine.py`
- `49-support-pell/nine/generated/`: `multitarget_nine_natural.json`, `multitarget_nine_natural_degree_certificate.json`, `multitarget_nine_positive.json`, `multitarget_nine_positive_degree_certificate.json`
- `49-support-pell/quartic/`: `QUADRATIC_TARGETS.json`
- `49-support-pell/sections/`: `coefficients.tex`, `eleven.tex`, `nine.tex`, `short.tex`, `sparse.tex`, `ten.tex`, `verification.tex`
- `49-support-pell/short/`: `PROOF.md`, `WAVE2_README.md`, `audit_offset44.py`, `build_offset44.py`, `offset44.audit.json`, `offset44.json`, `section.tex`
- `49-support-pell/short/historical/`: `GAP_AUXILIARY_PROOF.md`, `POSITIVE_GAP_SHEARS.md`, `Q56_ordinary_section.tex`, `Q56_report.tex`, `SOURCES.json`, `ordinary_blank_four_sos_74.json`, `ordinary_gap_sos78.json`
- `49-support-pell/short/upstream/`: `p69_unscaled.json`, `package31_COEFFICIENT_BINDING.json`
- `49-support-pell/upstream/`: `ADDITIONAL_SOURCE_PINS.json`, `MULTITARGET_NINE_PROOF_PACKAGE45.md`, `NOTICE_PACKAGE40.md`, `NOTICE_PACKAGE45.md`, `audit_parent_packing_PACKAGE40.py`, `parent_system60.json`, `verify_multitarget_nine_PACKAGE45.py`
- `49-support-pell/upstream/baseline/`: `COMPILER_AT_PIN.md`, `README_AT_PIN.md`, `SHORT_EQUATION_AT_PIN.md`, `SHORT_FRONTIER_AT_PIN.md`, `SHORT_SYSTEM_AT_PIN.md`, `STATUS_AT_PIN.md`
- `49-support-pell/upstream/norm/`: `ELEVEN_POSITIVE_PROOF_PACKAGE38.md`, `PROOF_PACKAGE37.md`, `PROOF_PACKAGE44.md`, `RATIO12_PROOF_PACKAGE26.md`, `SHIFTED12_PROOF_PACKAGE34.md`
- `49-support-pell/upstream/ten/`: `PACKAGE40_REPORT.tex`
- `50-midpoint11/`: `ARTIFACT_MANIFEST.json`, `LICENSE`, `Makefile`, `NOTICE.md`, `PDF_QA.json`, `README.md`, `VERIFICATION.json`, `report.pdf`, `report.tex`, `requirements.txt`, `verify.py`
- `50-midpoint11/coefficients/`: `ports.json`
- `50-midpoint11/coefficients/upstream/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `50-midpoint11/eleven/`: `PROOF.md`, `build.py`, `check.py`
- `50-midpoint11/eleven/generated/`: `METRICS.json`, `VERIFICATION.json`, `eleven_full_product.json`, `eleven_full_shifted_system.json`, `eleven_full_system.json`, `eleven_midpoint_product.json`, `eleven_midpoint_shifted_system.json`, `eleven_midpoint_system.json`
- `50-midpoint11/fourteen/`: `FOURTEEN_PROOF.md`, `build_fourteen.py`, `check_fourteen.py`, `fourteen_audit.json`, `fourteen_positive.json`, `section.tex`
- `50-midpoint11/packing/`: `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `SUPPORT_PROOF.md`, `support_section.tex`, `verify.py`
- `50-midpoint11/packing/certificates/`: `degree.json`, `metrics.json`, `nine_audit.json`, `release_verification.json`, `sun_formula_replay.json`, `support_isolation.json`
- `50-midpoint11/packing/code/`: `audit_full_circuit.py`, `audit_nine.py`, `audit_parent_packing.py`, `build.py`, `nine_formula_helpers.py`, `verify_support.py`
- `50-midpoint11/packing/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `50-midpoint11/packing/data/`: `polynomial.json`, `weights.json`
- `50-midpoint11/packing/licenses/31-sun10/`: `LICENSE`, `NOTICE.md`
- `50-midpoint11/packing/licenses/40-packing10/`: `LICENSE`, `NOTICE.md`
- `50-midpoint11/packing/licenses/45-multioutput/`: `LICENSE-NEW-MATERIAL.txt`, `NOTICE.md`
- `50-midpoint11/packing/nine/`: `build_multitarget_nine.py`, `port_polynomial.py`
- `50-midpoint11/packing/nine/generated/`: `multitarget_nine_natural.json`, `multitarget_nine_natural_degree_certificate.json`, `multitarget_nine_positive.json`, `multitarget_nine_positive_degree_certificate.json`
- `50-midpoint11/packing/quartic/`: `QUADRATIC_TARGETS.json`
- `50-midpoint11/packing/upstream/`: `README.md`
- `50-midpoint11/provenance/`: `NOTICE-package31.md`, `README.md`, `SOURCE_PINS.json`
- `50-midpoint11/provenance/licenses/`: `LICENSE`, `LICENSE-package32`, `LICENSE-package38`, `LICENSE-package44`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-package32.md`, `NOTICE-package38.md`, `NOTICE-package44.md`
- `50-midpoint11/provenance/repository/`: `COLLECTION_README.md`, `COMPILER.md`, `INCOMING_README.md`, `STATUS.md`
- `50-midpoint11/review/`: `FINAL_REVIEW.md`, `HALF_CARRIER_AUDIT.md`, `ORDINARY_FOURTEEN_AUDIT.md`, `README.md`, `SUPPORT_AUDIT.md`, `audit_midpoint_independent.py`, `midpoint_independent_audit.json`
- `51-sparse-arith/`: `CORE_README.md`, `FINALIZER_PROOF.md`, `LICENSE`, `NOTICE.md`, `README.md`, `SOURCES.json`, `SOURCE_PROOF.md`, `verify_all.py`, `verify_release.py`
- `51-sparse-arith/certificates/`: `degree.json`, `full_circuit.json`, `nine_interface.json`, `separator.json`, `source.json`, `toy.json`
- `51-sparse-arith/code/`: `build.py`, `check_toy.py`, `polynomial.py`, `verify_full_circuit.py`, `verify_nine_interface.py`, `verify_separator.py`, `verify_source.py`
- `51-sparse-arith/coefficients/native31/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `51-sparse-arith/coefficients/payloads/`: `base_floor.bin.gz`, `c001.bin.gz`, `c003.bin.gz`, `c004.bin.gz`, `c005.bin.gz`, `c007.bin.gz`, `c008.bin.gz`
- `51-sparse-arith/data/`: `coefficient_recipes.json`, `fixed_values.json`, `polynomial.json`, `targets.json`
- `51-sparse-arith/nine/`: `INDEPENDENT_REVIEW.md`, `PROOF.md`, `build_nine.py`, `fixed_values.json`, `verify_nine.py`
- `51-sparse-arith/nine/generated/`: `VERIFICATION.json`, `multitarget_nine_natural.json`, `multitarget_nine_natural_degree_certificate.json`, `multitarget_nine_positive.json`, `multitarget_nine_positive_degree_certificate.json`
- `51-sparse-arith/provenance/`: `ASSEMBLY_VERIFICATION.json`, `COEFFICIENT_SOURCES.json`, `DOCUMENT_QA.json`, `JONES_SOURCES.json`
- `51-sparse-arith/report/`: `report.pdf`, `report.tex`
- `51-sparse-arith/short/`: `INDEPENDENT_SEPARATOR_REVIEW.md`, `NORM_SUFFIX_CSE.md`, `README.md`, `SOURCE_PINS.json`, `SQUARED_MODULUS_PROOF.md`, `build_and_audit.py`, `normal_audit_output.json`, `optimized_audit_output.json`, `short_section.tex`
- `51-sparse-arith/short/coefficients/`: `NOTICE.md`
- `51-sparse-arith/short/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `51-sparse-arith/short/generated/`: `AUDIT.json`, `p66_degree157.json`, `p68_degree113.json`, `p72_degree80.json`, `p74_degree68.json`
- `51-sparse-arith/short/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `51-sparse-arith/short/upstream/`: `PACKAGE36_NOTICE.md`
- `51-sparse-arith/upstream/`: `FINALIZER_NOTICE.md`, `JONES_DEPENDENCY.md`, `PACKAGE40_NOTICE.md`
- `51-sparse-arith/upstream/JONES_RATIO_LEAN/`: `CLOSURE.json`, `SOURCE_AUDIT.json`
- `52-sparse-pell/`: `LICENSE`, `NOTICE.md`, `README.md`, `RELEASE_HASHES.json`, `VALIDATION.json`, `negative_controls.py`, `verify_release.py`
- `52-sparse-pell/audit/`: `CANONICAL_SOURCE_POLYNOMIALS.json`, `CONDITIONAL_SEPARATION_THEOREM.md`, `INDEPENDENT_NINE_VERIFICATION.json`, `README.md`, `SHARED_SOURCE_SYMBOLIC_VERIFICATION.json`, `verify_nine_independently.py`, `verify_shared_source_symbolically.py`
- `52-sparse-pell/coefficients/`: `COEFFICIENT_BINDING.json`, `K.bin`, `MC.bin`, `MF_source.bin`, `PARENT_COEFFICIENT_BOUND.json`, `README.md`, `beta.bin`
- `52-sparse-pell/inherited/`: `ADDITIONAL_SOURCE_PINS.json`, `SOURCE_PINS.json`
- `52-sparse-pell/inherited/sources/31-sun10/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/inherited/sources/31-sun10/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `52-sparse-pell/inherited/sources/31-sun10/signed10/`: `NOTICE.md`
- `52-sparse-pell/inherited/sources/32-integer15/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/inherited/sources/32-integer15/compiler/`: `NOTICE.md`
- `52-sparse-pell/inherited/sources/32-integer15/integer15/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/inherited/sources/32-integer15/integer16/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/inherited/sources/33-signed16/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `52-sparse-pell/inherited/sources/33-signed16/upstream/`: `norm_source_notice.md`
- `52-sparse-pell/inherited/sources/34-integer14/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/inherited/sources/34-integer14/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `52-sparse-pell/inherited/sources/34-integer14/review/`: `ATTRIBUTION_SOURCE_MAP.json`
- `52-sparse-pell/inherited/sources/35-cancel12/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/inherited/sources/35-cancel12/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `52-sparse-pell/inherited/sources/36-small-tuple/`: `NOTICE.md`
- `52-sparse-pell/inherited/sources/36-small-tuple/coefficients/`: `NOTICE.md`
- `52-sparse-pell/inherited/sources/36-small-tuple/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `52-sparse-pell/inherited/sources/37-wave5/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/inherited/sources/37-wave5/licenses/`: `LICENSE`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE-source28.md`
- `52-sparse-pell/inherited/sources/37-wave5/signed/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/integer/`: `FIXED_BINDING.json`, `LICENSE`, `METRICS.json`, `NOTICE.md`, `README.md`, `RECOMMENDED.json`, `SOURCE_AND_TAIL_PROOF.md`, `SOURCE_BOUNDS.json`, `VERIFICATION.json`, `VERIFICATION_RUN.txt`, `build_integer.py`, `section.tex`, `verify_integer.py`
- `52-sparse-pell/integer/fixed/`: `q000.bin.gz`, `q001.bin.gz`, `q002.bin.gz`, `q004.bin.gz`, `q005.bin.gz`, `q006.bin.gz`, `q007.bin.gz`, `q009.bin.gz`, `q010.bin.gz`, `q011.bin.gz`, `q012.bin.gz`, `q013.bin.gz`, `q014.bin.gz`, `q015.bin.gz`, `q016.bin.gz`, `q017.bin.gz`, `q018.bin.gz`, `q019.bin.gz`, `q020.bin.gz`, `q021.bin.gz`
- `52-sparse-pell/integer/generated/`: `sun10_interior_packed_global.json`, `sun10_interior_packed_row.json`, `sun10_interior_packed_shifted_global.json`, `sun10_interior_packed_shifted_homogeneous.json`, `sun10_interior_packed_shifted_row.json`, `sun10_interior_regular_global.json`, `sun10_interior_regular_homogeneous.json`, `sun10_interior_regular_row.json`, `sun10_packed_global.json`, `sun10_packed_row.json`, `sun10_regular_global.json`, `sun10_regular_homogeneous.json`, `sun10_regular_row.json`
- `52-sparse-pell/integer/upstream/`: `build.py`, `coefficient_recipes.json`, `polynomial.json`, `report.tex`, `weights.json`
- `52-sparse-pell/nine/`: `COEFFICIENT_INSTANCE.json`, `METRICS.json`, `PROOF.md`, `README.md`, `build_nine.py`, `materialize_coefficients.py`, `verify_nine.py`
- `52-sparse-pell/nine/generated/`: `VERIFICATION.json`, `nine_174_interior_packed_natural.json`, `nine_174_interior_packed_natural_degree_certificate.json`, `nine_174_interior_packed_positive.json`, `nine_174_interior_packed_positive_degree_certificate.json`, `nine_174_interior_regular_natural.json`, `nine_174_interior_regular_natural_degree_certificate.json`, `nine_174_interior_regular_positive.json`, `nine_174_interior_regular_positive_degree_certificate.json`, `nine_174_interior_shifted_natural.json`, `nine_174_interior_shifted_natural_degree_certificate.json`, `nine_174_interior_shifted_positive.json`, `nine_174_interior_shifted_positive_degree_certificate.json`, `nine_174_packed_natural.json`, `nine_174_packed_natural_degree_certificate.json`, `nine_174_packed_positive.json`, `nine_174_packed_positive_degree_certificate.json`, `nine_174_regular_natural.json`, `nine_174_regular_natural_degree_certificate.json`, `nine_174_regular_positive.json`, `nine_174_regular_positive_degree_certificate.json`
- `52-sparse-pell/nine/generated/fixed/`: `c000.bin.gz`, `c001.bin.gz`, `c003.bin.gz`, `c004.bin.gz`, `c005.bin.gz`, `c006.bin.gz`, `c007.bin.gz`, `c017.bin.gz`, `c018.bin.gz`, `c019.bin.gz`, `c020.bin.gz`, `c021.bin.gz`, `c022.bin.gz`, `c023.bin.gz`, `c024.bin.gz`, `c025.bin.gz`, `c026.bin.gz`, `c027.bin.gz`, `c028.bin.gz`, `c029.bin.gz`, `c030.bin.gz`, `c031.bin.gz`, `c033.bin.gz`, `c034.bin.gz`, `c035.bin.gz`, `radix_scale.bin.gz`
- `52-sparse-pell/packing/`: `CERTIFICATE_174_interior_packed.json`, `CERTIFICATE_174_interior_packed_shifted.json`, `CERTIFICATE_174_interior_regular.json`, `CERTIFICATE_174_interior_shifted.json`, `CERTIFICATE_174_packed.json`, `CERTIFICATE_174_regular.json`, `CERTIFICATE_200_packed.json`, `CERTIFICATE_200_regular.json`, `README.md`, `SPARSE_PACKING_PROOF.md`, `VERIFICATION.json`, `section.tex`, `verify_certificate.py`
- `52-sparse-pell/positive/`: `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`, `COEFFICIENT_BINDING.json`, `NOTICE.md`, `README.txt`, `SOURCE_PINS.json`, `Y_ABSORPTION_PROOF.md`, `build_absorbed.py`, `check_absorbed.py`, `positive11_Y_lean_product.json`, `positive11_Y_lean_shifted_system.json`, `positive11_Y_lean_system.json`, `positive12_none_lean_product.json`, `positive12_none_lean_shifted_system.json`, `positive12_none_lean_system.json`, `section.tex`
- `52-sparse-pell/positive/upstream/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/report/`: `comparison.tex`, `metrics.tex`, `nine.tex`, `positive_details.tex`, `report.pdf`, `report.tex`, `vectors.tex`, `verification.tex`
- `52-sparse-pell/review/`: `NATIVE_INDEPENDENT_CHECKS.json`, `POSITIVE_LEADING_FORM_CHECKS.json`, `POSITIVE_THEOREM_REVIEW.md`, `SOURCE_PINS.json`, `VARIANT_LEDGER_CHECKS.json`, `WAVE6_COMPARISON.md`, `check_native_independently.py`, `check_parent_coefficients.py`, `check_positive_leading_form.py`, `check_variant_ledgers.py`
- `52-sparse-pell/review/postpin/`: `COMPILER.md`, `SOURCE.json`, `STATUS.md`
- `52-sparse-pell/review/sources/44-b4-sparse/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/review/sources/44-b4-sparse/native/`: `NOTICE-upstream.md`
- `52-sparse-pell/review/sources/44-b4-sparse/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `52-sparse-pell/review/sources/`: `INCOMING_README.md`, `README.md`
- `53-selective-quad/`: `DEPENDENCY_MAP.json`, `LICENSE`, `NOTICE.md`, `PLACEMENT.md`, `README.md`, `REBUILD_FILES.json`, `REPLAY_SUMMARY.json`, `negative_controls.py`, `report.pdf`, `report.tex`, `results.tex`, `validation.tex`, `verify.py`
- `53-selective-quad/batching/`: `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`, `COEFFICIENT_BINDING.json`, `DEPENDENCIES.md`, `LICENSE`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_eleven.py`, `check_eleven.py`, `full_product.json`, `full_shifted_system.json`, `full_sos.json`, `full_system.json`, `report.pdf`, `report.tex`, `section.tex`, `short_product.json`, `short_shifted_system.json`, `short_sos.json`, `short_system.json`
- `53-selective-quad/elimination/`: `AUDIT_RESULTS.json`, `INDEPENDENT_REVIEW.md`, `PACKAGE_AUDIT_RESULTS.json`, `TRANSPORT_OBSTRUCTION.json`, `audit_eleven.py`, `audit_package.py`
- `53-selective-quad/jones/`: `ARTIFACT_HASHES.json`, `CHECK_RESULTS.json`, `CODE.json`, `FIXED_BINDING.json`, `INDEPENDENT_AUDIT_RESULTS.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `RATIO_SOURCE_PINS.json`, `README.md`, `SOURCE_PINS.json`, `b4_support.py`, `build_jones.py`, `check_jones.py`, `circuit.py`, `independent_seeded_audit.py`, `report.pdf`, `report.tex`, `section.tex`
- `53-selective-quad/jones/generated/`: `LEDGER.json`, `signed.json`, `signed_degree.json`, `signed_seeded.json`, `signed_seeded_degree.json`
- `53-selective-quad/jones/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `53-selective-quad/jones/upstream/`: `QUADRATIC_TARGETS.json`, `nine__MULTITARGET_NINE_PROOF.md`, `nine__build_multitarget_nine.py`, `quartic__QUADRATIC_MULTI_TARGET_PROOF.md`, `weights__MULTI_OUTPUT_EXTRACTION_PROOF.md`
- `53-selective-quad/nine/`: `COEFFICIENT_BINDING.json`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `STANDALONE_REPLAY.json`, `build_nine.py`, `circuit.py`, `report.pdf`, `report.tex`, `section.tex`, `verify_nine.py`
- `53-selective-quad/nine/generated/`: `LEDGER.json`, `VALIDATION.json`, `build_optimized_stdout.json`, `calibrated_natural.json`, `calibrated_natural_certificate.json`, `calibrated_natural_degree.json`, `calibrated_positive.json`, `calibrated_positive_certificate.json`, `calibrated_positive_degree.json`, `check_optimized_stdout.json`, `check_stdout.json`, `three_natural.json`, `three_natural_certificate.json`, `three_natural_degree.json`, `three_positive.json`, `three_positive_certificate.json`, `three_positive_degree.json`, `two_natural.json`, `two_natural_certificate.json`, `two_natural_degree.json`, `two_positive.json`, `two_positive_certificate.json`, `two_positive_degree.json`
- `53-selective-quad/nine/upstream/`: `SELECTIVE_EXTRACTION_PROOF.md`, `SELECTIVE_SOURCE_PINS.json`, `SOURCE_PINS.json`, `code_v1.json`, `nine__MULTITARGET_NINE_PROOF.md`, `source_support.json`, `verify_selective.py`
- `53-selective-quad/packing/mask_popcount/`: `INSTANCE.json`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `circuit.py`, `evaluate.py`, `independent_check.py`, `parameters.json`, `report.pdf`, `report.tex`, `reproduce.py`, `section.tex`
- `53-selective-quad/packing/mask_popcount/generated/`: `INDEPENDENT_CHECKS.json`, `METRICS.json`, `REPRODUCTION.json`, `signed10_b2.json`, `source_records.json`
- `53-selective-quad/packing/mask_popcount/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `53-selective-quad/review/`: `38-batching11_README.md`, `39-direct10_README.md`, `40-packing10_README.md`, `41-bose-chowla_README.md`, `42-additive-b4_README.md`, `43-sidon10_README.md`, `44-b4-sparse_README.md`, `45-multioutput_README.md`, `INCOMING_README.md`, `POST_PIN_COLLECTION.md`, `POST_PIN_SHORT_FRONTIER.md`, `POST_PIN_SHORT_SYSTEM.md`, `POST_PIN_STATUS.md`, `README.md`, `SHORT_FRONTIER.md`, `STATUS.md`
- `53-selective-quad/root_checks/`: `DEPENDENCY_AUDIT.md`, `DEPENDENCY_REPLAY.json`, `NINE_INDEPENDENT_REVIEW.md`, `POPCOUNT_BRIDGE_REVIEW.md`, `SUN_SOURCE_REVIEW.md`, `check_calibrated_block.json`, `check_calibrated_block.py`, `check_nine_degree_independent.json`, `check_nine_degree_independent.py`, `check_popcount_bridge.json`, `check_popcount_bridge.py`, `check_seeded_norm.json`, `check_seeded_norm.py`, `check_sparse_padding.json`, `check_sparse_padding.py`, `check_square_threshold_padding.json`, `check_square_threshold_padding.py`
- `53-selective-quad/short/`: `AUDIT_RESULTS.json`, `COEFFICIENT_BINDING.json`, `INDEPENDENT_LITERAL_RESULTS.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `audit_relaxed.py`, `build_relaxed.py`, `independent_literal_audit.py`, `p72_relaxed.json`, `p74_relaxed.json`, `relaxed15_system61.json`, `report.pdf`, `report.tex`, `section.tex`
- `53-selective-quad/short/history/`: `ordinary_blank_four_sos_74.json`
- `53-selective-quad/short/upstream/`: `SHORT_EQUATION.md`, `SHORT_SYSTEM.md`, `tools__audit_sos_circuit.py`, `tools__build_short_circuit.py`, `tools__build_sos_circuit.py`
- `53-selective-quad/weights/`: `LICENSE`, `README.md`, `SELECTIVE_EXTRACTION_PROOF.md`, `SOURCE_PINS.json`, `TEST_RESULTS.json`, `code_v1.json`, `prepare.py`, `report.pdf`, `report.tex`, `section.tex`, `source_support.json`, `test_selective.py`, `verification_v1.json`, `verify_selective.py`
- `54-calibrated-carry/`: `LICENSE`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `RELEASE_HASHES.json`, `VALIDATION.json`, `negative_controls.py`, `rebuild_artifacts.py`, `verify_release.py`
- `54-calibrated-carry/audit/`: `INDEPENDENT_ARITHMETIC_VERIFICATION.json`, `INDEPENDENT_NINE_CIRCUIT_VERIFICATION.json`, `MAJORANT_AND_COMPOSITION_AUDIT.md`, `verify_majorant_independently.py`, `verify_nine_circuits_independently.py`
- `54-calibrated-carry/inherited/arrivals/ZFC_Diophantine_Selective_Quadratic_2026-10-23/licenses/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/arrivals/con-zfc-selective-2026-10-23/licenses/`: `LICENSE`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE.md`, `NOTICE.source31.md`, `NOTICE.source40.md`, `UPSTREAM_COEFFICIENT_NOTICE.md`, `UPSTREAM_LICENSE`
- `54-calibrated-carry/inherited/arrivals/con-zfc-support-majorants-2026-10-23/licenses/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/arrivals/con_zfc_sparse_arithmetic_2026-10-23/licenses/`: `FINALIZER_NOTICE.md`, `LICENSE`, `NOTICE.md`, `PACKAGE40_NOTICE.md`
- `54-calibrated-carry/inherited/sources/31-sun10/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/sources/31-sun10/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `54-calibrated-carry/inherited/sources/31-sun10/signed10/`: `NOTICE.md`
- `54-calibrated-carry/inherited/sources/32-integer15/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/sources/32-integer15/compiler/`: `NOTICE.md`
- `54-calibrated-carry/inherited/sources/32-integer15/integer15/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/sources/32-integer15/integer16/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/sources/33-signed16/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `54-calibrated-carry/inherited/sources/33-signed16/upstream/`: `norm_source_notice.md`
- `54-calibrated-carry/inherited/sources/34-integer14/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/sources/34-integer14/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `54-calibrated-carry/inherited/sources/34-integer14/review/`: `ATTRIBUTION_SOURCE_MAP.json`
- `54-calibrated-carry/inherited/sources/35-cancel12/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/sources/35-cancel12/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `54-calibrated-carry/inherited/sources/36-small-tuple/`: `NOTICE.md`
- `54-calibrated-carry/inherited/sources/36-small-tuple/coefficients/`: `NOTICE.md`
- `54-calibrated-carry/inherited/sources/36-small-tuple/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `54-calibrated-carry/inherited/sources/37-wave5/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/inherited/sources/37-wave5/licenses/`: `LICENSE`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE-source28.md`
- `54-calibrated-carry/inherited/sources/37-wave5/signed/`: `LICENSE`, `NOTICE.md`
- `54-calibrated-carry/integer/`: `CONDITIONAL_SEPARATOR_PROOF.md`, `FIXED_BINDING.json`, `LICENSE`, `LOCAL_LEMMA_CHECKS.json`, `METRICS.json`, `NOTICE.md`, `README.md`, `RECOMMENDED.json`, `SOURCE_BOUNDS.json`, `SPARSE_SOURCE_PROOF.md`, `VERIFICATION.json`, `build_integer.py`, `check_local_lemmas.py`, `section.tex`, `verify_integer.py`
- `54-calibrated-carry/integer/fixed/`: `Y_scale.bin.gz`, `beta_source.bin.gz`, `q00b46663e441.bin.gz`, `q26858c993f3f.bin.gz`, `q4a0434e611b8.bin.gz`, `q4bab765c3f71.bin.gz`, `q7f362c6a0c7a.bin.gz`, `q87e553a0619c.bin.gz`, `qb847ac266219.bin.gz`, `qc9fbb29b4b37.bin.gz`, `qe287bc76f779.bin.gz`, `qec454a3eb800.bin.gz`
- `54-calibrated-carry/integer/generated/`: `sun10_163_selective12_packed_global_sparse_popcount_equal.json`, `sun10_163_selective12_packed_hybrid_sparse_popcount_equal.json`, `sun10_163_selective12_packed_shifted_global_sparse_popcount_equal.json`, `sun10_163_selective12_packed_shifted_homogeneous_sparse_popcount_equal.json`, `sun10_163_selective12_packed_shifted_hybrid_sparse_popcount_equal.json`, `sun10_163_selective12_regular_global_sparse_popcount_equal.json`, `sun10_163_selective12_regular_homogeneous_sparse_popcount_equal.json`, `sun10_163_selective12_regular_hybrid_sparse_popcount_equal.json`, `sun10_170_selective12_packed_global_sparse_popcount_equal.json`, `sun10_170_selective12_packed_hybrid_sparse_popcount_equal.json`, `sun10_170_selective12_packed_shifted_global_sparse_popcount_equal.json`, `sun10_170_selective12_packed_shifted_homogeneous_sparse_popcount_equal.json`, `sun10_170_selective12_packed_shifted_hybrid_sparse_popcount_equal.json`, `sun10_170_selective12_regular_global_sparse_popcount_equal.json`, `sun10_170_selective12_regular_homogeneous_sparse_popcount_equal.json`, `sun10_170_selective12_regular_hybrid_sparse_popcount_equal.json`, `sun10_174_selective12_packed_global_sparse_popcount_equal.json`, `sun10_174_selective12_packed_hybrid_sparse_popcount_equal.json`, `sun10_174_selective12_packed_shifted_global_sparse_popcount_equal.json`, `sun10_174_selective12_packed_shifted_homogeneous_sparse_popcount_equal.json`, `sun10_174_selective12_packed_shifted_hybrid_sparse_popcount_equal.json`, `sun10_174_selective12_regular_global_sparse_popcount_equal.json`, `sun10_174_selective12_regular_homogeneous_sparse_popcount_equal.json`, `sun10_174_selective12_regular_hybrid_sparse_popcount_equal.json`
- `54-calibrated-carry/native/`: `COEFFICIENT_BINDING.json`, `README.md`, `SEPARATED_TUPLE_CHECKS.json`, `verify_native_tuple.py`
- `54-calibrated-carry/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `54-calibrated-carry/nine/`: `FIXED_BINDING.json`, `METRICS.json`, `RATIO_TAIL_CHECKS.json`, `README.md`, `REFINED_DEFECT_POLYNOMIAL.json`, `REFINED_MAJORANT_CHECKS.json`, `REFINED_MAJORANT_PROOF.md`, `SEARCH_METRICS.json`, `SOURCE_CIRCUIT_VERIFICATION.json`, `build_nine.py`, `check_ratio_tail.py`, `check_refined_majorant.py`, `majorant_section.tex`, `materialize_fixed.py`, `ratio_tail.py`, `scan_variants.py`, `verify_source_circuits.py`
- `54-calibrated-carry/nine/fixed/`: `0ede388edfbcbc404cf7edf3b5a227933e335e4562b91ca70b8734ffa32f096a.bin.gz`, `2f2001b703a8c1ef2d7b4d679dfb28d88211b1b2236d064048aba99881e098a3.bin.gz`, `42fb05989fe3941f1bb058885cf10782e89254c9c09fd59bc179c1cf0975163c.bin.gz`, `7f1e1a5a12c498774306e768b1e0b7995ef7beae6f78d708f0091a5adb764d26.bin.gz`, `83a260caab3b563c1e34c201c393213e514b22f096ba5adc38c17a6851ba124c.bin.gz`, `96c1653af1220df6f24493afd542dccf3530762c1c98885163cbed2d77ea708d.bin.gz`, `a02c1e89bed6970eab3bfc3cefc018395748212d0d1fbcaf73119d4d8eea22e6.bin.gz`, `b096db84678df9a255c929c4ec21bb84c920b6fbdb66624b7c0870e84a97f56a.bin.gz`, `bde08f265ad725dfe2166427f7ba2a4092aa774bc3750d56d2a7dd4eba696d52.bin.gz`, `ca5c42ada4ad72f91083482ff264a47c991864440bf80dac9743444e28cdf09e.bin.gz`, `d5dc85ae1b41cb5fc688cf3c5acbffd4a57ce0b115567eef225cf8e7a89c6276.bin.gz`, `fbf1d60cf3b86754bc880ffdaa4b3427d2ebfd78f1fb94a708ab5ab0198cfbe9.bin.gz`, `fd5b2f841916090ba829f8f1525041822071500e08818c647d6ab392fae2a462.bin.gz`
- `54-calibrated-carry/nine/generated/`: `nine_163_selective12_regular_simple64_natural.json`, `nine_163_selective12_regular_simple64_positive.json`, `nine_163_selective12_regular_simple64_positive_certificate.json`, `nine_170_selective12_packed_quotient2048_natural.json`, `nine_170_selective12_packed_quotient2048_positive.json`, `nine_170_selective12_packed_quotient2048_positive_certificate.json`, `nine_170_selective12_packed_shifted_quotient2048_natural.json`, `nine_170_selective12_packed_shifted_quotient2048_positive.json`, `nine_170_selective12_packed_shifted_quotient2048_positive_certificate.json`, `nine_170_selective12_packed_shifted_simple64_natural.json`, `nine_170_selective12_packed_shifted_simple64_positive.json`, `nine_170_selective12_packed_shifted_simple64_positive_certificate.json`, `nine_170_selective12_packed_shifted_support2048_natural.json`, `nine_170_selective12_packed_shifted_support2048_positive.json`, `nine_170_selective12_regular_simple64_natural.json`, `nine_170_selective12_regular_simple64_positive.json`, `nine_170_selective12_regular_simple64_positive_certificate.json`, `nine_174_selective12_packed_quotient2048_natural.json`, `nine_174_selective12_packed_quotient2048_positive.json`, `nine_174_selective12_packed_quotient2048_positive_certificate.json`, `nine_174_selective12_packed_simple64_natural.json`, `nine_174_selective12_packed_simple64_positive.json`, `nine_174_selective12_packed_simple64_positive_certificate.json`, `nine_174_selective12_packed_support2048_natural.json`, `nine_174_selective12_packed_support2048_positive.json`, `nine_174_selective12_regular_simple64_natural.json`, `nine_174_selective12_regular_simple64_positive.json`, `nine_174_selective12_regular_simple64_positive_certificate.json`
- `54-calibrated-carry/packing/`: `CERTIFICATE_163_selective12_packed.json`, `CERTIFICATE_163_selective12_packed_shifted.json`, `CERTIFICATE_163_selective12_regular.json`, `CERTIFICATE_170_selective12_packed.json`, `CERTIFICATE_170_selective12_packed_shifted.json`, `CERTIFICATE_170_selective12_regular.json`, `CERTIFICATE_174_selective12_packed.json`, `CERTIFICATE_174_selective12_packed_shifted.json`, `CERTIFICATE_174_selective12_regular.json`, `PROOF.md`, `README.md`, `SUMMARY.json`, `VERIFICATION.json`, `build_certificates.py`, `interior_weights_150_8150.txt`, `interior_weights_160_8160.txt`, `interior_weights_165_8165.txt`, `interior_weights_170_8170.txt`, `packed163.txt`, `packed165.txt`, `packed170.txt`, `packed174.txt`, `row_pairs.txt`, `row_pairs_numeric.txt`, `section.tex`, `support_pairs.txt`, `verify_certificates.py`, `weights174.txt`
- `54-calibrated-carry/packing/data/`: `selective12_source.json`
- `54-calibrated-carry/positive/`: `README.txt`, `SHORT_BUILD_RECEIPT.json`, `SHORT_CHECK_RESULTS.json`, `SHORT_COMPOSITIONS_PROOF.md`, `SOURCE_PINS.json`, `build_short.py`, `check_short.py`, `p66_degree157.json`, `p68_degree101.json`, `p70_degree80.json`, `p71_degree78.json`, `p72_degree64.json`, `p73_degree62.json`, `section.tex`
- `54-calibrated-carry/positive/comparisons/`: `p70_degree84.json`, `p73_degree68.json`
- `54-calibrated-carry/report/`: `build.sh`, `carry.tex`, `comparison.tex`, `generate_tables.py`, `metrics.tex`, `native.tex`, `nine_interface.tex`, `nine_metrics.tex`, `parent.tex`, `report.pdf`, `report.tex`, `selective.tex`, `short_details.tex`, `vectors.tex`, `verification.tex`
- `54-calibrated-carry/review/`: `COMMIT_METADATA.json`, `LITERAL_LEDGER_CHECKS.json`, `LOCAL_ADAPTER_PROOF_REVIEW.md`, `NATIVE_ADAPTER_REVIEW.md`, `NEW_LOCAL_ADAPTER_CHECKS.json`, `SEPARATED_TUPLE_CHECKS.json`, `SOURCE_PINS.json`, `WAVE7_COMPARISON.md`, `check_new_local_adapters.py`
- `54-calibrated-carry/review/postpin/`: `OBJECT_ZFC.md`, `QUADRATIC_CODING.md`, `SOURCE.json`, `STATUS.md`
- `54-calibrated-carry/short_audit/`: `INDEPENDENT_SHORT_AUDIT.md`, `INDEPENDENT_SHORT_RESULTS.json`, `audit_short_independent.py`
- `54-calibrated-carry/source/`: `README.md`, `SELECTIVE_POSITIVITY_PROOF.md`, `SELECTIVE_SOURCE_VERIFICATION.json`, `SPARSE_POPCOUNT_CHECKS.json`, `SPARSE_POPCOUNT_SOURCE_PROOF.md`, `all31_row_pairs.txt`, `all31_source.json`, `all31_support_pairs.txt`, `build_selective_source.py`, `check_sparse_popcount.py`, `section.tex`, `selective12_row_pairs.txt`, `selective12_source.json`, `selective12_support_pairs.txt`, `verify_selective_source.py`
- `55-congruence-norms/`: `BASELINE.json`, `INTEGRATION.md`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `REPRODUCTION.json`, `RESULTS.json`, `metrics.tex`, `report.pdf`, `report.tex`, `verify.py`
- `55-congruence-norms/audits/`: `FRONTIER_AUDIT.md`, `REPORT_REVIEW.md`, `TEN_ROOT_AUDIT.md`, `TEN_ROOT_CHECKS.json`, `audit_fused_positive_source.py`, `fused_positive_source_audit.json`, `fused_positive_source_review.md`, `ten_root_audit.py`
- `55-congruence-norms/fourteen/`: `AUDIT.json`, `NOTICE.txt`, `PROOF.md`, `SOURCE_PINS.json`, `build.py`, `polynomial.json`, `verify.py`
- `55-congruence-norms/fourteen/coefficients/`: `ports.json`
- `55-congruence-norms/fourteen/upstream/`: `LICENSE.package31`, `NOTICE.package31.md`
- `55-congruence-norms/fourteen/upstream/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `55-congruence-norms/native/`: `LICENSE`, `SOURCE31_ADAPTER.md`, `SOURCE_CHAIN.md`, `SOURCE_MANIFEST.json`, `VERIFICATION.json`, `verify_native.py`
- `55-congruence-norms/native/calibration/`: `NOTICE.md`
- `55-congruence-norms/native/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE.package31.md`
- `55-congruence-norms/native/licenses/k215/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `SOURCE_PINS.json`
- `55-congruence-norms/native/licenses/k215/provenance/partial-selector/`: `NOTICE.md`
- `55-congruence-norms/native/licenses/k215/provenance/partial-selector/provenance/`: `ATTRIBUTION.md`
- `55-congruence-norms/native/licenses/k215/provenance/permuted-commands/provenance/`: `ATTRIBUTION.md`, `PREDECESSOR_ATTRIBUTION.md`
- `55-congruence-norms/nine_fast/`: `CIRCUIT_AUDIT.json`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `SOURCE_FUSION_AUDIT.json`, `build_nine.py`, `check_circuits.py`, `verify_source.py`
- `55-congruence-norms/nine_fast/generated/`: `LEDGER.json`, `calibrated_natural.json`, `calibrated_natural_certificate.json`, `calibrated_natural_degree.json`, `calibrated_positive.json`, `calibrated_positive_certificate.json`, `calibrated_positive_degree.json`
- `55-congruence-norms/nine_fast/upstream/`: `code_positive.json`
- `55-congruence-norms/nine_majorant/`: `CIRCUIT_AUDIT.json`, `LICENSE`, `MAJORANT_PROOF.md`, `NOTICE.md`, `PROOF.md`, `build_nine.py`, `check_circuits.py`, `check_ring_identities.py`
- `55-congruence-norms/nine_majorant/generated/`: `LEDGER.json`, `calibrated_natural.json`, `calibrated_natural_certificate.json`, `calibrated_natural_degree.json`, `calibrated_positive.json`, `calibrated_positive_certificate.json`, `calibrated_positive_degree.json`
- `55-congruence-norms/nine_majorant/upstream/`: `code_positive.json`
- `55-congruence-norms/ten/`: `INHERITED_SOURCE.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `build.py`, `code_positive.json`, `verify.py`
- `55-congruence-norms/ten/generated/`: `METRICS.json`, `VERIFIED.json`, `signed10_b2.json`, `source_records.json`
- `55-congruence-norms/ten/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `56-free-coordinate/`: `LICENSE`, `NOTICE.md`, `README.md`, `verify_all.py`
- `56-free-coordinate/nine/`: `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_FILES.json`, `VERIFICATION.json`, `build.py`, `evaluate.py`, `hybrid_section.tex`, `materialize.py`, `source_algebra.py`, `verify.py`, `verify_core.py`
- `56-free-coordinate/nine/audit_logs/`: `core_normal.txt`, `core_optimized.txt`
- `56-free-coordinate/nine/fixed/`: `MANIFEST.json`, `a004.bin.gz`, `a005.bin.gz`, `a006.bin.gz`, `a007.bin.gz`, `a020.bin.gz`, `a026.bin.gz`, `a027.bin.gz`, `a028.bin.gz`, `a030.bin.gz`, `a031.bin.gz`, `a032.bin.gz`, `a033.bin.gz`, `a034.bin.gz`, `base_scale.bin.gz`, `threshold_scale.bin.gz`
- `56-free-coordinate/nine/generated/`: `CANDIDATE_CHECKS.json`, `LEDGER.json`, `calibrated_absorbed_natural.json`, `calibrated_absorbed_natural_certificate.json`, `calibrated_absorbed_natural_degree.json`, `calibrated_absorbed_positive.json`, `calibrated_absorbed_positive_certificate.json`, `calibrated_absorbed_positive_degree.json`, `calibrated_original_natural.json`, `calibrated_original_natural_certificate.json`, `calibrated_original_natural_degree.json`, `calibrated_original_positive.json`, `calibrated_original_positive_certificate.json`, `calibrated_original_positive_degree.json`
- `56-free-coordinate/nine/upstream/`: `SELECTIVE_NOTICE.md`, `SPARSE_PELL_NOTICE.md`
- `56-free-coordinate/provenance/`: `FINAL_AUDIT.json`, `SOURCE_PINS.json`
- `56-free-coordinate/report/`: `report.pdf`, `report.tex`
- `56-free-coordinate/review/`: `baseline_review.md`, `free_C_review.md`, `report_review.md`
- `56-free-coordinate/short/`: `INDEPENDENT_REVIEW.md`, `LICENSE`, `PROOF.md`, `README.md`, `SOURCES.json`, `build_and_audit.py`, `section.tex`
- `56-free-coordinate/short/coefficients31/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `56-free-coordinate/short/generated/`: `AUDIT.json`, `COEFFICIENT_AUDIT.json`, `gap_minima74_squared_modulus_degree46.json`, `ordinary_gap_minima73_squared_modulus_degree54.json`
- `56-free-coordinate/short/upstream/`: `PACKAGE36_NOTICE.md`
- `57-separated-degrees/`: `INTEGRATION.md`, `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `README.md`, `RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `materialize.py`, `reproduce.py`, `verify.py`
- `57-separated-degrees/certificates/`: `INDEPENDENT_CHECKS.json`, `PDF_QA.json`, `RELOCATION_CHECK.json`, `REPRODUCTION.json`
- `57-separated-degrees/coefficients/`: `NOTICE.md`, `REBUILD_CHECK.json`
- `57-separated-degrees/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `57-separated-degrees/data/`: `CHANNEL_CHECKS.json`, `TOY_CHANNEL_CHECKS.json`, `channel_certificate.json`, `channel_certificate108.json`, `check_toy_channels.py`, `degree_channels.json`, `verify_channels.py`
- `57-separated-degrees/fixed/`: `FIXED_BINDING.json`, `base_scale.bin.gz`, `coefficient_00.bin.gz`, `coefficient_01.bin.gz`, `coefficient_02.bin.gz`, `coefficient_03.bin.gz`, `coefficient_04.bin.gz`, `coefficient_06.bin.gz`, `mask_scale.bin.gz`, `threshold_scale.bin.gz`
- `57-separated-degrees/generated/`: `METRICS.json`, `nine_natural.json`, `nine_natural_degree.json`, `nine_natural_degree_certificate.json`, `nine_positive.json`, `nine_positive_degree.json`, `nine_positive_degree_certificate.json`, `ten_integer.json`, `ten_integer_degree.json`
- `57-separated-degrees/low_degree/`: `CHECKS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `build_thirteen.py`, `build_twelve.py`, `build_twelve_balanced.py`, `build_twelve_reduced.py`, `thirteen_positive_degree132.json`, `twelve_positive_degree242.json`, `twelve_positive_degree258.json`, `twelve_positive_degree314.json`, `verify.py`
- `57-separated-degrees/low_degree/upstream/`: `LICENSE.ProveIt`, `SOURCE_PINS.json`
- `57-separated-degrees/proofs/`: `CHANNEL_PROOF.md`, `INDEPENDENT_ORDINATE_AUDIT.md`, `LOGICAL_DEPENDENCY_REVIEW.md`, `SEPARATE_NORMS_INDEPENDENT_REVIEW.md`, `TEN_INTEGER_SOURCE_INDEPENDENT_REVIEW.md`, `WAVE7_AUDIT.md`
- `57-separated-degrees/quartic/`: `AUDIT.json`, `QUARTIC45_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `WAVE7_AUDIT.md`, `build_verify.py`, `quartic45.json`, `quartic45_expanded.json`
- `57-separated-degrees/quartic/upstream/34-integer14/`: `LICENSE`
- `57-separated-degrees/quartic/upstream/34-integer14/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `57-separated-degrees/report/`: `channel_table.tex`, `channels.tex`, `low_degree.tex`, `main.pdf`, `main.tex`, `nine.tex`, `quartic.tex`, `ten.tex`
- `57-separated-degrees/upstream/`: `NOTICE-wave7-nine.md`, `NOTICE-wave7-sun.md`
- `57-separated-degrees/upstream/logical_calibration/`: `OBJECT_ZFC.md`, `SOURCE_PINS.json`
- `58-integral-root/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `RESULTS.json`, `package.py`, `verify_all.py`
- `58-integral-root/certificates/`: `BUILD.json`, `DOMAIN_TRANSLATIONS.json`, `EXACT_ALGEBRA.json`, `INDEPENDENT_FORMULA_CHECK.json`, `PDF_QA.json`, `VERIFY_ALL.json`, `VERIFY_ALL_OPTIMIZED.json`
- `58-integral-root/circuits/`: `p15_degree24.json`, `p15_degree24_degree_certificate.json`, `p15_degree26.json`, `p15_degree26_degree_certificate.json`, `p15_degree30.json`, `p15_degree30_degree_certificate.json`, `p15_nonnegative_degree24.json`, `p60_integer_degree48.json`
- `58-integral-root/code/`: `build.py`, `domain_translations.py`, `independent_check.py`, `verify.py`
- `58-integral-root/coefficients/`: `NOTICE-upstream.md`
- `58-integral-root/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `58-integral-root/report/`: `report.pdf`, `report.tex`
- `58-integral-root/review/`: `INDEPENDENT_ALGEBRA_REVIEW.md`, `INTERNAL_MATHEMATICAL_REVIEW.md`
- `58-integral-root/twelve/`: `BUILD_RECEIPT.json`, `CHECKER_PORTABILITY_RECEIPT.json`, `INTEGRATION_RECEIPT.json`, `NOTICE.md`, `P12_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_p12.py`, `check_p12.py`, `p12_check_results.json`, `p12_desaturated_product.json`, `p12_desaturated_shifted_system.json`, `p12_desaturated_system.json`, `section.tex`
- `58-integral-root/twelve/upstream/`: `LICENSE.source35`, `LICENSE.source38`, `LICENSE.source44`, `LICENSE.source52`, `NOTICE.source35.md`, `NOTICE.source44.md`, `NOTICE.source52.md`
- `58-integral-root/upstream/`: `ACTIVE_STATUS.md`, `LICENSE_MINIMA_PRIOR`
- `59-degree-separated/`: `INCOMING_PINS.json`, `LICENSE`, `NOTICE.md`, `PDF_QA.json`, `PLACEMENT.md`, `README.md`, `REBUILD_FILES.json`, `REPLAY_SUMMARY.json`, `SECTION_LAYOUT_MAP.json`, `build_report.sh`, `build_sections.py`, `late_comparison.tex`, `negative_controls.py`, `report.pdf`, `report.tex`, `results.tex`, `validation.tex`, `verify.py`
- `59-degree-separated/encoding/`: `LICENSE`, `NOTICE.md`, `PDF_QA.json`, `README.md`, `RELEASE_FILES.json`, `SOURCE_PINS.json`, `SPLIT_SOURCE_PROOF.md`, `TEST_RESULTS.json`, `VERIFICATION.json`, `report.pdf`, `report.tex`, `section.tex`, `split_code.json`, `split_kernels.json`, `test_split.py`, `verify_split.py`
- `59-degree-separated/nine/`: `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PDF_QA.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `STANDALONE_REPLAY.json`, `build_nine.py`, `independent_review.py`, `report.pdf`, `report.tex`, `section.tex`, `verify_nine.py`
- `59-degree-separated/nine/coefficients/`: `COEFFICIENT_BINDING.json`
- `59-degree-separated/nine/coefficients/old_tuple/`: `COEFFICIENT_BINDING.json`
- `59-degree-separated/nine/data/`: `split_code.json`, `split_kernels.json`
- `59-degree-separated/nine/generated/`: `174_interior_packed_natural.json`, `174_interior_packed_natural_certificate.json`, `174_interior_packed_natural_certificate_degree.json`, `174_interior_packed_positive.json`, `174_interior_packed_positive_certificate.json`, `174_interior_packed_positive_certificate_degree.json`, `174_interior_regular_natural.json`, `174_interior_regular_natural_certificate.json`, `174_interior_regular_natural_certificate_degree.json`, `174_interior_regular_positive.json`, `174_interior_regular_positive_certificate.json`, `174_interior_regular_positive_certificate_degree.json`, `174_interior_shifted_natural.json`, `174_interior_shifted_natural_certificate.json`, `174_interior_shifted_natural_certificate_degree.json`, `174_interior_shifted_positive.json`, `174_interior_shifted_positive_certificate.json`, `174_interior_shifted_positive_certificate_degree.json`, `BUILD_LOG.json`, `CHECK_LOG.json`, `INDEPENDENT_REVIEW.json`, `LEDGER.json`, `VALIDATION.json`, `split_116_natural.json`, `split_116_natural_certificate.json`, `split_116_natural_certificate_degree.json`, `split_116_positive.json`, `split_116_positive_certificate.json`, `split_116_positive_certificate_degree.json`
- `59-degree-separated/nine/upstream/`: `SPLIT_SOURCE_PROOF.md`
- `59-degree-separated/nine_free_adjunct/`: `INDEPENDENT_REVIEW.md`, `INDEPENDENT_REVIEW_RECEIPT.json`, `INDEPENDENT_SOURCE_CHECK.json`, `INDEPENDENT_SOURCE_RECEIPT.json`, `INDEPENDENT_SOURCE_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_nine.py`, `check_source_independent.py`, `independent_review.py`, `section.tex`, `verify_nine.py`
- `59-degree-separated/nine_free_adjunct/coefficients/`: `COEFFICIENT_BINDING.json`
- `59-degree-separated/nine_free_adjunct/coefficients/old_tuple/`: `COEFFICIENT_BINDING.json`
- `59-degree-separated/nine_free_adjunct/data/`: `split_code.json`, `split_kernels.json`
- `59-degree-separated/nine_free_adjunct/generated/`: `INDEPENDENT_REVIEW.json`, `LEDGER.json`, `VALIDATION.json`, `split_116_natural.json`, `split_116_natural_certificate.json`, `split_116_natural_certificate_degree.json`, `split_116_positive.json`, `split_116_positive_certificate.json`, `split_116_positive_certificate_degree.json`
- `59-degree-separated/nine_free_adjunct/upstream/`: `SPLIT_SOURCE_PROOF.md`, `free_coordinate_PROOF.md`, `free_coordinate_README.md`, `free_coordinate_REVIEW.md`, `free_coordinate_SOURCE_PINS.json`, `frozen_nine_PROOF.md`
- `59-degree-separated/positive/`: `BUILD_RECEIPT.json`, `CHECK_RESULTS.json`, `DEPENDENCIES.md`, `INDEPENDENT_CHECK.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `PROOF.md`, `README.md`, `REVIEW_RECEIPT.json`, `SOURCE_PINS.json`, `build_ordinary_merger.py`, `check_merger_independent.py`, `check_optimized_stdout.json`, `check_ordinary_merger.py`, `check_stdout.json`, `ordinary_merger_product.json`, `ordinary_merger_shifted_system.json`, `ordinary_merger_sos.json`, `ordinary_merger_system.json`, `report.pdf`, `report.tex`, `requirements.txt`, `section.tex`
- `59-degree-separated/positive13_adjunct/`: `CHECKS.json`, `INDEPENDENT_REVIEW.md`, `INDEPENDENT_REVIEW_NORMAL.json`, `INDEPENDENT_REVIEW_OPTIMIZED.json`, `INDEPENDENT_REVIEW_RECEIPT.json`, `LICENSE`, `PARENT_PIN.json`, `PROOF.md`, `README.md`, `READONLY_PINS.json`, `build.py`, `check.py`, `independent_check.py`, `section.tex`, `thirteen_positive_degree126.json`
- `59-degree-separated/positive13_adjunct/coefficients/`: `NOTICE.md`, `REBUILD_CHECK.json`
- `59-degree-separated/positive13_adjunct/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `59-degree-separated/positive13_adjunct/upstream/`: `SOURCE_PINS.json`
- `59-degree-separated/positive13_adjunct/upstream/low_degree/`: `CHECKS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `thirteen_positive_degree132.json`, `twelve_positive_degree242.json`, `twelve_positive_degree258.json`, `twelve_positive_degree314.json`
- `59-degree-separated/positive13_adjunct/upstream/low_degree/upstream/`: `SOURCE_PINS.json`
- `59-degree-separated/review/`: `FORMAL_STATUS_AT_PIN.md`, `LATE_ConZFC_Free_Coordinate_2026-10-23_README.md`, `LATE_ConZFC_Separated_Degrees_2026-10-23_README.md`, `LATE_INPUTS.json`, `LATE_POSITIVE_COMPARISON.md`, `LATE_REPLAY.py`, `LATE_REPLAY.stdout.txt`, `LATE_REPLAY_INPUT_HASHES.json`, `LATE_REPLAY_REPORT.md`, `LATE_REPLAY_RESULTS.json`, `LATE_REPLAY_SHORT_COMPARISON.json`, `LATE_REPLAY_free_coordinate_normal.stdout.txt`, `LATE_REPLAY_free_coordinate_normal__nine__VERIFICATION.json`, `LATE_REPLAY_free_coordinate_normal__short__generated__AUDIT.json`, `LATE_REPLAY_free_coordinate_optimized.stdout.txt`, `LATE_REPLAY_free_coordinate_optimized__nine__VERIFICATION.json`, `LATE_REPLAY_free_coordinate_optimized__short__generated__AUDIT.json`, `LATE_REPLAY_separated_normal.stdout.txt`, `LATE_REPLAY_separated_normal__certificates__REPRODUCTION.json`, `LATE_REPLAY_separated_normal__generated__METRICS.json`, `LATE_REPLAY_separated_optimized.stderr.txt`, `LATE_REPLAY_separated_optimized__certificates__REPRODUCTION.json`, `LATE_REPLAY_separated_optimized__generated__METRICS.json`, `LATE_SIGNED_COFINAL_REVIEW.md`, `NINE_FREE_INDEPENDENT_NORMAL.json`, `NINE_FREE_INDEPENDENT_OPTIMIZED.json`, `POSITIVE13_ADJUNCT_INDEPENDENT.py`, `POSITIVE13_ADJUNCT_INDEPENDENT_NORMAL.json`, `POSITIVE13_ADJUNCT_INDEPENDENT_OPTIMIZED.json`, `POSITIVE13_ADJUNCT_INDEPENDENT_REVIEW.md`
- `59-degree-separated/root_checks/`: `DEPENDENCY_AUDIT.md`, `DEPENDENCY_FINAL_SNAPSHOT_CHECK.json`, `DEPENDENCY_INPUT_HASHES.json`, `DEPENDENCY_METADATA.json`, `DEPENDENCY_METADATA.stdout.txt`, `DEPENDENCY_PDF_METRICS.json`, `DEPENDENCY_REPLAY.json`, `DEPENDENCY_REPLAY.stdout.txt`, `ORDINARY_MERGER_REVIEW.md`, `check_coprime_spectator.json`, `check_coprime_spectator.py`, `check_dependency_metadata.py`, `check_primary_circuits.json`, `check_primary_circuits.py`, `encoding__pdf_text.txt`, `encoding__test_split__normal.stdout.txt`, `encoding__test_split__optimized.stdout.txt`, `encoding__verify_split__normal.stdout.txt`, `encoding__verify_split__optimized.stdout.txt`, `nine__independent_review__normal.stdout.txt`, `nine__independent_review__optimized.stdout.txt`, `nine__pdf_text.txt`, `nine__verify_nine__normal.stdout.txt`, `nine__verify_nine__optimized.stderr.txt`, `positive__build_ordinary_merger__normal.stdout.txt`, `positive__check_merger_independent__normal.stdout.txt`, `positive__check_merger_independent__optimized.stdout.txt`, `positive__check_ordinary_merger__normal.stdout.txt`, `positive__check_ordinary_merger__optimized.stdout.txt`, `positive__pdf_text.txt`, `run_dependency_replay.py`, `short__audit__normal.stdout.txt`, `short__audit__optimized.stdout.txt`, `short__build__normal.stdout.txt`, `short__pdf_text.txt`, `signed__check_jones__normal.stdout.txt`, `signed__check_jones__optimized.stdout.txt`, `signed__check_source_minimum_independent__normal.stdout.txt`, `signed__check_source_minimum_independent__optimized.stdout.txt`, `signed__pdf_text.txt`, `sun__independent_check__optimized.stdout.txt`, `sun__pdf_text.txt`, `sun__reproduce__normal.stdout.txt`
- `59-degree-separated/sections/`: `encoding.tex`, `nine.tex`, `nine_free_adjunct.tex`, `positive.tex`, `positive13_adjunct.tex`, `short.tex`, `signed.tex`, `sun.tex`
- `59-degree-separated/short/`: `AUDIT.json`, `COEFFICIENT_BINDING.json`, `FRONTIER_COMPARISON.json`, `LICENSE`, `MANIFEST.json`, `Makefile`, `NOTICE.md`, `PDF_QA.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `audit.py`, `audit_optimized_stdout.json`, `audit_stdout.json`, `build.py`, `explore_frontier.py`, `report.pdf`, `report.tex`, `section.tex`
- `59-degree-separated/short/circuits/`: `p67_d125.json`, `p68_d101.json`, `p69_d91.json`, `p70_d84.json`, `p71_d80.json`, `p72_d74.json`, `p73_d60.json`, `p74_d50.json`, `p75_d46.json`, `p76_d44_reference.json`, `p79_d52_14positive.json`
- `59-degree-separated/short/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`
- `59-degree-separated/signed/`: `ARTIFACT_HASHES.json`, `CHECK_RESULTS.json`, `COMPACT_CALIBRATION_PROOF.md`, `CRT_PROVENANCE.json`, `FIXED_BINDING.json`, `INDEPENDENT_SOURCE_CHECK.json`, `INDEPENDENT_SOURCE_NORMAL.json`, `INDEPENDENT_SOURCE_OPTIMIZED.json`, `INDEPENDENT_SOURCE_RECEIPT.json`, `INDEPENDENT_SOURCE_REVIEW.md`, `LICENSE`, `NOTICE.md`, `NO_TWELVE_VARIABLE_CLAIM.md`, `PDF_QA.json`, `README.md`, `SPLIT_CHECK_RESULTS.json`, `build_jones.py`, `build_stdout.json`, `check_jones.py`, `check_optimized_stdout.json`, `check_source_minimum_independent.py`, `check_stdout.json`, `compact_section.tex`, `old_source_report.pdf`, `old_source_report.tex`, `old_source_section.tex`, `report.pdf`, `report.tex`, `scaled_split_section.tex`, `section.tex`, `split_source.py`
- `59-degree-separated/signed/generated/`: `LEDGER.json`, `signed.json`, `signed_coprime.json`, `signed_coprime_compact_split_crt.json`, `signed_coprime_compact_split_crt_degree.json`, `signed_coprime_crt.json`, `signed_coprime_crt_degree.json`, `signed_coprime_degree.json`, `signed_coprime_split_crt.json`, `signed_coprime_split_crt_degree.json`, `signed_seeded.json`
- `59-degree-separated/signed/licenses/`: `LICENSE`, `LICENSE.SparsePell`, `LICENSE.Wade`, `NOTICE-K215.md`
- `59-degree-separated/signed/split/`: `SPLIT_SOURCE_PROOF.md`, `split_code.json`, `split_kernels.json`, `verify_split.py`
- `59-degree-separated/sun/`: `INSTANCE.json`, `NOTICE.md`, `README.md`, `build.py`, `circuit.py`, `evaluate.py`, `independent_check.py`, `report.pdf`, `report.tex`, `reproduce.py`, `section.tex`, `source_audit.py`
- `59-degree-separated/sun/data/`: `layout.json`
- `59-degree-separated/sun/generated/`: `INDEPENDENT_CHECKS.json`, `METRICS.json`, `source_records.json`, `sun10.json`, `verification_optimized_run.json`, `verification_run.json`
- `59-degree-separated/sun/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `60-positive-gap/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PROVENANCE.json`, `README.md`
- `60-positive-gap/checks/`: `PDF_QA.json`, `REPRODUCTION.json`, `verify_all.py`
- `60-positive-gap/report/`: `report.pdf`, `report.tex`
- `60-positive-gap/research_alternatives/`: `NINE_CANDIDATE_REVIEW.md`, `alternatives.tex`, `check_positive_gap.py`, `positive_gap_independent_check.json`
- `60-positive-gap/research_low_degree/`: `audit_gap_source.py`, `gap_source_audit.json`, `gap_source_audit.md`
- `60-positive-gap/research_low_degree/supplement15/`: `LICENSE`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `build.py`, `reproduce.py`, `section.tex`, `verify.py`
- `60-positive-gap/research_low_degree/supplement15/certificates/`: `BUILD.json`, `REPRODUCE.json`, `VERIFY.json`
- `60-positive-gap/research_low_degree/supplement15/circuits/`: `p15_degree24_source58_baseline90.json`, `p15_degree24_source58_baseline90_degree_certificate.json`, `p15_degree24_transport89.json`, `p15_degree24_transport89_degree_certificate.json`
- `60-positive-gap/research_low_degree/supplement15/native/`: `NOTICE-upstream.md`
- `60-positive-gap/research_low_degree/supplement15/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `60-positive-gap/research_low_degree/supplement15/upstream/`: `RELAXED_KERNEL_COMPLETE.md`, `source58_NOTICE.md`, `source58_build.py`, `source58_p90.json`, `source58_report.tex`
- `60-positive-gap/research_nine/`: `NEW_SOURCE_PROOF.md`
- `60-positive-gap/research_nine/candidate/`: `SOURCE_CHECK.json`, `build_nine.py`, `circuit.py`
- `60-positive-gap/research_nine/candidate/data/`: `parent_source.json`, `split_code.json`, `split_kernels.json`
- `60-positive-gap/research_nine/candidate/generated/`: `LEDGER.json`, `gap_100_natural.json`, `gap_100_natural_certificate.json`, `gap_100_natural_certificate_degree.json`, `gap_100_positive.json`, `gap_100_positive_certificate.json`, `gap_100_positive_certificate_degree.json`
- `60-positive-gap/research_nine/compact_candidate/`: `DEGREE_AND_BINDING.md`, `README.md`, `SOURCE_CHECK.json`, `audit_circuit.py`, `build_nine.py`, `circuit.py`, `source_equations.tex`, `write_source_table.py`
- `60-positive-gap/research_nine/compact_candidate/data/`: `parent_source.json`, `split_code.json`, `split_kernels.json`
- `60-positive-gap/research_nine/compact_candidate/generated/`: `INDEPENDENT_CIRCUIT_AUDIT.json`, `LEDGER.json`, `SOURCE_TABLE_AUDIT.json`, `gap_100_natural.json`, `gap_100_natural_certificate.json`, `gap_100_natural_certificate_degree.json`, `gap_100_positive.json`, `gap_100_positive_certificate.json`, `gap_100_positive_certificate_degree.json`
- `60-positive-gap/research_nine/data/`: `positive_gap_records.json`, `positive_gap_shift_records.json`, `reconstructed_records.json`
- `60-positive-gap/upstream-status/`: `PROPOSAL_REVIEW.md`, `README.md`
- `60-positive-gap/upstream31/`: `FETCH_LEDGER.json`, `LICENSE`, `NOTICE.md`
- `60-positive-gap/upstream31/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `60-positive-gap/upstream44/native/`: `NOTICE-upstream.md`
- `60-positive-gap/upstream44/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `61-congruence-carriers/`: `LICENSE`, `MANIFEST.json`, `Makefile`, `NOTICE.md`, `README.md`, `REPORT_QA.json`, `RESULTS.json`, `VERIFICATION.json`, `verify_all.py`
- `61-congruence-carriers/integer/`: `REDUCTIONS_PROOF.md`, `REDUCTION_VERIFICATION.json`, `SOURCE_TRANSPORT_CLARIFICATION.md`, `build_reductions.py`, `eliminate.py`, `octic34.json`, `sextic37.json`
- `61-congruence-carriers/integer/coefficients_source/`: `ACTIVE_BINDING.json`, `DOSSIER_VERIFICATION.json`, `EXACT_REPRODUCTION.json`, `LICENSE`, `NOTICE.md`, `README_DOSSIER.md`, `TRANSFER_LEDGER.json`, `verify_dossier.py`
- `61-congruence-carriers/integer/coefficients_source/historical/`: `DOMAIN_REDUCTION_PROOF.md`, `integer36_degree8_odd_scale.json`, `integer42_degree6_odd_scale.json`
- `61-congruence-carriers/integer/coefficients_source/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `61-congruence-carriers/integer/coefficients_source/licenses/package57/`: `LICENSE`, `NOTICE.md`
- `61-congruence-carriers/licenses/`: `FETCH_MANIFEST.json`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.package44`, `LICENSE.root`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-package44.md`, `NOTICE-upstream-native44.md`, `NOTICE_K215.md`, `README.md`, `SOURCE_PINS-native44.json`
- `61-congruence-carriers/positive/`: `ACTIVE_BINDING.json`, `AUDIT12.md`, `CHECK12.json`, `CHECK13.json`, `CIRCUIT_OPTIMIZATION.md`, `PROOF13.md`, `PROOF14.md`, `REVIEW_P13.md`, `SIGNED_INDEX_LEMMA.md`, `build12.py`, `build13.py`, `check12.py`, `check13.py`, `dag.py`, `p12_product_split2.json`, `p12_sos_split2.json`, `p13_degree34.json`
- `61-congruence-carriers/positive/intermediate14/`: `CHECK14.json`, `build14.py`, `check14.py`, `p14_degree34.json`
- `61-congruence-carriers/positive/reference/`: `p12_product_split2_105.json`, `p12_sos_split2_104.json`, `p13_degree34_95.json`
- `61-congruence-carriers/provenance/`: `SOURCE_BLOBS.json`
- `61-congruence-carriers/provenance/signed_source/`: `SNAPSHOT.json`
- `61-congruence-carriers/report/`: `congruence_carriers.pdf`, `congruence_carriers.tex`
- `62-sign-and-norm/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RESEARCH_NOTES.md`, `RESULTS.json`, `SOURCE_SNAPSHOT.json`, `build_report.py`, `report.pdf`, `report.tex`, `verify_all.py`
- `62-sign-and-norm/nine/`: `COEFFICIENT_BINDING.json`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_nine.py`, `build_source.py`, `circuit.py`, `independent_review.py`, `materialize.py`, `reproduce.py`, `rewrite_powers.py`, `section.tex`, `verify.py`
- `62-sign-and-norm/nine/certificates/`: `INDEPENDENT_REVIEW.json`, `SOURCE.json`, `VERIFIED.json`
- `62-sign-and-norm/nine/data/`: `parent_source.json`, `split_code.json`, `split_kernels.json`
- `62-sign-and-norm/nine/fixed/`: `BINDING.json`, `c007.bin.gz`, `c010.bin.gz`, `threshold_scale.bin.gz`
- `62-sign-and-norm/nine/generated/`: `LEDGER.json`, `split_116_natural.json`, `split_116_natural_certificate.json`, `split_116_natural_certificate_degree.json`, `split_116_natural_global.certificate.json`, `split_116_natural_global.json`, `split_116_positive.json`, `split_116_positive_certificate.json`, `split_116_positive_certificate_degree.json`, `split_116_positive_global.certificate.json`, `split_116_positive_global.json`
- `62-sign-and-norm/nine/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`
- `62-sign-and-norm/nine/upstream/`: `FREE_COORDINATE_PROOF.md`, `FROZEN_NINE_PROOF.md`, `NOTICE-native.md`, `NOTICE-source53.md`, `NOTICE-source59.md`, `SPLIT_SOURCE_PROOF.md`
- `62-sign-and-norm/positive13/`: `BUILD_RECEIPT.json`, `CHECKS.json`, `COEFFICIENT_BINDING.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `PROOF.md`, `README.md`, `REVIEW_CHECKS.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `p13_independent_check.py`, `polynomial.json`, `section.tex`
- `62-sign-and-norm/positive13/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`
- `62-sign-and-norm/quartic42/`: `AUDIT.json`, `DEPENDENCY_AUDIT.json`, `INDEPENDENT_ALGEBRA.json`, `INDEPENDENT_REVIEW.md`, `PROOF.md`, `READABLE_FORMULAS.json`, `SOURCE_PINS.json`, `build_verify.py`, `companions_section.tex`, `independent_algebra.py`, `quartic42.json`, `quartic42_expanded.json`, `section.tex`, `verify_dependencies.py`
- `62-sign-and-norm/quartic42/companions/`: `AUDIT.json`, `INDEPENDENT_CHECK.json`, `INDEPENDENT_REVIEW.md`, `PROOF.md`, `build_companions.py`, `check_low_degree_companions.py`, `octic30.json`, `octic30_expanded.json`, `octic30_readable.json`, `quartic42_x_square.json`, `sextic35.json`, `sextic35_expanded.json`, `sextic35_readable.json`
- `62-sign-and-norm/quartic42/dependencies/12-gap-norm14/proofs/`: `quartic32_proof.md`
- `62-sign-and-norm/quartic42/dependencies/12-gap-norm14/quadratic/`: `quartic32.json`
- `62-sign-and-norm/quartic42/dependencies/20-root12/`: `LICENSE.ProveIt`
- `62-sign-and-norm/quartic42/dependencies/20-root12/domains/`: `DOMAIN_REDUCTION_PROOF.md`, `integer54_quartic.json`
- `62-sign-and-norm/quartic42/dependencies/20-root12/domains/sources/15-release/evidence/diophantine_zfc_round2/integers/`: `SIGNED_DOMAIN_PROOF.md`
- `62-sign-and-norm/quartic42/dependencies/20-root12/domains/sources/15-release/evidence/diophantine_zfc_round2/quadratic/`: `LOW_DEGREE_PROOF.md`
- `62-sign-and-norm/quartic42/dependencies/23-separating12/`: `NOTICE.md`
- `62-sign-and-norm/quartic42/dependencies/23-separating12/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`
- `62-sign-and-norm/quartic42/dependencies/23-separating12/proofs/`: `ODD_SCALE_27_PROOF.md`
- `62-sign-and-norm/quartic42/dependencies/29-simpler-forms/`: `integer54_quartic.json`
- `62-sign-and-norm/quartic42/dependencies/`: `README.md`, `SOURCE_PINS.json`
- `62-sign-and-norm/quartic42/dependencies/source34/`: `LICENSE`, `NOTICE.md`
- `62-sign-and-norm/quartic42/dependencies/source34/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `62-sign-and-norm/verification/`: `PDF_QA.json`, `REPLAY.json`, `REPLAY_OPTIMIZED.json`
- `63-sign-recovery/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `README.md`, `RESULTS.json`, `VERIFICATION.json`, `verify.py`
- `63-sign-recovery/nine/`: `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `check_exact.py`, `check_source.py`, `section.tex`, `verify.py`
- `63-sign-recovery/nine/coefficients/`: `BINDING.json`
- `63-sign-recovery/nine/data/`: `order7_majorant_positive_certificate.json`
- `63-sign-recovery/nine/generated/`: `ORDER7_LEDGER.json`, `order7_natural.json`, `order7_natural_certificate.json`, `order7_natural_degree.json`, `order7_positive.json`, `order7_positive_certificate.json`, `order7_positive_degree.json`
- `63-sign-recovery/nine/licenses/31-sun10/`: `LICENSE`, `NOTICE.md`
- `63-sign-recovery/nine/licenses/48-majorants/`: `LICENSE`, `NOTICE.md`
- `63-sign-recovery/nine/licenses/55-congruence-norms/`: `LICENSE`, `NOTICE.md`
- `63-sign-recovery/nine/licenses/59-degree-separated/`: `LICENSE`, `NOTICE.md`
- `63-sign-recovery/positive14/`: `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `pell14_degree34.json`, `pell14_degree34_degree_certificate.json`, `pell14_degree34_unshifted.json`, `pell14_natural_degree34.json`, `section.tex`, `verify.py`
- `63-sign-recovery/provenance/`: `SOURCES.json`
- `63-sign-recovery/quartic/`: `AUDIT.json`, `build_verify.py`, `quartic42.json`, `quartic42_expanded.json`
- `63-sign-recovery/report/`: `QA.json`, `metrics.tex`, `report.pdf`, `report.tex`
- `63-sign-recovery/reviews/`: `NINE_REVIEW.md`, `POSITIVE14_REVIEW.md`, `QUARTIC42_REVIEW.md`, `ZFC_INTERNALIZATION_SCOPE.md`, `check_nine_independent.py`
- `63-sign-recovery/upstream/licenses/`: `34-integer14-LICENSE`, `34-integer14-NOTICE.md`, `57-separated-degrees-LICENSE`, `57-separated-degrees-NOTICE.md`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `64-structural-reductions/`: `LICENSE`, `MANIFEST.sha256`, `METRICS.json`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `build_report.py`, `verify_all.py`
- `64-structural-reductions/certificates/`: `PDF_CHECKS.json`, `REPLAY_LOG_OPTIMIZED.json`, `ROOT_CHECKS_OPTIMIZED.json`
- `64-structural-reductions/integer41/`: `COMPANIONS_PROOF.md`, `NOTICE.md`, `PROOF41.md`, `PROOF44.md`, `SOURCE_PINS.json`, `build_companions.py`, `build_verify41.py`, `build_verify44.py`, `octic31.json`, `quartic41.json`, `quartic44.json`, `section.tex`, `sextic36.json`
- `64-structural-reductions/integer41/certificates/`: `COEFFICIENT_CHECKS.json`, `OCTIC31_CHECKS.json`, `QUARTIC41_CHECKS.json`, `QUARTIC41_EXPANSION.json`, `QUARTIC44_CHECKS.json`, `SEXTIC36_CHECKS.json`
- `64-structural-reductions/integer41/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `64-structural-reductions/nine-positive-111/`: `PROOF.md`, `README.md`, `SOURCE_AUDIT.json`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build_nine.py`, `circuit.py`, `materialize_fixed.py`, `section.tex`, `verify_candidate.py`
- `64-structural-reductions/nine-positive-111/data/`: `split_code.json`, `split_kernels.json`
- `64-structural-reductions/nine-positive-111/fixed/`: `BINDING.json`, `c007.bin.gz`, `c008.bin.gz`, `c010.bin.gz`, `threshold_scale.bin.gz`
- `64-structural-reductions/nine-positive-111/generated/`: `LEDGER.json`, `split_111_natural.json`, `split_111_natural_certificate.json`, `split_111_natural_certificate_degree.json`, `split_111_positive.json`, `split_111_positive_certificate.json`, `split_111_positive_certificate_degree.json`
- `64-structural-reductions/nine-positive-111/native/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `64-structural-reductions/positive14/`: `CHECKS.json`, `NATIVE_REBUILD.json`, `PROOF.md`, `SOURCE_PINS.json`, `build.py`, `polynomial.json`, `section.tex`, `verify.py`
- `64-structural-reductions/positive14/native/`: `NOTICE-upstream.md`
- `64-structural-reductions/positive14/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `64-structural-reductions/report/`: `report.pdf`, `report.tex`
- `64-structural-reductions/review/`: `BASELINE_PINS.json`, `INTERNAL_MATHEMATICAL_REVIEW.md`, `active_README.pinned.md`, `collection_README.pinned.md`
- `65-shared-taps/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `report.pdf`, `report.tex`, `verify_all.py`
- `65-shared-taps/nine/`: `LICENSE`, `NATIVE_RECONSTRUCTION.json`, `NOTICE.md`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `circuit.py`, `construct.py`, `materialize_fixed.py`, `section.tex`, `verify.py`
- `65-shared-taps/nine/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `65-shared-taps/nine/data/`: `kernels.json`, `kernels_economy.json`, `layout.json`, `layout_economy.json`
- `65-shared-taps/nine/fixed/shared_taps/`: `BINDING.json`, `c006.bin.gz`, `c007.bin.gz`, `c010.bin.gz`, `threshold_scale.bin.gz`
- `65-shared-taps/nine/fixed/shared_taps_economy/`: `BINDING.json`, `c006.bin.gz`, `c007.bin.gz`, `c010.bin.gz`, `threshold_scale.bin.gz`
- `65-shared-taps/nine/generated/`: `LEDGER.json`, `shared_taps_economy_natural.json`, `shared_taps_economy_natural_certificate.json`, `shared_taps_economy_natural_certificate_degree.json`, `shared_taps_economy_positive.json`, `shared_taps_economy_positive_certificate.json`, `shared_taps_economy_positive_certificate_degree.json`, `shared_taps_natural.json`, `shared_taps_natural_certificate.json`, `shared_taps_natural_certificate_degree.json`, `shared_taps_positive.json`, `shared_taps_positive_certificate.json`, `shared_taps_positive_certificate_degree.json`
- `65-shared-taps/nine/inherited/`: `nine_free_proof.md`, `split_code.json`, `split_kernels.json`, `split_source_proof.md`
- `65-shared-taps/pell/`: `CHECK_RESULTS.json`, `INDEPENDENT_PROOF_AUDIT.md`, `LICENSE`, `METRICS.json`, `NOTICE.md`, `README.md`, `REPLAY_RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `candidate14.py`, `carrier14.py`, `evaluate.py`, `independent_check.py`, `proof.md`, `section.tex`, `verify_all.py`
- `65-shared-taps/pell/circuits/`: `p14_degree26.json`, `p14_degree30.json`
- `65-shared-taps/pell/coefficients/`: `NOTICE-upstream.md`
- `65-shared-taps/pell/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `65-shared-taps/sun/`: `INDEPENDENT_PROOF_AUDIT.md`, `NOTICE.md`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `algebra_audit.py`, `build.py`, `fixed.py`, `section.tex`, `source_audit.py`, `tail.py`, `verify.py`
- `65-shared-taps/sun/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `65-shared-taps/sun/data/`: `kernels.json`, `layout.json`
- `65-shared-taps/sun/generated/`: `METRICS.json`, `VERIFICATION.json`, `sun10.json`
- `65-shared-taps/sun/inherited/`: `package59_NOTICE.md`, `shared_taps_proof.md`
- `66-gap-congruence/`: `ARTIFACT_MAP.md`, `NOTICE.md`, `PDF_QA.json`, `PROVENANCE.json`, `README.md`, `RELEASE_CHECKS.json`, `negative_controls.py`, `verify.py`
- `66-gap-congruence/algebra/`: `RESULTS.json`, `SHORTENED_INTEGRAL_ROOT_PROOF.md`, `build_and_check.py`, `p15_78_degree30.json`, `p15_87_degree26.json`, `p15_88_degree24.json`
- `66-gap-congruence/algebra/upstream/`: `LICENSE.source`, `NOTICE.source.md`
- `66-gap-congruence/carry/`: `CERTIFICATES.json`, `PROOF.md`, `README.md`, `REBUILD.json`, `TEST_RESULTS.json`, `VERIFICATION.json`, `gapN116_H2068_code.json`, `gapN116_H2068_kernels.json`, `gapNmirror116_H2057_code.json`, `gapNmirror116_H2057_kernels.json`, `gapNq116_H2082_code.json`, `gapNq116_H2082_kernels.json`, `rebuild_kernels.py`, `section.tex`, `test_certificates.py`, `verify_certificates.py`
- `66-gap-congruence/direct/`: `OneStackEquation.lean`, `README.md`, `SOURCE_PINS.json`, `build_stack_step.py`, `check_stack.py`, `emit_stack_constructor.py`, `flatten_stack_step.py`, `section.tex`, `stack_step.json`, `stack_step_quartic.json`, `stack_step_quartic16.json`, `stack_step_quartic4.json`, `stack_step_quartic64.json`
- `66-gap-congruence/direct_audit/`: `REVIEW.md`, `audit.py`, `receipt.json`, `receipt_optimized.json`
- `66-gap-congruence/integer/`: `CHECKS.json`, `FINAL_METRICS.json`, `NEGATIVE_CONTROLS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_integer.py`, `negative_controls.py`, `section.tex`, `verify_integer.py`
- `66-gap-congruence/integer/alternative_low_cost/`: `CHECKS.json`, `README.md`, `build_integer.py`, `verify_integer.py`
- `66-gap-congruence/integer/alternative_low_cost/data/`: `gapN116_H2068_code.json`, `gapN86_source.json`, `gapNmirror116_H2057_code.json`, `gapNq116_H2082_code.json`, `gapNq85_source.json`, `layout.json`
- `66-gap-congruence/integer/alternative_low_cost/fixed/`: `MANIFEST.json`, `c003.bin.gz`, `c004.bin.gz`, `c005.bin.gz`, `c006.bin.gz`, `radix.bin.gz`, `threshold.bin.gz`
- `66-gap-congruence/integer/alternative_low_cost/generated/`: `METRICS.json`, `integer10.json`, `source_records.json`
- `66-gap-congruence/integer/data/`: `gapN116_H2068_code.json`, `gapN86_source.json`, `gapNmirror116_H2057_code.json`, `gapNq116_H2082_code.json`, `gapNq85_source.json`, `layout.json`
- `66-gap-congruence/integer/fixed/`: `MANIFEST.json`, `c000.bin.gz`, `c007.bin.gz`, `c008.bin.gz`, `radix.bin.gz`, `threshold.bin.gz`
- `66-gap-congruence/integer/generated/`: `METRICS.json`, `integer10.json`, `source_records.json`
- `66-gap-congruence/integer/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `66-gap-congruence/integer/upstream/`: `GAP_SOURCE_PROOF.md`
- `66-gap-congruence/integer_audit/`: `AUDIT.md`, `INDEPENDENT_INTEGER_AUDIT.json`, `independent_integer_audit.py`
- `66-gap-congruence/nine/`: `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_nine.py`, `check_defect_exact.py`, `section.tex`, `verify_nine.py`
- `66-gap-congruence/nine/data/H2057/`: `kernels.json`, `layout.json`, `source.json`
- `66-gap-congruence/nine/data/H2068/`: `kernels.json`, `layout.json`, `source.json`
- `66-gap-congruence/nine/data/H2082/`: `kernels.json`, `layout.json`, `source.json`
- `66-gap-congruence/nine/data/`: `OLD_TUPLE_BINDING.json`
- `66-gap-congruence/nine/fixed/`: `BINDING.json`, `c_33afcc0215e266df.bin.gz`, `c_50b8a3599b18e0a9.bin.gz`, `c_e3dd773f14077424.bin.gz`, `c_f69b40d0743298dc.bin.gz`, `threshold_16012032.bin.gz`, `threshold_17079501.bin.gz`
- `66-gap-congruence/nine/generated/`: `DEFECT_IDENTITY.json`, `H2057_refined_natural.json`, `H2057_refined_positive.json`, `H2057_simple_natural.json`, `H2057_simple_positive.json`, `H2068_refined_natural.json`, `H2068_refined_positive.json`, `H2068_simple_natural.json`, `H2068_simple_positive.json`, `H2082_refined_natural.json`, `H2082_refined_positive.json`, `H2082_simple_natural.json`, `H2082_simple_positive.json`, `METRICS.json`, `VERIFICATION.json`
- `66-gap-congruence/nine/upstream/`: `INHERITED_LICENSE`, `INHERITED_NOTICE.md`
- `66-gap-congruence/nine_audit/`: `AUDIT.md`, `INDEPENDENT_NINE_AUDIT.json`, `LOCAL_IDENTITIES.json`, `check_local_identities.py`, `independent_nine_audit.py`
- `66-gap-congruence/report/`: `algebra.tex`, `check_metrics.tex`, `comparison.tex`, `direct.tex`, `integer.tex`, `metrics.tex`, `nine.tex`, `packing.tex`, `report.pdf`, `report.tex`, `research.tex`, `scope.tex`, `source.tex`, `verification.tex`
- `66-gap-congruence/review/`: `INTAKE_CHECKS.json`, `LITERAL_LEDGER_CHECKS.json`, `RECENT_COMMITS.json`, `SOURCE_PINS.json`, `WAVE8_COMPARISON.md`
- `66-gap-congruence/review/formal/`: `QUADRATIC_CODING.md`, `SELECTIVE_SOURCE52.md`, `SOURCE.json`, `STATUS.md`
- `66-gap-congruence/source/`: `EIGHT_GUARD_PROOF.md`, `GAP_SOURCE_CHECKS.json`, `GAP_SOURCE_PROOF.md`, `README.md`, `SOURCE_RELEASE_FILES.json`, `build_gap_source.py`, `gap87_kernels.json`, `gap87_source.json`, `gapL86_kernels.json`, `gapL86_source.json`, `gapN86_kernels.json`, `gapN86_source.json`, `gapNq85_kernels.json`, `gapNq85_source.json`, `section.tex`
- `66-gap-congruence/source_audit/`: `AUDIT.md`, `INDEPENDENT_SOURCE_AUDIT.json`, `independent_sources.py`
- `67-oriented-guards/`: `INCOMING_PINS.json`, `LICENSE`, `NOTICE.md`, `PDF_QA.json`, `PLACEMENT.md`, `PRESEAL_REPLAY.json`, `README.md`, `REBUILD_FILES.json`, `SECTION_LAYOUT_MAP.json`, `SIGNED_DELIVERABLES.json`, `build_sections.py`, `negative_controls.py`, `report.pdf`, `report.tex`, `verify.py`
- `67-oriented-guards/alternatives/`: `REVIEW.md`, `SOURCE_HASHES.txt`, `section.tex`
- `67-oriented-guards/encoding/`: `CARRY_TESTS.json`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `RELEASE_FILES.txt`, `SIGNED_PAD.md`, `SOURCE_PINS.json`, `TESTS.json`, `VERIFICATION.json`, `check_carry.py`, `section.tex`, `split_code.json`, `split_kernels.json`, `test_split.py`, `verify_split.py`
- `67-oriented-guards/encoding/upstream/`: `LICENSE-separated-degrees`, `NOTICE-separated-degrees.md`
- `67-oriented-guards/nine/`: `CHECK_NINE.json`, `CHECK_NINE_OPTIMIZED.json`, `GENERATED_HASHES.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_nine.py`, `check_nine.py`, `check_ring.py`, `report.tex`, `section.tex`, `test_corruption.py`
- `67-oriented-guards/nine/data/`: `split108_code.json`, `split108_kernels.json`
- `67-oriented-guards/nine/generated/`: `LEDGER.json`, `split_108_order-1_natural.json`, `split_108_order-1_natural_certificate.json`, `split_108_order-1_natural_certificate_degree.json`, `split_108_order-1_positive.json`, `split_108_order-1_positive_certificate.json`, `split_108_order-1_positive_certificate_degree.json`, `split_108_order0_natural.json`, `split_108_order0_natural_certificate.json`, `split_108_order0_natural_certificate_degree.json`, `split_108_order0_positive.json`, `split_108_order0_positive_certificate.json`, `split_108_order0_positive_certificate_degree.json`, `split_108_order1_natural.json`, `split_108_order1_natural_certificate.json`, `split_108_order1_natural_certificate_degree.json`, `split_108_order1_positive.json`, `split_108_order1_positive_certificate.json`, `split_108_order1_positive_certificate_degree.json`, `split_108_order2_natural.json`, `split_108_order2_natural_certificate.json`, `split_108_order2_natural_certificate_degree.json`, `split_108_order2_positive.json`, `split_108_order2_positive_certificate.json`, `split_108_order2_positive_certificate_degree.json`, `split_108_order3_natural.json`, `split_108_order3_natural_certificate.json`, `split_108_order3_natural_certificate_degree.json`, `split_108_order3_positive.json`, `split_108_order3_positive_certificate.json`, `split_108_order3_positive_certificate_degree.json`, `split_108_order4_natural.json`, `split_108_order4_natural_certificate.json`, `split_108_order4_natural_certificate_degree.json`, `split_108_order4_positive.json`, `split_108_order4_positive_certificate.json`, `split_108_order4_positive_certificate_degree.json`
- `67-oriented-guards/nine/review/`: `MAJORANT_SYMPY.json`, `NINE_INDEPENDENT.json`, `check_majorant_sympy.py`, `check_nine_independent.py`
- `67-oriented-guards/positive/`: `CHECK_RECEIPT.json`, `LICENSE`, `NEGATIVE_CONTROL_RECEIPT.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `fourteen_positive_degree30.json`, `fourteen_positive_degree30_certificate.json`, `fourteen_positive_system.json`, `negative_controls.py`, `report.pdf`, `report.tex`, `section.tex`
- `67-oriented-guards/positive/coefficients/`: `NOTICE-upstream.md`
- `67-oriented-guards/positive/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `67-oriented-guards/quartic/`: `CHECKS.json`, `LICENSE`, `NOTICE.md`, `PROJECTIONS.md`, `PROJECTION_CHECKS.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `TEX_RESIDUAL_CHECK.json`, `build_projections.py`, `build_verify.py`, `check_tex_residuals.py`, `octic32.json`, `octic32_expanded.json`, `quartic42.json`, `quartic42_expanded.json`, `section.tex`, `sextic36.json`, `sextic36_expanded.json`
- `67-oriented-guards/quartic/upstream/q45/upstream/34-integer14/`: `LICENSE`
- `67-oriented-guards/quartic/upstream/q45/upstream/34-integer14/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`
- `67-oriented-guards/review/`: `ARRIVAL_COMMIT.json`
- `67-oriented-guards/review/baseline/`: `BASELINE_REVIEW.md`, `ConZFC_Integral_Root_2026-10-23.stdout.txt`, `EXECUTION_SURFACE.json`, `FORMAL_COMMIT.json`, `FRONTIER_COUNTS.json`, `PROPOSAL_REVIEW.md`, `README.md`, `REPLAY_RESULTS.json`, `SELECTED_PARETO.json`, `SELECTIVE_SOURCE52.md`, `SOURCE_PINS.json`, `STATUS.md`, `ZFC_Diophantine_Degree_Separated_2026-10-23.stdout.txt`, `con-zfc-calibrated-carry-4b4349064a.stdout.txt`, `con_zfc_congruence_norms_2026-10-23.stdout.txt`, `count_frontier.py`, `pareto.py`, `replay_inputs.py`
- `67-oriented-guards/review/positive14/`: `RECEIPT.json`, `REVIEW.md`, `check_independent.py`
- `67-oriented-guards/review/projections/`: `AUDIT.md`, `REVIEW.json`, `check.py`, `normal.stdout.txt`, `optimized.stdout.txt`
- `67-oriented-guards/review/quartic42/`: `LITERAL_REVIEW.json`, `PRELIMINARY.md`, `REPAIRED_PROOF_REVIEW.md`, `SNAPSHOT.json`, `TRANSPORT_CORRECTION.json`, `TRANSPORT_CORRECTION.md`, `check_literal.py`, `check_literal_intake.py`, `normal.stdout.txt`, `optimized.stdout.txt`
- `67-oriented-guards/review/signed10/`: `AUDIT.md`, `FINAL_REPLAY.json`, `FINAL_SNAPSHOT.json`, `REPLAY.json`, `SNAPSHOT.json`, `STRUCTURE.json`, `final_normal.stdout.txt`, `final_optimized.stdout.txt`, `normal.stdout.txt`, `optimized.stdout.txt`
- `67-oriented-guards/review/signed108/`: `AUDIT.md`, `REPLAY.json`, `SNAPSHOT.json`, `STRUCTURE.json`, `normal.stdout.txt`, `optimized.stdout.txt`
- `67-oriented-guards/review/signed108trim/`: `AUDIT.md`, `FINAL_DOCUMENT_HASHES.json`, `REPLAY.json`, `SNAPSHOT.json`, `STRUCTURE.json`, `normal.stdout.txt`, `optimized.stdout.txt`
- `67-oriented-guards/review/signed13/`: `AUDIT.md`, `FINAL_DOCUMENT_HASHES.json`, `REPLAY.json`, `SNAPSHOT.json`, `STRUCTURE.json`, `normal.stdout.txt`, `optimized.stdout.txt`
- `67-oriented-guards/root_checks/`: `check_bindings.json`, `check_bindings.py`, `check_endpoints.json`, `check_endpoints.py`
- `67-oriented-guards/sections/`: `alternatives.tex`, `encoding.tex`, `nine.tex`, `positive.tex`, `quartic.tex`, `signed108trim.tex`, `signed13.tex`
- `67-oriented-guards/signed/`: `INSTANCE.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `independent_check.py`, `report.pdf`, `report.tex`, `section.tex`
- `67-oriented-guards/signed/generated/`: `INDEPENDENT_CHECKS.json`, `METRICS.json`, `sun10.json`
- `67-oriented-guards/signed/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `67-oriented-guards/signed108/`: `INSTANCE.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `independent_check.py`, `report.pdf`, `report.tex`, `section.tex`, `source_audit.py`
- `67-oriented-guards/signed108/data/`: `layout.json`
- `67-oriented-guards/signed108/generated/`: `INDEPENDENT_CHECKS.json`, `METRICS.json`, `source_records.json`, `sun10.json`
- `67-oriented-guards/signed108/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `67-oriented-guards/signed108trim/`: `INSTANCE.json`, `NOTICE.md`, `PDF_QA.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `evaluate.py`, `independent_check.py`, `report.pdf`, `report.tex`, `section.tex`, `source_audit.py`
- `67-oriented-guards/signed108trim/data/`: `layout.json`
- `67-oriented-guards/signed108trim/generated/`: `INDEPENDENT_CHECKS.json`, `METRICS.json`, `source_records.json`, `sun10.json`
- `67-oriented-guards/signed108trim/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `67-oriented-guards/signed13/`: `FIXED_BINDING.json`, `LICENSE`, `NOTICE.md`, `README.md`, `build_jones.py`, `report.pdf`, `report.tex`, `reproduce.py`, `section.tex`, `split_source.py`, `verify.py`
- `67-oriented-guards/signed13/generated/`: `CHECKS.json`, `LEDGER.json`, `signed_coprime_compact_split_crt.json`, `signed_coprime_compact_split_crt_degree.json`
- `67-oriented-guards/signed13/licenses/`: `LICENSE`, `LICENSE.SparsePell`, `LICENSE.Wade`, `NOTICE-K215.md`
- `67-oriented-guards/signed13/split/`: `split_code.json`, `split_kernels.json`, `verify_split.py`
- `68-joint-positivity/`: `ARTIFACT_MAP.md`, `NOTICE.md`, `PDF_QA.json`, `PROVENANCE.json`, `README.md`, `RELEASE_CHECKS.json`, `negative_controls.py`, `verify.py`
- `68-joint-positivity/alternative/`: `CHECK_RESULTS.json`, `README.md`, `branch_scratch.json`, `branch_scratch.tex`, `branch_scratch_eliminate0.json`, `branch_scratch_eliminate1.json`, `branch_scratch_independent.json`, `branch_scratch_output_independent.json`, `branch_scratch_split.json`, `build_branch_scratch.py`, `check_branch_scratch.py`, `horn_output_independent.json`, `independent_scratch.py`
- `68-joint-positivity/direct/`: `AFFINE_PRODUCT_CERTIFICATES.md`, `AFFINE_PRODUCT_CHECKS.json`, `AffineProductEquation.lean`, `COMMUTATIVE_CERTIFICATES.md`, `FLOW_CHECKS.json`, `README.md`, `SHARED_AFFINE_CHECKS.json`, `SharedAffineProductEquation.lean`, `affine_shared_step.json`, `build_shared_affine_step.py`, `check_affine_products.py`, `check_flow.py`, `check_shared_affine_step.py`, `emit_shared_affine_constructor.py`, `horn_shared_source.json`, `section.tex`
- `68-joint-positivity/direct_audit/`: `CHECKS.json`, `REVIEW.md`, `check.py`
- `68-joint-positivity/disjointness/`: `CHECKS.json`, `DIRECT_PARITY.md`, `check_direct_parity.py`
- `68-joint-positivity/disjointness_audit/`: `AUDIT.md`, `CHECKS.json`, `PRIMARY_SOURCE_SHA256.txt`, `check_independent.py`
- `68-joint-positivity/free_carrier_audit/`: `FIXED_MOD_THREE_AUDIT.md`, `LOCAL_CHECKS.json`, `check_literal_degree.py`, `check_literal_tail.py`, `check_local_lemmas.py`, `integer10_DEGREE_AUDIT.json`, `integer10_TAIL_AUDIT.json`, `strengthened_lucas.tex`
- `68-joint-positivity/integer_system/`: `CHECK_RESULTS.json`, `PAIR_GUARD_PROOF.md`, `build_pair_guard.py`, `degree16_26.json`, `octic28.json`, `section.tex`
- `68-joint-positivity/integer_system_audit/`: `AUDIT.md`, `BINDING.json`, `RESULTS.json`, `RESULTS_OPTIMIZED.json`, `independent_check.py`
- `68-joint-positivity/integer_system_audit/licenses/`: `LICENSE.SignAndNorm`, `LICENSE.Source34`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE.SignAndNorm.md`, `NOTICE.Source34.md`
- `68-joint-positivity/norm/final10/`: `CHECKS.json`, `FIXED_COEFFICIENTS.json`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `REPLAY_COMMANDS.json`, `build.py`, `check.py`, `circuit.py`, `independent_formula.py`, `integer10.json`, `section.tex`
- `68-joint-positivity/norm/final10/data/`: `code.json`, `kernels.json`
- `68-joint-positivity/norm/final10/fixed/`: `c000.signed-le.gz`, `c002.signed-le.gz`, `c003.signed-le.gz`, `c004.signed-le.gz`, `c005.signed-le.gz`, `c006.signed-le.gz`, `threshold.signed-le.gz`
- `68-joint-positivity/norm/final10/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `68-joint-positivity/norm/final10/provenance/`: `PACKING_SOURCE_PINS.json`
- `68-joint-positivity/packing/`: `AUDIT.json`, `CHECKS.json`, `MANIFEST.sha256`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `audit.py`, `gap87.txt`, `gap87_code.json`, `gap87_input.json`, `gap87_kernels.json`, `gapL86.txt`, `gapL86_code.json`, `gapL86_input.json`, `gapL86_kernels.json`, `gapN86.txt`, `gapN86_code.json`, `gapN86_input.json`, `gapN86_kernels.json`, `gapNq85.txt`, `gapNq85_code.json`, `gapNq85_input.json`, `gapNq85_kernels.json`, `section.tex`, `split89.txt`, `split89_code.json`, `split89_input.json`, `split89_kernels.json`, `split89_source.json`, `verify.py`
- `68-joint-positivity/report/`: `branches.tex`, `check_displayed_rows.py`, `comparison.tex`, `direct.tex`, `explicit_joint.tex`, `free.tex`, `joint.tex`, `lucas.tex`, `packing.tex`, `parity.tex`, `references.tex`, `report.pdf`, `report.tex`, `verification.tex`
- `68-joint-positivity/review/`: `FORMAL_PINS.json`, `INTAKE_CHECKS.json`, `LITERAL_LEDGER_CHECKS.json`, `RECENT_COMMITS.json`, `SOURCE_PINS.json`, `WAVE9_ARCHITECTURES.md`
- `68-joint-positivity/review/formal/`: `NATIVE_CALIBRATION52.md`, `OBJECT_ZFC.md`, `SPLIT_SOURCE59.md`, `STATUS.md`
- `69-cones-pell/`: `LICENSE`, `MANIFEST.sha256`, `METRICS.json`, `NOTICE.md`, `README.md`, `VERIFICATION.json`, `verify.py`
- `69-cones-pell/integer/`: `CHECKS.json`, `PROOF.md`, `REVIEW.md`, `SOURCE_PINS.json`, `octic27.json`, `quartic38.json`, `reproduce.py`, `sextic32.json`
- `69-cones-pell/integer/certificates/`: `octic27_expansion.json`, `quartic38_expansion.json`, `sextic32_expansion.json`
- `69-cones-pell/integer/coefficients/`: `COEFFICIENT_BINDING.json`, `WC.bin.gz`, `Walpha.bin.gz`
- `69-cones-pell/integer/upstream/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-Q41.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`
- `69-cones-pell/positive/`: `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `REVIEW.md`, `SOURCE_PINS.json`, `build.py`, `equation.json`, `section.tex`, `verify.py`
- `69-cones-pell/positive/certificates/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`
- `69-cones-pell/positive/native/`: `ACTIVE_BINDING.json`, `FETCH_PROVENANCE.json`, `NOTICE-upstream.md`
- `69-cones-pell/positive/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `69-cones-pell/positive/upstream/source44/`: `NOTICE.md`
- `69-cones-pell/positive/upstream/source61/`: `NOTICE.md`
- `69-cones-pell/report/`: `report.pdf`, `report.tex`
- `69-cones-pell/review/`: `PDF_QA.json`, `SOURCE_PINS.json`
- `69-cones-pell/review/upstream/`: `OBJECT_ZFC.md`
- `70-residue-orientation/`: `BASELINE.json`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RESULTS.json`, `build_report.py`, `report.pdf`, `report.tex`, `verify.py`
- `70-residue-orientation/baseline/`: `OBJECT_ZFC.md`, `active_research_README.md`
- `70-residue-orientation/certificates/`: `INTEGRATED_REVIEW.json`, `PDF_QA.json`, `ROOT_NORMAL.json`, `ROOT_OPTIMIZED.json`
- `70-residue-orientation/eleven/`: `INDEPENDENT_AUDIT.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `OPTIMIZED_VERIFICATION.json`, `PROOF.md`, `RADICAL_INTEGRALITY_REVIEW.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `exact_ring.py`, `independent_audit.py`, `independent_ring.py`, `p11_positive_degree325.json`, `section.tex`, `verify.py`
- `70-residue-orientation/eleven/coefficients/`: `ACTIVE_BINDING.json`
- `70-residue-orientation/eleven/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `70-residue-orientation/integer/`: `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_verify.py`, `independent_literal_audit.py`, `octic29.json`, `octic29_expanded.json`, `quartic40.json`, `quartic40_direct.json`, `quartic40_direct_orientation_expanded.json`, `quartic40_residue_orientation_expanded.json`, `section.tex`, `sextic34.json`, `sextic34_expanded.json`, `typeset_residuals.json`
- `70-residue-orientation/integer/certificates/`: `COEFFICIENT_CHECKS.json`, `INDEPENDENT_LITERAL_AUDIT.json`, `NORMAL_STDOUT.json`, `OPTIMIZED_STDOUT.json`, `TYPESET_RESIDUAL_CHECK.json`, `VERIFIED.json`, `octic29_CHECKS.json`, `quartic40_direct_orientation_CHECKS.json`, `quartic40_residue_orientation_CHECKS.json`, `sextic34_CHECKS.json`
- `70-residue-orientation/integer/upstream/`: `LICENSE.ProveIt`
- `70-residue-orientation/integer/upstream/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `70-residue-orientation/positive/`: `INDEPENDENT_AUDIT.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `OPTIMIZED_VERIFICATION.json`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `independent_audit.py`, `independent_ring.py`, `p12_positive_degree84.json`, `p13_positive_degree30.json`, `section.tex`, `verify.py`
- `70-residue-orientation/positive/coefficients/`: `ACTIVE_BINDING.json`
- `70-residue-orientation/positive/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `71-determinant-guards/`: `LICENSE`, `MANIFEST.sha256`, `METRICS.json`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `build_coefficients.py`, `build_integer_forms.py`, `build_report.py`, `check_determinant_guard.py`, `check_integer_independent.py`, `make_archive.py`, `polynomial.py`, `report.pdf`, `report.tex`, `verify_all.py`
- `71-determinant-guards/certificates/`: `DETERMINANT_GUARD_CHECK.json`, `INTEGER_AUDIT.json`, `VERIFICATION_normal.json`, `VERIFICATION_optimized.json`, `octic27_audit.json`, `quartic38_audit.json`, `sextic32_audit.json`
- `71-determinant-guards/coefficients/`: `NEW_BINDING.json`
- `71-determinant-guards/coefficients/payloads/`: `cone_A.bin.gz`, `cone_B.bin.gz`
- `71-determinant-guards/integer_forms/`: `octic27.json`, `octic27_expanded.json`, `quartic38.json`, `quartic38_expanded.json`, `sextic32.json`, `sextic32_expanded.json`
- `71-determinant-guards/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE-source64.md`
- `71-determinant-guards/nine_positive/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `build_composed.py`, `check_composed.py`, `check_majorant.py`, `section.tex`
- `71-determinant-guards/nine_positive/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `71-determinant-guards/nine_positive/generated/`: `RESULTS.json`, `composed9_natural.json`, `composed9_natural_certificate.json`, `composed9_natural_degree.json`, `composed9_natural_power_chain.json`, `composed9_natural_pre_rewrite.json`, `composed9_positive.json`, `composed9_positive_certificate.json`, `composed9_positive_degree.json`, `composed9_positive_power_chain.json`, `composed9_positive_pre_rewrite.json`
- `71-determinant-guards/positive12/`: `CHECKS.json`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `adaptive_centered12.json`, `build.py`, `check.py`, `section.tex`
- `71-determinant-guards/positive12/native/`: `NOTICE-upstream.md`
- `71-determinant-guards/positive12/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `71-determinant-guards/positive12/source/`: `LICENSE`
- `71-determinant-guards/proofs/`: `DETERMINANT_GUARD.md`
- `71-determinant-guards/reviews/`: `FINAL_REVIEW.md`, `INTEGER_INDEPENDENT_REVIEW.json`, `INTEGER_INDEPENDENT_REVIEW.md`, `POSITIVE12_MATHEMATICAL_REVIEW.md`
- `71-determinant-guards/upstream/`: `ACTIVE_FORMALIZATION_README.md`
- `72-congruence-sextic/`: `DELIVERY_QA.json`, `FILE_MANIFEST.json`, `LICENSE`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_MANIFEST.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `report.pdf`, `report.tex`, `verify_all.py`, `verify_integrity.py`
- `72-congruence-sextic/integer34/`: `PROOF_SEXTIC34.md`, `README.md`, `SEXTIC34_CHECKS.json`, `SEXTIC34_INDEPENDENT_AUDIT.json`, `SEXTIC34_INDEPENDENT_REVIEW.md`, `SEXTIC34_VERIFICATION.json`, `UPSTREAM_FILES.json`, `audit_sextic34.py`, `build_sextic34.py`, `section34.tex`, `sextic34.json`, `sextic34_expanded.json`, `verify_sextic34.py`
- `72-congruence-sextic/integer34/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE.source34.md`, `NOTICE.source64.md`
- `72-congruence-sextic/positive13/`: `ACTIVE_BINDING.json`, `CHECK13.json`, `COEFFICIENT_VERIFICATION.json`, `PROOF13.md`, `README.md`, `SOURCE_DEPENDENCIES.md`, `build13.py`, `check13.py`, `p13_degree28.json`, `section13.tex`, `verify_coefficients.py`
- `72-congruence-sextic/positive13/independent/`: `INDEPENDENT_REVIEW.md`, `REVIEW13_DIAGNOSTICS.json`, `REVIEW13_FROM_INTEGER.md`, `check_independent.py`, `independent_algebra.json`, `review13.py`
- `72-congruence-sextic/positive13/native/`: `NOTICE-upstream.md`
- `72-congruence-sextic/positive13/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `72-congruence-sextic/positive14/`: `ACTIVE_BINDING.json`, `AUDIT14_INDEPENDENT.json`, `CHECK14.json`, `DIRECT_COORDINATE_LIMIT.md`, `PROOF14.md`, `README.md`, `REVIEW14_INDEPENDENT.md`, `audit14_independent.py`, `build14.py`, `check14.py`, `p13_degree28.json`, `p14_degree24.json`, `section14.tex`
- `72-congruence-sextic/provenance/`: `ALTERNATIVE_ROUTES.md`, `NATIVE_CALIBRATION52.md`, `NOTICE_K215.md`, `OBJECT_ZFC.md`
- `73-guard-reanchoring/`: `EQUATIONS.json`, `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `README.md`, `report.pdf`, `report.tex`, `verify_all.py`
- `73-guard-reanchoring/compact_coefficients/`: `INTEGRATION.md`, `LICENSE`, `NOTICE.md`, `POSITIVE_PORTS.json`, `README.md`, `REPRODUCIBILITY_CHECKS.json`, `REPRODUCIBILITY_CHECKS_OPTIMIZED.json`, `UPSTREAM_FILES.json`, `verify.py`
- `73-guard-reanchoring/compact_coefficients/native/`: `NOTICE-upstream.md`
- `73-guard-reanchoring/compact_coefficients/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `73-guard-reanchoring/integer34/`: `COMPACT_ADAPTER_CHECKS.json`, `COMPACT_S34_ADAPTER.md`, `PROOF.md`, `VERIFICATION.json`, `build_compact_instance.py`, `build_sextic34.py`, `sextic34.json`, `sextic34_compact.json`, `sextic34_expanded.json`, `verify_compact_adapter.py`, `verify_sextic34.py`
- `73-guard-reanchoring/integer_coefficients/`: `BUILD_CHECKS.json`, `COEFFICIENT_BINDING.json`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build_coefficients.py`, `provenance.py`, `verify_coefficients.py`
- `73-guard-reanchoring/integer_coefficients/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE-source64-integer41.md`
- `73-guard-reanchoring/positive/`: `CENTERED_NORM_EXPANSION.json`, `CHECK_NEW.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `PROOF.md`, `SOURCE61_NOTICE.md`, `build_adaptive13.py`, `build_centered12.py`, `check_new.py`, `dag.py`, `p12_centered_product_split2.json`, `p12_centered_sos_split2.json`, `p13_degree30.json`, `sparse.py`, `upstream_build12.py`, `upstream_build13.py`
- `73-guard-reanchoring/provenance/`: `AUDIT_SUMMARY.md`
- `73-guard-reanchoring/research/`: `junk_conservative_syntax.md`, `pell_jet_carrier.md`, `reusable_lemmas.tex`, `reusable_lemmas_checks.json`, `reusable_lemmas_checks_optimized.json`, `verify_reusable_lemmas.py`
- `73-guard-reanchoring/validation/`: `MANUSCRIPT_REVIEW.md`, `PDF_QA.json`, `VERIFICATION_normal.json`, `VERIFICATION_optimized.json`, `compact_normal.json`, `compact_optimized.json`, `reusable_normal.json`, `reusable_optimized.json`
- `74-centered-pell-gaps/`: `DOCUMENT_QA.json`, `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `README.md`, `VERIFICATION.json`, `build.py`, `build_domains.py`, `evaluate.py`, `report.pdf`, `report.tex`, `verify.py`
- `74-centered-pell-gaps/checks/`: `CENTERED_NORM_CHECK.json`, `CHECK12.json`, `check12.py`, `check_centered_norm.py`
- `74-centered-pell-gaps/circuits/`: `integer36.json`, `natural12.json`, `positive12_product.json`, `positive12_sos.json`
- `74-centered-pell-gaps/positive13/`: `CHECK13.json`, `NOTICE.md`, `PROOF.md`, `build13.py`, `check13.py`, `dag.py`, `p13_degree30.json`
- `74-centered-pell-gaps/research/`: `CENTERED12_AUDIT.md`, `LOW_DEGREE_EXPLORATION.md`, `SCALE_BARRIER.md`
- `74-centered-pell-gaps/upstream/`: `FETCH_LEDGER.json`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE44.md`, `NOTICE61.md`, `NOTICE_K215.md`
- `75-signed-bootstrap/`: `DEPENDENCIES.md`, `INCOMING_PINS.json`, `README.md`, `REBUILD_FILES.json`, `build_report.sh`, `check_displayed_system.py`, `negative_controls.py`, `report.pdf`, `report.tex`, `verify.py`
- `75-signed-bootstrap/certificates/`: `CHECK_RESULTS.json`, `INERT_PRIME_CLOSURE.md`, `check_certificate.py`, `section.tex`
- `75-signed-bootstrap/direct/`: `AUDIT.json`, `BOUNDARY_THEOREM.md`, `REMAINING_FINITE_ARTIFACTS.md`, `SOURCE_PINS.json`, `TOY_INITIALIZER.json`, `build_initializer.py`, `check_boundary.py`, `section.tex`
- `75-signed-bootstrap/guards/`: `AUDIT.json`, `CHECK.json`, `PROOF.md`, `README.md`, `SEXTIC_RESTORATION.json`, `UPSTREAM_COPY_RECEIPT.json`, `absorbed30_octic.json`, `build.py`, `check.py`, `section.tex`, `signed34_sextic.json`, `signed40_sextic.json`
- `75-signed-bootstrap/guards/review/`: `CHECK.json`, `MATHEMATICAL_REVIEW.md`, `check_independent.py`
- `75-signed-bootstrap/guards/upstream/q41/`: `NOTICE.md`
- `75-signed-bootstrap/guards/upstream/q41/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `75-signed-bootstrap/low_degree/`: `CHECK12.json`, `CHECK13.json`, `COEFFICIENT_BINDING.json`, `FAILED_ROOT_MERGER.md`, `NEGATIVE_CONTROLS.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build12.py`, `build13.py`, `check12.py`, `check13.py`, `p12_product_split2.json`, `p12_sos_split2.json`, `p13_degree30.json`, `section.tex`
- `75-signed-bootstrap/mixed_source/`: `COEFFICIENT_BINDING.json`, `PROOF.md`, `README.md`, `build.py`, `check.py`, `section.tex`, `source21.json`, `source24.json`, `source26.json`, `verification.txt`
- `75-signed-bootstrap/review/`: `ARRIVAL_COMMIT.json`, `COMMITS.json`
- `75-signed-bootstrap/review/baseline/`: `BASELINE_REVIEW.md`, `ConZFC_Gap_Congruence_2026-10-23.stdout.txt`, `ConZFC_Positive_Gap_2026-10-23.stdout.txt`, `EXECUTION_SURFACE.json`, `FORMAL_COMMIT.json`, `FORMAL_SOURCE_PINS.json`, `FRONTIER_COUNTS.json`, `LOW_DEGREE_COUNTS.json`, `NATIVE_CALIBRATION52.md`, `OBJECT_ZFC.md`, `REPLAY_RESULTS.json`, `SELECTED_PARETO.json`, `SPLIT_SOURCE59.md`, `STATUS.md`, `ZFC_Diophantine_Oriented_Guards_2026-10-23.stdout.txt`, `con-zfc-congruence-carriers.stdout.txt`, `con-zfc-sign-and-norm.stdout.txt`, `con-zfc-sign-recovery-2026-10-23.stderr.txt`, `con-zfc-structural-reductions-2026-10-23.stdout.txt`, `count_frontier.py`, `pareto.py`, `replay_inputs.py`
- `75-signed-bootstrap/review/formal/`: `PINS.json`, `STATUS.md`
- `75-signed-bootstrap/review/interfaces/`: `AUDIT.md`, `CHECK_RESULTS.json`, `PORTABILITY.json`, `REPLAY.md`, `check_independent.py`
- `75-signed-bootstrap/review/latest/`: `PINS.json`, `REVIEW.md`, `STATUS.md`
- `75-signed-bootstrap/review/positive/`: `AUDIT.md`, `BINDINGS_CHECK.json`, `CHECK.json`, `PORTABILITY.json`, `check.py`, `check_bindings.py`, `portability.py`
- `75-signed-bootstrap/review/signed34/`: `CHECK.json`, `MATHEMATICAL_REVIEW.md`, `MIXED_SOURCE_COMPARISON.json`, `check_independent.py`
- top level: `README.md` (this file), `PLACEMENT.md`

