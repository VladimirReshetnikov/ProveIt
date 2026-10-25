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
- During wave 11, the research session reviewed the arrivals as they came
  ([PROPOSAL_REVIEW_WAVE11.md](../PROPOSAL_REVIEW_WAVE11.md) and the
  `PROPOSAL_REVIEW_*.md` files of 23–24 October) and built its own
  candidates on them; [PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md)
  compares packages and candidates together. Several of its candidates
  dominate wave-11 packages the day they arrived (ten positive at
  degree 368 in 99 operations; direct quartics in 610 unrestricted integers).

The delivered packages remain unchanged.

**Explicit polynomials with fixed integer coefficients whose unsolvability
ZFC proves equivalent to Con(ZFC). Waves 5–15 are all in the tree. The stated
frontier, over the packages of this collection, is now:**

- **nine positive unknowns** in 420 operations at degree 1,472,168 (101), or
  at degree 997,810 in 1,057 operations (101);
- **ten positive unknowns** in 78 operations at degree 630 (134), or at
  degree 246 in 121 (130), with thirteen further Pareto points between;
- **ten unrestricted integers** at degree 1,245,324 in 467 operations and at
  degree 1,080,888 in 507 (106), via Sun's reduction;
- **eleven unrestricted integers without Sun's reduction** in 107
  operations at degree 924 (138), or at degree 328 in 130 (135); twelve at
  degree 500 in 139 (121), or in 123 operations at degree 1,084 (113);
  thirteen at degree 156 in 127 (137) or 536 in 126 (118); fourteen at
  degree 88 in 119 (137); fifteen at degree 44 in 111 (132) or 48 in 108
  (121) (each count ranked on its own; across counts, 125's 11ℤ 488 / 118
  and 135's 398 / 121 dominate both 12ℤ points and 13ℤ 536 / 126; both 15ℤ
  points dominate every 16ℤ point, and 48 / 108 also 17ℤ 88 / 110);
  sixteen at 98 in 138 (106) and 112 in 119 (93); seventeen at 88 in 110 (88);
- **direct quartics in the numerical proof calculus C222**, with no
  coefficient tuple and without K215, Jones or Sun: 226 naturals (139) and
  282 unrestricted integers (135), and quartics with every coefficient ±1
  in 793 integers (135);
- **eleven positive unknowns** at degree 211 in 107 operations (115);
- **twelve positive unknowns** at degree 70 in 95 operations (115), or in 89
  operations (57's 258 form);
- **thirteen positive unknowns** at degree 28 (72), at degree 51 in 87
  operations (115), or in 83 operations at degree 114 (62);
- **fourteen positive unknowns** at degree 24 (72), or in 79 operations at
  degree 52 (55, 59);
- **fifteen positive unknowns** at degree 24 in 88 operations (66), and in
  66 operations (51's P66, degree 157), both unchanged;
- **a quartic in 37 unrestricted integers** (76, 82; 77), a sextic in 30
  (76), an octic in 25 in 127 operations (77), and a degree-14 form in 22
  (79, 81);
- **the smallest native tuple binding an equation**, B = 2^429959 (54,
  unchanged); the direct quartics bind no tuple at all.

Results in this repository that are not intake packages are compared
separately. The four-root ten-positive equation
[candidates/ten-positive-scaled-norm](../candidates/ten-positive-scaled-norm/README.md)
(degree 816, 124 operations) was written here on 23 October 2026; wave-11
packages 107 and 109 and the research session's zero-offset kernel descend
from it. [candidates/ten-positive-gap-fusion](../candidates/ten-positive-gap-fusion/README.md)
(24 October) combines wave 12's coprime fusion with 118's auxiliary-index
gap. Its six equations (89 / 288 to 97 / 254) turned out to be preceded by
wave-13 packages 119 and 121 (four identical polynomials in 121); it is kept
as an independent derivation with its own proof, adding no frontier point.
The research session's own candidates are compared in
[PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md). Its canonical page
is 113's universal 92 / 283 circuit on a third tuple; by 17:12 on 24 October
it also had 89 / 288 (`90d8b714f9`, page `0ca3812ae9`) and a ten-positive
86 / 466 (`75f850496c`), which wave-14 package 133's 84 / 436 dominates.
At 22:03 it accepted 133's 84 / 436 and 85 / 328 (`a223b3e174`) with an
explicit completeness repair (the canonical bound R > 3q ≥ 96).
[candidates/ten-positive-qcube-product-square](../candidates/ten-positive-qcube-product-square/README.md)
applies q-cube normalization to 133's product square: 81 operations at
degree 750 and 82 at 560. The research session committed the same
composition first, as a code-free proposal (`a576e152f4`, 22:07); this
repository's package, written concurrently, supplies the emitted circuits
and their checks (`a2c20ea419`). Wave-15 package 137 ships the same two
polynomials, built by 21:44, before either commit; wave-15 package 134's
78 / 630 and 79 / 468 (built 21:48) dominate them.

The report holds one hundred and nine research packages. All but 60, 66, 68, 97, 102,
106, 110, 121 and 125 state AI assistance. Some do so only in part: 74
for its reviews; 77, 78, 101 and 130 in their TeX author lines; 88, 131, 132 and 137
in copied notices; 111 in its PDF author field; 116 in one component file.

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

- **Wave 11**, sources 76–110: batch 227 (seventeen arrivals `c1a102936a` to
  `e13c748234`, placed in `240bf9e422` and `c16a89ad94`), pinned to
  `2605669a53`, `cf4a5218a5`, `9a33342a03`, `a88aefd7dd`, `08200eb10f`,
  `04a1d79222`, `7e533c3381` and `ec80841c07` among others.
- **Wave 12**, sources 111–118: batch 228 (arrival `45b399ec51`, placed in
  `55fe52f28c`), all pinned to `84e16e4309`.
- **Wave 13**, sources 119–126: batch 229 (arrival `5f3379063d`, placed in
  `9f7ff01558`), all pinned to the wave-12 arrival `45b399ec51`.
- **Wave 14**, sources 127–133: batch 230 (arrival `fd3e384e92`, placed in
  `1c5367452a`), all pinned to `f4d8db99e0`.
- **Wave 15**, sources 134–139: batch 231 (arrival `e0c98c629b`, placed in
  `1eed4b48cd`), pinned to the wave-14 placement `1c5367452a` (137 to
  `b30ddde0aa`).

**Earlier waves are kept.** By Vladimir's direction, waves 6–15 are each
placed beside the earlier waves rather than replacing them. Wave-7 packages
cite wave-5 and wave-6 packages by number; no wave-7 package cites another.
In wave 8, only 59 cites a sibling: it reviews and builds on 56 and 57,
which reached it during packaging. No wave-9 or wave-10 package cites a
sibling of its own wave. Wave 11 spans seventeen arrivals, and later
packages of it cite earlier ones; no package of waves 12–15 cites a
sibling.

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

Until wave 11, every finished equation encoded the K215 blank run through
the native compiler, and most also used Jones's reduction or Sun's;
[The common theorem](#the-common-theorem) below describes that route. Wave
11 adds a second finished route: direct quartics in the repository's
numerical proof calculus C222 (87, 89, 93–96, 98–109, see the wave-11
section), with no coefficient tuple and without K215, Jones or Sun. Neither
route is a rule. Part of the route has
checked infrastructure here: the K215 endpoint in Lean and Rocq, and the
Lean development of Jones's reduction. The compiler and the Diophantine
bridge are not formalized.

Other routes in the repository:
- **Finished by packages.** The direct C222 quartics of waves 11–15 (87's
  27,916 integers down to 139's 226 naturals and 135's 282 integers) are complete
  explicit polynomials on a route without K215 or Jones; their calibration
  is two Lean interfaces plus an ordinary proof of "polynomial zero iff
  C222 derivation" (wave-11 section). Wave 9's 60, 66 and 67 and wave 10's
  68 and 75 had discussed or built pieces of such routes; 68's local step
  is the source both wave-11 lineages compile.
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
| 10 | 226 | `9513bd88ce` | `d79b41884d` … (kept) | `3956ae57a3` |
| 11 | 227 | `c1a102936a` … `e13c748234` (17 commits) | `240bf9e422`, `c16a89ad94` … (kept) | `84e955a03a` |
| 12 | 228 | `45b399ec51` | `55fe52f28c` … (kept) | `e87cc5c80c` |
| 13 | 229 | `5f3379063d` | `9f7ff01558` … (kept) | `e87cc5c80c` |
| 14 | 230 | `fd3e384e92` | `1c5367452a` … (kept) | `55a1e3a19d` |
| 15 | 231 | `e0c98c629b` | `1eed4b48cd` … | this file |

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

[`PLACEMENT.md`](PLACEMENT.md) is the recovery map for all eleven waves: the
batch-221 record, then the appended batch-222 to batch-231 records.

| Wave | Archive members | Staged | Omitted copies | Ignored |
|---|---:|---:|---:|---:|
| 5 | 1,197 | 1,129 | 46 | 22 |
| 6 | 1,149 | 773 | 371 | 5 |
| 7 | 1,571 | 1,043 | 524 | 4 |
| 8 | 1,736 | 974 | 759 | 3 |
| 9 | 1,829 | 1,030 | 766 | 33 |
| 10 | 1,192 | 703 | 440 | 49 |
| 11 | 7,386 | 5,291 | 2,043 | 52 |
| 12 | 1,693 | 1,150 | 535 | 8 |
| 13 | 2,686 | 1,058 | 1,624 | 4 |
| 14 | 3,294 | 1,148 | 2,140 | 6 |
| 15 | 3,468 | 1,258 | 2,205 | 5 |

Omitted copies are byte-identical (up to line ends) to repository files.
Most of the later waves' are copies of earlier-wave files of this
report, which stay in the tree. Copies within one wave are kept: 59's copies
of 56's and 57's files are staged twice. 75's bundled copies of the eight
wave-9 ZIPs are omitted and mapped to their arrival commit `0c6be9a074`.
Wave 10 also ships ignored TeX build artifacts. Ignored members are checksum ledgers and logs, excluded by the root
`.gitignore`. Wave 11's packages bundle one another and earlier arrivals
wholesale (77 carries all eight wave-10 archives), which is why 2,043 of its
members are copies. Its omission rule is narrower than before: a member whose
only repository copies are the research session's volatile files
(`candidates/`, `research/`, worktree copies) is kept, because that session
copies and rewrites arriving packages; the first placement had omitted
1,119 such members (1,108 staged files; the rest are ignored ledgers and
logs) and `c16a89ad94` restored them.

## The common theorem

This is the route the packages so far have taken; it is not required (see
above). Each finished equation defines polynomials or small systems with four
**fixed integer coefficient ports** (69's and 71's integer forms use six
payloads):

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
- **Residue orientation** (70) removes the X = 2u² witness from the integer
  quartic. **Root transfer** (70) moves Pell roots into an existing positive
  gap: one root for twelve positive unknowns, three for eleven.
- **Congruence carriers** (72) give thirteen positive unknowns at degree 28
  and fourteen at 24.
- **Rational Pell descent** (69) recovers integrality after a norm merger,
  for twelve positive unknowns at degree 82.
- **Adaptive carrier moduli and centred norms** (71, 73, 74) and a
  **signed-power bootstrap** (75).
- **Composed sources and finalizers**: 71's nine-positive form, and 68's
  ten-integer form with a strengthened Lucas-index lemma.

## Combined frontier, waves 5–15 (intake findings)

Numbers are the packages' own. At intake, read-only dossiers recounted
every operation count and measured the degrees of the headline circuits
(two each for waves 12 to 14, three for wave 15, five for wave 11, four for each earlier wave); all checked
figures agree with the claims. The mathematics was not re-derived, and
every dominance statement assumes the competing proofs are correct. Only
packages of this collection are ranked here, each unknown count on its own
row. The active research session's own candidates and this
repository's `candidates/ten-positive-gap-fusion` (an independent
derivation of package points) are compared in its
[PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md).
At the wave-15 intake several research circuits dominate package rows: its
nine-positive 405 operations at degree 1,191,570 and 413 at 1,316,546
(`23d8510a10`; the 413 form on the 2^429959 tuple), 722 at 1,158,228 and
1,056 at 997,810 dominate every nine-positive package point; its
ten-positive 84 / 328 (operations / degree, `b33b254625`) dominates 133's
85 / 328; and its fourteen-positive 73 / 342 to 76 / 191 use fewer
operations than the packages' 79. Its ℤ quartics of height 15,109
(315 / 217 / 5,620 and 316 / 218 / 5,614) are Pareto with 135's.

- "u / e / d / o" means unknowns / equations / degree / operations; pairs
  are degree / operations, except in the ten-positive rows and the wave-14
  and wave-15 sections' ten-positive entries, which give operations / degree. For the
  direct quartics (degree 4 throughout) the measures are variables /
  residuals / expanded terms / coefficient
  height.
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
    takes 7 operations;
  - the wave-11 ten-integer and nine-positive forms use eleven or twelve
    derived leaves (radix and threshold powers, recipe outputs), all
    materialized and checked.
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
    product adds twelve;
  - in wave 11, 85's nine-positive forms add seven, 84's ten-positive form
    ten, and 110's ten.

  The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package. Within one wave, the
lower directory number counts as earlier.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Nine positive, fewest operations | **420** at degree 1,472,168 (ℕ: not shipped) | 101 | 101 |
| Nine positive, lowest degree | **997,810 / 1,057** | 101 | 101 |
| Nine positive, Pareto frontier | 1,472,168 / 420 (101); 1,376,378 / 456 (105); 1,158,228 / 726 (82); 997,810 / 1,057 (101). Dominated by these: 66's 444 and every earlier nine-positive form; 101's 428 and 85's 434 ≡ 86's 435 (one polynomial), 105's 442, 86's 449, 79's 1,753, 85's 1,074, 86's 1,086 | 82, 101, 105 | — |
| Nine positive on the 2^429959 tuple | **1,626,248 / 428** (101); 1,628,768 / 434 (85; 86 evaluates the same polynomial in 435); 1,520,186 / 442 (105). Earlier: 54's 490 | 85, 101, 105 | 85 |
| Ten positive, Pareto frontier | **78 / 630** and 79 / 468 (134); 83 / 436 (138, 133's 84 / 436 with T replaced by T − α); 85 / 328 (133); 87 / 323 and 88 / 318 (139); 89 / 288, 91 / 283, 92 / 278, 94 / 262, 96 / 258, 97 / 254 (119 on the BFS tuple, 121 on the original one; 119's 92 / 278 is 117's polynomial in one operation fewer, 121's the same circuit on the other tuple); 102 / 253 and 104 / 252 (132); **121 / 246** (130). Dominated: 138's 80 / 750 and 81 / 560, 137's 81 / 750 and 82 / 560, 133's 84 / 436, 130's 86 / 466, 87 / 466, 89 / 450 and 90 / 450, 131's 87 / 436 and 88 / 380, 113's, 116's, 117's and 118's forms, 115's 98 / 368 and 103 / 340, and every earlier form | 119, 121, 130, 132, 133, 134, 138, 139 | 84 (first), 113 (fusion) |
| 10ℤ (Sun's reduction), Pareto frontier | **1,245,324 / 467**, 1,179,788 / 470, 1,114,252 / 473, **1,080,888 / 507** (106, re-evaluating 87's 471 form and the research session's three shears of it). Other polynomials: 76's 480 / 1,245,324, 83's 484 / 1,179,788, 487 / 1,114,252 and 521 / 1,081,125, 87's 485, 496 and 545 / 1,080,888, 91's re-evaluations. All dominate 68's 1,576,864 / 481 | 76, 83, 87, 106 | 76 (degree), 87 (operations) |
| 11ℤ, without Sun's reduction, Pareto frontier | **924 / 107** and 840 / 108 (138); 810 / 112 (131); 648 / 115 (137); 488 / 118 and 464 / 119 (125); 398 / 121, 352 / 125, 340 / 129 and **328 / 130** (135). Dominated: 132's 924 / 109, 840 / 110, 428 / 123, 412 / 127, 396 / 128, 376 / 127, 364 / 131 and 352 / 132, 131's 966 / 109, 882 / 110 and 654 / 117, 137's 640 / 118, 580 / 119 and 574 / 122, 135's controls 382 / 125 and 366 / 126, 123's forms, 125's 456 / 124 and 416 / 125, 127's 440 / 126 and 412 / 127, 116's, 120's, 121's and 126's forms, 110's three | 125, 131, 135, 137, 138 | 110 |
| 12ℤ, Pareto frontier | **500 / 139** (121's evaluator of 116's polynomial); **1,084 / 123** (113). Dominated: 116's 500 / 148, 112's 768 / 141, 111's 1,040 / 140 and four further forms, 110's 1,000 / 180 and 1,024 / 179, 118's two, and every wave-11 form | 97, 111, 112, 113, 116, 121 | 97 |
| 13ℤ, Pareto frontier | **156 / 127** (137); 536 / 126 (118). Dominated: 116's 274 / 129, 105's 1,072 / 186, 1,392 / 177 and 1,408 / 176 and every earlier 13ℤ form | 118, 137 | 88 |
| 14ℤ | **88 / 119** (137). Dominated: 116's 108 / 119, 106's 378 / 145, 88's 792 / 137 and every earlier 14ℤ form | 137 | 88 |
| 15ℤ, Pareto frontier | **44 / 111** (132); **48 / 108** (121). Dominated: 116's 56 / 110, 106's 172 / 123 and every earlier 15ℤ form | 116, 121, 132 | 88 (first 15ℤ form, 344 / 131) |
| 16ℤ, Pareto frontier | **98 / 138** (106); 108 / 132 (91); **112 / 119** (93); 124 / 118 (98); **160 / 115** (92). Dominated: 92's 152 / 120, 132 / 128 and 120 / 123, 93's 112 / 120, 86's 184 / 135 and 192 / 134 | 86, 91, 92, 93, 98, 106 | 86 |
| 17ℤ | **88 / 110** (88). 82's and 86's 17ℤ / 88 forms are different polynomials (82 uncounted, 86 at 114); 84's 112 / 124 and 110 / 140 dominated | 82, 86, 88 | 82 |
| 18ℤ–20ℤ | 18ℤ **32 / 112** (88) and 88 / 105 (85; 82's 18ℤ / 32 uncounted, 84's 80 / 115 and 77's 88 / 109 dominated); 19ℤ **28 / 116** (88) and 32 / 108 (85, the pivot polynomial of 83 and 84; 82 uncounted; 89's 19ℤ / 40 and 77's 32 / 112 dominated); 20ℤ **18 / 115** (93) and 20 / 111 (85; the pivot polynomial of 83 and 84; 88's 24 / 120 and 77's 32 / 112 dominated) | 82, 83, 85, 88, 89, 93 | 82 (18ℤ, 19ℤ), 83 (20ℤ) |
| 21ℤ–24ℤ | 21ℤ / 16 (89, 9 residuals; 83 ≡ 84 ≡ 85 at 114 operations; 87, different); 22ℤ / 14 (79; 81 at 123) and 22ℤ / 16 / 118 (77); 23ℤ / 10 (83 ≡ 86 at 131) and 23ℤ / 12 (77 at 121; 79, 81, 82); 24ℤ / 10 (78; 81 at 135; 82). All beat 68's 26ℤ / 16 and 37's 24ℤ / 1,936 | 77, 78, 79, 81, 83, 86, 89 | 77 |
| Integer octic | **25ℤ** in 127 operations (77). Dominated: the 26ℤ octics of 76, 77, 78, 79, 81, 82 and 68's 28ℤ, 69's and 71's 27ℤ | 77 | 77 |
| Integer sextic | **30ℤ** (76). Dominated: the 31ℤ sextics of 77, 79, 81 (144 operations), 82, and the 32ℤ and 34ℤ sextics of waves 9–10 | 76 | 76 |
| Integer quartic | **37ℤ** (76 ≡ 82, two variants; 77's four variants differ in one guard row). Dominated: 69's and 71's 38ℤ | 76, 77, 82 | 76 |
| Direct C222 quartic, ℕ (no K215, Jones, Sun or coefficient tuple) | **226 / 175 / 10,314 / 87,839,583** and 227 / 176 / 7,905 / 87,839,583 (139); 229 / 179 / 9,184 / 83,954,634 and 230 / 180 / 6,858 / 83,954,472 (135); 255 / 203 / 5,743 / 64,214,623 (133); 242 / 190 / 9,308 / 18,049,118 (128); 278 / 215 / 5,524 / 83,852,788 (131); 320 (123), 331ds / 255 / 15,769 / 15,246,025 and 332ss / 255 / 14,184 / 10,785,132 (125) and 333 / 264 / 4,357 (122) on height or terms; 4,860 / 4,476 / 14,719 / **1,837** (98, lowest height). Raw systems: 332 / 281 / 5,256 / 64,189,687 (139), 334 / 284 / 4,871 / 64,000,374 (135), 337 / 286 / 4,696 / 64,174,125 (138), 339 / 288 / 5,000 / 63,933,525 (134), 343 / 291 / 4,593 / 64,174,057 (133), 359 / 307 / 5,706 / 1,418,780 (128), 412 / 349 / **2,852** / 63,907,302 (131), 479 / 414 / 3,042 / 1,144,307 (123), 554 / 476 / 3,276 / 1,142,323 (112). Dominated: 135's 228 (by 139's 227), 134's 233, 138's 235 and 236, 129's 233 and 234, 133's 237, 239 and 240, 131's 249, 124's 261 and 292, 127's, 130's 241 and dense 239, 108's and 109's 395; raw: 138's 336, 130's 349, 131's 387, 123's 465, 124's 435 and 406, and earlier forms | 98, 112, 122, 123, 125, 128, 131, 133, 134, 135, 138, 139 | 87 (earliest), 89 (this lineage) |
| Direct C222 quartic, ℤ | **282 / 192 / 5,491 / 128,446**, 287 / 197 / 4,313 / 128,446 and 309 / 219 / **3,922** / 128,446 (135); 793 integers / 51,982 terms, 806 / 23,719 and 994 / 11,744, all at **height 1** (135; not sums of squares, so compared on variables, terms and height). Dominated: 134's 314, 136's 306, 137's 307, 308 and 310, 138's 286 and 319, 131's 324 and 338, 102's 3,776, 114's 3,564, the height-one forms of 127 (2,215 / 30,468), 136 and 139, 125's 442, 132's 352 and 355, 128's 378, 127's 381 and 391, 130's 964, 120's height-one 7,431, and every earlier form | 135 | 87 |
| Eleven positive | **211 / 107** (115's evaluator of the research session's polynomial, which 105 evaluates in 110). Dominated: 83's 211 / 112, 86's 213 / 112, 87's 211 / 113, 82's 269 / 111, the 277 / 111 polynomial of 76, 77, 78, 79, 81, 77's 257 / 114, and 70's 325 / 113 | 83, 105, 115 | 76 (277), 83 (211) |
| Twelve positive, Pareto frontier | **70 / 95** (115's evaluator of 98's free-J polynomial); 57's **258 / 89**. Dominated: 98's 70 / 98, 76's 78 / 101 ≡ 82's 78 / 102, 78's ≡ 81's 78 / 103, 87's 70 / 100, 69's 82 / 102, 74's forms | 98, 115; 57 | 80 (claim), 87 (first artifact), 98 |
| Thirteen positive, Pareto frontier | **28 / 98** (72); 30 / 92 (73; 74 evaluates the same polynomial in 93); **51 / 87** (115's evaluator of 98's polynomial); **114 / 83** (62). Dominated: 98's 51 / 88, 70's and 75's 30 / 94, 61's 34 / 93 | 72; 73; 98, 115; 62 | — |
| Fourteen positive, Pareto frontier | unchanged: **24 / 101** (72); 65's 26 / 92; 64's 30 / 83; 55's and 59's **52 / 79** | 72; 65; 64; 55 | — |
| Fifteen positive | unchanged: 66 ops (51's P66, degree 157); lowest degree 24 / 88 (66); Pareto frontier as after wave 9 | 51; 66 | — |
| Twelve positive, systems | unchanged: 59's three-equation system at 94 operations | 59 | 59 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125. From wave 2 (history only, see the wave-2 README `5b0c9ae9fd`): 15's positive-domain sextic in 25 and octic in 20 unknowns, which still dominate 75's 26- and 21-unknown versions | waves 2, 5, 6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^429959** (54) among tuple-bound equations; 85, 86, 101 and 105 bind nine-positive forms to it. The direct quartics bind no tuple at all: their coefficients are the small integers of the expanded polynomial (heights from 1 (135; earlier 127, 120) and 2 (114) to about 9.9·10^27 (115)) | 54; 87–89 | 54 |




## Wave 15 (sources 134–139)

The six archives of arrival `e0c98c629b` (25 October 2026, 13:29) were
placed as batch 231 in `1eed4b48cd`, in archive-name order. Five pin the
wave-14 placement `1c5367452a` (24 October, 21:20). 137 pins `b30ddde0aa`
(21:23), with a late check against the research commit `a6a4cb5a71` (21:38).
None pins the wave-14 reconciliation. Their PDFs were built on 24 October
between 21:45 and 21:57 (136 at 21:45, 134 at 21:48, 138 at 21:49, 139 at
21:52, 135 at 21:57). 137's PDF date is forced to 17:00 by `SOURCE_DATE_EPOCH`;
its unforced standalone PDFs date from 21:37 and 21:43. None cites a sibling.
17 placed paths exceed 250 characters. In this section ten-positive pairs are
operations / degree, integer-circuit pairs degree / operations.

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`134-certificate-reductions/`](134-certificate-reductions/) | `ConZFC_Certificate_Reductions_2026-10-25.zip` | *Eliminating Auxiliary Witnesses in Diophantine Consistency* (README and PDF metadata in sentence case) | ten positive **78 / 630** and **79 / 468** (133's indexed tuple); direct quartics ℤ 314 / 204 / 5,721 / 128,446 and ℕ 233 / 182 / 7,313 / 86,543,666; raw ℕ 339 / 288 / 5,000 / 63,933,525 |
| [`135-cofinal-anchors-round17/`](135-cofinal-anchors-round17/) | `ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip` | *Cofinal anchors and height one equations for ZFC consistency* (round 17 of 106, 112, 125 and 131's series) | direct quartics **ℤ 282 / 192 / 5,491**, **287 / 197 / 4,313** and **309 / 219 / 3,922** (height 128,446); **ℕ 229 / 179 / 9,184 / 83,954,634** and **230 / 180 / 6,858 / 83,954,472**, ℕ 228 / 178 / 9,866 / 2.4·10^12; **height one in 793 / 51,982, 806 / 23,719 and 994 / 11,744** (integers / terms); raw ℕ 334 / 284 / 4,871 / 64,000,374; 11ℤ **398 / 121, 352 / 125, 340 / 129, 328 / 130** (source34) |
| [`136-local-certificates/`](136-local-certificates/) | `ConZFC_Local_Certificates_2026-10-24.zip` | *Local certificates for Diophantine consistency* (`README.txt`, no H1) | direct quartic ℤ 306 / 206 / 6,259 / 128,446; height one 1,252 / 27,738, 985 / 95,609, 1,122 / 25,922 |
| [`137-odd-helpers-saturated-carriers/`](137-odd-helpers-saturated-carriers/) | `ConZFC_Odd_Helpers_Saturated_Carriers_2026-10-25.zip` (wrapper `ConZFC_Odd_Helpers_Saturated_Carriers`) | *Odd Pell helpers and saturated carriers* (round 17 of 116, 121 and 132's series) | direct quartics ℤ 307 / 211 / 22,532 / 394,412, 308 / 212 / 5,364 / 195,962, 310 / 214 / 5,612 / 128,446; **14ℤ 88 / 119**, **13ℤ 156 / 127**, **11ℤ 648 / 115** (source34); ten positive 81 / 750 and 82 / 560 (133's indexed tuple); bundles the whole 132 archive, which nests the whole 121 and 116 archives |
| [`138-semantic-signs/`](138-semantic-signs/) | `ConZFC_Semantic_Signs_2026-10-24.zip` | *Semantic Sign Recovery and Cofinal Bounds* (README H1 in sentence case; PDF metadata adds the subtitle) | direct quartics ℤ 286 / 196 / 6,607 and 319 / 207 / 5,779 (height 128,446), ℕ 235 / 184 / 22,185 and 236 / 185 / 15,645; raw ℕ 336 / 285 / 6,122 and **337 / 286 / 4,696 / 64,174,125**; ten positive 80 / 750, 81 / 560, **83 / 436** (133's indexed tuple); **11ℤ 924 / 107, 840 / 108** (source34) |
| [`139-graph-digits/`](139-graph-digits/) | `conzfc_graph_digits_2026-10-24.zip` | *Smaller explicit Diophantine equations for Con(ZFC)* | **direct quartics ℕ 226 / 175 / 10,314 / 87,839,583** and **227 / 176 / 7,905 / 87,839,583**; raw ℕ **332 / 281 / 5,256 / 64,189,687**; height one 951 / 56,916, 984 / 30,076, 1,050 / 21,766, 1,137 / 23,105; ten positive **87 / 323** and **88 / 318**; a degree-8 substitution recipe in 678 integers |

### Identities and dominance (intake findings)

Three read-only dossiers recounted every circuit, measured every headline
degree on random lines, re-expanded every direct quartic, rebuilt every
height-one polynomial from its certificate and replayed the elimination
certificates of 134, 135, 137, 138 and 139; every claimed figure was
confirmed. The unbounded proofs were not re-derived.

- **Ten positive.** 134's 78 / 630 and 79 / 468 are 133's two circuits with
  the scale μ = q² + 1 removed (Y = q³s, net −6 operations). They dominate
  every other point below 83 operations. 138's 83 / 436 is 133's 84 / 436 with
  T replaced by T − α, and dominates it. 139's 87 / 323 and 88 / 318 are
  133's 85 / 328 with n replaced by n + d·V (d = (A − 1)UE and AUE). 137's
  81 / 750 and 82 / 560 satisfy q⁶·P₁₃₇(n, s) = P₁₃₃(n − s, q³s); 138's
  80 / 750 and 81 / 560 are 137's two with T replaced by T − α. 134's,
  138's and 139's points are all new Pareto points.
- **Direct ℤ quartics.** 135's three charts dominate every other package
  quartic at height 128,446: 282 / 192 / 5,491 dominates 134's 314, 136's
  306, 137's 307 and 310, 138's 286 and 319, and 131's 324; 287 / 197 / 4,313
  dominates 137's 308 and 131's 338. On variables, terms and height, 135's
  height-one 994 / 11,744 dominates 102's 3,776 / 20,194 / 47,959, 114's
  3,564 / 14,518 / 2, 127's 2,215 / 30,468 and every height-one form of 136
  and 139 (graph forms have no residual count).
- **Direct ℕ quartics.** 139's 226 is the fewest-variable direct quartic;
  135's 230 dominates 129's 234, 134's 233, 138's 235 and 236, 133's 239 and
  240 and 131's 249; 134's 233 / 182 / 7,313 dominates 129's 233. 139's 227
  dominates 135's 228. Raw: 139's 332 dominates 138's 336, and 134's 339
  dominates 130's 349.
- **Integers without Sun's reduction.** 138's 924 / 107 and 840 / 108 are
  new polynomials dominating 132's 924 / 109 and 840 / 110. 137's 648 / 115
  dominates 131's 654 / 117. 135's 398 / 121 dominates 132's 428 / 123, and
  352 / 125 dominates 132's 352 / 132, 364 / 131 and 376 / 127 and 125's
  416 / 125. 137's 13ℤ 156 / 127 and 14ℤ 88 / 119 dominate 116's 274 / 129
  and 108 / 119.
- **Degree-8 recipes.** 139's 678 integers (x = a² + b² + c(c + 1) on
  every natural coordinate) undercut 129's 699 and 702, 133's 717 and 124's
  783.

### Tensions, not adjudicated at intake

- **One composition, found three times.** 137's 81 / 750 and 82 / 560 are
  the same polynomials as this repository's
  [candidates/ten-positive-qcube-product-square](../candidates/ten-positive-qcube-product-square/README.md)
  (`a2c20ea419`, 22:20) and the research session's (proposal `a576e152f4`,
  22:07; circuits accepted `de1e2b85a6`, 22:41). 138's 80 / 750, 81 / 560
  and 83 / 436 are the research session's unshifted-T circuits (accepted
  `b33b254625`, 23:29). Both packages were built earlier (137 by 21:44, 138
  at 21:49) than those commits; no package saw them, so priority cannot be
  settled from the artifacts. 134's 78 / 630 and 79 / 468, built at 21:48,
  dominate all of them.
- **One gadget, three packages.** 135, 136 and 139 all build height-one
  quartics with the equality energy a⁴ + b⁴ − a³b − ab³, and 136 and 139
  both replace 127's global C4-free rule by certified coefficients. 134 and
  135 both cap 131's parent with a syntax-label Pell pair; 135 and 136 both
  remove front sign guards by recovering orientation.
- **The R > 3q repair.** The research review of 133 found that its
  completeness needs the canonical bound R > 3q. 138 and 139 state that
  bound; 134 inherits "canonical outer data" without restating it; 137
  copies 133's proof with the generic R ≥ 3.
- **Unclaimed quartics.** 135's affine-refactored height-one sources,
  326 / 236 / 3,566 / 4,178 and 348 / 258 / 3,175 / 4,178, would be complete
  ℤ quartics by its own refactor theorem but are not claimed; they are not
  ranked here.
- **The research session moved in parallel and has reviewed this wave.** At
  arrival it had ten-positive 84 / 328, which dominates 133's 85 / 328; its
  code-free review of 134–139 (`884c9631ab`, 25 October 14:02) prioritizes
  134's 78 / 630 and 79 / 468 and 135's 282 / 287 / 309 family for full review
  and accepts none yet.
- **The undelivered archives.** 137 carries the five finished equations of
  `ConZFC_Prime_Power_375_553` and `ConZFC_Shell_Reciprocal_660` twice, inside
  its nested copy of 132. 134 and 135 carry the 660 packet's code and route
  their natural builders through it; 138 and 139 carry no file of either.

### Delivery discrepancies (wave 15)

- **Drivers fail in place** (full-manifest checks in all six). 137 requires
  exactly Python 3.12.14 and SymPy 1.14.0 and creates sibling directories;
  134, 135, 137, 138 and 139 have builders that rewrite delivered files
  (138's `integer286/build.py` overwrites its delivered companion by default;
  139's `build_report.sh` overwrites `report.pdf`).
- **Not shipped.** 135's integer315, integer321, the orientation checkpoints
  285, 286 and 290 and its matched 1,254 / 27,714 (hash only); 136's hub
  profiles. 138's ten-positive tuple has no executable recipe.
- **Comparisons.** 138 compares its ℕ quartics only with 133's 237, although
  129's 234 dominates both; its two centred ℤ equations carry the same
  `variant` string.
- **Titles.** README H1 differs: 134, 138 (case), 136 (no H1).
- **Licence and attribution.** No root licence or NOTICE: 137. No root
  NOTICE: 134. 139's graph component has no NOTICE. No AI statement of its
  own: 137 (only in copied notices).

### Further questions (wave 15)

1. Prove the unshifted-T versions of 134's circuits, measured at 77 / 630 and
   78 / 468.
2. Apply 134's deterministic centre and 136's trace orientation to 135's
   282 source.
3. Decide whether 135's refactored ℤ quartics count as endpoints.
4. Combine 139's carrier shears with 134's removal of the scale μ.

## Wave 14 (sources 127–133)

The seven archives of arrival `fd3e384e92` (24 October 2026, 21:17) were
placed as batch 230 in `1c5367452a`, in archive-name order. All seven pin
`f4d8db99e0` (24 October, 16:45), which holds the wave-13 archives in
`docs/incoming/` and this repository's `candidates/ten-positive-gap-fusion`
but not the wave-13 placement; their PDFs were built between 17:09 and
17:17, except 132's, whose date is forced to 17:00 (its QA receipt is dated
17:19). None cites a sibling. 37 placed paths exceed 250 characters.

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`127-graph-certificates/`](127-graph-certificates/) | `ConZFC_Graph_Certificates_2026-10-24.zip` | *Shared arithmetic certificates and graph energies for Diophantine consistency* (README: *… for Con(ZFC)*) | **coefficient-height-one quartics in 2,215 integers / 30,468 terms** (graph certificates, three profiles); direct quartics ℕ 240 / 188 / 25,987, 239 / 187 / 360,097, ℤ 381 / 225 / 13,179, 391 / 235 / 10,764; 11ℤ 412 / 127, 440 / 126 |
| [`128-one-row-pell/`](128-one-row-pell/) | `ConZFC_One_Row_Pell_Certificates_2026-10-24.zip` | *One quadratic constraint for many Pell certificates* | direct quartics **ℕ 242 / 190 / 9,308 / 18,049,118** and ℤ 378 / 230 / 9,421 / 3,054,220; a one-row Pell cap V = W + Σ((X_i − 1)² + (Y_i − e_i)²) + (A − 1)Q |
| [`129-semantic-pell-anchor/`](129-semantic-pell-anchor/) | `ConZFC_Semantic_Pell_Anchor_2026-10-24.zip` (wrapper `con_zfc_pooled_residues`) | *Semantic Anchors for Diophantine Consistency* | direct quartics **ℕ 233 / 182 / 50,762 / 88,674,690** and **234 / 183 / 9,019 / 87,741,134**; two degree-8 substitution recipes in 702 and 699 integers |
| [`130-shared-index/`](130-shared-index/) | `ConZFC_Shared_Index_2026-10-24.zip` | *Shared Pell bounds for modular certificates* (README H1 is its subtitle) | direct quartic ℕ 241 / 189 / 30,058 / 85,187,728 (and a dense 239); ℤ 964 lift; ten positive **121 / 246** and 86 / 466 (original tuple), with controls 87 / 466, 89 / 450, 90 / 450; bundles this repository's `ten-positive-gap-fusion` |
| [`131-shared-pell-caps-round16/`](131-shared-pell-caps-round16/) | `ConZFC_Shared_Pell_Caps_Round16_2026-10-25.zip` | *Shared Pell caps and coprime product equations for ZFC consistency* (round 16 of 106, 112 and 125's series) | direct quartics **ℤ 324 / 208 / 5,808 / 128,446** and **338 / 222 / 4,493 / 128,446**, ℕ 249 / 186 / 27,078 and 278 / 215 / 5,524, raw ℕ 412 / 349 / **2,852** and 387 / 324 / 6,020; 11ℤ 966 / 109, 882 / 110, **810 / 112, 654 / 117**; ten positive 87 / 436, 88 / 380 |
| [`132-signed-caps-free-scales/`](132-signed-caps-free-scales/) | `ConZFC_Signed_Caps_Free_Scales_2026-10-25.zip` (wrapper `ConZFC_Signed_Caps_Free_Scales`) | *Signed Pell caps and free scale carriers for Diophantine consistency* (README omits "for …"; round 16 of 116 and 121's series) | **11ℤ 924 / 109, 840 / 110**, 428 / 123, 376 / 127, 364 / 131, 352 / 132; **15ℤ 44 / 111**; ten positive **102 / 253, 104 / 252**; direct quartics ℤ 352 / 219 / 9,355 and 355 / 220 / 9,370 (height 15·10^6); bundles one whole copy of 121's archive and a second copy of its `alternative/inherited_proofs/` |
| [`133-staged-certificates/`](133-staged-certificates/) | `ConZFC_Staged_Certificates_2026-10-24.zip` | *Staged Pell certificates and a product-square equation for Con(ZFC)* | ten positive **84 / 436** and **85 / 328** (the research session's indexed tuple); direct quartics ℕ 239 / 187 / 20,015 / 84,062,635, 240 / 188 / 12,836 / 84,062,620, 255 / 203 / 5,743 / 64,214,623, 237 / 185 / 69,710, raw 343 / 291 / 4,593; a 717ℤ degree-8 companion |

### Identities and dominance (intake findings)

Two read-only dossiers recounted every count, measured every degree,
re-expanded every quartic, replayed the elimination certificates of 131–133
and rebuilt 127's height-one graphs; every claimed figure was confirmed.

- **Ten positive.** 133's 84 / 436 and 85 / 328 dominate 131's 87 / 436 and
  88 / 380 and 130's 86 / 466. Collapsing the two-root norm into one square
  was found twice (131 and 133) by different devices; their degree-436
  polynomials differ. 130's 86 / 466 is the research session's `zero86`
  circuit on another tuple; P_89/288 with Y replaced by q³s equals
  q¹²·P_87, and P_86 is P_87 with n replaced by n − s. 132's 102 / 253 and
  104 / 252 are 121's 94 / 262 polynomial with i replaced by 2i and n shifted
  by an explicit polynomial. 130's 121 / 246 has the lowest degree.
- **Eleven integers.** 132's 924 / 109 and 840 / 110 dominate 131's 966 / 109
  and 882 / 110, which dominate 123's; 132's 428 / 123 dominates 125's
  456 / 124, and 132's 376 / 127 dominates 127's and its own 412 / 127. 127's
  440 / 126, called a tradeoff by 127, is dominated by 125's 416 / 125.
- **Direct quartics.** All four of 127–130 combine 123's shared binomial with
  124's single Pell cap, each covering the modular indices differently, from
  four distinct raw sources; 127 and 128 independently extend the cap to
  signed pairs, and the signed pooled cap appears again in 131, 132 and the
  research session. 131's 324 and 338 are their projected polynomials with
  z_i shifted at 61 and 58 coordinates; 128's 378 likewise at 13.
- **Height one.** 127's three graph profiles beat 120's 7,431 / 34,086 in
  variables and terms at the same height 1; the dossier rebuilt every
  certificate.

### Tensions, not adjudicated at intake

- **The research session moved in parallel.** Its ℤ 327 / 216 / 5,718 /
  128,446 (`a6a4cb5a71`, 21:38; it dominates its earlier 329) is Pareto with
  131's 324 and 338 (fewer variables than 338, fewer terms than 324); 131's
  324 and 338 dominate its 359 and 364. 133's 84 / 436 dominates its 86 / 466,
  which 133 never saw.
- **The research review of wave 14** (`6834703279`, 21:51) authenticated all
  seven archives. It found that 133's 84 / 436 and 85 / 328 completeness
  needs the canonical bound R > 3q (the generic R ≥ 3 does not suffice;
  `reviews/staged-certificates-compact-ordinary-peer.md`), that 132's
  claimed full leading form of the free-scale first root is false although
  its degree 44 survives (`reviews/signed-free-scales-ordinary-peer.md`), and
  that 131's 324 cannot be composed with the compressed signed guards
  without a new proof. It then accepted 133's two circuits with that repair
  (`a223b3e174`, 22:03).
- **The undelivered archives keep spreading.** 127, 129, 130, 132 and 133
  carry finished equations of `ConZFC_Shell_Reciprocal_660` (132 all five of
  both archives, twice); 128 and 131 carry none. 127–131 and 133 route their
  direct builders through that packet's code (127–130 through 112's
  `build_hybrid.py`).
- **Bundles of bundles.** 132 carries one whole copy of 121's archive (which
  carries 116's) and a second copy of its inherited proofs; 130 bundles this
  repository's `ten-positive-gap-fusion` and
  credits it but not 119 or 121, which have the same polynomials.

### Delivery discrepancies (wave 14)

- **Drivers fail in place** (full-manifest checks). 132 requires exactly
  Python 3.12.14 and SymPy 1.14.0 and creates sibling directories; 131 and
  133 overwrite their PDFs from `build_report.sh`; 130's documented check
  commands rewrite delivered files.
- **Stale parents.** 131's positive JSONs name a parent file other than the
  one their hash and proof use; 132's record the hash of 121's sharp
  97 / 254 parent, while its proof uses the uncentred 94 / 262; 130's
  `center246` README and report name a 97 / 254 parent, but it ships the
  94 / 262 one.
- **Not shipped.** 128's 243 form, 131's 906 / 111 and other radix variants,
  133's 242 checkpoint and `build_combined.py`. 131's README names a
  directory that does not exist; 127's copied upstream notice names files
  not in 127.
- **Titles.** README H1 differs: 127, 129 (case), 130 (its subtitle), 132.
- **Licence and attribution.** No root licence for new material: 132. No
  root NOTICE: 129, 130, 132, 133. No AI statement of its own: 131 and 132
  (only in copied notices); only in the TeX author line: 130.

### Further questions (wave 14)

1. Compose 131's and 132's improvements of 123's 11ℤ circuits.
2. Combine 133's one-square collapse with 132's free scales on the
   ten-positive kernel.
3. Place or not the two undelivered archives, now carried by most packages.

### Frontier after wave 14, as placed

The combined frontier near the top of this README supersedes this table,
which is kept as the state after wave 14.

Numbers are the packages' own. At intake, read-only dossiers recounted
every operation count and measured the degrees of the headline circuits
(two each for waves 12 to 14, five for wave 11, four for each earlier wave); all checked
figures agree with the claims. The mathematics was not re-derived, and
every dominance statement assumes the competing proofs are correct. Only
packages of this collection are ranked here, each unknown count on its own
row. The active research session's own candidates and this
repository's `candidates/ten-positive-gap-fusion` (an independent
derivation of package points) are compared in its
[PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md).
At intake several research circuits dominate package rows: its
nine-positive 405 operations at degree 1,191,570 and 413 at 1,316,546
(`23d8510a10`; the 413 form on the 2^429959 tuple), 722 at 1,158,228 and
1,056 at 997,810 dominate every nine-positive package point. Its ℤ quartic
327 / 216 / 5,718 / 128,446 (`a6a4cb5a71`) is Pareto with 131's 324 and
338, and its fourteen-positive 73 / 342 to 76 / 191 (operations / degree)
use fewer operations than the packages' 79.

- "u / e / d / o" means unknowns / equations / degree / operations; pairs
  are degree / operations, except in the ten-positive rows and the wave-14
  section's ten-positive entries, which give operations / degree. For the
  direct quartics (degree 4 throughout) the measures are variables /
  residuals / expanded terms / coefficient
  height.
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
    takes 7 operations;
  - the wave-11 ten-integer and nine-positive forms use eleven or twelve
    derived leaves (radix and threshold powers, recipe outputs), all
    materialized and checked.
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
    product adds twelve;
  - in wave 11, 85's nine-positive forms add seven, 84's ten-positive form
    ten, and 110's ten.

  The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package. Within one wave, the
lower directory number counts as earlier.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Nine positive, fewest operations | **420** at degree 1,472,168 (ℕ: not shipped) | 101 | 101 |
| Nine positive, lowest degree | **997,810 / 1,057** | 101 | 101 |
| Nine positive, Pareto frontier | 1,472,168 / 420 (101); 1,376,378 / 456 (105); 1,158,228 / 726 (82); 997,810 / 1,057 (101). Dominated by these: 66's 444 and every earlier nine-positive form; 101's 428 and 85's 434 ≡ 86's 435 (one polynomial), 105's 442, 86's 449, 79's 1,753, 85's 1,074, 86's 1,086 | 82, 101, 105 | — |
| Nine positive on the 2^429959 tuple | **1,626,248 / 428** (101); 1,628,768 / 434 (85; 86 evaluates the same polynomial in 435); 1,520,186 / 442 (105). Earlier: 54's 490 | 85, 101, 105 | 85 |
| Ten positive, Pareto frontier | **84 / 436** and 85 / 328 (133); 89 / 288, 91 / 283, 92 / 278, 94 / 262, 96 / 258, 97 / 254 (119 on the BFS tuple, 121 on the original one; 119's 92 / 278 is 117's polynomial in one operation fewer, 121's the same circuit on the other tuple); 102 / 253 and 104 / 252 (132); **121 / 246** (130). Dominated: 130's 86 / 466, 87 / 466, 89 / 450 and 90 / 450, 131's 87 / 436 and 88 / 380, 113's, 116's, 117's and 118's forms, 115's 98 / 368 and 103 / 340, and every earlier form | 119, 121, 130, 132, 133 | 84 (first), 113 (fusion) |
| 10ℤ (Sun's reduction), Pareto frontier | **1,245,324 / 467**, 1,179,788 / 470, 1,114,252 / 473, **1,080,888 / 507** (106, re-evaluating 87's 471 form and the research session's three shears of it). Other polynomials: 76's 480 / 1,245,324, 83's 484 / 1,179,788, 487 / 1,114,252 and 521 / 1,081,125, 87's 485, 496 and 545 / 1,080,888, 91's re-evaluations. All dominate 68's 1,576,864 / 481 | 76, 83, 87, 106 | 76 (degree), 87 (operations) |
| 11ℤ, without Sun's reduction, Pareto frontier | **924 / 109** and 840 / 110 (132); 810 / 112 and 654 / 117 (131); 488 / 118 and 464 / 119 (125); 428 / 123 (132); 416 / 125 (125); 376 / 127, 364 / 131 and **352 / 132** (132). Dominated: 131's 966 / 109 and 882 / 110, 123's forms, 125's 456 / 124, 127's 440 / 126 and 412 / 127, 132's 412 / 127 and 396 / 128, 116's, 120's, 121's and 126's forms, 110's three | 125, 131, 132 | 110 |
| 12ℤ, Pareto frontier | **500 / 139** (121's evaluator of 116's polynomial); **1,084 / 123** (113). Dominated: 116's 500 / 148, 112's 768 / 141, 111's 1,040 / 140 and four further forms, 110's 1,000 / 180 and 1,024 / 179, 118's two, and every wave-11 form | 97, 111, 112, 113, 116, 121 | 97 |
| 13ℤ, Pareto frontier | **274 / 129** (116); 536 / 126 (118). Dominated: 105's 1,072 / 186, 1,392 / 177 and 1,408 / 176 and every earlier 13ℤ form | 116, 118 | 88 |
| 14ℤ | **108 / 119** (116). Dominated: 106's 378 / 145, 88's 792 / 137 and every earlier 14ℤ form | 116 | 88 |
| 15ℤ, Pareto frontier | **44 / 111** (132); **48 / 108** (121). Dominated: 116's 56 / 110, 106's 172 / 123 and every earlier 15ℤ form | 116, 121, 132 | 88 (first 15ℤ form, 344 / 131) |
| 16ℤ, Pareto frontier | **98 / 138** (106); 108 / 132 (91); **112 / 119** (93); 124 / 118 (98); **160 / 115** (92). Dominated: 92's 152 / 120, 132 / 128 and 120 / 123, 93's 112 / 120, 86's 184 / 135 and 192 / 134 | 86, 91, 92, 93, 98, 106 | 86 |
| 17ℤ | **88 / 110** (88). 82's and 86's 17ℤ / 88 forms are different polynomials (82 uncounted, 86 at 114); 84's 112 / 124 and 110 / 140 dominated | 82, 86, 88 | 82 |
| 18ℤ–20ℤ | 18ℤ **32 / 112** (88) and 88 / 105 (85; 82's 18ℤ / 32 uncounted, 84's 80 / 115 and 77's 88 / 109 dominated); 19ℤ **28 / 116** (88) and 32 / 108 (85, the pivot polynomial of 83 and 84; 82 uncounted; 89's 19ℤ / 40 and 77's 32 / 112 dominated); 20ℤ **18 / 115** (93) and 20 / 111 (85; the pivot polynomial of 83 and 84; 88's 24 / 120 and 77's 32 / 112 dominated) | 82, 83, 85, 88, 89, 93 | 82 (18ℤ, 19ℤ), 83 (20ℤ) |
| 21ℤ–24ℤ | 21ℤ / 16 (89, 9 residuals; 83 ≡ 84 ≡ 85 at 114 operations; 87, different); 22ℤ / 14 (79; 81 at 123) and 22ℤ / 16 / 118 (77); 23ℤ / 10 (83 ≡ 86 at 131) and 23ℤ / 12 (77 at 121; 79, 81, 82); 24ℤ / 10 (78; 81 at 135; 82). All beat 68's 26ℤ / 16 and 37's 24ℤ / 1,936 | 77, 78, 79, 81, 83, 86, 89 | 77 |
| Integer octic | **25ℤ** in 127 operations (77). Dominated: the 26ℤ octics of 76, 77, 78, 79, 81, 82 and 68's 28ℤ, 69's and 71's 27ℤ | 77 | 77 |
| Integer sextic | **30ℤ** (76). Dominated: the 31ℤ sextics of 77, 79, 81 (144 operations), 82, and the 32ℤ and 34ℤ sextics of waves 9–10 | 76 | 76 |
| Integer quartic | **37ℤ** (76 ≡ 82, two variants; 77's four variants differ in one guard row). Dominated: 69's and 71's 38ℤ | 76, 77, 82 | 76 |
| Direct C222 quartic, ℕ (no K215, Jones, Sun or coefficient tuple) | **233 / 182 / 50,762 / 88,674,690** and 234 / 183 / 9,019 / 87,741,134 (129); 239 / 187 / 20,015 / 84,062,635, 240 / 188 / 12,836 / 84,062,620 and 255 / 203 / 5,743 / 64,214,623 (133); 242 / 190 / 9,308 / 18,049,118 (128); 249 / 186 / 27,078 / 85,178,741 and 278 / 215 / 5,524 / 83,852,788 (131); 320 (123), 331ds / 255 / 15,769 / 15,246,025 and 332ss / 255 / 14,184 / 10,785,132 (125) and 333 / 264 / 4,357 (122) on height or terms; 4,860 / 4,476 / 14,719 / **1,837** (98, lowest height). Raw systems: 412 / 349 / **2,852** / 63,907,302 (131), 343 / 291 / 4,593 / 64,174,057 (133), 349 / 297 / 6,102 / 64,028,049 (130), 359 / 307 / 5,706 / 1,418,780 (128), 479 / 414 / 3,042 / 1,144,307 (123), 554 / 476 / 3,276 / 1,142,323 (112). Dominated: 131's raw 387 / 324 / 6,020 / 64,028,044 (by 128's raw 359), 127's and 129's raws (by 133's 343), 124's 261 and 292, 127's, 130's 241 and dense 239, 133's 237, 108's and 109's 395, 123's raw 465, 124's raw 435 and 406, and earlier forms | 98, 112, 122, 123, 125, 128, 129, 130, 131, 133 | 87 (earliest), 89 (this lineage) |
| Direct C222 quartic, ℤ | **324 / 208 / 5,808 / 128,446** and 338 / 222 / **4,493** / 128,446 (131, fewest terms); 3,776 / 2,015 / 20,194 / 47,959 (102); 3,564 / 3,350 / 14,518 / height 2 (114); 2,215 integers / 30,468 terms / **height 1** (127's principal profile, not a sum of squares; its two 519-based profiles, 2,776 / 30,554 and 2,988 / 31,218 at height 1, are dominated). Dominated: 125's 442, 132's 352 and 355, 128's 378, 127's 381 and 391, 130's 964, 120's height-one 7,431, and every earlier form | 102, 114, 127, 131 | 87 |
| Eleven positive | **211 / 107** (115's evaluator of the research session's polynomial, which 105 evaluates in 110). Dominated: 83's 211 / 112, 86's 213 / 112, 87's 211 / 113, 82's 269 / 111, the 277 / 111 polynomial of 76, 77, 78, 79, 81, 77's 257 / 114, and 70's 325 / 113 | 83, 105, 115 | 76 (277), 83 (211) |
| Twelve positive, Pareto frontier | **70 / 95** (115's evaluator of 98's free-J polynomial); 57's **258 / 89**. Dominated: 98's 70 / 98, 76's 78 / 101 ≡ 82's 78 / 102, 78's ≡ 81's 78 / 103, 87's 70 / 100, 69's 82 / 102, 74's forms | 98, 115; 57 | 80 (claim), 87 (first artifact), 98 |
| Thirteen positive, Pareto frontier | **28 / 98** (72); 30 / 92 (73; 74 evaluates the same polynomial in 93); **51 / 87** (115's evaluator of 98's polynomial); **114 / 83** (62). Dominated: 98's 51 / 88, 70's and 75's 30 / 94, 61's 34 / 93 | 72; 73; 98, 115; 62 | — |
| Fourteen positive, Pareto frontier | unchanged: **24 / 101** (72); 65's 26 / 92; 64's 30 / 83; 55's and 59's **52 / 79** | 72; 65; 64; 55 | — |
| Fifteen positive | unchanged: 66 ops (51's P66, degree 157); lowest degree 24 / 88 (66); Pareto frontier as after wave 9 | 51; 66 | — |
| Twelve positive, systems | unchanged: 59's three-equation system at 94 operations | 59 | 59 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125. From wave 2 (history only, see the wave-2 README `5b0c9ae9fd`): 15's positive-domain sextic in 25 and octic in 20 unknowns, which still dominate 75's 26- and 21-unknown versions | waves 2, 5, 6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^429959** (54) among tuple-bound equations; 85, 86, 101 and 105 bind nine-positive forms to it. The direct quartics bind no tuple at all: their coefficients are the small integers of the expanded polynomial (heights from 1 (127; earlier 120) and 2 (114) to about 9.9·10^27 (115)) | 54; 87–89 | 54 |

## Wave 13 (sources 119–126)

The eight archives of arrival `5f3379063d` (24 October 2026, 16:35) were
placed as batch 229 in `9f7ff01558`, in archive-name order. All eight pin
the wave-12 arrival `45b399ec51`; their PDFs were built between 15:52 and
16:12. None cites a sibling. 43 placed paths exceed 250 characters (maximum
383); all are licence and notice files kept by the always-keep rule, 33 in
125, 6 in 121 and 2 each in 122 and 123, mostly inside nested `intake/`
bundles. The research session accepted 125's 442 quartic (`12a6f5a037`)
and reviewed the eight bundles (`a71b5bc67a`) before this reconciliation.

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`119-cofinal-witnesses/`](119-cofinal-witnesses/) | `ConZFC_Cofinal_Witnesses_2026-10-24.zip` | *Reusing witnesses in Diophantine consistency equations* | direct quartic ℤ 508 / 308 / 6,545 / 996,521 (and a 512 checkpoint, a specialization of 112's 517); the six fused ten-positive profiles 89 / 288, 91 / 283, 92 / 278, 94 / 262, 96 / 258, 97 / 254 (BFS tuple) |
| [`120-height-one-degree464/`](120-height-one-degree464/) | `ConZFC_Height_One_and_Degree_464_2026-10-24.zip` | *Coefficient height one and an eleven-integer degree-464 equation for Con(ZFC)* | a degree-4 polynomial in **7,431 integers with every coefficient ±1** (34,086 terms; twice it is a sum of squares, built from 112's 519); 11ℤ 464 / 122 and 488 / 121 |
| [`121-paired-guards-centered/`](121-paired-guards-centered/) | `ConZFC_Paired_Guards_Centered_Carriers_2026-10-24.zip` (wrapper `ConZFC_Paired_Guards_Centered_Carriers`) | *Paired sign conditions and centered Pell carriers for Diophantine consistency* (README: *Paired guards and centered carriers for Con(ZFC)*) | direct quartic ℤ 489 / 308 / 6,905 / 11,302,118; the six fused ten-positive profiles on the original tuple; **15ℤ 48 / 108**; 12ℤ 500 / 139 and four 11ℤ forms (116's polynomials, cheaper); 11ℤ 820 / 119, 964 / 118; bundles 116's whole archive |
| [`122-residue-compiler/`](122-residue-compiler/) | `ConZFC_Residue_Compiler_2026-10-24.zip` (wrapper `con_zfc_residue_compiler_2026-10-24`) | *One modulus for all binomial digits* | direct quartics ℕ 332 / 263 / 11,823 / 85,243,454 and 333 / 264 / 4,357 / 209,508,384; raw ℕ systems 475 / 406 / 3,089 and 487 / 418 / 3,106 |
| [`123-shared-binomial/`](123-shared-binomial/) | `ConZFC_Shared_Binomial_Certificates_2026-10-24.zip` | *Shared Binomial Certificates and Short Carriers* (title page; README and PDF metadata word it differently) | **11ℤ 966 / 111, 882 / 112**, and 488 / 121, 464 / 125, 440 / 126; direct quartics ℕ 319 and 320 (height 15.2·10^6); raw ℕ systems 465 / 400 / 2,977 and 479 / 414 / 3,042 |
| [`124-shared-pell-bound261/`](124-shared-pell-bound261/) | `ConZFC_Shared_Pell_Bound_261_2026-10-24.zip` | *One Pell bound and one error congruence* | direct quartics **ℕ 261 / 194 / 31,679 / 85,566,955** and **292 / 225 / 6,140 / 83,933,334**; raw ℕ systems 435 / 368 / 2,980 and 406 / 339 / 6,690; a 783ℤ degree-8 substitution recipe; bundles 112's whole archive |
| [`125-unified-binomial-round15/`](125-unified-binomial-round15/) | `ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.zip` | *Diophantine consistency equations with unified binomials and even Pell indices* (round 15 of 106 and 112's series) | direct quartic **ℤ 442 / 290 / 4,652 / 128,446** (and its uncentred 442 / 290 / 4,872 / 414,308); ℕ 329, 331, 332; **11ℤ 488 / 118, 464 / 119, 456 / 124, 416 / 125** |
| [`126-weak-carriers-shared-signs/`](126-weak-carriers-shared-signs/) | `ConZFC_Weak_Carriers_and_Shared_Signs_2026-10-24.zip` | *Weak divisibility and shared sign certificates for Diophantine consistency* | direct quartic ℤ 478 / 305 / 5,484 / 511,326; 11ℤ 488 / 120, 464 / 123, 456 / 126, 416 / 129 |

### Identities and dominance (intake findings)

Two read-only dossiers recounted every operation count, measured every
degree and re-expanded every quartic; every claimed figure was confirmed.

- **Ten positive.** 119 and 121 ship the same six profiles, found
  independently, dominating every ten-positive package point of waves 11
  and 12. 119's six are identical to research-session polynomials
  (`zero89`, reused-b `saturated_upper` and `saturated_sharp`, and its
  direct-carrier circuits); 92 / 278 is 117's polynomial in one operation
  fewer, and neither 119 nor 121 credits 117. Four of 121's (89, 92, 94, 97)
  are identical to this repository's later `candidates/ten-positive-gap-fusion`.
  Wave-12 dossier F had predicted all six as counts and degrees; 119 and 121
  supply the proofs.
- **Eleven integers.** The degrees 488, 464, 456 and 416 recur in 120, 123,
  125 and 126 as pairwise different polynomials (their differences have full
  degree). 125's and 126's share every register through the carrier and
  differ in 125's guard weight 81 and paired norm. 120's 464 form is its
  488 form with n replaced by n + QV.
- **Direct quartics.** 125's 442 is its uncentred form with z_i replaced by
  z_i + d_i at 47 coordinates; 126's 478 is its uncentred form with z
  replaced by z − 1 at 13 coordinates; 119's 508 likewise at 13. 123 and
  125 independently use one binomial C(F² + t, t) as both the factorial
  binomial and the CRT modulus product. 119 and 121 independently reuse the
  existing F² wire to fix signs before F is interpreted.
- **Height one.** 120's polynomial has every coefficient +1 or −1 and
  constant term 1; the dossier rebuilt 2P from the certificate and
  checked that each of the 321 source rows pulls back. It beats 114's
  height 2 on height only (2.1 times the variables, 2.3 times the terms).

### Tensions, not adjudicated at intake

- **The undelivered archives keep spreading.** All eight packages carry
  parts of `ConZFC_Prime_Power_375_553` and `ConZFC_Shell_Reciprocal_660`
  through 112's `intake/` folder; 121's and 122's copies include all five
  of their finished equations (ℤ 553 and 660, ℕ 375, 363 and 364) and 123's
  the 660 packet's three, 124 bundles 112's whole
  archive, and all four direct builders of 123–126 run the 660 packet's
  engine code, which exists here only through those copies.
- **Priority.** On the ten-positive points, 117 (12:53) is first on the
  92 / 278 circuit. 119 (built 16:12) has the research session's `zero89`
  polynomial before that commit (16:29) and its reused-b 91 / 283 and
  92 / 278 before `fc77fcd31a` (16:14); 121 (15:58) has four of this
  repository's `ten-positive-gap-fusion` polynomials (16:00 to 16:45) and the
  zero89 circuit on the original tuple. No dossier tested whether these were
  independent.
- **Uncredited reuse.** 126 does not credit 118 for the pair-product guard
  lemma, although its snapshot hashes 118.

### Delivery discrepancies (wave 13)

- **Drivers fail in place** (every root driver checks a full manifest).
  121 and 125 need SymPy; 121 creates a `<dir>_replay` directory next to its
  package before failing; most packages ship builders or component scripts
  that write in place. 125's reproduction commands name the wrong directory.
- **Titles.** 121 and 125 differ between README and printed title; 122's
  and 124's PDF metadata titles differ; 123 has three wordings.
- **Licence and attribution.** No root licence for new material: 121, 123.
  No root NOTICE: 121, 124. No AI-assistance statement: 121; none explicit in 125.
- **Inside packages.** 119 lists four 508 variants it does not ship and
  names its old modulus V² + 3F² − 1 where the 512 file uses V² + 3F − 1.
  125 describes a 446 companion and a `projection_frontier/` sweep that are
  absent. 122's proofs name output paths that ship under other names. 123's
  two review files are identical, and 123 and 125 share a byte-identical
  file without citing each other.

### Further questions (wave 13)

1. Place or not the two undelivered archives; four wave-13 packages now
   depend on their code.
2. Stack 125's unified binomial with 119's and 121's F² sign reuse and 124's
   single Pell bound on one source.
3. Carry the height-one compilation to the 442-variable quartic.

### Frontier after wave 13, as placed

The combined frontier near the top of this README supersedes this table,
which is kept as the state after wave 13.

Numbers are the packages' own. At intake, read-only dossiers recounted
every operation count and measured the degrees of the headline circuits
(two each for waves 12 and 13, five for wave 11, four for each earlier wave); all checked
figures agree with the claims. The mathematics was not re-derived, and
every dominance statement assumes the competing proofs are correct. Only
packages of this collection are ranked here, each unknown count on its own
row. The active research session's own candidates (at intake none dominates
a package row; its ten-positive 86 / 466 is a further Pareto point) and this
repository's `candidates/ten-positive-gap-fusion` (an independent
derivation of package points) are compared in its
[PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md).

- "u / e / d / o" means unknowns / equations / degree / operations; pairs
  are degree / operations. For the direct quartics (degree 4 throughout)
  the measures are variables / residuals / expanded terms / coefficient
  height.
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
    takes 7 operations;
  - the wave-11 ten-integer and nine-positive forms use eleven or twelve
    derived leaves (radix and threshold powers, recipe outputs), all
    materialized and checked.
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
    product adds twelve;
  - in wave 11, 85's nine-positive forms add seven, 84's ten-positive form
    ten, and 110's ten.

  The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package. Within one wave, the
lower directory number counts as earlier.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Nine positive, fewest operations | **420** at degree 1,472,168 (ℕ: not shipped) | 101 | 101 |
| Nine positive, lowest degree | **997,810 / 1,057** | 101 | 101 |
| Nine positive, Pareto frontier | 1,472,168 / 420 (101); 1,376,378 / 456 (105); 1,158,228 / 726 (82); 997,810 / 1,057 (101). Dominated by these: 66's 444 and every earlier nine-positive form; 101's 428 and 85's 434 ≡ 86's 435 (one polynomial), 105's 442, 86's 449, 79's 1,753, 85's 1,074, 86's 1,086 | 82, 101, 105 | — |
| Nine positive on the 2^429959 tuple | **1,626,248 / 428** (101); 1,628,768 / 434 (85; 86 evaluates the same polynomial in 435); 1,520,186 / 442 (105). Earlier: 54's 490 | 85, 101, 105 | 85 |
| Ten positive, Pareto frontier | **89 / 288**, 91 / 283, 92 / 278, 94 / 262, 96 / 258, **97 / 254** (119 on the BFS tuple, 121 on the original one; 119's 92 / 278 is 117's polynomial in one operation fewer, 121's the same circuit on the other tuple). Dominated: 113's 92 / 283, 93 / 278, 98 / 258 and 99 / 254 and its four four-root centred variants, 116's 96 / 266, 117's 93 / 278, 118's 96 / 360 and 102 / 332 and its stage graphs, 115's 98 / 368 and 103 / 340, and every earlier form | 113, 116, 117, 119, 121 | 84 (first), 113 (fusion) |
| 10ℤ (Sun's reduction), Pareto frontier | **1,245,324 / 467**, 1,179,788 / 470, 1,114,252 / 473, **1,080,888 / 507** (106, re-evaluating 87's 471 form and the research session's three shears of it). Other polynomials: 76's 480 / 1,245,324, 83's 484 / 1,179,788, 487 / 1,114,252 and 521 / 1,081,125, 87's 485, 496 and 545 / 1,080,888, 91's re-evaluations. All dominate 68's 1,576,864 / 481 | 76, 83, 87, 106 | 76 (degree), 87 (operations) |
| 11ℤ, without Sun's reduction, Pareto frontier | **966 / 111** and 882 / 112 (123); 488 / 118, 464 / 119, 456 / 124 and **416 / 125** (125). Dominated: 116's 688 / 126, 728 / 122, 1,632 / 114 and 1,892 / 114 (also as 121's cheaper evaluators), 121's 820 / 119, 964 / 118, 796 / 122 and 772 / 124, 120's 464 / 122 and 488 / 121, 123's three norm forms, 126's four forms, 110's three | 110, 116, 120, 121, 123, 125, 126 | 110 |
| 12ℤ, Pareto frontier | **500 / 139** (121's evaluator of 116's polynomial); **1,084 / 123** (113). Dominated: 116's 500 / 148, 112's 768 / 141, 111's 1,040 / 140 and four further forms, 110's 1,000 / 180 and 1,024 / 179, 118's two, and every wave-11 form | 97, 111, 112, 113, 116, 121 | 97 |
| 13ℤ, Pareto frontier | **274 / 129** (116); 536 / 126 (118). Dominated: 105's 1,072 / 186, 1,392 / 177 and 1,408 / 176 and every earlier 13ℤ form | 116, 118 | 88 |
| 14ℤ | **108 / 119** (116). Dominated: 106's 378 / 145, 88's 792 / 137 and every earlier 14ℤ form | 116 | 88 |
| 15ℤ | **48 / 108** (121). Dominated: 116's 56 / 110, 106's 172 / 123 and every earlier 15ℤ form | 116, 121 | 88 (first 15ℤ form, 344 / 131) |
| 16ℤ, Pareto frontier | **98 / 138** (106); 108 / 132 (91); **112 / 119** (93); 124 / 118 (98); **160 / 115** (92). Dominated: 92's 152 / 120, 132 / 128 and 120 / 123, 93's 112 / 120, 86's 184 / 135 and 192 / 134 | 86, 91, 92, 93, 98, 106 | 86 |
| 17ℤ | **88 / 110** (88). 82's and 86's 17ℤ / 88 forms are different polynomials (82 uncounted, 86 at 114); 84's 112 / 124 and 110 / 140 dominated | 82, 86, 88 | 82 |
| 18ℤ–20ℤ | 18ℤ **32 / 112** (88) and 88 / 105 (85; 82's 18ℤ / 32 uncounted, 84's 80 / 115 and 77's 88 / 109 dominated); 19ℤ **28 / 116** (88) and 32 / 108 (85, the pivot polynomial of 83 and 84; 82 uncounted; 89's 19ℤ / 40 and 77's 32 / 112 dominated); 20ℤ **18 / 115** (93) and 20 / 111 (85; the pivot polynomial of 83 and 84; 88's 24 / 120 and 77's 32 / 112 dominated) | 82, 83, 85, 88, 89, 93 | 82 (18ℤ, 19ℤ), 83 (20ℤ) |
| 21ℤ–24ℤ | 21ℤ / 16 (89, 9 residuals; 83 ≡ 84 ≡ 85 at 114 operations; 87, different); 22ℤ / 14 (79; 81 at 123) and 22ℤ / 16 / 118 (77); 23ℤ / 10 (83 ≡ 86 at 131) and 23ℤ / 12 (77 at 121; 79, 81, 82); 24ℤ / 10 (78; 81 at 135; 82). All beat 68's 26ℤ / 16 and 37's 24ℤ / 1,936 | 77, 78, 79, 81, 83, 86, 89 | 77 |
| Integer octic | **25ℤ** in 127 operations (77). Dominated: the 26ℤ octics of 76, 77, 78, 79, 81, 82 and 68's 28ℤ, 69's and 71's 27ℤ | 77 | 77 |
| Integer sextic | **30ℤ** (76). Dominated: the 31ℤ sextics of 77, 79, 81 (144 operations), 82, and the 32ℤ and 34ℤ sextics of waves 9–10 | 76 | 76 |
| Integer quartic | **37ℤ** (76 ≡ 82, two variants; 77's four variants differ in one guard row). Dominated: 69's and 71's 38ℤ | 76, 77, 82 | 76 |
| Direct C222 quartic, ℕ (no K215, Jones, Sun or coefficient tuple) | **261 / 194 / 31,679 / 85,566,955** and 292 / 225 / 6,140 / 83,933,334 (124); 333 / 264 / 4,357 / 209,508,384 (122); 320 (123), 331ds / 255 / 15,769 / 15,246,025 and 332ss (125), heights near 10^7; 395 (108, 109) on height; 4,860 / 4,476 / 14,719 / **1,837** (98, lowest height). Raw (uncontracted) systems: 465 / 400 / **2,977** / 63,907,653 and 479 / 414 / 3,042 / 1,144,307 (123), 435 / 368 / 2,980 / 63,975,558 and 406 / 339 / 6,690 / 64,170,614 (124), 554 / 476 / 3,276 / 1,142,323 (112). Dominated: 112's 349 and 350, 115's 358 and 361, 122's 332 and its raw 475 and 487, 123's 319, 125's 329, 330sq, 331sc and 333sqss, 108's raw 655, 100's 407 and earlier forms | 98, 108, 109, 112, 122, 123, 124, 125 | 87 (earliest), 89 (this lineage) |
| Direct C222 quartic, ℤ | **442 / 290 / 4,652 / 128,446** (125, also fewest terms); 3,776 / 2,015 / 20,194 / 47,959 (102); 3,564 / 3,350 / 14,518 / height 2 (114); 7,431 integers / 34,086 terms / **height 1** (120, not a sum of squares; twice it is). Dominated: 126's 478, 121's 489, 119's 508, 112's 517 and 519, 111's, 114's 577 to 591, 117's, 118's and every earlier form | 102, 114, 120, 125 | 87 |
| Eleven positive | **211 / 107** (115's evaluator of the research session's polynomial, which 105 evaluates in 110). Dominated: 83's 211 / 112, 86's 213 / 112, 87's 211 / 113, 82's 269 / 111, the 277 / 111 polynomial of 76, 77, 78, 79, 81, 77's 257 / 114, and 70's 325 / 113 | 83, 105, 115 | 76 (277), 83 (211) |
| Twelve positive, Pareto frontier | **70 / 95** (115's evaluator of 98's free-J polynomial); 57's **258 / 89**. Dominated: 98's 70 / 98, 76's 78 / 101 ≡ 82's 78 / 102, 78's ≡ 81's 78 / 103, 87's 70 / 100, 69's 82 / 102, 74's forms | 98, 115; 57 | 80 (claim), 87 (first artifact), 98 |
| Thirteen positive, Pareto frontier | **28 / 98** (72); 30 / 92 (73; 74 evaluates the same polynomial in 93); **51 / 87** (115's evaluator of 98's polynomial); **114 / 83** (62). Dominated: 98's 51 / 88, 70's and 75's 30 / 94, 61's 34 / 93 | 72; 73; 98, 115; 62 | — |
| Fourteen positive, Pareto frontier | unchanged: **24 / 101** (72); 65's 26 / 92; 64's 30 / 83; 55's and 59's **52 / 79** | 72; 65; 64; 55 | — |
| Fifteen positive | unchanged: 66 ops (51's P66, degree 157); lowest degree 24 / 88 (66); Pareto frontier as after wave 9 | 51; 66 | — |
| Twelve positive, systems | unchanged: 59's three-equation system at 94 operations | 59 | 59 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125. From wave 2 (history only, see the wave-2 README `5b0c9ae9fd`): 15's positive-domain sextic in 25 and octic in 20 unknowns, which still dominate 75's 26- and 21-unknown versions | waves 2, 5, 6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^429959** (54) among tuple-bound equations; 85, 86, 101 and 105 bind nine-positive forms to it. The direct quartics bind no tuple at all: their coefficients are the small integers of the expanded polynomial (heights from 1 (120) and 2 (114) to about 9.9·10^27 (115)) | 54; 87–89 | 54 |

## Wave 12 (sources 111–118)

The eight archives of arrival `45b399ec51` (24 October 2026, 15:28, "Con(ZFC)
in Diophantine form") were placed as batch 228 in `55fe52f28c`, in
archive-name order. All eight pin `84e16e4309` (24 October, 12:17); 116
also pins `56b4d15d12`. None cites a sibling. The research session triaged
them statically at
[research/intake-45b399ec51/TRIAGE.md](../research/intake-45b399ec51/TRIAGE.md)
and has since accepted 112's 517 and 519 integer quartics
(`72f5374bc0`) and adopted 113's universal 92 / 283 circuit, on a third
tuple, as its canonical page (`adb42f031d`).

Notation as in the wave-11 section: "u / d / o" is unknowns / exact degree /
operations, ℤ unrestricted integers, ℕ naturals, otherwise strictly
positive; direct quartics give variables / residuals / expanded terms /
coefficient height.

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`111-carriers-even-indices/`](111-carriers-even-indices/) | `ConZFC_Carriers_and_Even_Indices_2026-10-24.zip` | *Weaker congruences and even Pell indices* (title block; no `\title`) | direct quartics ℤ 566 / 372 / 6,431 / 2.45·10^12, **597 / 403 / 4,767 / 938,267** (fewest terms), 590 / 396 / 4,776 / 964,219, 589 / 371 / 8,157 and two unlisted 601 and 608 variants; an even-index Pell compiler; **12ℤ 1,040 / 140**, 768 / 161, 784 / 154, 800 / 147, 816 / 144 (34's tuple) |
| [`112-powered-saturation-round14/`](112-powered-saturation-round14/) | `ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip` | *Diophantine consistency equations with powered saturation and factorial carriers* (round 14 of 106's series) | direct quartics **ℤ 517 / 310 / 6,774 / 3,904,267** and **519 / 321 / 6,253 / 411,060**, ℕ **349 / 268 / 12,768 / 86,915,503** and 350 / 268 / 11,472 / 86,523,090, raw ℕ systems 537–554; **12ℤ 768 / 141**; bundled partial copies of two archives never delivered (see below) |
| [`113-saturated-pell/`](113-saturated-pell/) | `ConZFC_Saturated_Pell_2026-10-24.zip` (wrapper `con_zfc_saturated_pell_2026-10-24`) | *Saturating a Pell witness to remove a radical* (README: *Saturated Pell consistency equations*) | **10 / 283 / 92**, 10 / 278 / 93, 10 / 258 / 98, 10 / 254 / 99 (BFS tuple); four retained four-root centred variants; **12ℤ 1,084 / 123** and controls |
| [`114-signed-powers-height-two/`](114-signed-powers-height-two/) | `ConZFC_Signed_Powers_Height_Two_2026-10-24.zip` | *Signed power recovery and small-coefficient quartics for the consistency of ZFC* (README and PDF metadata word it differently) | direct quartics ℤ 577 / 363 / 7,326 / 2.45·10^12, 582 / 368 / 6,069 / 964,213, 591 / 377 / 5,835 / 964,213, 586; **ℤ 3,564 / 3,350 / 14,518 / height 2** |
| [`115-synchronized-exponents/`](115-synchronized-exponents/) | `ConZFC_Synchronized_Exponents_2026-10-24.zip` | *Synchronized exponent certificates for ZFC consistency* | direct quartics ℕ 358 / 275 / 8,229 / 9.9·10^27, 361 / 278 / 6,759; a 1,074ℤ degree-8 composition; cheaper evaluators of existing polynomials: **11 / 211 / 107**, **12 / 70 / 95**, **13 / 51 / 87**, 10 / 368 / 98, 10 / 340 / 103 |
| [`116-coprime-projection/`](116-coprime-projection/) | `ZFC_Diophantine_Coprime_Projection_2026-10-24.zip` (wrapper `ZFC_Diophantine_Coprime_Projection`) | *Coprime Pell products and rational projection for Diophantine consistency* (README: *Coprime fusion and low-degree Diophantine projections*) | **10 / 266 / 96** (original tuple); **11ℤ 688 / 126, 728 / 122, 1,632 / 114**; **15ℤ 56 / 110**, **14ℤ 108 / 119**, **13ℤ 274 / 129**, **12ℤ 500 / 148**; an uncalibrated nine-auxiliary power graph (`alternative/`) |
| [`117-quadratic-frames/`](117-quadratic-frames/) | `con-zfc-quadratic-frames-2026-10-24.zip` (wrapper `con-zfc-quadratic-frames`) | *Two reductions for Diophantine consistency* | 10 / 278 / 93 (BFS tuple; a different polynomial from 113's 93 / 278) and its 30ℤ companion 556 / 163; direct quartics ℤ 576 / 368 / 7,172 / 2.45·10^12, 582 / 374 / 6,200 / 964,213 |
| [`118-structural-compression/`](118-structural-compression/) | `con-zfc-structural-compression-2026-10-24.zip` | *Removing Redundancy from Diophantine Consistency Equations* | 10 / 360 / 96 and 10 / 332 / 102 (with stages 98 / 368, 104 / 340); 13ℤ 536 / 126; 12ℤ 1,200 / 138, 1,456 / 137; direct quartics ℤ 589, 595, 600 |

Each directory's `README.md` is its entry point.

### One device, three packages

113's "saturated Pell", 116's "coprime first/strong fusion" and 117's
"saturation" are one construction, found independently from the same pin:
put the first Pell radicand D into the strong one, F_s = 1 + Δ·D·(i·c²)²,
so that F_s ≡ 1 (mod D); require D·F_s to be a square, which by
coprimality makes both squares; exclude a zero root sum because the two
radicands differ modulo D. The three-radical octic norm becomes a quartic
in two radicals. 113 and 117 add a centre above τ·f (113 at (A+1)·D·E or
A·D·E, 117 at A·D·E); 116 uses the larger majorant H·D·E + b instead. 117
already takes the existing register b as its transport weight. 118's
devices (equal-weight radicals, and an auxiliary-index gap that makes b a
valid majorant without a centre) act on the unfused kernel; equal weights
are subsumed by fusion.

### Identities and dominance (intake findings)

**How the dossiers checked.** Two read-only dossiers recounted every
operation count and measured every degree with their own evaluators and
the actual payloads, re-expanded every direct quartic, and tested identity
both with each circuit's own tuple and with shared random ports. Every
claimed figure was confirmed.

- **Ten positive.** All of 113's, 116's, 117's and 118's circuits are
  distinct polynomials. 113's and 117's 93 / 278 differ: P_113sharp is
  P_117 with n replaced by n + (c(T+α) − R − k(T+α))·B_t. 117's polynomial
  can be evaluated in 92 operations by the expanded-transport identity,
  and 113's two direct forms in 97 and 98 by 116's direct schedule (intake
  findings: exact rewrites, no new proof needed).
- **Eleven to thirteen positive.** 115's 107 / 211, 95 / 70 and 87 / 51 are
  cheaper evaluators of the research session's 211 / 111 polynomial (also
  105's 110 / 211), of 98's free-J 70 / 98 and of 98's 51 / 88 polynomial.
  Its 98 / 368 and 103 / 340 evaluate the research session's 99 / 368 and
  105 / 340.
- **Twelve integers.** 111's and 112's 768-degree forms start from the same
  research parent by different mechanisms and are different polynomials.
- **Direct quartics.** 111's 589 / 371 / 8,157 and 118's 589 / 371 / 8,156
  have the same variable-kind profile and are different polynomials (their
  constant terms differ by one). 111, 114, 117 and 118 all start from the
  research session's 75-predicate source; 112 and 115 from 100's engine.
- **Height two.** 114's anchored quartic has coefficients only −2, 1 and 2
  and constant term 1; the dossier re-checked its zero-set transfer for
  all 1,243 source rows. It costs about 6.9 times the variables of 112's 519.

### Tensions, not adjudicated at intake

- **Two packages never delivered, bundled inside 112.** Under `intake/`, 112
  carries partial copies of `ConZFC_Prime_Power_375_553_2026-10-23` and
  `ConZFC_Shell_Reciprocal_660_2026-10-24`, which reach this repository only
  as these partial copies (and wave-13 copies of them). Their finished
  quartics (ℕ 375, 364 / 292 / 6,613 / 7,002,666 and
  **363 / 291 / 6,674 / 83,842,716**, ℤ 553 and 660) re-expand exactly. The
  ℕ 363 and 364 would dominate 108's and 109's naturals. They are recorded here as
  part of 112's directory, not as packages of their own; whether to treat
  them as sources is Vladimir's decision.
- **Baselines moved during the wave.** None of the eight could have seen the
  research page of 14:48 (98 / 360). After intake the research session
  published 113's 92 / 283 as its page and the reused-b profiles 91 / 283,
  92 / 278, 97 / 258 and 98 / 254 (`fc77fcd31a`); see also this repository's
  `candidates/ten-positive-gap-fusion` (above the frontier table).
- **Restricted claims.** 116's nine-auxiliary power graph has no calibrated
  tiling source (the raw 943-tile list contains an all-zero tile), as 116
  says. 112's three architecture proofs are written out in full; the
  research review approved the 517 / 519 branch but did not replay the raw
  generators, the 349 / 350 naturals or the 12ℤ norm.

### Delivery discrepancies (wave 12)

- **Drivers fail in place.** Every root driver checks a manifest or reads
  omitted inputs first; rerun from the arrival archive. 111, 115, 117 and
  118 write receipts in place, 113's and 116's builders rewrite outputs
  without `--check`, and 112, 116 need SymPy.
- **Titles.** PDF metadata title empty: 116. README H1 differs from the
  printed title: 113, 114 (three wordings), 116. No `\title`: 111.
- **Licence and attribution.** No root licence for new material: 111, 113,
  114, 116, 118. No root NOTICE: 111, 113, 114, 115, 116, 118. AI statement only in a
  PDF author field: 111; only in a component file: 116.
- **Inside packages.** 112 describes naturals 360, 361 and two of 351, two
  horizon-32 endpoints and an 800 / 141 companion that it does not ship.
  111's two mixed-modulus graphs carry the name of a different file. 111
  ships two 589-variant quartics absent from its README. 113's headline
  JSONs omit their syntactic degree.
- **Bundled copies.** 111 and 114 bundle 100's whole arrival archive; 115
  bundles 100's tree; 112 bundles partial copies of two undelivered archives (above).

### Further questions (wave 12)

1. Place or not the two archives bundled in 112's `intake/`.
2. Combine 112's 519 / 517 architecture with 111's even-index compiler and
   114's quotient frames on one source.
3. Carry 116's integer projections (11ℤ to 15ℤ) over to the fused positive
   kernel's centred forms.

## Wave 11 (sources 76–110)

Thirty-six archives arrived in seventeen commits between 23 October 2026,
18:35, and 24 October, 12:14 (`c1a102936a` to `e13c748234`), all titled
"Con(ZFC) in Diophantine form". They were placed as one batch (227) in
arrival order. The packages call themselves rounds 11, 12 and 13 of their
own series; several were written within minutes of one another and none
cites a sibling that arrived after its pin. Thirty-five directories hold
them: `ZFC_Diophantine_Centered_Compression_2026-10-24_Dependency.zip`
(`922185752d`) is a byte copy of 77's archive inside a wrapper and has no
directory, and `report.zip` is a single TeX file (80). The research
session reviewed most of these arrivals as they came
([PROPOSAL_REVIEW_WAVE11.md](../PROPOSAL_REVIEW_WAVE11.md),
[PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md) and the
`PROPOSAL_REVIEW_*.md` files dated 23–24 October); 94, 105–110 and parts
of 86, 87, 101 had no review there at placement.

Unless marked, unknowns are strictly positive; "u / d / o" is unknowns /
exact degree / operations; ℤ is unrestricted integers and ℕ naturals. For
the direct quartics (degree 4, no coefficient tuple) the figures are
variables / residuals / expanded terms / coefficient height.

| Dir | Archive | Title as printed | Constructions |
|---|---|---|---|
| [`76-structural-round11/`](76-structural-round11/) | `ConZFC_Structural_Reductions_Round11_2026-10-24.zip` | *Structural reductions for Diophantine consistency equations* | **10ℤ 1,245,324 / 480** (31's tuple; also 1,248,364 / 481); 11 / 277 / 111; **12 / 78 / 101**; **37ℤ quartic**, **30ℤ sextic**, 26ℤ octic, 25ℤ / 10, 24ℤ / 12, 23ℤ / 16 (34's tuple); uncompiled height-register source (`commutative/`) |
| [`77-joint-guards/`](77-joint-guards/) | `ZFC_Diophantine_Joint_Guards_2026-10-24.zip` | *Joint sign guards and Pell descent for smaller consistency equations* | **25ℤ octic in 127 operations**; 23ℤ / 12 / 121, 22ℤ / 16 / 118, 21ℤ / 20 / 115, 20ℤ / 32 / 112, 19ℤ / 88 / 109; 37ℤ quartics and 31ℤ sextics in cone and determinant variants; 11 / 277 / 111 and **11 / 257 / 114**; bundles all eight wave-10 archives; `certificates/` gadgets for the direct route |
| [`78-budget-centering/`](78-budget-centering/) | `con-zfc-budget-and-centering-2026-10-23.zip` | *Smaller Diophantine Forms for Con(ZFC): two Pell-root translations, joint positivity, and coefficient-bounded proof certificates* (README: *Pell translations and coefficient budgets for Con(ZFC)*) | 26ℤ / 8, **24ℤ / 10**, 23ℤ / 16 (no counts); 11 / 277 / 111; 12 / 78 / 103; local two-accumulator Horn certificate (`direct/`, not materialized) |
| [`79-radical-guard-descent/`](79-radical-guard-descent/) | `con-zfc-radical-guard-descent-2026-10-23.zip` (wrapper `con-zfc-cross-guard-descent-2026-10-23`) | *Radical majorants, guard compression, and Pell descent for Diophantine consistency equations* | **9 / 1,158,228 / 1,753** (31's tuple); 11 / 277 / 111; 31ℤ / 6, 26ℤ / 8, 23ℤ / 12, **22ℤ / 14** (no counts); single-loop local source (`alternative/`) |
| [`80-twelve-manuscript/`](80-twelve-manuscript/) | `report.zip` | *Diophantine consistency without redundant denominator guards* (cover page; no `\title`) | one TeX file; claims 11 / 277 / 111, **12 / 70 / 100**, a 31ℤ sextic and 9 / 1,158,240 / 811; ships no artifact (see below) |
| [`81-centered-pell-norms/`](81-centered-pell-norms/) | `con-zfc-centered-pell-norms.zip` | *Centered Pell norms and shared positivity: a degree-fourteen consistency equation in twenty-two integers* | **22ℤ / 14 / 123**, 23ℤ / 12 / 122, 24ℤ / 10 / 135, 26ℤ / 8 / 131, 31ℤ / 6 / 144, 25ℤ / 12 / 128; 11 / 277 / 111; 12 / 78 / 103 |
| [`82-pell-congruences/`](82-pell-congruences/) | `con_zfc_pell_congruences_2026-10-23.zip` | *Pell Congruences, Shared Positivity, and Smaller Diophantine Consistency Equations* (README: *Pell congruences and smaller Diophantine consistency equations*) | **9 / 1,158,228 / 726**; **11 / 269 / 111**; 12 / 78 / 102; **20ℤ / 20, 19ℤ / 28, 18ℤ / 32, 17ℤ / 88** (no counts); 37ℤ quartic, 31ℤ sextic, 26ℤ octic, 24ℤ / 10, 23ℤ / 12, 22ℤ / 16 |
| [`83-polynomial-shears/`](83-polynomial-shears/) | `ConZFC_Polynomial_Shears_2026-10-23.zip` | *Polynomial shears and sign recovery for Diophantine consistency* | 10ℤ 1,179,788 / 484, 1,114,252 / 487, 1,081,125 / 521; **11 / 211 / 112**; 23ℤ / 10, 21ℤ / 16, 20ℤ / 20, 19ℤ / 32, 18ℤ / 88 (no counts) |
| [`84-radical-residue/`](84-radical-residue/) | `con-zfc-radical-residue-2026-10-23.zip` | *Ten-variable Diophantine consistency: four square roots, small rational residues, and a seventeen-integer companion* (title page; no `\title`; README: *… by small rational residues*) | **10 / 1,152 / 131** (ℕ 141), the first ten-positive package equation; 17ℤ / 112 / 124, 17ℤ / 110 / 140, 18ℤ / 80 / 115; pivots 21ℤ–18ℤ (83's polynomials) |
| [`85-saturation-projection/`](85-saturation-projection/) | `con-zfc-saturation-and-projection-2026-10-23.zip` | *Smaller Diophantine consistency equations: Pell saturation, exact transport elimination, and coprime proof-flow certificates* | **9 / 1,628,768 / 434** (ℕ 441) and 9 / 1,103,950 / 1,074 on the 2^429959 tuple; 18ℤ / 88 / 105, 19ℤ / 32 / 108, 20ℤ / 20 / 111, 21ℤ / 16 / 114; coprime Horn-flow theorem (`alternative/`, not compiled) |
| [`86-saturated-certificates/`](86-saturated-certificates/) | `ConZFC_Saturated_Certificates_2026-10-24.zip` | *Saturated Pell certificates and quotient recovery: eight explicit Diophantine equations for syntactic consistency of ZFC* (README: *… for Con(ZFC)*) | 9 / 1,628,768 / 435 (85's polynomial), **9 / 1,474,688 / 449**, **9 / 999,518 / 1,086** (31's tuple); 11 / 213 / 112; 23ℤ / 10 / 131 (83's polynomial), **17ℤ / 88 / 114**, 16ℤ / 192 / 134, 16ℤ / 184 / 135 |
| [`87-direct-centered-round12/`](87-direct-centered-round12/) | `ConZFC_Direct_Centered_Round12_2026-10-24.zip` | *Direct and centered Diophantine consistency equations* | **direct C222 quartic, 27,916ℤ / 758,275 terms** (and a 16,036ℕ residual system), the earliest finished direct equation; **10ℤ 1,245,324 / 471**, 1,179,788 / 485, 1,114,252 / 496, **1,080,888 / 545**; 11 / 211 / 113; 12 / 70 / 100 (80's claim, materialized); 21ℤ / 16 and 20ℤ–18ℤ forms |
| [`88-root-fusion13/`](88-root-fusion13/) | `ConZFC_13_Integer_Norms_2026-10-24.zip` (wrapper `con-zfc-root-fusion-2026-10-24`) | *Thirteen Integer Variables through a Single Five-Radical Norm* | **13ℤ 1,088 / 195**, 1,392 / 186, 1,408 / 185; **14ℤ 696 / 150, 792 / 137**; 15ℤ 344 / 131; quotient companions 20ℤ / 24 / 120, 19ℤ / 28 / 116, 18ℤ / 32 / 112, **17ℤ / 88 / 110** (34's tuple) |
| [`89-shared-certificates/`](89-shared-certificates/) | `ConZFC_Shared_Certificates_2026-10-24.zip` | *Direct proof certificates and smaller Diophantine consistency equations* (README: *Direct certificates and coordinated Diophantine reductions*) | **direct quartic ℕ 3,614 / 2,954 / 15,996 / 127,778,545**, the first of the affine-step lineage, and 6,183ℕ at height 1,993; **21ℤ / 16** (9 residuals), 20ℤ / 18, **19ℤ / 40** (six-payload tuple) |
| [`90-fixed-prime-radicals/`](90-fixed-prime-radicals/) | `ConZFC_FixedPrime_Radicals_2026-10-23.zip` (wrapper `con-zfc-padic-compression`) | *Thirteen integer variables for Diophantine ZFC consistency* | 13ℤ 1,392 / 475, 1,408 / 473; **14ℤ 652 / 230, 664 / 223**, 700 / 217, 748 / 215; 15ℤ 214 / 139; bundles 82's archive |
| [`91-prime-separation13/`](91-prime-separation13/) | `ConZFC_Prime_Separation_13_Integer_2026-10-23.zip` | *Prime separation for Diophantine ZFC consistency* | 13ℤ 1,392 / 205; 14ℤ 696 / 151; 15ℤ 244 / 137; **16ℤ 108 / 132**; 10ℤ re-evaluations of 83's forms (477, 481, 484, 518) |
| [`92-parity-norms/`](92-parity-norms/) | `con-zfc-parity-norms-2026-10-23.zip` | *Parity norms for a smaller Diophantine consistency equation* (README: *… smaller ZFC consistency equation*) | 13ℤ 1,392 / 211, 1,888 / 205; 14ℤ 862 / 150, 1,696 / 147; **15ℤ 204 / 128, 352 / 124**; **16ℤ 160 / 115**, 152 / 120, 132 / 128, 120 / 123; bundles 82 |
| [`93-parity-pell-witnesses/`](93-parity-pell-witnesses/) | `con-zfc-parity-norms-2026-10-23 (2).zip` (wrapper `con-zfc-parity-norms`; a different package from 92) | *Parity and Pell Witnesses: smaller explicit Diophantine equations for syntactic consistency and a reduced direct proof-calculus quartic* (README: *Parity and Pell witnesses for syntactic Con(ZFC)*) | **16ℤ / 112 / 119** (and 112 / 120); 15ℤ 306 / 139, 310 / 136; **20ℤ / 18 / 115**; direct quartic 26,188ℤ / 724,768 terms (14,956ℕ) |
| [`94-direct-projection7617/`](94-direct-projection7617/) | `ConZFC_Direct_Projection_7617.zip` | *Projection before Diophantine encoding: a smaller direct quartic for Con(ZFC)* (README: *An eight-column direct C222 consistency polynomial*) | direct quartic **7,617ℤ / 4,379 / 148,220 / 8.97·10^21**; the source projection inherited by 103 |
| [`95-synchronized-certificates/`](95-synchronized-certificates/) | `ConZFC_Synchronized_Certificates_2026-10-24.zip` | *Synchronized arithmetic certificates for ZFC refutability* | direct quartics **ℕ 522 / 400 / 20,225 / 83,900,628**, 529, 596 / 474 / 7,263 / 63,909,160, 895 / 773 / 4,863 / 63,908,265; ℤ 2,088 |
| [`96-batched-certificates/`](96-batched-certificates/) | `con_zfc_batched_certificates_2026-10-23.zip` (wrapper `con-zfc-batched-certificates`) | *Shared arithmetic certificates for Diophantine consistency equations* | direct quartics ℕ 667, 680, 1,153, 1,968, 2,108; ℤ 1,690 (and 1,702); **13ℤ 1,072 / 195** (88's polynomial reanchored, 1,088 → 1,072); bundles 88 and 89 |
| [`97-twelve-interpolation/`](97-twelve-interpolation/) | `ConZFC_Twelve_Integer_Interpolation_2026-10-24.zip` (wrapper `con_zfc_trace_and_interpolation`) | *Twelve Integer Variables through Interpolated Pell Certificates* | **12ℤ 4,832 / 248**, 16,000 / 223, the first twelve-integer forms; **13ℤ 1,072 / 190**; bundles 88 |
| [`98-congruence-certificates/`](98-congruence-certificates/) | `ConZFC_Congruence_Certificates_2026-10-24.zip` | *Congruence, Radical Norms, and Direct Proof Certificates for Diophantine ZFC Consistency* (README: *… for Con(ZFC)*) | **12 / 70 / 98**, **13 / 51 / 88** (free-J forms); 13ℤ 1,072 / 195, **14ℤ 414 / 148**, 558 / 149, 15ℤ 218 / 130, **16ℤ 124 / 118**; direct quartics ℕ 2,473 and 4,860 (height 1,837) |
| [`99-shared-pell608/`](99-shared-pell608/) | `ConZFC_Shared_Pell_608_2026-10-23.zip` | *Shared Arithmetic Witnesses for Direct ZFC-Consistency Quartics* | direct quartics ℕ 608 / 491 / 7,582 / 79,824,571 and **ℤ 1,685 / 850 / 12,082 / 79,827,802**; a self-bounding factorial radius |
| [`100-quartics407-888/`](100-quartics407-888/) | `ConZFC_407_888_Quartics_2026-10-24.zip` | *Residue certificates and nonnegative gates for the consistency of ZFC* (README: *Explicit quartics for Con(ZFC)*) | direct quartics **ℕ 407 / 323 / 8,420 / 83,843,774**, 410; **ℤ 888 / 470 / 10,156 / 2.45·10^12**, 917 / 499 / 6,986 / 63,906,036 |
| [`101-constructive-reductions/`](101-constructive-reductions/) | `ConZFC_Constructive_Reductions_2026-10-23.zip` | *Smaller Diophantine Equations for ZFC Consistency: four-root separation, normalized radix positions, and direct certificates with recovered domains* | **9 / 1,472,168 / 420** and **9 / 997,810 / 1,057** (31's tuple), 9 / 1,626,248 / 428 (2^429959 tuple); **14ℤ 568 / 147**, 540 / 160; direct quartics ℕ 495 and ℤ 977 |
| [`102-direct-quartics3776/`](102-direct-quartics3776/) | `ConZFC_Direct_Quartics_3776_3671_2026-10-23.zip` (wrapper `conzfc_signed_quartic`) | *Smaller direct quartic equations for ZFC consistency: signed witnesses, sign normalization, and polynomial elimination* | direct quartics **ℤ 3,776 / 2,015 / 20,194 / 47,959**, 3,671, **7,058 at height 1,992**; parents are research-session candidates |
| [`103-shared-pell1873/`](103-shared-pell1873/) | `ConZFC_Shared_Pell_1873.zip` (wrapper `con_zfc_batched_pell`) | *A shared Pell certificate for Con(ZFC)* (README: *An explicit quartic for Con(ZFC), with shared Pell certificates*) | direct quartics ℤ 1,873 / 1,468 / 77,523 / 1.32·10^18 and **3,292 / 2,887 / 11,218 / 14,869,246**; a signed Pell-index theorem |
| [`104-valuation-signed/`](104-valuation-signed/) | `ConZFC_Valuation_and_Signed_Certificates_2026-10-23.zip` | *Valuation separation and signed certificates: explicit Diophantine forms of Con(ZFC)* | **12ℤ 2,400 / 215**, 2,912 / 209; direct quartic **ℤ 1,190 / 600 / 26,411 / 83,900,628**; 12 / 70 / 98 (the 100-operation polynomial re-evaluated); bundles 88, 95, 97 |
| [`105-bootstrap-certificates/`](105-bootstrap-certificates/) | `ConZFC_Bootstrap_Certificates_2026-10-24.zip` | *Factorial fixed points and smaller Diophantine consistency equations* | **9 / 1,376,378 / 456** (31's tuple), 9 / 1,520,186 / 442 (2^429959); **11 / 211 / 110** (the research session's polynomial, nine operations saved on 88's 13ℤ forms too); direct quartics ℕ 467, 468, 469 and ℤ 956 / 510 / 10,988 / 2.45·10^12, 989 / 543 / 7,705 / 63,910,295 |
| [`106-compact-certificates-round13/`](106-compact-certificates-round13/) | `ConZFC_Compact_Proof_Certificates_Round13_2026-10-24.zip` | *Compact proof certificates for ZFC consistency* (round 13; no `\title`) | **10ℤ 1,245,324 / 467, 1,179,788 / 470, 1,114,252 / 473, 1,080,888 / 507** (31's tuple; re-evaluations of 87's and the research session's polynomials); 12ℤ 2,048 / 233; 13ℤ 1,072 / 192; **14ℤ 378 / 145**; **15ℤ 172 / 123**, 170 / 134; **16ℤ 98 / 138**; direct quartics ℕ 1,859, 2,560 and ℤ 3,179 |
| [`107-dyadic-pell/`](107-dyadic-pell/) | `ConZFC_Dyadic_Pell_Reductions_2026-10-23.zip` | *Dyadic descaling and delayed Pell sign recovery* | **10 / 706 / 133** (descends from this repository's `ten-positive-scaled-norm`); direct quartic ℤ 780 / 434 / 9,628 / 2.45·10^12; bundles 100 |
| [`108-pell-residues/`](108-pell-residues/) | `ConZFC_Pell_Residues_2026-10-23.zip` | *Pell residues instead of power values* (README.txt: *Pell residues instead of power values: explicit Diophantine consistency equations for ProveIt*) | direct quartics **ℕ 395 / 321 / 7,323 / 83,842,758**, **394 / 320 / 39,208 / 84,233,382**, **ℤ 663 / 397 / 7,268 / 2.45·10^12**, 687 / 421 / 5,602 / 63,906,013; 12ℤ 2,400 / 210, 2,368 / 216 (104's forms with n replaced by n + QV, n + V); bundles 100 and 104 |
| [`109-valuations-centered/`](109-valuations-centered/) | `ConZFC_Valuations_and_Centered_Certificates.zip` | *Fixed Valuations and Centered Certificates: smaller explicit Diophantine equations for Con(ZFC)* | **12ℤ 2,304 / 216**, 2,336 / 215, 2,848 / 209; **10 / 718 / 126** (descends from `ten-positive-scaled-norm`, bundled as `positive10/provenance/parent816/`); direct quartics ℕ 395 / 313 / 8,292 / 83,843,425, 398, ℤ 853; bundles 97 and 100 |
| [`110-budget-interpolation/`](110-budget-interpolation/) | `ZFC_Diophantine_Budget_Interpolation_2026-10-24.zip` | *Budget constraints and radical compression for Diophantine consistency* (README: *Centered-budget Diophantine reductions: portable research release*) | **11ℤ 2,240 / 206**, 2,272 / 204, 2,912 / 200, the first eleven-integer forms; **12ℤ 1,000 / 180, 1,024 / 179**; 15ℤ 176 / 125; 10 / 912 / 126 (ℕ 136); bundles 88 and 92; tiling-certificate interfaces (`alternative/`, uncompiled) |

Directory numbers follow arrival order, and archive-name order within one
commit. Wrapper directories whose names differ from the archive stem are
listed in `PLACEMENT.md`; the furthest from it are 79's
`con-zfc-cross-guard-descent-2026-10-23`, 88's `con-zfc-root-fusion-2026-10-24`,
90's `con-zfc-padic-compression`, 93's `con-zfc-parity-norms`, 96's
`con-zfc-batched-certificates`, 97's `con_zfc_trace_and_interpolation`,
102's `conzfc_signed_quartic` and 103's `con_zfc_batched_pell`. 108's entry
point is `README.txt`. Each other directory's `README.md` is its entry
point.

### Coefficient tuples

Four fixed tuples occur, never mixed within one construction:
- the compact44 four-port tuple, B = 2^590069 (positive forms of 76–79,
  81–84, 86, 87, 98, 104, 105, 107, 109, 110);
- the six-payload source-34 tuple, B = 2^1064921 with two cone scales
  (every unrestricted-integer form with 11–37 unknowns, in 76–79, 81–93,
  96–98, 101, 104–106, 108–110);
- the original 31 tuple, B = 2^1064921 with its own masks (nine-positive
  and ten-integer forms of 76, 79, 82, 83, 86, 87, 91, 101, 105, 106);
- the compact54 tuple, B = 2^429959 (nine-positive forms of 85, 86, 101,
  105).

The direct quartics bind no tuple: their coefficients are the small
integers of the expanded polynomials. Every payload shipped in the batch
decompresses to the repository's values; the dossiers checked them all.

### Encodings beyond K215 and Jones

Wave 10 said of 68's `direct/` constructor that "its final polynomial is
neither produced nor counted". Wave 11 finishes it, twice over. Sixteen
packages (87's `direct/fixed_base`, 89, 93, 94, 95, 96, 98, 99, 100, 101,
102, 103, 104, 105, 106, 107, 108 and 109) ship finished quartics that
encode the repository's numerical proof calculus **C222** directly: a zero of the polynomial is a finite C222
derivation of the contradiction code, which is a finite ZF refutation by the
Lean theorem `KEndpoint.c222_iff_zf_refutation`
(`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean`), hence a
finite ZFC refutation by `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
Powers, binomials, factorials, remainders and bounded quantifiers are
expanded into quadratic rows through the repository's Pell and power
representation modules (`PellRepresentation.criterion_iff_pell` and its
siblings under `Computability/DiophantineConsistency/Lean/`), so every
direct equation is a sum of squares of quadratic residuals: a **quartic with
literal coefficients and no coefficient tuple**. None of them simulates
K215, instantiates Jones's equation, uses Sun's reduction or runs the
native-window/Pell compiler. The Lean side is inherited (the two refutation
interfaces and the representation modules, copied inertly into the
packages); the step "polynomial zero iff C222 derivation" is an ordinary
proof in each package, checked by finite replays, not a Lean theorem. None
of the packages uses `DirectQuarticZFC.noNaturalZero_iff_conZFC`; they
compile C222 themselves.

Two lineages, both rooted in 68:

- **Affine shared step.** 68's `direct/affine_shared_step.json` (its
  23-witness local step) is compiled by 89 into the first finished equation
  of this line, 3,614 naturals with 55 separate Pell frames. 95, 96 and 99
  then share the Pell frames in three different ways within six minutes of
  one another (95: one global frame for 27 power requests and one common
  binomial radix; 96: a common radix, a common offset for signed quotients
  and a pooled frame including the outputs; 99: one frame excluding the
  outputs, with a self-bounding factorial radius), reaching 522, 667 and
  608 naturals. 102 works on the research session's prime-lift descendant
  of 89 with signed witnesses and sign normalization, for low height.
- **Horn fixed base.** 68's `direct/horn_shared_source.json` is compiled
  by 87's `direct/fixed_base` (27,916 integers), projected by 94 to eight
  columns (7,617 integers) and batched by 103 onto one bootstrap Pell base
  with a signed-index theorem (1,873 integers).

For these quartics the cost axes are variables, residuals, expanded terms
and coefficient height at fixed degree 4; operation counts are not
meaningful. The dossiers re-expanded every shipped residual list and
recovered every published expansion, term count and height exactly. The
table below covers the two lineages at the time of their own arrivals
(87, 89, 94, 95, 96, 99, 102, 103); the later packages 98, 100, 101 and
104–109 reach fewer variables, and the combined frontier near the top of
this README ranks all of them.

| Domain | Fewest variables in these eight | Pareto points among them (variables / residuals / terms / height) |
|---|---|---|
| ℕ | **522 / 400 / 20,225 / 83,900,628** (95) | 529 / 407 / 10,782 / 211,184,624 and 596 / 474 / 7,263 / 63,909,160 (95); 895 / 773 / 4,863 / 63,908,265 (95, fewest terms); 6,183 / 5,523 / 17,430 / 1,993 (89, lowest height) |
| ℤ | **1,685 / 850 / 12,082 / 79,827,802** (99) | 3,292 / 2,887 / 11,218 / 14,869,246 (103, fewest terms); 3,776 / 2,015 / 20,194 / 47,959 (102); 7,058 / 5,297 / 24,277 / 1,992 (102, lowest height) |

95's 596-variable form dominates 89 (3,614), 96 (667, 680, 1,153, 1,968,
2,108) and 99 (608) in variables, terms and height at once; 99's 1,685
dominates 96's 1,690, 103's 1,873, 95's 2,088, 102's 3,671 and 94's 7,617
in all three. The batching that saves the most variables (96, 103) raises
the height by many orders of magnitude; 95 and 99 save variables without
that. 103 inherits 94's source projection byte for byte. Later wave-11
packages push this route further: 100 (407 naturals, 888 integers), 105
(467 naturals, 956 integers), 107 (780 integers), 108 (394 and 395
naturals, 663 integers) and 109 (395 naturals). The research session's own
candidates (naturals 399, integers 610 and below) are not packages and are
listed in its own comparison, not here.

Bundled copies: 68's two local-step files recur byte for byte in 76, 83, 87,
89, 93, 94, 95, 96, 98, 102 and 103; 96's `direct/upstream/` is 89's whole `direct/`, and
its `guard13/upstream/` is 88's complete archive.

Other pieces outside the common route, none a finished equation: 76's
height-register source and three uncompiled Lean constructors
(`commutative/`); 77's natural-domain checker gadgets and an index-free
inert-prime CRT closure (`certificates/`); 78's two-accumulator Horn
certificate with a linear budget (`direct/`, "not materialized"); 79's
single-loop affine certificate source (`alternative/`); 81's CRT compiler
lemma (`exploratory/`); 83's local selector polynomials (`alternative/`);
85's coprime Fermat-label Horn-flow theorem (`alternative/`, "not an
ordinary fixed-dimensional polynomial"); 110's tiling-certificate
interfaces with uncompiled power and binomial graphs (`alternative/`).

Within the common route, Jones's reduction enters only through the
nine-positive forms (79, 82, 85, 86, 101, 105, via 66's and 71's sources),
and Sun's only through the ten-integer forms (76, 83, 87, 91, 106). Every
form with 11 to 37 unrestricted integers, and every ten-, eleven-,
twelve- and thirteen-positive form, uses neither.

### Identities and dominance (intake findings)

**How the dossiers checked.** Five read-only dossiers evaluated every
literal circuit with their own code, modulo 2^127 − 1 with the actual
fixed values (the two 1.16-million-degree forms modulo 2^31 − 1), measured
degrees exactly along random lines (the smaller ones by finite
differences, the larger by top-coefficient tracking or Lagrange
agreement), recounted every live operation, and re-expanded every direct
quartic from its residual list. All 160-odd measured figures agree with
the packages' claims; no claimed count or degree was found wrong.

- **One eleven-positive polynomial, five times.** 76, 77, 78, 79 and 81
  ship the same 11 / 277 / 111 polynomial (77 and 79 byte-identical, 78 and
  81 byte-identical, 76 differently scheduled); 87 bundles it as an
  interface copy. Base: 76. 82's 269 / 111, 77's 257 / 114, 83's 211 / 112,
  86's 213 / 112, 87's 211 / 113 and the research session's 211 / 111
  (re-evaluated by 105 in 110 operations) are six further, pairwise
  different polynomials; none is a coordinate shift of another.
- **Twelve positive.** 76's 78 / 101 and 82's 78 / 102 are one polynomial;
  78's and 81's 78 / 103 are another. 80's claimed 70 / 100 polynomial is
  materialized by 87 (100 operations), bundled by 98 and 104 (104 in 98
  operations); 98's 70 / 98 free-J polynomial is the research session's
  96 / 70 candidate (identical); the 100-operation polynomial is 98's
  free-J polynomial with J restricted to 6j+1 — a restriction, not a shift.
- **Nine positive.** 85's 434 and 86's 435 evaluate one polynomial (also the
  research session's 433 evaluator and 105's bundled parent). 79's 1,753
  and 82's 726 are different polynomials of the same degree 1,158,228. 86's
  449 and 105's parent are one polynomial. 101's 420, 428 and 1,057, 105's
  442 and 456, 86's 1,086 and 85's 1,074 are all distinct.
- **Ten integers.** 76's 480 and 481, 68's 481, 83's 484 / 487 / 521 (76's
  polynomial with the last coordinate sheared by a polynomial), 87's 471
  (a different short-guard polynomial) and 485 / 496 / 545 (its shears) are
  ten pairwise different polynomials on one tuple and twelve shared fixed
  leaves. 91's 477 / 481 / 484 / 518 re-evaluate 83's and 76's polynomials;
  106's 467 / 470 / 473 / 507 re-evaluate 87's polar form and the research
  session's three shears of it.
- **Integer forms with 12 to 37 unknowns.** Only four identities hold
  across packages: 76's 37ℤ quartics ≡ 82's (two variants each); 83's
  21ℤ–18ℤ pivots ≡ 84's ≡ 85's transports (85 ships the only counted
  evaluators); 83's 23ℤ / 10 ≡ 86's (86 counts it, 131); 105's four 13ℤ
  circuits ≡ 88's polynomials (nine operations cheaper each). Everything else of
  equal size is a different polynomial: 77's four 37ℤ quartics differ from
  76's in one guard row; the three 13ℤ / 1,392 forms of 88, 90 and 91 and
  the three 17ℤ / 88 forms of 82, 86 and 88 have identical per-variable
  degree profiles and are not related by renaming, shift or sign; 108's
  12ℤ forms are 104's with n replaced by n + QV and n + V.
- **Independent rediscoveries.** Three fixed-prime (3-adic) separations
  (90, 91, 104) and two parity separations (92, 93) were found
  independently; none cites the others. 95, 96 and 99 share a Pell frame
  across power graphs in three different ways within six minutes. The
  wave-10 further questions (68's guard lemma on a 27ℤ octic; 70's
  orientation with 69's or 71's guard) are realized by 76, 77 and 82; 76
  acknowledges this.
- **Dominance at intake.** Among packages, 101's 420 / 1,472,168 and
  1,057 / 997,810 and 105's 456 / 1,376,378 are the new nine-positive
  frontier; 105's 11 / 211 / 110 dominates every other eleven-positive
  form; 98's 70 / 98 dominates every wave-10 twelve-positive polynomial;
  110's 12ℤ 1,000 / 180 and 1,024 / 179 dominate every other twelve-integer
  form; 106's
  15ℤ 172 / 123 and 16ℤ 98 / 138, 93's 16ℤ 112 / 119 and 92's 16ℤ 160 / 115
  are new Pareto points; 108's 394- and 395-variable and 663-variable
  direct quartics are the smallest direct equations in the batch. The
  combined frontier near the top of this README gives the rest.

### Tensions, not adjudicated at intake

- **Baselines moved during the wave.** The research session's own
  candidates (built on the same arrivals, and on this repository's
  `ten-positive-scaled-norm`) often dominate a package the day it arrives:
  its 99 / 368 ten-positive equation dominates 84's 1,152 / 131, 107's
  706 / 133, 109's 718 / 126 and 110's 912 / 126; its 13ℤ 536 / 135, 14ℤ
  312 / 117 and 12ℤ 1,200 / 145 dominate most 13–14ℤ package forms. Those
  candidates are not packages and are listed in
  [PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md), not here.
  Several packages compare themselves against research-session evaluators
  (433, 475, 111) rather than package points (85's 434, 71's 478, 76's 111).
- **Same polynomial, claimed improvement.** 86 presents 435 / 1,628,768 as
  improving a 440-operation research evaluator; the polynomial is 85's,
  evaluated one operation worse. 91's and 106's ten-integer "improvements"
  are re-evaluations of 83's, 76's, 87's and the research session's
  polynomials.
- **80's report.** Its abstract promises "a self-contained ZIP containing
  literal polynomial graphs"; the ZIP holds one TeX file that does not
  compile (`\input`s absent). Its printed eleven-positive formula is not the
  delivered 277 / 111 polynomial (different weight L and gate split); its
  twelve-positive 70 / 100 claim is materialized elsewhere (87, 98, 104,
  research); its 9 / 1,158,240 / 811 claim has no artifact anywhere in the
  batch (82 ships the missing section revised to 726 / 1,158,228). 84 and
  87 record the missing artifacts.
- **Four-root limits.** 77's `pell/FOUR_ROOT_LIMITS.md` shows a four-radical
  rationality extension fails as stated; 78's four-radical appendix labels
  itself an ingredient with the carrier problem open; 84 and this
  repository's `ten-positive-scaled-norm` prove the four-root extraction
  with the stronger subset-sum hypothesis.
- **Restricted optimality.** 83 and 106 state their shear forms are
  "optimal" within polynomial translations of the final coordinate; 87
  bypasses that family by changing the guard (545 / 1,080,888 against 83's
  521 / 1,081,125).
- **A counterexample to a 76 lemma without its guard.** 76 reports that its
  Lucas saturation theorem is false without |C| > 1 (A = 72, B = 31,
  C = −1) and discharges the guard first.
- **No package calls this README wrong.** 88, 92 and 110 carry copies of it
  at their pins.

### Delivery discrepancies (wave 11)

- **Drivers fail in place.** Every root driver authenticates a manifest or
  pinned-upstream hashes first. The placement omits members byte-identical
  to repository files, so all 35 drivers stop in the placed tree; rerun
  from the arrival archives, as `PLACEMENT.md` explains. (The first
  placement had also omitted members matched only by research-session
  files, among them 95's headline residual lists and 103's signed-index
  theorem; `c16a89ad94` restored those 1,119 members, 1,108 of them staged
  files.) 77's and 82's
  manifests are git-ignored (`SHA256SUMS*`). Writers in place: 78, 79, 81,
  84, 85, 86, 88, 89 (`direct/audit_calculus.py`), 90, 91 (receipt), 92,
  93, 96 (`guard13/build_reanchored.py` regenerates its equation), 103,
  104 (`direct/build.py`), 108 (`render_residuals.py`), 109 (root
  verifier's default receipt path).
- **Dependencies.** SymPy: 76 (builders), 77 (required; refuses `-O`), 78
  (audit), 79 (optional), 83, 87, 98, 106 (Python ≥ 3.12), 110 (also three
  parallel jobs by default). All others are standard library. 82's positive
  driver drops `-O` for its children (research review).
- **Titles.** PDF metadata title empty: 79, 92, 93, 95. README H1 differs
  from the TeX title: 78 (three wordings), 82, 84, 86, 89, 92, 93, 94, 98,
  100, 103, 104, 108, 110. No `\title`: 80, 84, 85, 106.
- **Licence and attribution.** No root licence for new material: 77, 106,
  109, 110. No root NOTICE: 77, 79, 85, 88, 96, 101, 102, 106, 107, 109,
  110. No AI-assistance
  statement anywhere: 97, 102, 106, 110; statement only in the TeX author
  line: 77, 78, 101; only in copied notices: 88. 104's README is dated
  23 October while its sources are dated 24 October; 94's and 103's PDFs
  are dated 23 October and their READMEs 24 October (UTC).
- **Inside packages.** 76's three `Height*CommutativeEquation.lean`
  constructors define objects and prove nothing. 85's README says the
  natural translation shifts one coordinate; the circuit shifts all nine.
  88's `check_integrated.py` references unshipped inputs. 96 ships a
  1,702ℤ form absent from its table. 98 ships a 14ℤ 558 / 149 graph its
  `FAMILY.md` excludes. 106's replay authenticates 397 of 398 manifest
  entries. 107's `dyadic10/README.md` names a file with a stray space.
  110 cites "wave-12" points (16ℤ / 106 / 123, 17ℤ / 48 / 110) that exist
  nowhere; only residual files for 17ℤ–19ℤ forms are bundled. 93's
  "incoming 22ℤ parent" of degree 14 is its own centring of 77's degree-16
  form.
- **Bundled copies.** 77 bundles all eight wave-10 archives; 90 bundles
  82's archive; 110 bundles 88's and 92's; 107 and 108 bundle 100's; 109
  bundles 97's and 100's whole tree and this repository's
  `ten-positive-scaled-norm`; 96 bundles 88's whole archive and 89's
  `direct/`; 97 and 104 bundle 88; 92 bundles 82; 91 bundles 82's
  `inherited/` and 83's `norm10/`; 93 bundles 86's integer component, 77's
  joint files and 87's fixed-base files; 88 and 92 carry this README at
  their pins. All are omitted from the tree and mapped in `PLACEMENT.md`.
- **Retained intermediates.** 76's 481-operation Lucas form; 77's 26ℤ octic
  and 24ℤ / 12 checkpoints; 81's 25ℤ / 12; 82's ten integer intermediates;
  86's two 16ℤ forms; 90's six self-declared controls; 102's three
  intermediates; 104's 1,224 checkpoint and 2,912 companion; 109's
  monotone31 checkpoints.

### Further questions (wave 11)

1. **Direct route.** Combine 108's Pell residues, 99's self-bounding
   factorial and 103's signed indices in one compiler; the research
   session has begun this. Bound the height together with the variable
   count: the batching that saves the most variables (96, 103) raises the
   height by orders of magnitude.
2. **Combinations (intake observations, untested as proofs).** 106's 3-adic
   15ℤ / 172 with 93's parity 16ℤ / 112 for a cheaper 15ℤ form; 110's 11ℤ
   budget with 104's valuation weights for a 10ℤ form without Sun; 97's
   interpolation with 110's budget for 11 integers below degree 2,000.
3. **Ten positive at fewer operations.** The research session's 99 / 368
   descends from this repository's four-root equation; 107's dyadic
   descaling and 109's fixed valuations are alternative descendants and
   have not been combined with its folding lemma.
4. **Formal status.** No wave-11 equation is Lean-checked end to end; the
   direct quartics rest on two Lean interfaces and an ordinary proof of
   "polynomial zero iff C222 derivation". Formalizing that step for one
   small direct quartic (108's 394 naturals) would make it the first fully
   checked Con(ZFC) equation.

### Frontier after wave 11, as placed

The combined frontier near the top of this README supersedes this table,
which is kept as the state after wave 11.

Numbers are the packages' own. At intake, read-only dossiers recounted
every operation count and measured the degrees of the headline circuits
(five dossiers for wave 11, four for each earlier wave); all checked
figures agree with the claims. The mathematics was not re-derived, and
every dominance statement assumes the competing proofs are correct. Only
packages of this collection are ranked here. The active research session's
own candidates, several of which dominate rows below (ten positive at
degree 368 in 99 operations, twelve positive at 70 / 96, 13ℤ at 536 / 135,
direct quartics in 610 unrestricted integers), are
compared in its [PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md).

- "u / e / d / o" means unknowns / equations / degree / operations; pairs
  are degree / operations. For the direct quartics (degree 4 throughout)
  the measures are variables / residuals / expanded terms / coefficient
  height.
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
    takes 7 operations;
  - the wave-11 ten-integer and nine-positive forms use eleven or twelve
    derived leaves (radix and threshold powers, recipe outputs), all
    materialized and checked.
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
    product adds twelve;
  - in wave 11, 85's nine-positive forms add seven, 84's ten-positive form
    ten, and 110's ten.

  The domain translation and its actual circuit must be stated.

The base is the earliest-arriving package that presents the construction in
full; where only one package has it, that package. Within one wave, the
lower directory number counts as earlier.

| Criterion | Best stated | Found by | Base |
|---|---|---|---|
| Nine positive, fewest operations | **420** at degree 1,472,168 (ℕ: not shipped) | 101 | 101 |
| Nine positive, lowest degree | **997,810 / 1,057** | 101 | 101 |
| Nine positive, Pareto frontier | 1,472,168 / 420 (101); 1,376,378 / 456 (105); 1,158,228 / 726 (82); 997,810 / 1,057 (101). Dominated by these: 66's 444 and every earlier nine-positive form; 101's 428 and 85's 434 ≡ 86's 435 (one polynomial), 105's 442, 86's 449, 79's 1,753, 85's 1,074, 86's 1,086 | 82, 101, 105 | — |
| Nine positive on the 2^429959 tuple | **1,626,248 / 428** (101); 1,628,768 / 434 (85; 86 evaluates the same polynomial in 435); 1,520,186 / 442 (105). Earlier: 54's 490 | 85, 101, 105 | 85 |
| Ten positive | **718 / 126** (109) and **706 / 133** (107), both descendants of this repository's four-root equation; dominated: 84's 1,152 / 131 (ℕ 141), the first ten-positive package form, and 110's 912 / 126 | 84, 107, 109 | 84 |
| 10ℤ (Sun's reduction), Pareto frontier | **1,245,324 / 467**, 1,179,788 / 470, 1,114,252 / 473, **1,080,888 / 507** (106, re-evaluating 87's 471 form and the research session's three shears of it). Other polynomials: 76's 480 / 1,245,324, 83's 484 / 1,179,788, 487 / 1,114,252 and 521 / 1,081,125, 87's 485, 496 and 545 / 1,080,888, 91's re-evaluations. All dominate 68's 1,576,864 / 481 | 76, 83, 87, 106 | 76 (degree), 87 (operations) |
| 11ℤ, without Sun's reduction | **2,240 / 206**, 2,272 / 204, **2,912 / 200** — the first eleven-integer forms; the "fewest integers without Sun" row moves from 13ℤ (67, 59) to 11ℤ | 110 | 110 |
| 12ℤ | **1,000 / 180**, 1,024 / 179 (110). Dominated: 104's 2,400 / 215 and 2,912 / 209, 109's 2,304 / 216, 108's 2,400 / 210 (104's form, n replaced by n + QV), 106's 2,048 / 233, 97's 4,832 / 248 and 16,000 / 223 (the first twelve-integer forms) | 97, 104, 106, 108, 109, 110 | 97 |
| 13ℤ | **1,072 / 186**, 1,392 / 177 and 1,408 / 176 (105's evaluators of 88's polynomials). Dominated: 97's 1,072 / 190 (a different polynomial), 88's 1,088 / 195, 1,392 / 186 and 1,408 / 185, 96's 1,072 / 195 (88's polynomial reanchored), 98's 1,072 / 195, 106's 1,072 / 192, 90's 475 and 473, 91's 205, 92's 211 and 205, and 67's 10,461,744 / 519 | 88, 97, 105 | 88 |
| 14ℤ | **378 / 145** (106); **792 / 137** (88). Dominated: 98's 414 / 148, 101's 568 / 147 and 540 / 160, 88's 696 / 150, 90's 652 / 230 and 664 / 223, 91's 696 / 151, 92's 862 / 150 | 88, 106 | 88 |
| 15ℤ | **172 / 123** and 170 / 134 (106). Dominated: 92's 204 / 128 and 352 / 124, 110's 176 / 125, 98's 218 / 130, 90's 214 / 139, 91's 244 / 137, 93's 306 / 139, 88's 344 / 131 | 106 | 88 (first 15ℤ form, 344 / 131) |
| 16ℤ, Pareto frontier | **98 / 138** (106); 108 / 132 (91); **112 / 119** (93); 124 / 118 (98); **160 / 115** (92). Dominated: 92's 152 / 120, 132 / 128 and 120 / 123, 93's 112 / 120, 86's 184 / 135 and 192 / 134 | 86, 91, 92, 93, 98, 106 | 86 |
| 17ℤ | **88 / 110** (88). 82's and 86's 17ℤ / 88 forms are different polynomials (82 uncounted, 86 at 114); 84's 112 / 124 and 110 / 140 dominated | 82, 86, 88 | 82 |
| 18ℤ–20ℤ | 18ℤ **32 / 112** (88) and 88 / 105 (85; 82's 18ℤ / 32 uncounted, 84's 80 / 115 and 77's 88 / 109 dominated); 19ℤ **28 / 116** (88) and 32 / 108 (85, the pivot polynomial of 83 and 84; 82 uncounted; 89's 19ℤ / 40 and 77's 32 / 112 dominated); 20ℤ **18 / 115** (93) and 20 / 111 (85; the pivot polynomial of 83 and 84; 88's 24 / 120 and 77's 32 / 112 dominated) | 82, 83, 85, 88, 89, 93 | 82 (18ℤ, 19ℤ), 83 (20ℤ) |
| 21ℤ–24ℤ | 21ℤ / 16 (89, 9 residuals; 83 ≡ 84 ≡ 85 at 114 operations; 87, different); 22ℤ / 14 (79; 81 at 123) and 22ℤ / 16 / 118 (77); 23ℤ / 10 (83 ≡ 86 at 131) and 23ℤ / 12 (77 at 121; 79, 81, 82); 24ℤ / 10 (78; 81 at 135; 82). All beat 68's 26ℤ / 16 and 37's 24ℤ / 1,936 | 77, 78, 79, 81, 83, 86, 89 | 77 |
| Integer octic | **25ℤ** in 127 operations (77). Dominated: the 26ℤ octics of 76, 77, 78, 79, 81, 82 and 68's 28ℤ, 69's and 71's 27ℤ | 77 | 77 |
| Integer sextic | **30ℤ** (76). Dominated: the 31ℤ sextics of 77, 79, 81 (144 operations), 82, and the 32ℤ and 34ℤ sextics of waves 9–10 | 76 | 76 |
| Integer quartic | **37ℤ** (76 ≡ 82, two variants; 77's four variants differ in one guard row). Dominated: 69's and 71's 38ℤ | 76, 77, 82 | 76 |
| Direct C222 quartic, ℕ (no K215, Jones, Sun or coefficient tuple) | **394 / 320 / 39,208 / 84,233,382** and **395 / 321 / 7,323 / 83,842,758** (108); 395 / 313 / 8,292 / 83,843,425 (109); 655 / 581 / **3,748** / 63,905,960 (108's uncontracted source, fewest terms; 100's 690-variable source has 3,762); 4,860 / 4,476 / 14,719 / **1,837** (98, lowest height). Dominated: 100's 407 (by 109's 395 in all four measures), 95's 522, 596 and 895, 96's 667, 99's 608, 89's 3,614 and 6,183, and every larger form. Lineage: 68 → 89 (3,614) → 95 (522) → 100 (407) → 108, 109 (395); 87 (27,916ℤ, 16,036ℕ) → 94 → 103 is the other lineage | 89, 95, 98, 100, 108, 109 | 87 (earliest), 89 (this lineage) |
| Direct C222 quartic, ℤ | **663 / 397 / 7,268 / 2.45·10^12** and 687 / 421 / **5,602** / 63,906,013 (108, fewest terms); 3,776 / 2,015 / 20,194 / **47,959** (102); 7,058 / 5,297 / 24,277 / **1,992** (102, lowest height). Dominated: 104's 1,190, 99's 1,685, 96's 1,690, 103's 1,873 and 3,292, 95's 2,088, 102's 3,671, 94's 7,617, 93's 26,188 and 87's 27,916 | 102, 108 | 87 |
| Eleven positive | **211 / 110** (105's evaluator of the research session's polynomial). Dominated: 83's 211 / 112, 86's 213 / 112, 87's 211 / 113, 82's 269 / 111, the 277 / 111 polynomial of 76, 77, 78, 79, 81, 77's 257 / 114, and 70's 325 / 113 | 83, 105 | 76 (277), 83 (211) |
| Twelve positive, Pareto frontier | **70 / 98** (98's free-J form; 104 evaluates the 100-operation polynomial of 80 / 87 in 98 too); 57's **258 / 89**. Dominated: 76's 78 / 101 ≡ 82's 78 / 102, 78's ≡ 81's 78 / 103, 87's 70 / 100, 69's 82 / 102, 74's forms | 98; 57 | 80 (claim), 87 (first artifact), 98 |
| Thirteen positive, Pareto frontier | **28 / 98** (72); 30 / 92 (73; 74 evaluates the same polynomial in 93); **51 / 88** (98); **114 / 83** (62). Dominated: 70's and 75's 30 / 94, 61's 34 / 93 | 72; 73; 98; 62 | — |
| Fourteen positive, Pareto frontier | unchanged: **24 / 101** (72); 65's 26 / 92; 64's 30 / 83; 55's and 59's **52 / 79** | 72; 65; 64; 55 | — |
| Fifteen positive | unchanged: 66 ops (51's P66, degree 157); lowest degree 24 / 88 (66); Pareto frontier as after wave 9 | 51; 66 | — |
| Twelve positive, systems | unchanged: 59's three-equation system at 94 operations | 59 | 59 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125. From wave 2 (history only, see the wave-2 README `5b0c9ae9fd`): 15's positive-domain sextic in 25 and octic in 20 unknowns, which still dominate 75's 26- and 21-unknown versions | waves 2, 5, 6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^429959** (54) among tuple-bound equations; 85, 86, 101 and 105 bind nine-positive forms to it. The direct quartics bind no tuple at all: their coefficients are the small integers of the expanded polynomial (heights from 1,837 to 9·10^21) | 54; 87–89 | 54 |

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
| [`75-signed-bootstrap/`](75-signed-bootstrap/) | `ZFC_Diophantine_Signed_Bootstrap_2026-10-23.zip` | *Signed-power recovery and inert-prime certificates for ZFC consistency* (README: *Signed-power bootstrap and alternative certificate interfaces*) | 34ℤ sextic (19 residuals); 13 / 1 / 30 / 94; 12 / 1 / 114 / 105; `certificates/` and `direct/` interface work (see below); bundles the eight wave-9 ZIPs |

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
  named. At intake it read as a variant of the classical
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
  guards by one quadratic-form guard of the shape xy − (s − x − y)², up to
  constant factors (69's carries a factor 4). None cites the others.
- **69 and 71: same sizes, different polynomials.** Their 38ℤ quartics share
  24 of 25 rows and differ only in the guard row and its fixed numbers. Their
  32ℤ sextics share 13 of 19 rows and keep different coordinates. Their 27ℤ
  octics share 11 of 14 rows and the same coordinates apart from the guard
  witnesses; they differ in the guard and in how X is substituted (69:
  X = 4w(βJ + 1); 71: X = 2u²). Both packages'
  restoration maps back to the quartic check out exactly.
- **Derived forms.**
  - 70's direct 40ℤ quartic is 64's 41ℤ quartic with X replaced by
    3·X3 − 1 and the row X − 2u² deleted.
  - 68's 28ℤ octic is 62's 30ℤ octic with its two sign guards merged.
  - 68's ten-integer form uses 66's gap source repacked on 65's layout, with
    a strengthened Lucas-index lemma that drops a divisibility hypothesis.
  - 71's nine-positive form is 65's source with 63's majorant and 62's
    power rewrite. Wave-9 further question 2 had asked for 65's source with
    66's or 67's majorants; 71 used 63's.
- **Thirteen positive.** 73's 30 / 92 and 74's 30 / 93 are one polynomial,
  and 73 evaluates it in one operation fewer. 70's and 75's 30 / 94 are one
  other polynomial. 72's 28 / 98 is a third. None of these packages cites
  another.
- **Twelve positive.** All eleven wave-9 and wave-10 circuits (61 has two) are pairwise
  different, with no ±1 shift relating any two. Pieces are shared: 74's norm
  residual is 71's, and 71's carrier residual is 75's.
- **The four 34ℤ sextics** of 70, 72, 73 and 75 are four different
  polynomials (368 to 614 terms).

### Tensions, not adjudicated at intake

- **Parallel discoveries.** The triple guard idea; 69 and 71 at identical
  sizes; the 73 / 74 and 70 / 75 thirteen-positive pairs; four 34ℤ sextics.
- **A caution overtaken.** 74's research note says the naive combination of
  62 and 64 does not reach 34 or 29 variables, and that deleting the global
  square guard is not justified. Six siblings reach a sextic in at most 34
  integers and four an octic in at most 29. 70 and 75 each delete that
  guard with a new signed argument.
- **Comparisons against stale baselines.**
  - For fewest operations, 71 cites only 62's 453, though 66's 444 and 449
    were in the tree at its pin. (Its degree comparison, with 67's
    1,494,006 / 487, is right.)
  - 72 compares its 14-positive form with 60's 89-operation evaluator; 66's
    88-operation evaluator of the same polynomial was already there.
- **Stale README at the pins.** 69, 71 and 73 observe that this README, at
  `9cca523d9f`, still described waves 5–8. That was true; the wave-9
  reconciliation came later.
- **Placement side effects.** 72 reports that 61's `ACTIVE_BINDING.json`
  paths are broken. That is true in the placed tree, because intake omitted
  the payloads as copies; the arrival archives are intact. The binding paths
  of 68–73 and 75 break the same way, and 74's whole `coefficients/` folder
  was omitted.
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

- **Titles.** 69's and 70's PDF metadata titles differ from their TeX titles,
  and 68's PDF has none. 72's and 75's README H1s differ from their printed
  titles, and 72's title begins like 61's.
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
  binding, 71's and 75's companion and comparison circuits, and 68's
  prototypes named in its report. 74's natural and 36ℤ forms are domain
  translations, not intermediates.

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
     An intake check built this form and measured 25 unknowns at degree 12;
     its correctness is not proved.
   - 72's elimination with 73's guard change, for a smaller sextic.
3. **Coefficients.** Bind the new integer forms to a four-port compact
   tuple, as 73 does for its sextic.

### Frontier after wave 10, as placed

The combined frontier near the top of this README supersedes this table,
which is kept as the state after wave 10.

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
| Twelve positive, Pareto frontier | **82 / 102** (69); 110 / 100 and the sum of squares 164 / 99 (74); 57's 242 / 94 and **258 / 89**. Dominated: 70's 84 / 103, 71's 110 / 102, 73's 110 / 105 and 164 / 104, 75's 114 / 105 and SOS 172 / 104, and 61's forms | 69; 74; 57 | — |
| Thirteen positive, Pareto frontier | **28 / 98** (72); 30 / 92 (73; 74 has the same polynomial in 93); **114 / 83** (62). Dominated: 70's and 75's 30 / 94 (one polynomial) and 61's 34 / 93 | 72; 73; 62 | — |
| Fourteen positive, Pareto frontier | **24 / 101** (72); 65's 26 / 92; 64's 30 / 83; 55's and 59's **52 / 79** | 72; 65; 64; 55 | — |
| Nine positive on a smaller tuple | unchanged: 60's 1,797,796 / 465 and 62's 1,834,516 / 453 (2^590069); 54's 490 (2^429959) | 60, 62; 54 | — |
| Twelve positive, systems | unchanged: 59's three-equation system at 94 operations | 59 | 59 |
| Fifteen positive | unchanged: 66 ops (51's P66, degree 157); lowest degree 24 / 88 (66); Pareto frontier as after wave 9 | 51; 66 | — |
| Integer quartic | **38ℤ**, two different polynomials (25 residuals each) | 69; 71 | 69 |
| Integer sextic | **32ℤ**, two different polynomials (19 residuals each). The four 34ℤ sextics of 70, 72, 73 and 75 are dominated | 69; 71 | 69 |
| Integer octic | **27ℤ**, two different polynomials (14 residuals each). 68's 28ℤ, 70's 29ℤ and 75's 30ℤ (which ties 62's) are dominated | 69; 71 | 69 |
| Integer, degree 16 | 26ℤ, 13 residuals | 68 | 68 |
| Unchanged | the 59-op 16 / 7 / 24 system; the 31-unknown positive quartic system 60 / SOS 125; 24ℤ at 1936 / 161. From wave 2 (history only, see the wave-2 README `5b0c9ae9fd`): 15's positive-domain sextic in 25 and octic in 20 unknowns, which still dominate 75's 26- and 21-unknown versions | waves 2, 5, 6 | — |
| Smallest coefficients binding an equation | unchanged: **B = 2^429959** (54). 69's and 71's integer forms use six coefficient payloads (881,696 and 615,883 raw bytes) instead of four; 73's sextic is the first low-degree residual-system integer form bound to the 2^590069 tuple (39's and 52's ten-integer forms and 58's 60ℤ translation already were) | 54 | 54 |

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
combined frontier above supersedes it where waves 6–15 improve on it.

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
    postdates the wave-5 and wave-6 pins, but not the wave-7 to wave-15
    pins. Packages of waves 11–15 build on its reviews and candidates, and
    its candidates on them (see those sections).
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
    no theorem; 75's `certificates/` and `direct/` are paper-proved
    interface lemmas, not equations.
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
  - In wave 11, the nine-positive forms of 79, 82, 85, 86, 101 and 105 keep
    the ratio finalizer through 66's and 71's sources. No other wave-11
    form uses a Jones lemma; the direct quartics use none.
  - Waves 12–15 use no Jones lemma: their ten- to thirteen-positive
    forms, 117's 30ℤ companion and the 11ℤ–15ℤ forms are native K215 forms,
    and their quartics are direct.
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
  - It reviewed the wave-11 arrivals one by one as they came
    ([PROPOSAL_REVIEW_WAVE11.md](../PROPOSAL_REVIEW_WAVE11.md) and the
    later `PROPOSAL_REVIEW_*.md` files), and built its own candidates on
    them and on this repository's `ten-positive-scaled-norm`; its current
    comparison is [PROPOSAL_REVIEW_LATEST.md](../PROPOSAL_REVIEW_LATEST.md).
- **Direct C222 route (waves 11–15).** The direct quartics of 87, 89,
  93–96, 98–109, 111, 112, 114, 115 and 117–139 rest on two Lean theorems, `KEndpoint.c222_iff_zf_refutation`
  (`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean`) and
  `ConstructibleChoice.zf_refutation_iff_zfc_refutation`, and on the
  representation modules under `Computability/DiophantineConsistency/Lean/`
  (`PellRepresentation.criterion_iff_pell` and its siblings), all present at
  `HEAD` and copied inertly into the packages. The step "polynomial zero iff
  finite C222 derivation" is an ordinary proof in each package, checked by
  finite replays. None of these packages uses
  `DirectQuarticZFC.noNaturalZero_iff_conZFC` in its construction (116, 120,
  127, 131 and 132 cite it in copied provenance).
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
| 10 | `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` (68–73); `a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49` (74); both, and `bdd86761ba` (75) | `9513bd88ce` | `d79b41884d` |
| 11 | `2605669a53` (76–81; components of 83–86); `cf4a5218a5` (82, 90, 91); `cfbf118b4a` (90–92); `9a33342a03` (87, 88); `08200eb10f` (89; calibration of 95, 98–100, 105, 106); `04a1d79222` (94, 97); `a88aefd7dd` (95, 96, 98); `8b328dc180` (99); `85ae407001` (100, 104); `7e533c3381` (101, 106, 110); `278bc68df1` (102); `b594a5e988` (103); `8f8fac484b` (105); `43ac596e36` (93); `ec80841c07` (107–110) | `c1a102936a` … `e13c748234` (17 commits) | `240bf9e422`, `c16a89ad94` |
| 12 | `84e16e4309` (all; 116 also `56b4d15d12`) | `45b399ec51` | `55fe52f28c` |
| 13 | `45b399ec51` (all) | `5f3379063d` | `9f7ff01558` |
| 14 | `f4d8db99e0` (all) | `fd3e384e92` | `1c5367452a` |
| 15 | `1c5367452a` (134–136, 138, 139), `b30ddde0aa` (137) | `e0c98c629b` | `1eed4b48cd` |

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
- `31-sun10/quartic31/upstream/`: `PRODUCT67.json`, `quartic31.json`, `quartic31_circuit.json`, `quartic31_system.json`
- `31-sun10/quartic31/upstream/27-wave4/operations/`: `PROOF.md`
- `31-sun10/quartic31/upstream/27-wave4/operations/upstream/`: `RETAINED59_PROOF.md`, `build_retained59.py`, `retained16_system59.json`
- `31-sun10/quartic31/upstream/28-compact-norms/vendor/inherited/`: `FIXED_BLANK_67_PROOF.md`, `PELL_LEMMA_AUDIT.md`
- `31-sun10/quartic31/upstream/30-quartic31/arithmetic/`: `QUARTIC31_PROOF.md`, `build_arithmetic.py`
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
- `32-integer15/integer15/upstream/nine/`: `nine_compressor.py`, `nine_section.tex`, `verify_fixed_instance.py`
- `32-integer15/integer15/upstream/nine/generated/`: `constants.json`, `index_bound_s.json`
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
- `32-integer15/integer16/upstream/nine/`: `nine_compressor.py`, `nine_section.tex`, `verify_fixed_instance.py`
- `32-integer15/integer16/upstream/nine/generated/`: `constants.json`, `index_bound_s.json`
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
- `34-integer14/review/`: `ATTRIBUTION_SOURCE_MAP.json`, `COMPARISON_REVIEW.md`, `COUNT_AUDIT.json`, `PLACEMENT.md`, `README.md`, `SOURCE_LEDGER.json`, `TREE.json`, `audit_counts.py`
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
- `35-cancel12/integers/upstream/30-quartic31/review/`: `optimize_nine_circuit.py`
- `35-cancel12/integers/upstream/30-quartic31/review/18-jones9/proofs/`: `nine_source_audit.md`
- `35-cancel12/licenses/`: `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`
- `35-cancel12/positive/`: `CHECK_RESULTS.json`, `README.md`, `build_new.py`, `cancellation1065_product.json`, `cancellation1065_shifted_system.json`, `cancellation1065_system.json`, `check_new.py`, `economical_product.json`, `economical_shifted_system.json`, `economical_system.json`
- `35-cancel12/quartic/`: `QUARTIC31_62_AUDIT.json`, `QUARTIC31_62_PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_quartic31_62.py`, `quartic31_sos127.json`, `quartic31_system62.json`
- `35-cancel12/quartic/upstream/`: `QUARTIC31_PROOF.upstream.md`, `RETAINED59_PROOF.upstream.md`, `quartic31.json`
- `35-cancel12/reviews/`: `COEFFICIENTS_INDEPENDENT_AUDIT.json`, `COEFFICIENTS_INDEPENDENT_REVIEW.md`, `POSITIVE1065_INDEPENDENT_REVIEW.md`, `SIGNED16_INDEPENDENT_REVIEW.json`, `SIGNED16_INDEPENDENT_REVIEW.md`, `audit_coefficients_independent.py`, `audit_signed16.py`
- `35-cancel12/sections/`: `coefficients.tex`, `positive.tex`, `quartic.tex`, `signed.tex`, `verification.tex`
- `35-cancel12/sources/`: `SOURCE_MAP.json`
- `35-cancel12/sources/catalogue/`: `README.md`
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
- `37-wave5/sources/`: `PLACEMENT.md`, `README.md`
- `37-wave5/sources/24-integer24/`: `README.md`
- `37-wave5/sources/25-hybrid12/`: `README.md`
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
- `42-additive-b4/sources/`: `COLLECTION_README.md`, `README.md`
- `42-additive-b4/sources/31-sun10/coefficients/`: `COEFFICIENT_PROOF.md`
- `42-additive-b4/sources/31-sun10/quartic31/`: `QUARTIC60_PROOF.md`
- `42-additive-b4/sources/31-sun10/signed10/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`
- `42-additive-b4/sources/31-sun10/sources/`: `PELL_LEMMA_AUDIT.md`
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
- `52-sparse-pell/review/sources/`: `INCOMING_README.md`, `README.md`
- `52-sparse-pell/review/sources/44-b4-sparse/`: `LICENSE`, `NOTICE.md`
- `52-sparse-pell/review/sources/44-b4-sparse/native/`: `NOTICE-upstream.md`
- `52-sparse-pell/review/sources/44-b4-sparse/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
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
- `62-sign-and-norm/quartic42/dependencies/`: `README.md`, `SOURCE_PINS.json`
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
- `66-gap-congruence/nine/data/`: `OLD_TUPLE_BINDING.json`
- `66-gap-congruence/nine/data/H2057/`: `kernels.json`, `layout.json`, `source.json`
- `66-gap-congruence/nine/data/H2068/`: `kernels.json`, `layout.json`, `source.json`
- `66-gap-congruence/nine/data/H2082/`: `kernels.json`, `layout.json`, `source.json`
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
- `76-structural-round11/`: `DEPENDENCIES.md`, `LICENSE.NEW`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RELEASE_CHECKS.json`, `REPLAY.json`, `negative_controls.py`, `verify.py`
- `76-structural-round11/commutative/`: `BOOLEAN_CHECKS.json`, `CONSTRUCTOR_CHECKS.json`, `HEIGHT_CERTIFICATE.md`, `HEIGHT_CHECKS.json`, `HeightBooleanCommutativeEquation.lean`, `HeightCommutativeEquation.lean`, `HeightSelectedCommutativeEquation.lean`, `README.md`, `REPLAY_COMMANDS.json`, `SELECTOR_CHECKS.json`, `SOURCE_PIN.json`, `build_height_boolean.py`, `build_height_selector.py`, `build_height_step.py`, `check_constructor_literals.py`, `check_height_boolean.py`, `check_height_certificate.py`, `check_height_selector.py`, `emit_height_constructor.py`, `height_boolean_step.json`, `height_selector_step.json`, `height_shared_step.json`, `section.tex`
- `76-structural-round11/inherited/round10/calculus_api/sources/`: `BoundedForallRepresentation.lean`, `Bridge.lean`, `ComposeRepresentation.lean`, `ComputationRepresentation.lean`, `NativeFormulaGraphs.lean`, `NativeGraphEnumerator.lean`, `QuarticCompiler.lean`, `RemainderRepresentation.lean`, `Representation.lean`
- `76-structural-round11/inherited/round10/integer_licenses/`: `LICENSE.SignAndNorm`, `LICENSE.Source34`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE.SignAndNorm.md`, `NOTICE.Source34.md`
- `76-structural-round11/low_degree_audit/`: `ARCHIVE_MATCHES.json`, `AUDIT.md`, `README.md`, `RESULTS.json`, `RESULTS_RELEASE.json`, `SOURCE_ARCHIVE_PINS.json`, `audit_literals.py`
- `76-structural-round11/lucas/`: `CHECKS.json`, `INTERPOLATION_CHECKS.json`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `build.py`, `check.py`, `check_interpolation.py`, `independent_formula.py`, `integer10.json`, `section.tex`
- `76-structural-round11/lucas/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `76-structural-round11/lucas_audit/`: `AUDIT.md`, `BASELINE_PIN.json`, `INDEPENDENT_CHECKS.json`, `INDEPENDENT_CHECKS_NORMAL.json`, `INDEPENDENT_H1868_CHECKS.json`, `INDEPENDENT_H1868_CHECKS_NORMAL.json`, `check_independent.py`
- `76-structural-round11/lucas_h1868/`: `CHECKS.json`, `INTERPOLATION_CHECKS.json`, `METRICS.json`, `NOTICE.md`, `OPTIMIZED_POWER_PLAN.json`, `PROOF.md`, `README.md`, `REBUILD_CHECKS.json`, `RELEASE_FILES.json`, `REPLAY_COMMANDS.json`, `build.py`, `check.py`, `check_interpolation.py`, `independent_formula.py`, `integer10.json`, `section.tex`
- `76-structural-round11/lucas_h1868/data/`: `code.json`, `kernels.json`
- `76-structural-round11/lucas_h1868/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `76-structural-round11/packing/`: `RELEASE_FILES.json`
- `76-structural-round11/packing/certified/`: `CHECKS.json`, `PROOF.md`, `check.py`, `kernels.json`, `layout.json`
- `76-structural-round11/packing/factor_gap/`: `PROOF.md`, `check.py`, `source.json`
- `76-structural-round11/positive/`: `PROOF.md`, `PROOF11.md`, `build.py`, `build11.py`, `check.py`, `check11.py`, `check_coefficients.py`, `p11_degree277.json`, `p12_degree78.json`
- `76-structural-round11/positive/native/`: `NOTICE-upstream.md`
- `76-structural-round11/positive/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `76-structural-round11/positivity/`: `BINDING.json`, `CHECK_RESULTS.json`, `INHERITED_HASHES.json`, `PROOF.md`, `README.md`, `RELEASE_FILES.json`, `REPLAY_COMMANDS.json`, `build.py`, `check.py`, `degree10_25.json`, `degree12_24.json`, `degree16_23.json`, `octic26.json`, `quartic37.json`, `quartic37_direct.json`, `section.tex`, `sextic30.json`
- `76-structural-round11/positivity/inherited/`: `source71_LICENSE`, `source71_NOTICE.md`
- `76-structural-round11/report/`: `DISPLAYED_ROWS_CHECKS.json`, `PDF_QA.json`, `build.sh`, `check_displayed_rows.py`, `evidence.tex`, `explicit_low.tex`, `generate_kernel_appendix.py`, `height.tex`, `kernels.tex`, `low_degree.tex`, `lucas.tex`, `next.tex`, `positive.tex`, `references.tex`, `report.pdf`, `report.tex`
- `76-structural-round11/review/`: `ARCHIVE_PINS.json`, `FETCH_LEDGER.json`, `FORMAL_PINS.json`, `LITERAL_COUNTS.json`, `RECENT_COMMITS.json`, `UPSTREAM_README.md`, `WAVE10_REVIEW.md`, `check_literal_counts.py`
- `76-structural-round11/review/formal/`: `ALTERNATIVE_ENCODINGS.md`, `OBJECT_ZFC.md`, `PROPOSAL_REVIEW_WAVE10.md`, `PROPOSAL_REVIEW_WAVE10_GUARDS.md`, `PROPOSAL_REVIEW_WAVE10_NATIVE.md`, `README.md`, `STATUS.md`
- `76-structural-round11/review/formal/lean/`: `BoundedForallRepresentation.lean`, `QuarticCompiler.lean`, `RemainderRepresentation.lean`
- `76-structural-round11/root_audit/`: `check_height_independent.py`
- `77-joint-guards/`: `DEPENDENCIES.md`, `DISPLAYED_SYSTEM_CHECK.json`, `INCOMING_PINS.json`, `README.md`, `REBUILD_FILES.json`, `REBUILD_NUMERALS.json`, `REPLAY_COMMANDS.json`, `build_report.sh`, `check_displayed_system.py`, `negative_controls.py`, `report.pdf`, `report.tex`, `verify.py`
- `77-joint-guards/baseline/`: `ANNOTATED_REFUTATION_PR.md`, `ARRIVAL_COMMIT.json`, `BASELINE_REVIEW.md`, `ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.normal.stdout.txt`, `ConZFC_Joint_Positivity_Free_Lucas_2026-10-23.optimized.stdout.txt`, `DIRECT_GRAPH.md`, `DIRECT_PROGRAM.md`, `EXECUTION_SURFACE.json`, `FORMAL_SOURCE_PINS.json`, `FRONTIER_COUNTS.json`, `MANIFEST_CHECKS.json`, `NATIVE_CALIBRATION52.md`, `NATIVE_CLAUSE54.md`, `NATIVE_SPARSE_DIGITS54.md`, `NATURAL_REGISTER_PROGRAM.md`, `OBJECT_NUMERIC_WIRE.md`, `OBJECT_QUARTIC_COMPILER.md`, `OBJECT_ZFC.md`, `PDF_QA.json`, `PROPOSAL_REVIEW_WAVE10.md`, `PROPOSAL_REVIEW_WAVE10_GUARDS.md`, `PROPOSAL_REVIEW_WAVE10_NATIVE.md`, `QUADRATIC_GUARDED_GRAPHS.md`, `QUADRATIC_REGISTER_SYSTEM.md`, `QUADRATIC_TREE_CODE_GRAPHS.md`, `REPLAY_RESULTS.json`, `SHARED_REGISTER_RELATIONS.md`, `SMALL_INTEGER_FRONTIER.md`, `SMALL_INTEGER_SCAN.json`, `STATUS.md`, `ZFC_Diophantine_Signed_Bootstrap_2026-10-23.normal.stdout.txt`, `check_manifests.py`, `con-zfc-centered-pell-gaps-2026-10-23.normal.stdout.txt`, `con-zfc-centered-pell-gaps-2026-10-23.optimized.stdout.txt`, `con-zfc-cones-pell-2026-10-23.normal.stdout.txt`, `con-zfc-cones-pell-2026-10-23.optimized.stdout.txt`, `con-zfc-diophantine-forms_README.md`, `con_zfc_calibrated_determinant_guards_2026-10-23.normal.stdout.txt`, `con_zfc_calibrated_determinant_guards_2026-10-23.optimized.stdout.txt`, `con_zfc_congruence_and_sextic_2026-10-23.normal.stdout.txt`, `con_zfc_congruence_and_sextic_2026-10-23.optimized.stdout.txt`, `con_zfc_guard_reanchoring.normal.stdout.txt`, `con_zfc_guard_reanchoring.optimized.stdout.txt`, `count_frontier.py`, `replay_archives.py`, `section.tex`
- `77-joint-guards/certificates/`: `CRT_CHECK_RESULTS.json`, `INDEX_FREE_CRT.md`, `LOCAL_CHECK_RESULTS.json`, `LOCAL_GADGET_PROOFS.md`, `README.md`, `SOURCE_PINS.json`, `build_local_gadgets.py`, `check_index_free_crt.py`, `if_zero_quartic.json`, `list_head_quartic.json`, `max_square_pair_quartic.json`, `max_square_pair_sextic.json`, `max_square_pair_sos_quartic.json`, `predecessor_quartic.json`, `section.tex`, `tree_left_quartic.json`, `tree_right_quartic.json`, `unpair_left_quartic.json`, `unpair_right_quartic.json`, `zero_test_quartic.json`
- `77-joint-guards/circuits/`: `BUILD.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `PROOF.md`, `README.md`, `build.py`, `check.py`, `joint19_degree88_dag.json`, `joint20_degree32_dag.json`, `joint21_degree20_dag.json`, `joint22_degree16_dag.json`, `joint23_degree12_dag.json`, `joint25_octic_dag.json`, `section.tex`
- `77-joint-guards/guards/`: `CHECK.json`, `COEFFICIENT_BINDING.json`, `DISPLAY_CHECK.json`, `METRICS.json`, `PROOF.md`, `README.md`, `UPSTREAM_COPY_RECEIPT.json`, `build.py`, `build_coefficients.py`, `check.py`, `check_displayed.py`, `cone26_octic.json`, `cone31_sextic.json`, `cone37_quartic_affine.json`, `cone37_quartic_direct.json`, `determinant26_octic.json`, `determinant31_sextic.json`, `determinant37_quartic_affine.json`, `determinant37_quartic_direct.json`, `section.tex`
- `77-joint-guards/guards/upstream/determinant/`: `LICENSE`, `NOTICE.md`
- `77-joint-guards/guards/upstream/residue/`: `LICENSE`, `NOTICE.md`
- `77-joint-guards/guards/upstream/residue/dependencies/`: `LICENSE.ProveIt`
- `77-joint-guards/guards/upstream/residue/dependencies/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `77-joint-guards/joint/`: `BUILD_CHECK.json`, `CHECK_normal.json`, `CHECK_optimized.json`, `COMPACT_BASE24.json`, `PROJECTION_BUILD.json`, `PROJECTION_CHECK_normal.json`, `PROJECTION_CHECK_optimized.json`, `PROOF.md`, `README.md`, `SOURCE_PIN.json`, `build.py`, `build_projections.py`, `check.py`, `check_projections.py`, `joint19_degree88.json`, `joint20_degree32.json`, `joint21_degree20.json`, `joint22_degree16.json`, `joint23_degree12.json`, `joint23_degree12_eliminate_I.json`, `joint24_degree12.json`, `joint25_octic.json`, `section.tex`
- `77-joint-guards/joint/upstream/`: `determinant26_octic.json`
- `77-joint-guards/pell/`: `CENTERED_PROOF.md`, `CHECK_CENTERED.json`, `CHECK_CENTERED_OPTIMIZED.json`, `COMPOSITION_SOURCES.json`, `FOUR_ROOT_LIMITS.md`, `LICENSE`, `NEW_LEMMA_CHECKS.json`, `NEW_LEMMA_CHECKS_OPTIMIZED.json`, `NOTICE.md`, `OPTIMIZED_VERIFICATION.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `build_centered.py`, `check_new_lemmas.py`, `p11_positive_degree257.json`, `p11_positive_degree277.json`, `section.tex`, `verify.py`, `verify_centered.py`
- `77-joint-guards/pell/coefficients/`: `ACTIVE_BINDING.json`
- `77-joint-guards/pell/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `77-joint-guards/review/`: `ROOT_REPLAY.json`, `ROOT_REPLAY_INPUTS.json`
- `77-joint-guards/review/certificates/`: `CRT_CHECKS.json`, `CRT_CHECKS_OPTIMIZED.json`, `LOCAL_CHECKS.json`, `LOCAL_CHECKS_OPTIMIZED.json`, `MATHEMATICAL_REVIEW.md`, `REVIEW_RECEIPT.json`, `independent_crt_check.py`, `independent_local_check.py`
- `77-joint-guards/review/circuits/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `REVIEW.md`, `independent_check.py`
- `77-joint-guards/review/guards/`: `ALTERNATE23_SUPPORT.json`, `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `JOINT_CHECKS.json`, `JOINT_CHECKS_OPTIMIZED.json`, `MATHEMATICAL_REVIEW.md`, `PROJECTION_CHECKS.json`, `PROJECTION_CHECKS_OPTIMIZED.json`, `independent_check.py`, `independent_check_joint.py`, `independent_check_projections.py`
- `77-joint-guards/review/positive/`: `CHECK257.json`, `CHECK277.json`, `MATHEMATICAL_REVIEW.md`, `NORMAL257.stdout.json`, `NORMAL277.stdout.json`, `OPTIMIZED257.stdout.json`, `OPTIMIZED277.stdout.json`, `check_257.py`, `check_277.py`
- `78-budget-centering/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `build_release.py`, `independent_integer_audit.py`, `independent_positive_degree_audit.py`, `report.pdf`, `report.tex`, `verify.py`
- `78-budget-centering/direct/`: `CHECKS.json`, `LOCAL_METRICS.json`, `NOTICE-source68.md`, `NOTICE.md`, `README.md`, `TOY_CERTIFICATES.json`, `build.py`, `core.py`, `horn_source_rows.json`, `linear_budget_local.json`, `section.tex`, `verify.py`
- `78-budget-centering/integer/`: `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build_and_verify.py`, `section.tex`
- `78-budget-centering/integer/certificates/`: `COEFFICIENT_CHECKS.json`, `FINITE_DIAGNOSTICS.json`, `ROOT_INDEPENDENT_AUDIT.json`, `decic24_CHECKS.json`, `degree16_23_CHECKS.json`, `octic26_CHECKS.json`
- `78-budget-centering/integer/generated/`: `decic24.json`, `decic24_expanded.json`, `degree16_23.json`, `degree16_23_expanded.json`, `octic26.json`, `octic26_expanded.json`
- `78-budget-centering/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE-source64.md`, `NOTICE-source71.md`
- `78-budget-centering/positive/`: `MANIFEST.sha256.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `section.tex`
- `78-budget-centering/positive/coefficients/`: `ACTIVE_BINDING.json`
- `78-budget-centering/positive/eleven/`: `OPTIMIZED_VERIFICATION.json`, `VERIFICATION.json`, `build.py`, `p11_positive_degree277.json`, `verify.py`
- `78-budget-centering/positive/licenses/`: `LICENSE.69-cones-pell`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.eleven`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `78-budget-centering/positive/twelve/`: `build.py`, `equation.json`, `verify.py`
- `78-budget-centering/positive/twelve/certificates/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`
- `78-budget-centering/verification/`: `DOCUMENT_QA.json`, `INDEPENDENT_POSITIVE_DEGREES.json`, `MATHEMATICAL_REVIEW.json`, `RELEASE_CHECKS.json`, `__independent_positive_degree_audit_py.stdout.txt`, `direct_verify_py.stdout.txt`, `integer_build_and_verify_py.stdout.txt`, `positive_eleven_verify_py.stdout.txt`, `positive_twelve_verify_py.stdout.txt`
- `79-radical-guard-descent/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `PDF_LAYOUT_CHECKS.json`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `make_archive.py`, `report.pdf`, `report.tex`, `verify_all.py`
- `79-radical-guard-descent/alternative/`: `LOCAL_ADAPTER_CHECKS.json`, `README.md`, `SINGLE_LOOP_CHECKS.json`, `build_local_adapter.py`, `single_loop.py`, `single_loop.tex`, `single_loop_local.json`
- `79-radical-guard-descent/alternative/upstream/`: `NOTICE-source68.md`
- `79-radical-guard-descent/integer/`: `build.py`
- `79-radical-guard-descent/integer/audit/`: `INDEPENDENT_CHECKS.json`, `REVIEW.md`, `check_independent.py`
- `79-radical-guard-descent/integer/certificates/`: `ALGEBRA.json`, `degree12_23.json`, `degree14_22.json`, `octic26.json`, `sextic31.json`
- `79-radical-guard-descent/integer/coefficients/`: `BINDING.json`
- `79-radical-guard-descent/integer/forms/`: `compact23_display.json`, `degree12_23.json`, `degree12_23_expanded.json`, `degree14_22.json`, `degree14_22_expanded.json`, `octic26.json`, `octic26_expanded.json`, `sextic31.json`, `sextic31_expanded.json`
- `79-radical-guard-descent/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `79-radical-guard-descent/nine_positive/`: `COEFFICIENT_REBUILD.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `equation9.json`, `majorant_section.tex`, `rebuild_coefficients.py`, `regenerate_majorant.py`, `verify.py`
- `79-radical-guard-descent/nine_positive/certificates/`: `INDEPENDENT_DAG_AUDIT.json`, `INDEPENDENT_MAJORANT_AUDIT.json`, `P_shifted.json`, `defect_shifted.json`, `horner_choices.json`, `majorant_regeneration.json`
- `79-radical-guard-descent/nine_positive/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `79-radical-guard-descent/nine_positive/data/`: `radical.json`
- `79-radical-guard-descent/nine_positive/independent/`: `MAJORANT_AUDIT.md`, `audit_laurent_dag.py`, `audit_laurent_majorant.py`
- `79-radical-guard-descent/nine_positive/licenses/`: `LICENSE.Source65`, `LICENSE.Source71`
- `79-radical-guard-descent/positive11/`: `ALGEBRA_AUDIT.json`, `COEFFICIENT_REBUILD.json`, `INDEPENDENT_AUDIT.json`, `INDEPENDENT_DAG_AUDIT.json`, `INDEPENDENT_DAG_AUDIT_OPTIMIZED.json`, `LICENSE.upstream`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `audit.py`, `build.py`, `p11_positive_degree277.json`, `rebuild_coefficients.py`, `verify.py`
- `79-radical-guard-descent/positive11/coefficients/`: `ACTIVE_BINDING.json`
- `79-radical-guard-descent/positive11/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `79-radical-guard-descent/positive11/native_recipe/`: `NOTICE-upstream.md`
- `79-radical-guard-descent/provenance/`: `ALTERNATIVE_ENCODINGS.md`, `NATIVE_CALIBRATION52.md`, `OBJECT_ZFC.md`, `PROPOSAL_REVIEW_WAVE10.md`
- `80-twelve-manuscript/`: `report.tex`
- `81-centered-pell-norms/`: `CATALOGUE_ENTRY.md`, `LICENSE`, `MANIFEST.sha256.json`, `NOTICE.md`, `README.md`, `RESULTS.json`, `make_manifest.py`, `verify.py`
- `81-centered-pell-norms/coefficients/`: `ACTIVE_BINDING.json`
- `81-centered-pell-norms/coefficients/recipe/`: `NOTICE-upstream.md`, `RESTORED_DEPENDENCIES.json`
- `81-centered-pell-norms/coefficients/recipe/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `81-centered-pell-norms/exploratory/`: `HOMOGENEOUS_CHECKS.json`, `HOMOGENEOUS_CLOSURE.md`, `check_homogeneous_closure.py`
- `81-centered-pell-norms/integer/`: `CHECKS.json`, `CIRCUIT_CHECKS.json`, `DETERMINISM_CHECK.json`, `INTEGER23_INDEPENDENT_AUDIT.json`, `INTEGER23_MATHEMATICAL_REVIEW.md`, `INTEGER_EXTENSIONS_INDEPENDENT_AUDIT.json`, `INTEGER_EXTENSIONS_MATHEMATICAL_REVIEW.md`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFY_RESULTS.json`, `build.py`, `circuits.py`, `degree10_24.json`, `degree10_24_circuit.json`, `degree12_23.json`, `degree12_23_circuit.json`, `degree12_25.json`, `degree12_25_circuit.json`, `degree14_22.json`, `degree14_22_circuit.json`, `independent_check.py`, `independent_extensions.py`, `octic26.json`, `octic26_circuit.json`, `sextic31.json`, `sextic31_circuit.json`, `verify.py`
- `81-centered-pell-norms/integer/coefficients/`: `BINDING.json`
- `81-centered-pell-norms/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `81-centered-pell-norms/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `81-centered-pell-norms/positive11/`: `INDEPENDENT_AUDIT.json`, `audit.py`, `build.py`, `p11_positive_degree277.json`
- `81-centered-pell-norms/positive12/`: `audit.py`, `build.py`, `equation.json`
- `81-centered-pell-norms/positive12/certificates/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`
- `81-centered-pell-norms/provenance/`: `NATIVE_CALIBRATION52.md`, `OBJECT_ZFC.md`, `SOURCE_PINS.json`
- `81-centered-pell-norms/report/`: `centered.tex`, `compiler.tex`, `integer.tex`, `positive.tex`, `report.pdf`, `report.tex`
- `81-centered-pell-norms/validation/`: `PDF_QA.json`, `POSITIVE_COMPOSITION_REVIEW.md`, `VERIFICATION.json`, `VERIFICATION_NORMAL.json`
- `82-pell-congruences/`: `LICENSE`, `NOTICE.md`, `README.md`, `SOURCE_PROVENANCE.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `verify.py`
- `82-pell-congruences/certificates/`: `ALTERNATIVE_ROUTES_REVIEW.md`, `INDEPENDENT_INTEGER_AUDIT.json`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `INTEGER_CHECKS.json`, `NINE_INDEPENDENT_REVIEW.md`, `PDF_QA.json`, `RANK_REGISTER_REVIEW.md`, `crt_degree16_24_degree.json`, `crt_degree26_22_degree.json`, `crt_degree26_23_degree.json`, `crt_degree28_21_degree.json`, `crt_degree44_20_degree.json`, `degree10_25_degree.json`, `degree12_23_degree.json`, `degree20_22_degree.json`, `degree26_20_degree.json`, `degree32_19_degree.json`, `octic26_degree.json`, `quartic37_degree.json`, `quartic37_direct_degree.json`, `sextic31_degree.json`
- `82-pell-congruences/coefficients/`: `BINDING.json`, `VERIFICATION.json`, `verify.py`
- `82-pell-congruences/inherited/determinant71/`: `NOTICE.md`
- `82-pell-congruences/integer/`: `audit.py`, `build.py`, `crt_degree16_24.json`, `crt_degree26_22.json`, `crt_degree26_23.json`, `crt_degree28_21.json`, `crt_degree44_20.json`, `degree10_25.json`, `degree12_23.json`, `degree20_22.json`, `degree26_20.json`, `degree32_19.json`, `octic26.json`, `polynomial.py`, `quartic37.json`, `quartic37_direct.json`, `sextic31.json`
- `82-pell-congruences/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `82-pell-congruences/nine_full_radical/`: `COEFFICIENT_RECONSTRUCTION.json`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `build_correction.py`, `check_laurent_cone.py`, `laurent9_positive.json`, `laurent_candidate.json`, `laurent_cone_certificate.json`, `laurent_correction_nopad_4JDbasis.json`, `laurent_symbolic.py`, `section.tex`, `verify.py`
- `82-pell-congruences/nine_full_radical/upstream/31-sun10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `82-pell-congruences/nine_full_radical/upstream/71-determinant-guards/nine_positive/`: `LICENSE`, `NOTICE.md`
- `82-pell-congruences/positive/`: `AUDIT11.json`, `AUDIT12.json`, `LICENSE`, `NATIVE_FETCH.json`, `NOTICE.md`, `PROOF.md`, `UPSTREAM_FETCH.json`, `VERIFICATION.json`, `build11.py`, `build12.py`, `p11_positive_degree269.json`, `p12_positive_degree78.json`, `positive_reductions.tex`, `verify.py`, `verify11.py`, `verify12.py`
- `82-pell-congruences/positive/native/`: `NOTICE-upstream.md`
- `82-pell-congruences/positive/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `82-pell-congruences/report/`: `nine_section.tex`, `report.pdf`, `report.tex`
- `82-pell-congruences/transport/`: `PROOF.md`, `README.md`, `build_transport.py`, `check_transport.py`, `degree10_24.json`, `degree16_22.json`, `degree20_20_rank_register.json`, `degree28_19.json`, `degree32_18.json`, `degree88_17.json`
- `82-pell-congruences/transport/certificates/`: `DOMINATED_TRANSPORT_PROBES.json`, `INDEPENDENT_TRANSPORT_AUDIT.json`, `TRANSPORT_CHECKS.json`, `degree10_24_degree.json`, `degree16_22_degree.json`, `degree20_20_rank_register_degree.json`, `degree28_19_degree.json`, `degree32_18_degree.json`, `degree88_17_degree.json`
- `82-pell-congruences/transport/parents/`: `crt_degree44_20.json`, `degree10_25.json`, `degree12_23.json`, `degree20_22.json`, `degree26_20.json`, `degree32_19.json`, `octic26.json`, `quartic37.json`, `quartic37_direct.json`, `sextic31.json`
- `83-polynomial-shears/`: `LICENSE.NEW`, `MANIFEST.sha256`, `Makefile`, `NOTICE.md`, `PDF_QA.json`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `report.pdf`, `report.tex`, `verify.py`
- `83-polynomial-shears/alternative/`: `LICENSE.ProveIt`, `NOTICE.md`, `README.md`, `section.tex`
- `83-polynomial-shears/alternative/gadgets/`: `CHECKS.json`, `PROOF.md`, `build_and_verify.py`, `conditional_cubic.json`, `conditional_quartic.json`, `joint_zero_predecessor_quadratic.json`, `list_head_quartic.json`, `predecessor_cubic.json`, `predecessor_quadratic_relation.json`, `predecessor_quadratic_with_bit.json`, `predecessor_sos_quartic.json`, `tree_left_quartic.json`, `tree_right_quartic.json`, `zero_test_quadratic.json`
- `83-polynomial-shears/alternative/selector/`: `CHECKS.json`, `PROOF.md`, `build_and_verify.py`, `height_selector12.json`, `height_selector12_expanded.json`, `height_selector14.json`, `height_selector14_expanded.json`
- `83-polynomial-shears/calibration/`: `LICENSE.ProveIt`, `NOTICE.source63.md`, `README.md`, `SOURCE_PINS.json`
- `83-polynomial-shears/integer/`: `BINDING.json`, `BUILD_CHECKS.json`, `INDEPENDENT_CHECKS.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `section.tex`
- `83-polynomial-shears/integer/forms/`: `centered23_degree10.json`, `pivot18_degree88.json`, `pivot19_degree32.json`, `pivot20_degree20.json`, `pivot21_degree16.json`
- `83-polynomial-shears/integer/upstream/`: `guards__PROOF.md`, `joint__COMPACT_BASE24.json`, `joint__PROOF.md`, `joint__joint19_degree88.json`, `joint__joint20_degree32.json`, `joint__joint21_degree20.json`, `joint__joint22_degree16.json`, `joint__joint25_octic.json`
- `83-polynomial-shears/integer/upstream/licenses/`: `upstream__determinant__LICENSE`, `upstream__determinant__NOTICE.md`, `upstream__residue__LICENSE`, `upstream__residue__NOTICE.md`, `upstream__residue__dependencies__LICENSE.ProveIt`, `upstream__residue__dependencies__licenses__LICENSE-source57`, `upstream__residue__dependencies__licenses__LICENSE.ProveIt`, `upstream__residue__dependencies__licenses__LICENSE.Wade`, `upstream__residue__dependencies__licenses__NOTICE-K215.md`, `upstream__residue__dependencies__licenses__NOTICE-normalized-source.txt`, `upstream__residue__dependencies__licenses__NOTICE-source25.md`, `upstream__residue__dependencies__licenses__NOTICE-source34.md`, `upstream__residue__dependencies__licenses__NOTICE-source57.md`
- `83-polynomial-shears/norm10/`: `INDEPENDENT_AUDIT.json`, `METRICS.json`, `README.md`, `ROOT_CERTIFICATES.json`, `SOURCE_PINS.json`, `VERIFICATION.json`, `audit_independent.py`, `build.py`, `integer10_cubic.json`, `integer10_linear.json`, `integer10_sixterm.json`, `verify.py`
- `83-polynomial-shears/norm10/data/`: `code.json`, `kernels.json`
- `83-polynomial-shears/norm10/licenses/`: `LICENSE`, `LICENSE.Round11`, `LICENSE.Wade`, `NOTICE-K215.md`
- `83-polynomial-shears/norm10/upstream/`: `NOTICE.R11.md`, `OBJECT_ZFC.md`, `OPTIMIZED_POWER_PLAN.json`, `PACKING_H1868_PROOF.md`, `SATURATED_LUCAS_PROOF.md`, `integer10.json`
- `83-polynomial-shears/positive11/`: `ALGEBRA_AUDIT.json`, `COEFFICIENT_REBUILD.json`, `DOUBLE_CENTER_CERTIFICATE.json`, `INDEPENDENT_AUDIT.json`, `INDEPENDENT_REVIEW.md`, `LICENSE.upstream`, `NOTICE.md`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `audit.py`, `build.py`, `p11_positive_degree211.json`, `rebuild_coefficients.py`, `section.tex`, `verify.py`
- `83-polynomial-shears/positive11/coefficients/`: `ACTIVE_BINDING.json`
- `83-polynomial-shears/positive11/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `83-polynomial-shears/positive11/native_recipe/`: `NOTICE-upstream.md`
- `83-polynomial-shears/positive11/upstream/`: `CENTERED_PROOF.md`, `degree277_PROOF.md`, `p11_positive_degree257.json`
- `84-radical-residue/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PDF_QA.json`, `README.md`, `VERIFICATION.json`, `report.pdf`, `report.tex`, `verify_all.py`
- `84-radical-residue/audit/`: `MATHEMATICAL_AUDIT.md`, `README.md`, `audit_summary.json`
- `84-radical-residue/integer/`: `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `circuit.py`, `independent_review.py`, `section17.tex`, `verify.py`
- `84-radical-residue/integer/certificates/`: `BUILD.json`, `CIRCUITS.json`, `COMPACT_BASE18.json`, `INDEPENDENT_REVIEW.json`, `VERIFY.json`, `VERIFY_OPTIMIZED.json`
- `84-radical-residue/integer/coefficients/`: `BINDING.json`
- `84-radical-residue/integer/forms/`: `center18_degree80.json`, `center18_degree80_dag.json`, `norm17_degree110.json`, `norm17_degree110_dag.json`, `norm17_degree112.json`, `norm17_degree112_dag.json`, `pivot18_degree88.json`, `pivot19_degree32.json`, `pivot20_degree20.json`, `pivot21_degree16.json`
- `84-radical-residue/integer/upstream/`: `guards__COEFFICIENT_BINDING.json`, `joint__COMPACT_BASE24.json`, `joint__PROOF.md`, `joint__joint19_degree88.json`, `joint__joint20_degree32.json`, `joint__joint21_degree20.json`, `joint__joint22_degree16.json`
- `84-radical-residue/integer/upstream/licenses/upstream/determinant/`: `LICENSE`, `NOTICE.md`
- `84-radical-residue/integer/upstream/licenses/upstream/residue/`: `LICENSE`, `NOTICE.md`
- `84-radical-residue/integer/upstream/licenses/upstream/residue/dependencies/`: `LICENSE.ProveIt`
- `84-radical-residue/integer/upstream/licenses/upstream/residue/dependencies/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `84-radical-residue/ten_positive/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `PROOF.md`, `SOURCE_PINS.json`, `build.py`, `independent_check.py`, `local_checks.py`, `rebuild_coefficients.py`
- `84-radical-residue/ten_positive/coefficients/`: `BINDING.json`, `UPSTREAM_BINDING.json`
- `84-radical-residue/ten_positive/generated/`: `COEFFICIENT_CHECKS.json`, `INDEPENDENT_CHECKS.json`, `LOCAL_CHECKS.json`, `p10_natural.json`, `p10_positive.json`
- `84-radical-residue/ten_positive/upstream/`: `OBJECT_ZFC.md`, `SIZE_REDUCTION.md`, `STATUS.md`, `k215_transitions.json`
- `84-radical-residue/ten_positive/upstream/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `85-saturation-projection/`: `LICENSE`, `MANIFEST.sha256`, `Makefile`, `README.md`, `make_archive.py`, `metrics.tex`, `report.pdf`, `report.tex`, `verify.py`
- `85-saturation-projection/alternative/`: `VERIFICATION.json`, `section.tex`, `verify.py`
- `85-saturation-projection/integer/`: `BUILD.json`, `LICENSE`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build.py`, `evaluate.py`, `section.tex`, `transport18_degree88.json`, `transport19_degree32.json`, `transport20_degree20.json`, `transport21_degree16.json`, `verify.py`
- `85-saturation-projection/integer/upstream/`: `DEPENDENCIES.md`, `INCOMING_PINS.json`
- `85-saturation-projection/integer/upstream/circuits/`: `BUILD.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `PROOF.md`, `README.md`, `build.py`, `check.py`, `joint19_degree88_dag.json`, `joint20_degree32_dag.json`, `joint21_degree20_dag.json`, `joint22_degree16_dag.json`, `joint23_degree12_dag.json`, `joint25_octic_dag.json`, `section.tex`
- `85-saturation-projection/integer/upstream/guards/`: `CHECK.json`, `COEFFICIENT_BINDING.json`, `DISPLAY_CHECK.json`, `METRICS.json`, `PROOF.md`, `README.md`, `UPSTREAM_COPY_RECEIPT.json`, `build.py`, `build_coefficients.py`, `check.py`, `check_displayed.py`, `cone26_octic.json`, `cone31_sextic.json`, `cone37_quartic_affine.json`, `cone37_quartic_direct.json`, `determinant26_octic.json`, `determinant31_sextic.json`, `determinant37_quartic_affine.json`, `determinant37_quartic_direct.json`, `section.tex`
- `85-saturation-projection/integer/upstream/guards/upstream/determinant/`: `LICENSE`, `NOTICE.md`
- `85-saturation-projection/integer/upstream/guards/upstream/residue/`: `LICENSE`, `NOTICE.md`
- `85-saturation-projection/integer/upstream/guards/upstream/residue/dependencies/`: `LICENSE.ProveIt`
- `85-saturation-projection/integer/upstream/guards/upstream/residue/dependencies/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `85-saturation-projection/integer/upstream/joint/`: `BUILD_CHECK.json`, `CHECK_normal.json`, `CHECK_optimized.json`, `COMPACT_BASE24.json`, `PROJECTION_BUILD.json`, `PROJECTION_CHECK_normal.json`, `PROJECTION_CHECK_optimized.json`, `PROOF.md`, `README.md`, `SOURCE_PIN.json`, `build.py`, `build_projections.py`, `check.py`, `check_projections.py`, `joint19_degree88.json`, `joint20_degree32.json`, `joint21_degree20.json`, `joint22_degree16.json`, `joint23_degree12.json`, `joint23_degree12_eliminate_I.json`, `joint24_degree12.json`, `joint25_octic.json`, `section.tex`
- `85-saturation-projection/integer/upstream/joint/upstream/`: `determinant26_octic.json`
- `85-saturation-projection/nine/`: `COEFFICIENT_RECONSTRUCTION.json`, `FIXED_RECONSTRUCTION.json`, `METRICS.json`, `PROOF.md`, `RADICAL_METRICS.json`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `build_radical.py`, `discover_radical.py`, `radical_P.json`, `radical_P_shifted.json`, `radical_defect.json`, `radical_defect_shifted.json`, `radical_meta.json`, `radical_upper_P.json`, `radical_upper_defect.json`, `radical_upper_defect_shifted.json`, `reconstruct_fixed.py`, `saturated_natural.json`, `saturated_positive.json`, `saturated_radical_natural.json`, `saturated_radical_positive.json`, `section.tex`, `verify.py`
- `85-saturation-projection/nine/coefficients/`: `COEFFICIENT_BINDING.json`, `COMPACT54_ARITHMETIC.md`, `COMPACT54_SEED.txt`
- `85-saturation-projection/nine/coefficients/compact_tuple/`: `COEFFICIENT_BINDING.json`
- `85-saturation-projection/nine/fixed/`: `BINDING.json`, `base_scale.bin.gz`, `c_1f49e78f6521d0fe.bin.gz`, `c_33afcc0215e266df.bin.gz`, `c_50b8a3599b18e0a9.bin.gz`, `c_a749e84ec6806d92.bin.gz`, `c_bd70eebd66b6d548.bin.gz`, `c_d048f06bd476e521.bin.gz`, `c_e24dea94f889b837.bin.gz`, `c_e3dd773f14077424.bin.gz`, `c_f69b40d0743298dc.bin.gz`, `threshold_6480184.bin.gz`
- `85-saturation-projection/nine/provenance/`: `GAP_CIRCUIT_RECIPE66.md`, `GAP_NINE_POLYNOMIAL66.md`, `LICENSE.59`, `NATIVE_CLAUSE54.md`, `NATIVE_CONVOLUTION54.md`, `NATIVE_SOURCE_WINDOW.md`, `NOTICE.md`, `NOTICE.tuple.md`, `OBJECT_ZFC.md`, `nine-NOTICE.md`, `nine-upstream-INHERITED_LICENSE`, `nine-upstream-INHERITED_NOTICE.md`, `parent-CONFIG.json`, `parent-HEIGHT_CERTIFICATE.json`, `parent-PROVENANCE.json`, `parent-README.md`, `verify_one_page_tuple54.py`
- `85-saturation-projection/nine/provenance/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `85-saturation-projection/nine/upstream/`: `gap2082_natural.json`, `gap2082_positive.json`
- `85-saturation-projection/provenance/`: `BASELINE.json`, `DIRECT_INPUTS.json`, `DiophantineConsistency-OBJECT_ZFC.md`, `DiophantineConsistency-README.md`, `DiophantineConsistency-SIZE_REDUCTION.md`, `gap2082-shared-products-README.md`
- `85-saturation-projection/verification/`: `PDF_QA.json`, `RELEASE_CHECKS.json`, `SATURATION_INDEPENDENT_REVIEW.md`, `SEMANTIC_DEPENDENCIES_REVIEW.md`
- `86-saturated-certificates/`: `CANDIDATES.json`, `COEFFICIENT_COSTS.json`, `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PROOF_STATUS.md`, `README.md`, `report.pdf`, `report.tex`, `verify_all.py`
- `86-saturated-certificates/integer/`: `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `negative_controls.py`, `polynomial.py`, `section.tex`, `verify.py`
- `86-saturated-certificates/integer/certificates/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `NEGATIVE_CONTROLS.json`, `NORMAL_STDOUT.json`, `OPTIMIZED_STDOUT.json`, `VERIFIED.json`, `VERIFIED_NORMAL.json`, `VERIFIED_OPTIMIZED.json`
- `86-saturated-certificates/integer/circuits/`: `integer16_degree184.json`, `integer16_degree192.json`, `integer17_degree88.json`, `integer23_degree10.json`
- `86-saturated-certificates/integer/coefficients/`: `BINDING.json`
- `86-saturated-certificates/integer/equations/`: `integer16_degree184.json`, `integer16_degree192.json`, `integer17_degree88.json`, `integer23_degree10.json`
- `86-saturated-certificates/integer/licenses/`: `LICENSE-source57`, `LICENSE.Current.ProveIt`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE-source64.md`, `source71_LICENSE`, `source71_NOTICE.md`
- `86-saturated-certificates/integer/upstream/`: `NATIVE_PELL_STEP_DOWN.md`, `joint_COMPACT_BASE24.json`, `joint_PROOF.md`, `joint_joint19_degree88.json`, `quartic37.json`, `structural_round11_PROOF.md`
- `86-saturated-certificates/nine/`: `METRICS.json`, `README.md`, `build.py`, `poly.py`, `section.tex`, `verify.py`, `verify_majorant.py`
- `86-saturated-certificates/nine/baseline/compact2082/`: `README.md`, `parent.json`
- `86-saturated-certificates/nine/baseline/compact2082/coefficients/`: `COEFFICIENT_BINDING.json`
- `86-saturated-certificates/nine/baseline/compact2082/coefficients/compact_tuple/`: `COEFFICIENT_BINDING.json`
- `86-saturated-certificates/nine/baseline/compact2082/fixed/`: `BINDING.json`, `base_scale.bin.gz`, `c_1f49e78f6521d0fe.bin.gz`, `c_33afcc0215e266df.bin.gz`, `c_50b8a3599b18e0a9.bin.gz`, `c_a749e84ec6806d92.bin.gz`, `c_bd70eebd66b6d548.bin.gz`, `c_d048f06bd476e521.bin.gz`, `c_e24dea94f889b837.bin.gz`, `c_e3dd773f14077424.bin.gz`, `c_f69b40d0743298dc.bin.gz`, `threshold_6480184.bin.gz`
- `86-saturated-certificates/nine/baseline/compact2082/provenance/`: `LICENSE.59`, `NOTICE.md`, `NOTICE.tuple.md`, `nine-NOTICE.md`, `nine-upstream-INHERITED_LICENSE`, `nine-upstream-INHERITED_NOTICE.md`
- `86-saturated-certificates/nine/baseline/compact2082/provenance/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `86-saturated-certificates/nine/baseline/h1868/`: `PROOF.md`, `check.py`
- `86-saturated-certificates/nine/certificates/`: `FULL_NINE_SOUNDNESS.md`, `FULL_RADICAL_H1868_AUDIT.md`, `H1868_DEGREE_CHECKS.json`, `HORNER_CHOICES.json`, `SATURATED_POSITIVE_PELL_AUDIT.md`, `SATURATION_CHECKS.json`, `VERIFY_NORMAL.json`, `audit_h1868_degree.py`, `check_saturation.py`
- `86-saturated-certificates/nine/data/`: `code.json`, `correction.json`, `kernels.json`, `saturated_P.json`, `saturated_corrected_P.json`, `saturated_corrected_certificate.json`, `saturated_defect.json`
- `86-saturated-certificates/nine/equations/`: `compact2082_simple.json`, `h1868_complete.json`, `h1868_simple.json`
- `86-saturated-certificates/nine/fixed/h1868/`: `BINDING.json`
- `86-saturated-certificates/nine/licenses/`: `LICENSE-radical-parent`, `LICENSE.Source65`, `LICENSE.Source71`, `NOTICE-radical-parent.md`
- `86-saturated-certificates/nine/native_original31/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `86-saturated-certificates/positive11/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `build.py`, `p11_positive_degree213.json`, `section.tex`, `verify.py`
- `86-saturated-certificates/positive11/coefficients/`: `ACTIVE_BINDING.json`
- `86-saturated-certificates/positive11/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `86-saturated-certificates/positive11/provenance/`: `INDEPENDENT_REVIEW.md`, `INPUT_SHA256.json`, `joint_guards_CENTERED_PROOF.md`, `joint_guards_PROOF.md`, `joint_guards_build_centered.py`, `upstream_NOTICE.md`
- `86-saturated-certificates/provenance/`: `REPOSITORY_STATUS.md`, `SIZE_REDUCTION_AT_PIN.md`, `SOURCES.json`
- `86-saturated-certificates/verification/`: `PDF_QA.json`, `RELEASE_CHECKS_BOTH.json`, `integer_normal.stdout.txt`, `integer_optimized.stdout.txt`, `nine_independent_normal.stdout.txt`, `nine_independent_optimized.stdout.txt`, `nine_normal.stdout.txt`, `nine_optimized.stdout.txt`, `pell_saturation_normal.stdout.txt`, `pell_saturation_optimized.stdout.txt`, `positive11_normal.stdout.txt`, `positive11_optimized.stdout.txt`
- `87-direct-centered-round12/`: `COMPACT_STORAGE.json`, `DEPENDENCIES.md`, `LICENSE.NEW`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `REPLAY.json`, `RUNTIME.json`, `negative_controls.py`, `verify.py`
- `87-direct-centered-round12/checks/`: `FULL_REPLAY.json`, `NEGATIVE_CONTROLS.json`, `PDF_QA.json`, `RELEASE_VALIDATION.json`
- `87-direct-centered-round12/direct/`: `CLEAN_REPLAY.json`, `COMPACT_RELEASE_WHITELIST.json`, `README.md`, `REPLAY_COMMANDS.json`, `SOURCE_PINS.json`, `section.tex`
- `87-direct-centered-round12/direct/fixed_base/`: `CHECKS.json`, `LIVENESS.json`, `README.md`, `REPLAY_SHA256.json`, `build_direct.py`, `check_direct.py`, `circuit.json`, `equation_integer.json`, `reduce_affine.py`, `residuals_affine.json`, `row_source.json`, `summary.json`, `summary_affine.json`, `summary_integer.json`, `verify_replay.py`
- `87-direct-centered-round12/direct/sources/`: `ArithmeticRepresentation.lean`, `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `DivisionRepresentation.lean`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `QuarticCompiler.lean`, `RemainderRepresentation.lean`, `Representation.lean`
- `87-direct-centered-round12/direct_audit/`: `FINAL_AUDIT.json`, `MATHEMATICAL_AUDIT.md`, `NEGATIVE_CHECKS.json`, `REPLAY_COMMANDS.json`, `SOURCE_PINS.json`, `check_affine.py`, `negative_controls.py`
- `87-direct-centered-round12/direct_audit/fixed_base/`: `AFFINE_CHECK.json`, `COMPOSITION_CHECK.json`, `HORN_CHECK.json`, `INTERFACE_CHECK.json`, `SOURCE_BINDING_CHECK.json`, `STRUCTURE_CHECK.json`, `check_composition.py`, `check_horn.py`, `check_interfaces.py`, `check_source_binding.py`, `check_structure.py`
- `87-direct-centered-round12/inherited/round11/inherited/round10/integer_licenses/`: `LICENSE.SignAndNorm`, `LICENSE.Source34`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE.SignAndNorm.md`, `NOTICE.Source34.md`
- `87-direct-centered-round12/inherited/round11/packing/certified/`: `CHECKS.json`, `PROOF.md`, `check.py`, `kernels.json`, `layout.json`
- `87-direct-centered-round12/licenses/`: `LICENSE.ProveIt`
- `87-direct-centered-round12/low_degree/`: `BINDING.json`, `CHECK_NORMAL.json`, `CHECK_OPTIMIZED.json`, `FILE_HASHES.json`, `PROOF.md`, `README.md`, `SOURCE_HASHES.json`, `UPSTREAM_FETCH_PROVENANCE.json`, `build.py`, `check.py`, `integer18_degree88.json`, `integer19_degree32.json`, `integer20_degree20.json`, `integer20_degree20_free_scale.json`, `integer21_degree16.json`, `section.tex`
- `87-direct-centered-round12/low_degree/inherited/`: `CENTERED_NORM_PROOF.md`, `JOINT_PROJECTION_PROOF.md`, `ROUND11_PROOF.md`, `degree12_24.json`
- `87-direct-centered-round12/low_degree/inherited/round11_dependencies/`: `source71_LICENSE`, `source71_NOTICE.md`
- `87-direct-centered-round12/low_degree_supplement/`: `FILE_HASHES.json`, `LIBRARY_CHECK.json`, `LIBRARY_CHECK_OPTIMIZED.json`, `REVIEW.md`, `check_library.py`
- `87-direct-centered-round12/norm/`: `BASELINE_PROOF.md`, `CHECKS.json`, `METRICS_center0.json`, `METRICS_center1.json`, `METRICS_center2.json`, `METRICS_polar.json`, `NOTICE.md`, `OPTIMIZED_POWER_PLAN.json`, `PROOF.md`, `README.md`, `REBUILD_CHECKS.json`, `REPLAY_COMMANDS.json`, `build.py`, `check.py`, `independent_formula.py`, `independent_formula_short_guard.py`, `integer10_center0.json`, `integer10_center1.json`, `integer10_center2.json`, `integer10_polar.json`, `section.tex`
- `87-direct-centered-round12/norm/data/`: `code.json`, `kernels.json`
- `87-direct-centered-round12/norm/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `87-direct-centered-round12/norm_audit/`: `AUDIT.md`, `INDEPENDENT_CHECKS.json`, `INDEPENDENT_CHECKS_OPTIMIZED.json`, `check_independent.py`, `section.tex`
- `87-direct-centered-round12/positive/`: `CHECKS.json`, `PROOF11.md`, `PROOF12.md`, `README.md`, `build.py`, `check.py`, `p11_degree211.json`, `p12_degree70.json`, `section.tex`
- `87-direct-centered-round12/positive/interfaces/`: `incoming_report.tex`, `p11_degree277.json`, `p12_degree78.json`
- `87-direct-centered-round12/positive/native/`: `NOTICE-upstream.md`
- `87-direct-centered-round12/positive/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `87-direct-centered-round12/report/`: `ConZFC_Round12.pdf`, `ConZFC_Round12.tex`, `build.sh`
- `87-direct-centered-round12/review/`: `FETCH_LEDGER.json`, `LITERAL_COUNTS.json`, `ROUND12_REVIEW.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/`: `LICENSE`, `NOTICE.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/certificates/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/inherited/determinant71/`: `NOTICE.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/nine_full_radical/`: `LICENSE`, `NOTICE.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/nine_full_radical/upstream/31-sun10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/nine_full_radical/upstream/71-determinant-guards/nine_positive/`: `LICENSE`, `NOTICE.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/positive/`: `LICENSE`, `NOTICE.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/positive/native/`: `NOTICE-upstream.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/positive/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/report/`: `report.tex`
- `87-direct-centered-round12/review/library/pell_congruences/con_zfc_pell_congruences_2026-10-23/transport/`: `PROOF.md`, `degree20_20_rank_register.json`, `degree28_19.json`, `degree32_18.json`, `degree88_17.json`
- `87-direct-centered-round12/small_audit/`: `CHECKS.json`, `CHECKS_NORMAL.json`, `CHECKS_OPTIMIZED.json`, `REPORT.md`, `check.py`
- `87-direct-centered-round12/source/short_guard/`: `CHECKS.json`, `PROOF.tex`, `check.py`, `layout.json`
- `88-root-fusion13/`: `FUTURE_WORK.md`, `LICENSE`, `MANIFEST.json`, `README.md`, `RELEASE.json`, `build_equations.py`, `five_square_norm.py`
- `88-root-fusion13/coefficients/`: `BINDING.json`
- `88-root-fusion13/companions/quotient_fusion/`: `METRICS.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `quotient18_transport.json`, `quotient19_transport.json`, `quotient20.json`, `quotient20_transport.json`, `verify.py`
- `88-root-fusion13/equations/`: `METRICS.json`, `SCHEMA.md`, `norm13_crt_degree1088.json`, `norm13_degree1392.json`, `norm13_degree1408.json`, `norm14_degree696.json`, `norm14_degree792.json`, `norm15_degree344.json`
- `88-root-fusion13/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `88-root-fusion13/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `88-root-fusion13/provenance/upstream_ordinary/`: `SOURCES.json`
- `88-root-fusion13/report/`: `crt1088.tex`, `report.pdf`, `report.tex`
- `88-root-fusion13/verification/`: `CLEARED_EXACT_AUDIT.json`, `CRT_AUDIT.json`, `EXACT_AUDIT.json`, `INTEGRATED_AUDIT.json`, `INTEGRATED_AUDIT_OPTIMIZED.json`, `PDF_QA.json`, `RELEASE_AUDIT.json`, `RELEASE_AUDIT_OPTIMIZED.json`, `audit.py`, `audit_cleared.py`, `check_crt.py`, `check_integrated.py`, `exact_polynomial.py`, `five_square_norm_expanded.json`, `verify_release.py`
- `89-shared-certificates/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PROVENANCE.md`, `README.md`, `VERIFICATION.json`, `verify.py`
- `89-shared-certificates/coordinate_family/`: `COEFFICIENT_BINDING.json`, `COORDINATE_AUDIT.normal.json`, `COORDINATE_AUDIT.optimized.json`, `COORDINATE_PROOF.md`, `COORDINATE_VERIFICATION.json`, `INCOMING_PINS.json`, `LAYOUT_AND_PORTABILITY.json`, `MANIFEST.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build_coordinate_family.py`, `build_family.py`, `check_coordinate_maps.py`, `coordinate_audit.md`, `coordinate_section.tex`, `incoming_joint25.json`
- `89-shared-certificates/coordinate_family/comparison/`: `ZFC_Diophantine_Joint_Guards_2026-10-24__README.md`, `con-zfc-budget-and-centering-2026-10-23__README.md`, `con-zfc-centered-pell-norms__README.md`, `con-zfc-radical-guard-descent-2026-10-23__README.md`, `report__report.tex`, `round11__README.md`
- `89-shared-certificates/coordinate_family/equations/`: `compact_octic25.json`, `coordinate19_degree40.json`, `coordinate20_degree18.json`, `coordinate21_degree16.json`, `degree16_23.json`, `dodecic24.json`, `octic25.json`, `octic26_unmerged.json`, `quartic37.json`, `sextic31.json`
- `89-shared-certificates/coordinate_family/upstream/licenses/`: `LICENSE`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE71.md`
- `89-shared-certificates/direct/`: `AUDIT.normal.json`, `AUDIT.optimized.json`, `AUDIT.small_height.normal.json`, `AUDIT.small_height.optimized.json`, `BUILD.json`, `CALCULUS_AUDIT.json`, `LITERAL_AUDIT.json`, `LITERAL_AUDIT.optimized.json`, `POWER_GRAPH_AUDIT.json`, `README.md`, `SOURCE_AUDIT.json`, `audit_calculus.py`, `audit_literal.py`, `audit_power_graph.py`, `audit_source.py`, `build_equation.py`, `check_equation.py`, `direct_calculus.py`, `equation.json`, `expanded_polynomial.json`, `shared_crt_audit.md`, `wire_eliminated_source.json`
- `89-shared-certificates/direct/provenance/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `89-shared-certificates/direct/small_height/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`
- `89-shared-certificates/provenance/`: `SOURCES.json`, `new_incoming_comparison.md`
- `89-shared-certificates/report/`: `LAYOUT_QA.json`, `calculus.tex`, `crt.tex`, `integer.tex`, `primitives.tex`, `report.pdf`, `report.tex`
- `90-fixed-prime-radicals/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `verify.py`
- `90-fixed-prime-radicals/checks/`: `ADAPTER_CHECKS.json`, `ROOT_VERIFICATION.json`, `ROOT_VERIFICATION_OPTIMIZED.json`
- `90-fixed-prime-radicals/code/`: `check_adapters.py`
- `90-fixed-prime-radicals/coefficients/`: `BINDING.json`, `VERIFICATION.json`, `verify.py`
- `90-fixed-prime-radicals/forms/`: `COMPACT15_CHECKS.json`, `COMPACT15_PROOF.md`, `DEGREE_PROOF.md`, `METRICS.json`, `METRICS15.json`, `NORM_DAG_CHECKS.json`, `PROOF15.md`, `SOURCE_PIN.json`, `VERIFICATION.json`, `build15_compact.py`, `build_forms.py`, `check_norm_dag.py`, `generic_three_quadratic_norm.json`, `integer13_degree1392.json`, `integer13_degree1408.json`, `integer14_degree652.json`, `integer14_degree664.json`, `integer14_degree700.json`, `integer14_degree748.json`, `integer15_degree214.json`, `norm4_cleared_dag.json`, `norm5_cleared_dag.json`, `norm_dag.py`, `verify_final_forms.py`
- `90-fixed-prime-radicals/forms/coefficients/`: `BINDING.json`
- `90-fixed-prime-radicals/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `90-fixed-prime-radicals/proofs/`: `INDEPENDENT_REVIEW13.md`, `INDEPENDENT_REVIEW15.md`, `NORMALIZATION.md`, `PENTAGONAL_GUARD.md`
- `90-fixed-prime-radicals/report/`: `report.pdf`, `report.tex`
- `90-fixed-prime-radicals/upstream/`: `ALTERNATIVE_ENCODINGS.md`, `BASELINE_AUDIT.md`, `WAVE10_REVIEW.md`
- `90-fixed-prime-radicals/upstream/calibration/`: `NOTICE.source63.md`, `README.md`, `SOURCE_PINS.json`
- `90-fixed-prime-radicals/upstream/inherited/determinant71/`: `NOTICE.md`
- `90-fixed-prime-radicals/upstream/transport/`: `PROOF.md`, `degree88_17.json`
- `91-prime-separation13/`: `LICENSE`, `NOTICE.md`, `PDF_QA.json`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `VERIFICATION_NORMAL.json`, `build_pass2.txt`, `build_pass3.txt`, `report.pdf`, `report.tex`, `verify_all.py`
- `91-prime-separation13/independent_audit/`: `COMPACT_NORM_CHECK.json`, `FOUR_ROOT_REVIEW.md`, `PRIMARY_FORMULA_CHECK.json`, `check_compact_norms.py`, `check_primary_formula.py`
- `91-prime-separation13/inherited/`: `PARENT_SOURCE_PROVENANCE.json`, `README.md`, `degree88_17.json`, `source70_integer_section.tex`, `source71_report.tex`
- `91-prime-separation13/inherited/calibration/`: `LICENSE.ProveIt`, `NOTICE.source63.md`, `README.md`, `SOURCE_PINS.json`
- `91-prime-separation13/inherited/determinant71/`: `NOTICE.md`
- `91-prime-separation13/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `91-prime-separation13/new_integer_compact/`: `BUILD_METRICS.json`, `build.py`, `five_root_integer13_compact.json`, `fixed3_crt_integer16_compact.json`, `four_root_integer14_compact.json`, `three_root_integer15_compact.json`
- `91-prime-separation13/new_integer_compression/`: `BUILD_METRICS.json`, `DEGREE_LOWER_CERTIFICATES.json`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `build.py`, `check_degrees.py`, `circuit.py`, `five_root_integer13.json`, `fixed3_crt_integer16.json`, `four_root_integer14.json`, `three_root_integer15.json`
- `91-prime-separation13/new_integer_compression/coefficients/`: `BINDING.json`
- `91-prime-separation13/reviews/`: `FIVE_ROOT_INTEGER13_REVIEW.md`, `FOUR_ROOT_INTEGER14_REVIEW.md`, `VALUATION_SEPARATION_REVIEW.md`
- `91-prime-separation13/ten_integer/`: `CHECKS_cubic.json`, `CHECKS_linear.json`, `CHECKS_predecessor.json`, `CHECKS_sixterm.json`, `LICENSE.NEW`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `SUMMARY.json`, `VERIFICATION_NORMAL.json`, `VERIFICATION_OPTIMIZED.json`, `VERIFICATION_RUNS.json`, `integer10_cubic.json`, `integer10_linear.json`, `integer10_predecessor.json`, `integer10_sixterm.json`, `optimize.py`, `optimize_shears.py`, `verify.py`
- `91-prime-separation13/ten_integer/provenance/`: `LICENSE.NEW`, `MANIFEST.sha256`, `NOTICE.md`, `PROVENANCE.json`, `report.pdf`, `report.tex`
- `91-prime-separation13/ten_integer/provenance/alternative/`: `section.tex`
- `91-prime-separation13/ten_integer/provenance/calibration/`: `LICENSE.ProveIt`, `NOTICE.source63.md`, `README.md`, `SOURCE_PINS.json`
- `91-prime-separation13/ten_integer/provenance/integer/`: `section.tex`
- `91-prime-separation13/ten_integer/provenance/positive11/`: `section.tex`
- `91-prime-separation13/ten_integer/upstream/`: `INDEPENDENT_AUDIT.json`, `METRICS.json`, `README.md`, `ROOT_CERTIFICATES.json`, `SOURCE_PINS.json`, `VERIFICATION.json`, `audit_independent.py`, `build.py`, `integer10_cubic.json`, `integer10_linear.json`, `integer10_sixterm.json`, `verify.py`
- `91-prime-separation13/ten_integer/upstream/data/`: `code.json`, `kernels.json`
- `91-prime-separation13/ten_integer/upstream/licenses/`: `LICENSE`, `LICENSE.Round11`, `LICENSE.Wade`, `NOTICE-K215.md`
- `91-prime-separation13/ten_integer/upstream/upstream/`: `NOTICE.R11.md`, `OBJECT_ZFC.md`, `OPTIMIZED_POWER_PLAN.json`, `PACKING_H1868_PROOF.md`, `SATURATED_LUCAS_PROOF.md`, `integer10.json`
- `92-parity-norms/`: `AUDIT.json`, `COMPACT_INDEPENDENT_AUDIT.json`, `COMPACT_KERNEL_AUDIT.json`, `COMPACT_METRICS.json`, `COMPACT_NORM_REVIEW.md`, `DEGREE_CERTIFICATES.json`, `GRAPH_AUDIT.json`, `LICENSE`, `NORM_FAMILY_AUDIT.json`, `NORM_FAMILY_METRICS.json`, `NOTICE.md`, `PARITY_MERGER_REVIEW.md`, `PDF_QA.json`, `PROOF.md`, `PROOF15.md`, `README.md`, `RELEASE_VERIFICATION.json`, `SHIFT_AUDIT.json`, `SOURCE_PROVENANCE.json`, `THIRTEEN_MATHEMATICAL_REVIEW.md`, `abstract_norm5_dag.json`, `audit.py`, `audit_compact_kernel.py`, `audit_norm_family.py`, `audit_shift.py`, `build.py`, `build_norm_family.py`, `centered16_sos.json`, `centered16_sos_dag.json`, `centered16_unit_product.json`, `centered16_unit_product_dag.json`, `compact_norm.py`, `independent_checks.py`, `independent_compact_audit.py`, `independent_graph_audit.py`, `independent_proof_audit.md`, `norm4_expanded.json`, `norm4_kernel.json`, `norm5_expanded.json`, `norm5_kernel.json`, `parity13_direct.json`, `parity13_direct_dag.json`, `parity13_shifted.json`, `parity13_shifted_dag.json`, `parity14_sos.json`, `parity14_sos_dag.json`, `parity14_unit_product.json`, `parity14_unit_product_dag.json`, `parity15_sos.json`, `parity15_sos_dag.json`, `parity15_unit_product.json`, `parity15_unit_product_dag.json`, `parity16_sos.json`, `parity16_sos_dag.json`, `parity16_unit_product.json`, `parity16_unit_product_dag.json`, `results.json`, `verify_release.py`
- `92-parity-norms/coefficients/`: `BINDING.json`, `VERIFICATION.json`, `verify.py`
- `92-parity-norms/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `92-parity-norms/parent/`: `degree88_17.json`
- `92-parity-norms/provenance/`: `forms-README.md`
- `92-parity-norms/report/`: `parity-norms.pdf`, `parity-norms.tex`
- `92-parity-norms/upstream/pell-congruences-source/`: `LICENSE`, `NOTICE.md`, `README.md`, `SOURCE_PROVENANCE.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `verify.py`
- `92-parity-norms/upstream/pell-congruences-source/certificates/`: `ALTERNATIVE_ROUTES_REVIEW.md`, `INDEPENDENT_INTEGER_AUDIT.json`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `INTEGER_CHECKS.json`, `NINE_INDEPENDENT_REVIEW.md`, `PDF_QA.json`, `RANK_REGISTER_REVIEW.md`, `crt_degree16_24_degree.json`, `crt_degree26_22_degree.json`, `crt_degree26_23_degree.json`, `crt_degree28_21_degree.json`, `crt_degree44_20_degree.json`, `degree10_25_degree.json`, `degree12_23_degree.json`, `degree20_22_degree.json`, `degree26_20_degree.json`, `degree32_19_degree.json`, `octic26_degree.json`, `quartic37_degree.json`, `quartic37_direct_degree.json`, `sextic31_degree.json`
- `92-parity-norms/upstream/pell-congruences-source/coefficients/`: `BINDING.json`, `VERIFICATION.json`, `verify.py`
- `92-parity-norms/upstream/pell-congruences-source/inherited/determinant71/`: `NOTICE.md`
- `92-parity-norms/upstream/pell-congruences-source/integer/`: `audit.py`, `build.py`, `crt_degree16_24.json`, `crt_degree26_22.json`, `crt_degree26_23.json`, `crt_degree28_21.json`, `crt_degree44_20.json`, `degree10_25.json`, `degree12_23.json`, `degree20_22.json`, `degree26_20.json`, `degree32_19.json`, `octic26.json`, `polynomial.py`, `quartic37.json`, `quartic37_direct.json`, `sextic31.json`
- `92-parity-norms/upstream/pell-congruences-source/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `92-parity-norms/upstream/pell-congruences-source/nine_full_radical/`: `COEFFICIENT_RECONSTRUCTION.json`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `build_correction.py`, `check_laurent_cone.py`, `laurent9_positive.json`, `laurent_candidate.json`, `laurent_cone_certificate.json`, `laurent_correction_nopad_4JDbasis.json`, `laurent_symbolic.py`, `section.tex`, `verify.py`
- `92-parity-norms/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `92-parity-norms/upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/`: `LICENSE`, `NOTICE.md`
- `92-parity-norms/upstream/pell-congruences-source/positive/`: `AUDIT11.json`, `AUDIT12.json`, `LICENSE`, `NATIVE_FETCH.json`, `NOTICE.md`, `PROOF.md`, `UPSTREAM_FETCH.json`, `VERIFICATION.json`, `build11.py`, `build12.py`, `p11_positive_degree269.json`, `p12_positive_degree78.json`, `positive_reductions.tex`, `verify.py`, `verify11.py`, `verify12.py`
- `92-parity-norms/upstream/pell-congruences-source/positive/native/`: `NOTICE-upstream.md`
- `92-parity-norms/upstream/pell-congruences-source/positive/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `92-parity-norms/upstream/pell-congruences-source/report/`: `nine_section.tex`, `report.pdf`, `report.tex`
- `92-parity-norms/upstream/pell-congruences-source/transport/`: `PROOF.md`, `README.md`, `build_transport.py`, `check_transport.py`, `degree10_24.json`, `degree16_22.json`, `degree20_20_rank_register.json`, `degree28_19.json`, `degree32_18.json`, `degree88_17.json`
- `92-parity-norms/upstream/pell-congruences-source/transport/certificates/`: `DOMINATED_TRANSPORT_PROBES.json`, `INDEPENDENT_TRANSPORT_AUDIT.json`, `TRANSPORT_CHECKS.json`, `degree10_24_degree.json`, `degree16_22_degree.json`, `degree20_20_rank_register_degree.json`, `degree28_19_degree.json`, `degree32_18_degree.json`, `degree88_17_degree.json`
- `92-parity-norms/upstream/pell-congruences-source/transport/parents/`: `crt_degree44_20.json`, `degree10_25.json`, `degree12_23.json`, `degree20_22.json`, `degree26_20.json`, `degree32_19.json`, `octic26.json`, `quartic37.json`, `quartic37_direct.json`, `sextic31.json`
- `93-parity-pell-witnesses/`: `CANDIDATES.json`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RELEASE_CHECKS.json`, `build_report.py`, `verify.py`
- `93-parity-pell-witnesses/direct-quartic/`: `ARTIFACT_SHA256.json`, `README.md`, `REPLAY.json`, `SOURCE_PINS.json`, `UPSTREAM_MATHEMATICAL_AUDIT.md`, `UPSTREAM_SOURCE_PINS.json`, `affine_map.json`, `build_direct.py`, `circuit.json`, `equation.json`, `equation_affine.json`, `equation_integer.json`, `nonnegativity_residuals.json`, `normalization.tex`, `reduce_affine.py`, `replay.py`, `residuals.json`, `residuals_affine.json`, `row_source.json`, `summary.json`, `summary_affine.json`, `summary_integer.json`
- `93-parity-pell-witnesses/direct-quartic/audit/`: `AFFINE_CHECK.json`, `COMPOSITION_CHECK.json`, `HORN_CHECK.json`, `INTERFACE_CHECK.json`, `NORMALIZATION_CHECK.json`, `SOURCE_BINDING_CHECK.json`, `STRUCTURE_CHECK.json`, `check_affine.py`, `check_composition.py`, `check_horn.py`, `check_interfaces.py`, `check_normalization.py`, `check_source_binding.py`, `check_structure.py`
- `93-parity-pell-witnesses/direct-quartic/licenses/`: `LICENSE.ProveIt`
- `93-parity-pell-witnesses/direct-quartic/sources/`: `ArithmeticRepresentation.lean`, `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `DivisionRepresentation.lean`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `QuarticCompiler.lean`, `RemainderRepresentation.lean`, `Representation.lean`
- `93-parity-pell-witnesses/direct-quartic/upstream/`: `SHA256.json`, `build_direct.py`, `reduce_affine.py`, `summary_affine.json`, `summary_integer.json`
- `93-parity-pell-witnesses/integer-norms/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `INDEPENDENT_REVIEW.md`, `METRICS.json`, `MOD4_PROOF.md`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `UPSTREAM_PROOF.md`, `build.py`, `check.py`, `polynomial.py`, `upstream17.json`, `upstream_builder.py`
- `93-parity-pell-witnesses/integer-norms/circuits/`: `integer15_mod4_degree306.json`, `integer15_mod4_degree310.json`, `integer15_odd_degree306.json`, `integer15_odd_degree310.json`, `integer16_mod4_degree112.json`, `integer16_odd_degree112.json`
- `93-parity-pell-witnesses/integer-norms/coefficients/`: `BINDING.json`
- `93-parity-pell-witnesses/integer-norms/equations/`: `integer15_mod4_degree306.json`, `integer15_mod4_degree310.json`, `integer15_odd_degree306.json`, `integer15_odd_degree310.json`, `integer16_mod4_degree112.json`, `integer16_odd_degree112.json`
- `93-parity-pell-witnesses/integer-norms/independent_degree/`: `CHECKS.json`, `CHECKS_MOD4.json`, `NOTE.md`, `NOTE_MOD4.md`, `PARITY_AUDIT.md`, `audit.py`, `audit_mod4.py`, `ring.py`
- `93-parity-pell-witnesses/integer-norms/licenses/`: `LICENSE-source57`, `LICENSE.Current.ProveIt`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE-source64.md`, `source71_LICENSE`, `source71_NOTICE.md`
- `93-parity-pell-witnesses/integer20/`: `BUILD_CHECKS.json`, `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `build.py`, `check.py`, `circuit.json`, `equation.json`, `parent_ring.py`
- `93-parity-pell-witnesses/integer20/parent/`: `PROOF.md`, `README.md`, `VERIFY.normal.json`, `VERIFY.optimized.json`, `build.py`, `circuit.json`, `equation.json`
- `93-parity-pell-witnesses/integer20/parent/coefficients/`: `BINDING.json`
- `93-parity-pell-witnesses/integer20/parent/provenance/`: `PARENT_CIRCUIT_PROOF.md`, `PARENT_COEFFICIENT_BINDING.json`, `PARENT_PROOF.md`, `PINS.json`, `parent.json`, `parent_dag.json`
- `93-parity-pell-witnesses/provenance/`: `NATIVE_CALIBRATION52.md`, `OBJECT_ZFC.md`, `PROPOSAL_REVIEW_WAVE11.md`, `PROPOSAL_REVIEW_WAVE11_INTEGER.md`, `PROPOSAL_REVIEW_WAVE11_POSITIVE.md`, `SNAPSHOT.json`
- `93-parity-pell-witnesses/provenance/k215-calibration/`: `LICENSE.ProveIt`, `NOTICE.source63.md`, `README.md`, `SOURCE_PINS.json`
- `93-parity-pell-witnesses/provenance/saturated-parent/`: `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `negative_controls.py`, `polynomial.py`, `section.tex`, `verify.py`
- `93-parity-pell-witnesses/provenance/saturated-parent/certificates/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `NEGATIVE_CONTROLS.json`, `NORMAL_STDOUT.json`, `OPTIMIZED_STDOUT.json`, `VERIFIED.json`, `VERIFIED_NORMAL.json`, `VERIFIED_OPTIMIZED.json`
- `93-parity-pell-witnesses/provenance/saturated-parent/circuits/`: `integer16_degree184.json`, `integer16_degree192.json`, `integer17_degree88.json`, `integer23_degree10.json`
- `93-parity-pell-witnesses/provenance/saturated-parent/coefficients/`: `BINDING.json`
- `93-parity-pell-witnesses/provenance/saturated-parent/equations/`: `integer16_degree184.json`, `integer16_degree192.json`, `integer17_degree88.json`, `integer23_degree10.json`
- `93-parity-pell-witnesses/provenance/saturated-parent/licenses/`: `LICENSE-source57`, `LICENSE.Current.ProveIt`, `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE-source64.md`, `source71_LICENSE`, `source71_NOTICE.md`
- `93-parity-pell-witnesses/provenance/saturated-parent/upstream/`: `NATIVE_PELL_STEP_DOWN.md`, `joint_COMPACT_BASE24.json`, `joint_PROOF.md`, `joint_joint19_degree88.json`, `quartic37.json`, `structural_round11_PROOF.md`
- `93-parity-pell-witnesses/report/`: `con-zfc-parity-norms.pdf`, `con-zfc-parity-norms.tex`, `direct-normalization.tex`, `report.tex`
- `94-direct-projection7617/`: `LICENSE.NEW`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RUNTIME.json`, `SCHEMA.md`, `build.py`, `check_exact.py`, `check_signed_independent.py`, `polynomial.py`, `verify.py`
- `94-direct-projection7617/checks/`: `COMPARISON.json`, `DIRECT_FINAL_INDEPENDENT.json`, `DIRECT_FINAL_INDEPENDENT_OPTIMIZED.json`, `PDF_VISUAL_QA.json`, `RELEASE_VERIFY.json`, `REPLAY_CHECK.json`, `checkpoint9476_exact_check.json`, `checkpoint9476_metrics.json`
- `94-direct-projection7617/equations/`: `EXACT_CHECK.json`, `circuit_integer.json`, `equation_integer.json`, `residuals_integer.json`, `row_source.json`, `source_circuit_before_pruning.json`, `summary_integer.json`, `variable_map.json`
- `94-direct-projection7617/licenses/`: `LICENSE.ProveIt`
- `94-direct-projection7617/proofs/`: `INDEPENDENT_REVIEW.md`, `SIGNED_COMPILER.md`
- `94-direct-projection7617/provenance/`: `ARITHMETIC_SOURCE_PINS.json`, `BASELINE_INTEGER_METRICS.json`, `BASELINE_MATHEMATICAL_AUDIT.md`, `BASELINE_NOTICE.md`, `BASELINE_PINS.json`, `LOGICAL_SOURCE_PINS.json`
- `94-direct-projection7617/provenance/arithmetic/`: `ArithmeticRepresentation.lean`, `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `DivisionRepresentation.lean`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `QuarticCompiler.lean`, `RemainderRepresentation.lean`, `Representation.lean`
- `94-direct-projection7617/report/`: `ConZFC_Direct_Projection.pdf`, `ConZFC_Direct_Projection.tex`, `PDF_BUILD.json`, `build_report.py`, `metrics.tex`
- `94-direct-projection7617/source/`: `PREPROCESSING_PROOF.md`, `PROJECTION_CHECK.json`, `build_direct.py`, `check_projection.py`, `circuit.json`, `row_source.json`, `summary_circuit.json`
- `95-synchronized-certificates/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `report.pdf`, `report.tex`, `verify.py`
- `95-synchronized-certificates/code/`: `affine_contract.py`, `audit_factored_source.py`, `audit_shared_power.py`, `audit_shared_product.py`, `direct_source.py`, `direct_source_factored.py`, `make_integer.py`, `release.py`, `shared_index_power.py`, `shared_power.py`, `shared_product_power.py`, `synchronized_builder.py`, `verify_synchronized.py`
- `95-synchronized-certificates/equations/`: `CENSUS.json`
- `95-synchronized-certificates/equations/integer2088/`: `VERIFICATION.json`, `conversion_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `95-synchronized-certificates/equations/natural522/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `95-synchronized-certificates/equations/natural529/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `95-synchronized-certificates/equations/natural596/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `95-synchronized-certificates/equations/source895/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `macro_inventory.json`, `majorant_certificate.json`
- `95-synchronized-certificates/proofs/`: `contraction.md`, `factored_source.md`, `final_math_review.md`, `independent_mathematical_review.md`, `independent_structure_review.md`, `integer_guards.md`, `shared_indices.md`, `shared_powers.md`
- `95-synchronized-certificates/provenance/repository/`: `INCOMING_INDEX.json`, `PROPOSAL_REVIEW_DIRECT_C222_ROUND12.md`, `PROPOSAL_REVIEW_LATEST.md`, `README.md`
- `95-synchronized-certificates/provenance/upstream/`: `BUILD.json`, `LICENSE`, `NOTICE.md`, `README.md`, `audit_calculus.py`, `audit_source.py`, `build_equation.py`, `calculus.tex`, `crt.tex`, `direct_calculus.py`, `primitives.tex`, `wire_eliminated_source.json`
- `95-synchronized-certificates/provenance/upstream/calibration/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `95-synchronized-certificates/receipts/`: `pdf_qa.json`, `verification_normal.json`, `verification_optimized.json`
- `96-batched-certificates/`: `LICENSE`, `MANIFEST.json`, `PROVENANCE.json`, `README.md`, `RELEASE.json`, `verify.py`
- `96-batched-certificates/direct/`: `COMPONENT_AUDIT.normal.json`, `COMPONENT_AUDIT.optimized.json`, `LICENSE`, `PROVENANCE.json`, `README.md`, `audit_common_radix.py`, `build_common_radix.py`, `common_radix_section.tex`, `shared_frame_fixture.py`, `terminal_elimination.py`, `verify.py`, `verify_projection.py`
- `96-batched-certificates/direct/output/common_radix/`: `AUDIT.json`, `BUILD.json`, `construction_trace.json`, `equation.json`, `expanded_polynomial.json`
- `96-batched-certificates/direct/output/common_radix_offset/`: `AUDIT.json`, `BUILD.json`, `construction_trace.json`, `equation.json`, `expanded_polynomial.json`
- `96-batched-certificates/direct/output/compact667/`: `INDEPENDENT_PROJECTION.json`, `TERMINAL_ELIMINATION.json`, `equation.json`, `expanded_polynomial.json`, `terminal_elimination_certificate.json`
- `96-batched-certificates/direct/output/compact680/`: `TERMINAL_ELIMINATION.json`, `equation.json`, `expanded_polynomial.json`, `terminal_elimination_certificate.json`
- `96-batched-certificates/direct/output/shared_frame/`: `AUDIT.json`, `BUILD.json`, `FIXTURES.json`, `construction_trace.json`, `equation.json`, `expanded_polynomial.json`
- `96-batched-certificates/direct/upstream/`: `LICENSE`, `NOTICE.md`, `PROVENANCE.md`
- `96-batched-certificates/direct/upstream/direct/`: `AUDIT.normal.json`, `AUDIT.optimized.json`, `AUDIT.small_height.normal.json`, `AUDIT.small_height.optimized.json`, `BUILD.json`, `CALCULUS_AUDIT.json`, `LITERAL_AUDIT.json`, `LITERAL_AUDIT.optimized.json`, `POWER_GRAPH_AUDIT.json`, `README.md`, `SOURCE_AUDIT.json`, `audit_calculus.py`, `audit_literal.py`, `audit_power_graph.py`, `audit_source.py`, `build_equation.py`, `check_equation.py`, `direct_calculus.py`, `equation.json`, `expanded_polynomial.json`, `shared_crt_audit.md`, `wire_eliminated_source.json`
- `96-batched-certificates/direct/upstream/direct/provenance/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `96-batched-certificates/direct/upstream/direct/small_height/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`
- `96-batched-certificates/direct/upstream/report/`: `calculus.tex`, `crt.tex`, `integer.tex`, `primitives.tex`, `report.tex`
- `96-batched-certificates/guard13/`: `AUDIT.json`, `LICENSE`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_reanchored.py`, `equation.json`, `section.tex`, `verify_reanchored.py`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/`: `FUTURE_WORK.md`, `LICENSE`, `MANIFEST.json`, `README.md`, `RELEASE.json`, `build_equations.py`, `five_square_norm.py`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/coefficients/`: `BINDING.json`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/companions/quotient_fusion/`: `METRICS.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `quotient18_transport.json`, `quotient19_transport.json`, `quotient20.json`, `quotient20_transport.json`, `verify.py`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/equations/`: `METRICS.json`, `SCHEMA.md`, `norm13_crt_degree1088.json`, `norm13_degree1392.json`, `norm13_degree1408.json`, `norm14_degree696.json`, `norm14_degree792.json`, `norm15_degree344.json`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/`: `SOURCES.json`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/report/`: `crt1088.tex`, `report.pdf`, `report.tex`
- `96-batched-certificates/guard13/upstream/con-zfc-root-fusion-2026-10-24/verification/`: `CLEARED_EXACT_AUDIT.json`, `CRT_AUDIT.json`, `EXACT_AUDIT.json`, `INTEGRATED_AUDIT.json`, `INTEGRATED_AUDIT_OPTIMIZED.json`, `PDF_QA.json`, `RELEASE_AUDIT.json`, `RELEASE_AUDIT_OPTIMIZED.json`, `audit.py`, `audit_cleared.py`, `check_crt.py`, `check_integrated.py`, `exact_polynomial.py`, `five_square_norm_expanded.json`, `verify_release.py`
- `96-batched-certificates/integer/`: `LICENSE`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `audit_common_radix.py`, `build_integer.py`, `section.tex`, `terminal_elimination.py`, `verify_integer.py`, `verify_projection.py`
- `96-batched-certificates/integer/input/`: `domain_conversion_certificate.json`, `equation.json`
- `96-batched-certificates/integer/output/`: `BUILD.json`, `INDEPENDENT_PROJECTION.json`, `equation.json`, `expanded_polynomial.json`, `terminal_elimination_certificate.json`
- `96-batched-certificates/integer/signed_output/`: `BUILD.json`, `INDEPENDENT_INTEGER_AUDIT.json`, `INDEPENDENT_PROJECTION.json`, `equation.json`, `expanded_polynomial.json`, `terminal_elimination_certificate.json`
- `96-batched-certificates/integer/source/`: `parent_natural.json`
- `96-batched-certificates/report/`: `batched_powers.tex`, `calculus.tex`, `comparison_table.tex`, `guard13_section.tex`, `metrics.tex`, `report.pdf`, `report.tex`, `source_and_crt.tex`
- `96-batched-certificates/verification/`: `MATHEMATICAL_REVIEW.md`, `PDF_QA.json`, `RELEASE_AUDIT.normal.json`, `RELEASE_AUDIT.optimized.json`
- `97-twelve-interpolation/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `build_trace13.py`, `build_twelve.py`, `check_twelve.py`, `verify.py`
- `97-twelve-interpolation/equations/`: `METRICS.json`, `SCHEMA.md`, `monotone_intersective12_degree16000.json`, `monotone_intersective12_degree4832.json`, `trace13_degree1072.json`
- `97-twelve-interpolation/inherited/root_fusion/`: `FUTURE_WORK.md`, `LICENSE`, `MANIFEST.json`, `README.md`, `RELEASE.json`, `build_equations.py`, `five_square_norm.py`
- `97-twelve-interpolation/inherited/root_fusion/coefficients/`: `BINDING.json`
- `97-twelve-interpolation/inherited/root_fusion/companions/quotient_fusion/`: `METRICS.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `quotient18_transport.json`, `quotient19_transport.json`, `quotient20.json`, `quotient20_transport.json`, `verify.py`
- `97-twelve-interpolation/inherited/root_fusion/equations/`: `METRICS.json`, `SCHEMA.md`, `norm13_crt_degree1088.json`, `norm13_degree1392.json`, `norm13_degree1408.json`, `norm14_degree696.json`, `norm14_degree792.json`, `norm15_degree344.json`
- `97-twelve-interpolation/inherited/root_fusion/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `97-twelve-interpolation/inherited/root_fusion/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `97-twelve-interpolation/inherited/root_fusion/provenance/upstream_ordinary/`: `SOURCES.json`
- `97-twelve-interpolation/inherited/root_fusion/report/`: `crt1088.tex`, `report.pdf`, `report.tex`
- `97-twelve-interpolation/inherited/root_fusion/verification/`: `CLEARED_EXACT_AUDIT.json`, `CRT_AUDIT.json`, `EXACT_AUDIT.json`, `INTEGRATED_AUDIT.json`, `INTEGRATED_AUDIT_OPTIMIZED.json`, `PDF_QA.json`, `RELEASE_AUDIT.json`, `RELEASE_AUDIT_OPTIMIZED.json`, `audit.py`, `audit_cleared.py`, `check_crt.py`, `check_integrated.py`, `exact_polynomial.py`, `five_square_norm_expanded.json`, `verify_release.py`
- `97-twelve-interpolation/proofs/`: `INDEPENDENT_REVIEW_HILBERT.md`, `INDEPENDENT_TWELVE_AUDIT.md`, `INTERPOLATION12.md`, `TRACE13_PROOF.md`
- `97-twelve-interpolation/provenance/`: `INHERITED_FILES.json`, `REVIEWED_INCOMING.json`
- `97-twelve-interpolation/provenance/signed_guards/`: `JOINT_GUARDS_PROOF.md`, `LICENSE`, `NOTICE.md`, `SOURCE.json`
- `97-twelve-interpolation/report/`: `coefficient_recipe.tex`, `report.pdf`, `report.tex`, `trace13.tex`
- `97-twelve-interpolation/verification/`: `BUILD_INFO.json`, `PDF_QA.json`, `RELEASE_CHECKS.json`, `RELEASE_CHECKS_OPTIMIZED.json`, `TRACE13_CHECKS.json`, `TRACE13_CHECKS_OPTIMIZED.json`, `TWELVE16000_CHECKS.json`, `TWELVE16000_OPTIMIZED_CHECKS.json`, `TWELVE4832_CHECKS.json`, `TWELVE4832_OPTIMIZED_CHECKS.json`
- `97-twelve-interpolation/verification/trace_build/`: `TRACE13_CHECKS.json`, `trace13_degree1072.json`
- `98-congruence-certificates/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RESULTS.json`, `verify.py`
- `98-congruence-certificates/direct/`: `LICENSE`, `ORIENTED_AUDIT.normal.json`, `ORIENTED_AUDIT.optimized.json`, `ORIENTED_POWER_PROOF.md`, `PROVENANCE.json`, `README.md`, `audit_oriented.py`, `build_equation.py`, `build_integer_companion.py`, `direct_calculus.py`, `direct_section.tex`, `integer_companion.json`, `verify.py`, `wire_eliminated_source.json`
- `98-congruence-certificates/direct/eq/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`
- `98-congruence-certificates/direct/independent_review/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `CHECKS_SMALL_HEIGHT.json`, `CHECKS_SMALL_HEIGHT_OPTIMIZED.json`, `REVIEW.md`, `check_export.py`
- `98-congruence-certificates/direct/small_height/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`
- `98-congruence-certificates/direct/upstream/`: `Bridge.lean`, `CALIBRATION_PINS.json`, `LICENSE-mathlib`, `PARENT_BUILD.json`, `PellMatiyasevic.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `build_equation.py`, `direct_calculus.py`, `direct_flow_large_carrier_README.md`, `parent_calculus.tex`, `parent_crt.tex`, `parent_primitives.tex`
- `98-congruence-certificates/integer/`: `FAMILY.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `dag_support.py`, `five_square_norm.py`, `verification_normal.txt`, `verification_optimized.txt`, `verify.py`
- `98-congruence-certificates/integer/coefficients/`: `BINDING.json`
- `98-congruence-certificates/integer/equations/`: `integer13_crt_valuation_degree1072.json`, `integer14_crt_valuation_degree414.json`, `integer14_crt_valuation_degree558.json`, `integer15_crt_valuation_degree218.json`, `integer16_crt_valuation_degree124.json`
- `98-congruence-certificates/integer/independent_review/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `REVIEW.md`, `check.py`
- `98-congruence-certificates/integer/upstream/fixed_prime/`: `LICENSE`, `NOTICE.md`
- `98-congruence-certificates/integer/upstream/fixed_prime/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `98-congruence-certificates/integer/upstream/fixed_prime/proofs/`: `INDEPENDENT_REVIEW13.md`, `INDEPENDENT_REVIEW15.md`, `NORMALIZATION.md`, `PENTAGONAL_GUARD.md`
- `98-congruence-certificates/integer/upstream/fixed_prime/report/`: `report.tex`
- `98-congruence-certificates/integer/upstream/fixed_prime/upstream/calibration/`: `NOTICE.source63.md`, `README.md`
- `98-congruence-certificates/integer/upstream/fixed_prime/upstream/inherited/determinant71/`: `NOTICE.md`
- `98-congruence-certificates/integer/upstream/fixed_prime/upstream/transport/`: `PROOF.md`
- `98-congruence-certificates/integer/upstream/root_fusion/`: `LICENSE`
- `98-congruence-certificates/integer/upstream/root_fusion/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `98-congruence-certificates/integer/upstream/root_fusion/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `98-congruence-certificates/integer/upstream/root_fusion/provenance/upstream_ordinary/`: `SOURCES.json`
- `98-congruence-certificates/integer/upstream/root_fusion/report/`: `crt1088.tex`, `report.tex`
- `98-congruence-certificates/positive/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `PROOF.md`, `check.py`, `p12_free_J.json`, `p13_free_J.json`
- `98-congruence-certificates/positive/coefficients/`: `BINDING.json`, `README.md`, `SHA256.json`
- `98-congruence-certificates/positive/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `98-congruence-certificates/positive/coefficients/recipe/`: `NOTICE-upstream.md`
- `98-congruence-certificates/positive/parents/`: `ORDINARY13.md`, `README.md`, `p12_ordinary_degree70.json`, `p13_ordinary_degree51.json`
- `98-congruence-certificates/provenance/`: `README.md`, `SOURCES.json`
- `98-congruence-certificates/provenance/comparison16/`: `README.md`
- `98-congruence-certificates/provenance/comparison16/integer/`: `PROOF.md`
- `98-congruence-certificates/provenance/comparison16/integer/circuits/`: `integer16_degree184.json`, `integer16_degree192.json`
- `98-congruence-certificates/report/`: `budget.tex`, `degree_details.tex`, `direct.tex`, `free_j.tex`, `integer.tex`, `package.tex`, `report.pdf`, `report.tex`, `results.tex`, `verification.tex`
- `98-congruence-certificates/verification/`: `PDF_QA.json`, `README.md`, `REPLAY_NORMAL.json`, `REPLAY_OPTIMIZED.json`
- `99-shared-pell608/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `README.md`, `integer_indices.tex`, `natural_rows.tex`, `report.pdf`, `report.tex`, `shared_arithmetic_sections.tex`, `verify_all.py`
- `99-shared-pell608/artifacts/natural/`: `BUILD.json`, `before_terminal.json`, `elimination_trace.json`, `envelope_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_builder.json`
- `99-shared-pell608/artifacts/natural/integer/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `guard_certificate.json`
- `99-shared-pell608/provenance/`: `PROPOSAL_REVIEW_LATEST.md`, `SIZE_REDUCTION.md`, `SOURCE_PINS.json`, `STATUS.md`
- `99-shared-pell608/provenance/inherited/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`, `original_direct_calculus.py`, `parent_BUILD.json`
- `99-shared-pell608/provenance/mathlib/`: `LICENSE`, `PellMatiyasevic.lean`
- `99-shared-pell608/reviews/`: `FINAL_SEMANTIC_AUDIT.json`, `FINAL_SEMANTIC_AUDIT.optimized.json`, `FINAL_SEMANTIC_REVIEW.md`, `RELEASE_VALIDATION.json`, `VERIFY.normal.json`, `VERIFY.optimized.json`, `alternative_math_factorial_review.md`, `alternative_math_new_lemma_results.json`, `alternative_math_power_fixture_results.json`, `alternative_math_power_review.md`, `alternative_math_shared_pell_review.md`, `alternative_math_shared_radix_review.md`, `final1685_integer.normal.json`, `final1685_integer.optimized.json`, `final608_affine.normal.json`, `final608_affine.optimized.json`, `final608_terminal.normal.json`, `final608_terminal.optimized.json`, `independent_final_audit.txt`, `terminal_elimination_proof.txt`
- `99-shared-pell608/src/`: `base_builder.py`, `build.py`, `compress.py`, `direct_calculus.py`, `integer_export.py`, `power_builder.py`, `shared_power_builder.py`, `wire_eliminated_source.json`
- `99-shared-pell608/tests/`: `alternative_math_new_lemma_checks.py`, `alternative_math_power_fixtures.py`, `audit_final_semantics.py`, `audit_reductions.py`, `verify_affine_independent.py`, `verify_integer_independent.py`, `verify_printed_equation.py`, `verify_terminal_independent.py`
- `100-quartics407-888/`: `LICENSE`, `NOTICE.md`, `README.md`, `report.pdf`, `report.tex`, `reproduce.py`, `verify.py`
- `100-quartics407-888/appendix/`: `integer888_rows.tex`, `integer917_rows.tex`, `natural407_rows.tex`
- `100-quartics407-888/code/`: `additive_index.py`, `audit_new.py`, `build.py`, `build_fused.py`, `build_projected.py`, `render_residuals.py`, `reuse_radix.py`, `source_identity.py`
- `100-quartics407-888/code/integer_pipeline/`: `audit_common_radix.py`, `build_integer.py`, `independent_polynomial.py`, `sign_inference.py`, `terminal_elimination.py`, `verify_integer.py`, `verify_projection.py`
- `100-quartics407-888/code/psd_contract/`: `check.py`, `contract.py`, `negative_controls.py`
- `100-quartics407-888/equations/integer888/`: `BUILD.json`, `INDEPENDENT_AUDIT.json`, `INDEPENDENT_AUDIT_OPTIMIZED.json`, `SOURCE_PINS.json`, `domain_conversion.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `source_natural.json`
- `100-quartics407-888/equations/integer917/`: `BUILD.json`, `INDEPENDENT_AUDIT.json`, `INDEPENDENT_AUDIT_OPTIMIZED.json`, `SOURCE_PINS.json`, `domain_conversion.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `source_natural.json`
- `100-quartics407-888/equations/natural407/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `100-quartics407-888/equations/natural410/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `100-quartics407-888/equations/source690/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `index_derivations.json`, `label_majorant.json`, `local_majorant.json`, `macro_inventory.json`, `radix_certificate.json`
- `100-quartics407-888/proofs/`: `integer_sign_inference.md`, `nonnegative_contraction.md`, `radix_and_pell.md`
- `100-quartics407-888/provenance/`: `COMPARISON.json`, `INDEPENDENT_PROJECTED_AUDIT.json`, `UPSTREAM_SHA256.json`, `incoming_index.json`, `prior_projection_proof.md`, `projected_raw_audit_input.json`
- `100-quartics407-888/receipts/`: `document_check.json`, `mathematical_review.md`, `verification_normal.json`, `verification_optimized.json`
- `100-quartics407-888/upstream/`: `LICENSE`, `NOTICE.md`, `PROVENANCE.json`
- `100-quartics407-888/upstream/code/`: `affine_contract.py`, `audit_factored_source.py`, `audit_shared_power.py`, `audit_shared_product.py`, `direct_source.py`, `direct_source_factored.py`, `make_integer.py`, `release.py`, `shared_index_power.py`, `shared_power.py`, `shared_product_power.py`, `synchronized_builder.py`, `verify_synchronized.py`
- `100-quartics407-888/upstream/proofs/`: `contraction.md`, `factored_source.md`, `final_math_review.md`, `independent_mathematical_review.md`, `independent_structure_review.md`, `integer_guards.md`, `shared_indices.md`, `shared_powers.md`
- `100-quartics407-888/upstream/provenance/upstream/`: `BUILD.json`, `LICENSE`, `NOTICE.md`, `README.md`, `audit_calculus.py`, `audit_source.py`, `build_equation.py`, `calculus.tex`, `crt.tex`, `direct_calculus.py`, `primitives.tex`, `wire_eliminated_source.json`
- `100-quartics407-888/upstream/provenance/upstream/calibration/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `101-constructive-reductions/`: `ARTIFACT_INDEX.json`, `INTEGRATION.md`, `LICENSE`, `MANIFEST.sha256`, `README.md`, `SCHEMAS.md`, `verify_all.py`
- `101-constructive-reductions/direct/`: `AUDIT.json`, `DOMAIN_CERTIFICATE.json`, `DOMAIN_CHECK.json`, `DOMAIN_CHECK_OPTIMIZED.json`, `DOMAIN_NEGATIVE_CONTROLS.json`, `DOMAIN_NEGATIVE_CONTROLS_OPTIMIZED.json`, `PROOF_PROJECTED.md`, `RAW_FRAME_INTERFACE.json`, `README.md`, `SOURCE_PINS.json`, `domain_guard_seeds.json`, `report_section.tex`
- `101-constructive-reductions/direct/code/`: `affine_contract.py`, `audit_projected.py`, `build_domain_certificate.py`, `build_integer.py`, `build_projected.py`, `check_domain_certificate.py`, `direct_source.py`, `direct_source_factored.py`, `domain_negative_controls.py`, `projected_source.py`, `shared_power.py`, `shared_product_power.py`, `sign_rule_producer.py`, `signed_contract.py`, `synchronized_builder.py`, `verify_integer.py`, `verify_synchronized.py`
- `101-constructive-reductions/direct/equations_v3/cap64/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `101-constructive-reductions/direct/equations_v3/source/`: `equation.json`, `expanded_polynomial.json`, `label_bound_certificate.json`, `macro_inventory.json`, `majorant_certificate.json`
- `101-constructive-reductions/direct/integer977/`: `METRICS.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `101-constructive-reductions/direct/provenance/`: `contraction.md`, `final_math_review.md`, `shared_indices.md`, `shared_powers.md`
- `101-constructive-reductions/direct/provenance/upstream/`: `BUILD.json`, `LICENSE`, `NOTICE.md`, `README.md`, `audit_calculus.py`, `audit_source.py`, `build_equation.py`, `calculus.tex`, `crt.tex`, `direct_calculus.py`, `primitives.tex`, `wire_eliminated_source.json`
- `101-constructive-reductions/direct/provenance/upstream/calibration/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `101-constructive-reductions/direct/reviews/`: `integer-agent-review.md`, `integer977-review.md`
- `101-constructive-reductions/integer14/`: `AUDIT.json`, `AUDIT.optimized.json`, `LICENSE`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `crt14_degree540.json`, `crt14_degree568.json`, `report_section.tex`, `section.tex`, `verify.py`
- `101-constructive-reductions/integer14/upstream/`: `FUTURE_WORK.md`, `LICENSE`, `MANIFEST.json`, `README.md`, `RELEASE.json`, `build_equations.py`, `five_square_norm.py`
- `101-constructive-reductions/integer14/upstream/coefficients/`: `BINDING.json`
- `101-constructive-reductions/integer14/upstream/companions/quotient_fusion/`: `METRICS.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `quotient18_transport.json`, `quotient19_transport.json`, `quotient20.json`, `quotient20_transport.json`, `verify.py`
- `101-constructive-reductions/integer14/upstream/equations/`: `METRICS.json`, `SCHEMA.md`, `norm13_crt_degree1088.json`, `norm13_degree1392.json`, `norm13_degree1408.json`, `norm14_degree696.json`, `norm14_degree792.json`, `norm15_degree344.json`
- `101-constructive-reductions/integer14/upstream/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `101-constructive-reductions/integer14/upstream/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `101-constructive-reductions/integer14/upstream/provenance/upstream_ordinary/`: `SOURCES.json`
- `101-constructive-reductions/integer14/upstream/report/`: `crt1088.tex`, `report.pdf`, `report.tex`
- `101-constructive-reductions/integer14/upstream/verification/`: `CLEARED_EXACT_AUDIT.json`, `CRT_AUDIT.json`, `EXACT_AUDIT.json`, `INTEGRATED_AUDIT.json`, `INTEGRATED_AUDIT_OPTIMIZED.json`, `PDF_QA.json`, `RELEASE_AUDIT.json`, `RELEASE_AUDIT_OPTIMIZED.json`, `audit.py`, `audit_cleared.py`, `check_crt.py`, `check_integrated.py`, `exact_polynomial.py`, `five_square_norm_expanded.json`, `verify_release.py`
- `101-constructive-reductions/nine/`: `COEFFICIENT_RECONSTRUCTION.json`, `EXACT_AUDIT.json`, `LICENSE`, `METRICS.json`, `NORMALIZATION_CHECKS.json`, `NOTICE.md`, `README.md`, `REBUILD_CHECK.json`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `exact_audit.py`, `exact_audit.stdout.txt`, `exact_audit_optimized.stdout.txt`, `normalization_check.py`, `poly.py`, `report_section.tex`, `verify.py`, `verify_coefficients.py`
- `101-constructive-reductions/nine/certificates/`: `HORNER_CHOICES.json`
- `101-constructive-reductions/nine/compact/`: `SOURCE_PINS.json`
- `101-constructive-reductions/nine/compact/coefficients/`: `COEFFICIENT_BINDING.json`, `COMPACT54_ARITHMETIC.md`, `COMPACT54_SEED.txt`
- `101-constructive-reductions/nine/compact/coefficients/compact_tuple/`: `COEFFICIENT_BINDING.json`
- `101-constructive-reductions/nine/compact/data/`: `code.json`, `kernels.json`
- `101-constructive-reductions/nine/compact/provenance/`: `GAP_CIRCUIT_RECIPE66.md`, `GAP_NINE_POLYNOMIAL66.md`, `LICENSE.59`, `NATIVE_CLAUSE54.md`, `NATIVE_CONVOLUTION54.md`, `NATIVE_SOURCE_WINDOW.md`, `NOTICE.md`, `NOTICE.tuple.md`, `OBJECT_ZFC.md`, `nine-NOTICE.md`, `nine-upstream-INHERITED_LICENSE`, `nine-upstream-INHERITED_NOTICE.md`, `parent-CONFIG.json`, `parent-HEIGHT_CERTIFICATE.json`, `parent-PROVENANCE.json`, `parent-README.md`, `verify_one_page_tuple54.py`
- `101-constructive-reductions/nine/compact/provenance/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-partial-selector.md`, `NOTICE_K215.md`
- `101-constructive-reductions/nine/data/`: `code.json`, `correction.json`, `kernels.json`, `saturated_P.json`, `saturated_corrected_P.json`, `saturated_corrected_certificate.json`, `saturated_defect.json`
- `101-constructive-reductions/nine/equations/`: `boundary_complete.json`, `boundary_simple.json`, `compact_simple.json`
- `101-constructive-reductions/nine/fixed/boundary/`: `BINDING.json`
- `101-constructive-reductions/nine/fixed/compact/`: `BINDING.json`, `c000.bin.gz`, `c001.bin.gz`, `c002.bin.gz`, `c003.bin.gz`, `c004.bin.gz`, `c005.bin.gz`, `c007.bin.gz`, `threshold_scale.bin.gz`
- `101-constructive-reductions/nine/inherited/`: `FULL_NINE_SOUNDNESS.md`, `FULL_RADICAL_H1868_AUDIT.md`, `SATURATED_POSITIVE_PELL_AUDIT.md`, `h1868_code.json`, `h1868_kernels.json`
- `101-constructive-reductions/nine/licenses/`: `LICENSE-radical-parent`, `LICENSE.Source65`, `LICENSE.Source71`, `NOTICE-radical-parent.md`
- `101-constructive-reductions/nine/native_original31/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `101-constructive-reductions/nine/reviews/`: `integer-agent-review.md`
- `101-constructive-reductions/provenance/`: `COMPARISON_SNAPSHOT.json`
- `101-constructive-reductions/report/`: `ConZFC_Constructive_Reductions.pdf`, `ConZFC_Constructive_Reductions.tex`
- `101-constructive-reductions/verification/`: `MANUSCRIPT_REVIEW.md`, `PDF_QA.json`, `ROOT_NORMAL.json`, `ROOT_OPTIMIZED.json`, `direct_integer_normal.json`
- `102-direct-quartics3776/`: `LICENSE`, `MEASUREMENTS.json`, `README.md`, `verify.py`
- `102-direct-quartics3776/elimination/`: `build.py`, `check.py`
- `102-direct-quartics3776/equations/fewer_variables/`: `BUILD.json`, `INDEPENDENT_REPLAY.json`, `INDEPENDENT_REPLAY_OPTIMIZED.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`
- `102-direct-quartics3776/equations/main/`: `BUILD.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`
- `102-direct-quartics3776/guard_minimization/`: `PROOF.md`, `build.py`, `check.py`, `corruption_controls.py`, `explore.py`, `preliminary.json`, `retained_preliminary.json`, `retained_seed_names.json`, `seed_names.json`
- `102-direct-quartics3776/guard_minimization/candidate/`: `BUILD.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `CORRUPTION_CONTROLS.json`, `equation.json`, `expanded_polynomial.json`, `guard_certificate.json`
- `102-direct-quartics3776/guard_minimization/retained_candidate/`: `BUILD.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `equation.json`, `expanded_polynomial.json`, `guard_certificate.json`
- `102-direct-quartics3776/proofs/`: `INDEPENDENT_SEMANTIC_REVIEW.md`, `PROPOSAL_REVIEW_DIRECT_C222_ROUND12.md`, `PROPOSAL_REVIEW_LATEST.md`, `PROPOSAL_REVIEW_SHARED_CERTIFICATES_DIRECT.md`
- `102-direct-quartics3776/report/`: `Makefile`, `metrics.tex`, `report.pdf`, `report.tex`
- `102-direct-quartics3776/signed_quotients/`: `PROOF_SIGNED.md`, `build.py`, `check.py`, `verify_sources.py`
- `102-direct-quartics3776/signed_quotients/candidate/`: `BUILD.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `equation.json`, `expanded_polynomial.json`, `transformation_certificate.json`
- `102-direct-quartics3776/signed_quotients/retained_candidate/`: `BUILD.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `equation.json`, `expanded_polynomial.json`, `transformation_certificate.json`
- `102-direct-quartics3776/signed_quotients/source/`: `CHECK_PARENT.json`, `LICENSE.upstream`, `POWER_AUDIT.json`, `PROOF.md`, `SOURCE_PINS.json`, `SOURCE_REPLAY.json`, `SOURCE_REPLAY_OPTIMIZED.json`, `natural_equation.json`
- `102-direct-quartics3776/signed_quotients/source/affine/`: `BUILD.json`
- `102-direct-quartics3776/signed_quotients/source/retained/`: `equation.json`
- `102-direct-quartics3776/signed_quotients/source/upstream/`: `CALCULUS_AUDIT.json`, `audit_calculus.py`, `audit_power_graph.py`, `build_equation.py`, `check_equation.py`, `direct_calculus.py`, `wire_eliminated_source.json`
- `102-direct-quartics3776/source_calibration/`: `BoundedForallRepresentation.lean`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `RemainderRepresentation.lean`, `SOURCE_URLS.json`
- `102-direct-quartics3776/verification/`: `NORMAL.json`, `OPTIMIZED.json`
- `103-shared-pell1873/`: `FORMAT.md`, `LICENSE.upstream`, `NOTICE.md`, `README.md`, `build.py`, `check_refined_batch.py`, `polynomial.py`, `positive_arithmetic.py`, `signed_backend.py`, `verify_batch.py`, `verify_polynomial.py`, `verify_recurrence.py`, `verify_release.py`, `verify_signed_index.py`, `verify_source.py`, `verify_source_negative.py`
- `103-shared-pell1873/checks/`: `PDF_LAYOUT_CHECK.json`, `REFINED_BATCH_FINITE_CHECKS.json`, `RELEASE_BATCH_NORMAL.json`, `RELEASE_BATCH_OPTIMIZED.json`, `RELEASE_POLYNOMIAL_PRIMARY_NORMAL.json`, `RELEASE_POLYNOMIAL_PRIMARY_OPTIMIZED.json`, `RELEASE_POLYNOMIAL_SMALL_HEIGHT_NORMAL.json`, `RELEASE_POLYNOMIAL_SMALL_HEIGHT_OPTIMIZED.json`, `RELEASE_RECURRENCE_PRIMARY_NORMAL.json`, `RELEASE_RECURRENCE_PRIMARY_OPTIMIZED.json`, `RELEASE_RECURRENCE_SMALL_HEIGHT_NORMAL.json`, `RELEASE_RECURRENCE_SMALL_HEIGHT_OPTIMIZED.json`, `RELEASE_SIGNED_INDEX_NORMAL.json`, `RELEASE_SIGNED_INDEX_OPTIMIZED.json`, `RELEASE_SOURCE_NEGATIVE_NORMAL.json`, `RELEASE_SOURCE_NEGATIVE_OPTIMIZED.json`, `RELEASE_SOURCE_NORMAL.json`, `RELEASE_SOURCE_OPTIMIZED.json`, `RELEASE_VERIFY.json`, `SOURCE_NEGATIVE_CONTROLS.json`
- `103-shared-pell1873/equations/`: `circuit.json`, `local_row.json`, `metrics.json`, `polynomial.json`, `residuals.json`, `semantic_certificate.json`
- `103-shared-pell1873/equations_small_height/`: `circuit.json`, `local_row.json`, `metrics.json`, `polynomial.json`, `residuals.json`, `semantic_certificate.json`
- `103-shared-pell1873/proofs/`: `BATCHED_PELL_THEOREM.md`, `FINAL_SOURCE_REPORT_REVIEW.md`, `INDEPENDENT_BATCH_REVIEW.md`, `RECURRENCE_REDUCTION_PROOF.md`, `SIGNED_INDEX_INDEPENDENT_REVIEW.md`, `SIGNED_INDEX_THEOREM.md`, `SOURCE_AND_DOMAIN_AUDIT.md`, `SOURCE_PROJECTION.md`, `UPSTREAM_PRIME_LIFT.md`
- `103-shared-pell1873/provenance/`: `ARITHMETIC_SOURCE_PINS.json`, `LICENSE.mathlib`, `LOGICAL_SOURCE_PINS.json`, `PellMatiyasevic.lean`, `SOURCE_METADATA.json`
- `103-shared-pell1873/provenance/arithmetic/`: `ArithmeticRepresentation.lean`, `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `DivisionRepresentation.lean`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `QuarticCompiler.lean`, `RemainderRepresentation.lean`, `Representation.lean`
- `103-shared-pell1873/report/`: `Batched_Pell_1873.pdf`, `Batched_Pell_1873.tex`
- `103-shared-pell1873/source/`: `build_direct.py`
- `104-valuation-signed/`: `LICENSE`, `MANIFEST.json`, `METRICS.json`, `NOTICE.md`, `README.md`, `SOURCE_PINS.json`, `verify.py`
- `104-valuation-signed/direct/`: `BUILD.json`, `INDEPENDENT_CHECK.json`, `INDEPENDENT_CHECK_OPTIMIZED.json`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROJECTION_CHECK.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `UPSTREAM_REPLAY_OPTIMIZED.json`, `audit_common_radix.py`, `build.py`, `projection_sweep.json`, `section.tex`, `terminal_elimination.py`, `verify.py`, `verify_projection.py`
- `104-valuation-signed/direct/input/`: `domain_conversion_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `104-valuation-signed/direct/output/`: `equation.json`, `expanded_polynomial.json`, `terminal_elimination_certificate.json`
- `104-valuation-signed/direct/source/`: `parent_natural.json`
- `104-valuation-signed/direct/upstream/synchronized/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `report.pdf`, `report.tex`, `verify.py`
- `104-valuation-signed/direct/upstream/synchronized/code/`: `affine_contract.py`, `audit_factored_source.py`, `audit_shared_power.py`, `audit_shared_product.py`, `direct_source.py`, `direct_source_factored.py`, `make_integer.py`, `release.py`, `shared_index_power.py`, `shared_power.py`, `shared_product_power.py`, `synchronized_builder.py`, `verify_synchronized.py`
- `104-valuation-signed/direct/upstream/synchronized/equations/`: `CENSUS.json`
- `104-valuation-signed/direct/upstream/synchronized/equations/integer2088/`: `VERIFICATION.json`, `conversion_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `104-valuation-signed/direct/upstream/synchronized/equations/natural522/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `104-valuation-signed/direct/upstream/synchronized/equations/natural529/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `104-valuation-signed/direct/upstream/synchronized/equations/natural596/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `104-valuation-signed/direct/upstream/synchronized/equations/source895/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `macro_inventory.json`, `majorant_certificate.json`
- `104-valuation-signed/direct/upstream/synchronized/proofs/`: `contraction.md`, `factored_source.md`, `final_math_review.md`, `independent_mathematical_review.md`, `independent_structure_review.md`, `integer_guards.md`, `shared_indices.md`, `shared_powers.md`
- `104-valuation-signed/direct/upstream/synchronized/provenance/repository/`: `INCOMING_INDEX.json`, `PROPOSAL_REVIEW_DIRECT_C222_ROUND12.md`, `PROPOSAL_REVIEW_LATEST.md`, `README.md`
- `104-valuation-signed/direct/upstream/synchronized/provenance/upstream/`: `BUILD.json`, `LICENSE`, `NOTICE.md`, `README.md`, `audit_calculus.py`, `audit_source.py`, `build_equation.py`, `calculus.tex`, `crt.tex`, `direct_calculus.py`, `primitives.tex`, `wire_eliminated_source.json`
- `104-valuation-signed/direct/upstream/synchronized/provenance/upstream/calibration/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `104-valuation-signed/direct/upstream/synchronized/receipts/`: `pdf_qa.json`, `verification_normal.json`, `verification_optimized.json`
- `104-valuation-signed/integer12/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `EXACT_NORM.json`, `EXACT_NORM_OPTIMIZED.json`, `LICENSE.UPSTREAM`, `README.md`, `build_prime12.py`, `check_norm_exact.py`, `check_prime12.py`, `circuit.py`, `norm5.py`
- `104-valuation-signed/integer12/baselines/`: `monotone_intersective12_degree16000.json`, `monotone_intersective12_degree4832.json`
- `104-valuation-signed/integer12/equations/`: `prime_separated12_degree2400.json`, `prime_separated12_degree2912.json`
- `104-valuation-signed/integer12/inherited/root_fusion/`: `FUTURE_WORK.md`, `LICENSE`, `MANIFEST.json`, `README.md`, `RELEASE.json`, `build_equations.py`, `five_square_norm.py`
- `104-valuation-signed/integer12/inherited/root_fusion/coefficients/`: `BINDING.json`
- `104-valuation-signed/integer12/inherited/root_fusion/companions/quotient_fusion/`: `METRICS.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `quotient18_transport.json`, `quotient19_transport.json`, `quotient20.json`, `quotient20_transport.json`, `verify.py`
- `104-valuation-signed/integer12/inherited/root_fusion/equations/`: `METRICS.json`, `SCHEMA.md`, `norm13_crt_degree1088.json`, `norm13_degree1392.json`, `norm13_degree1408.json`, `norm14_degree696.json`, `norm14_degree792.json`, `norm15_degree344.json`
- `104-valuation-signed/integer12/inherited/root_fusion/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `104-valuation-signed/integer12/inherited/root_fusion/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `104-valuation-signed/integer12/inherited/root_fusion/provenance/upstream_ordinary/`: `SOURCES.json`
- `104-valuation-signed/integer12/inherited/root_fusion/report/`: `crt1088.tex`, `report.pdf`, `report.tex`
- `104-valuation-signed/integer12/inherited/root_fusion/verification/`: `CLEARED_EXACT_AUDIT.json`, `CRT_AUDIT.json`, `EXACT_AUDIT.json`, `INTEGRATED_AUDIT.json`, `INTEGRATED_AUDIT_OPTIMIZED.json`, `PDF_QA.json`, `RELEASE_AUDIT.json`, `RELEASE_AUDIT_OPTIMIZED.json`, `audit.py`, `audit_cleared.py`, `check_crt.py`, `check_integrated.py`, `exact_polynomial.py`, `five_square_norm_expanded.json`, `verify_release.py`
- `104-valuation-signed/integer12/proofs/`: `INDEPENDENT_REVIEW_HILBERT.md`, `INDEPENDENT_TWELVE_AUDIT.md`, `INTERPOLATION12.md`, `PRIME_TWELVE.md`, `TRACE13_PROOF.md`
- `104-valuation-signed/integer12/provenance/`: `INHERITED_FILES.json`, `REVIEWED_INCOMING.json`
- `104-valuation-signed/integer12/provenance/signed_guards/`: `JOINT_GUARDS_PROOF.md`, `LICENSE`, `NOTICE.md`, `SOURCE.json`
- `104-valuation-signed/report/`: `closing.tex`, `coefficient_recipe.tex`, `direct.tex`, `direct_metrics.tex`, `report.pdf`, `report.tex`, `soundness.tex`
- `104-valuation-signed/reviews/`: `ARTICLE_REVIEW.json`, `ARTICLE_REVIEW.md`, `DIRECT_QUARTIC_INDEPENDENT_REVIEW.md`, `PRIME_TWELVE_INDEPENDENT_REVIEW.md`
- `104-valuation-signed/supplemental/ordinary98/`: `CHECKS.json`, `PARENT_PROOF.md`, `PROVENANCE.json`, `README.md`, `build.py`, `carrier.py`, `check.py`, `ordinary12_98.json`, `ordinary12_parent100.json`
- `104-valuation-signed/supplemental/ordinary98/inherited/`: `PARENT_LITERAL.json`, `SHORT_UNIT_PRODUCTS.md`
- `104-valuation-signed/supplemental/ordinary98/native/`: `NOTICE-upstream.md`
- `104-valuation-signed/supplemental/ordinary98/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `104-valuation-signed/verification/`: `PDF_QA.json`, `RELEASE_CHECKS.json`, `RELEASE_CHECKS_OPTIMIZED.json`
- `105-bootstrap-certificates/`: `BASELINES.md`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RESULTS.json`, `build_report.sh`, `verify.py`
- `105-bootstrap-certificates/checks/`: `BASELINE_AUDIT.json`, `INTEGER_REVIEW.md`, `INTEGER_REVIEW_ADDENDUM.json`, `PDF_QA.json`, `RELEASE_NORMAL.json`, `RELEASE_OPTIMIZED.json`, `REPORT_REVIEW.md`, `verify_baselines.py`
- `105-bootstrap-certificates/checks/baselines/`: `eleven111.json`, `nine433.json`, `nine475.json`, `thirteen195.json`
- `105-bootstrap-certificates/checks/baselines/integer1690/`: `equation.json`, `expanded_polynomial.json`
- `105-bootstrap-certificates/checks/baselines/natural522/`: `equation.json`, `expanded_polynomial.json`
- `105-bootstrap-certificates/direct/`: `AUDIT.json`, `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `verify.py`
- `105-bootstrap-certificates/direct/code/`: `affine_contract.py`, `audit_bootstrap.py`, `audit_factored_source.py`, `audit_shared_power.py`, `audit_shared_product.py`, `bootstrap_builder.py`, `bootstrap_factorial.py`, `bootstrap_frame_audit.py`, `direct_source.py`, `direct_source_factored.py`, `hybrid_source.py`, `make_integer.py`, `release.py`, `shared_index_power.py`, `shared_power.py`, `shared_product_power.py`, `shift_power.py`, `synchronized_builder.py`, `verify_synchronized.py`
- `105-bootstrap-certificates/direct/equations/natural467/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `105-bootstrap-certificates/direct/equations/natural468/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `105-bootstrap-certificates/direct/equations/natural469/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `105-bootstrap-certificates/direct/equations/parent781/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `factorial_radius_certificate.json`, `macro_inventory.json`, `majorant_certificate.json`
- `105-bootstrap-certificates/direct/equations/parent782/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `factorial_radius_certificate.json`, `macro_inventory.json`, `majorant_certificate.json`
- `105-bootstrap-certificates/direct/equations/parent783/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `factorial_radius_certificate.json`, `macro_inventory.json`, `majorant_certificate.json`
- `105-bootstrap-certificates/direct/proofs/`: `NEW_RESULTS.md`
- `105-bootstrap-certificates/direct/proofs/independent_review/`: `FACTORIAL_IMPLEMENTATION_PINS.json`, `FACTORIAL_RADIUS_CHECKS.json`, `FACTORIAL_RADIUS_CHECKS_OPTIMIZED.json`, `check_factorial_radius.py`, `factorial_bootstrap_audit.md`, `factorial_final_implementation_audit.md`, `factorial_square_radius.md`
- `105-bootstrap-certificates/direct/proofs/inherited_synchronized/`: `contraction.md`, `factored_source.md`, `final_math_review.md`, `independent_mathematical_review.md`, `independent_structure_review.md`, `integer_guards.md`, `shared_indices.md`, `shared_powers.md`
- `105-bootstrap-certificates/direct/provenance/repository/`: `INCOMING_INDEX.json`, `PROPOSAL_REVIEW_DIRECT_C222_ROUND12.md`, `PROPOSAL_REVIEW_LATEST.md`, `README.md`
- `105-bootstrap-certificates/direct/provenance/synchronized/`: `LICENSE`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `report.tex`
- `105-bootstrap-certificates/direct/provenance/upstream/`: `BUILD.json`, `LICENSE`, `NOTICE.md`, `README.md`, `audit_calculus.py`, `audit_source.py`, `build_equation.py`, `calculus.tex`, `crt.tex`, `direct_calculus.py`, `primitives.tex`, `wire_eliminated_source.json`
- `105-bootstrap-certificates/direct/provenance/upstream/calibration/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `105-bootstrap-certificates/integer/`: `PROOF.md`, `SOURCE_PINS.json`, `build_integer.py`, `projection.py`, `verify_integer.py`
- `105-bootstrap-certificates/integer/equations/integer956/`: `equation.json`, `guarded.json`, `metrics.json`, `polynomial.json`, `projection.json`, `sign_certificate.json`
- `105-bootstrap-certificates/integer/equations/integer989/`: `equation.json`, `guarded.json`, `metrics.json`, `polynomial.json`, `projection.json`, `sign_certificate.json`
- `105-bootstrap-certificates/nine/`: `LICENSE`, `MANIFEST.json`, `PROOF.md`, `README.md`, `REVIEW.md`, `SOURCE_PINS.json`, `build.py`, `notes.tex`, `verify.py`
- `105-bootstrap-certificates/nine/equations/`: `compact2082.json`, `h1868.json`
- `105-bootstrap-certificates/nine/fixed/compact2082/`: `BINDING.json`, `base_scale.bin.gz`, `c_1f49e78f6521d0fe.bin.gz`, `c_33afcc0215e266df.bin.gz`, `c_50b8a3599b18e0a9.bin.gz`, `c_a749e84ec6806d92.bin.gz`, `c_bd70eebd66b6d548.bin.gz`, `c_d048f06bd476e521.bin.gz`, `c_e24dea94f889b837.bin.gz`, `c_e3dd773f14077424.bin.gz`, `c_f69b40d0743298dc.bin.gz`, `threshold_6480184.bin.gz`
- `105-bootstrap-certificates/nine/fixed/h1868/`: `BINDING.json`
- `105-bootstrap-certificates/nine/inherited/`: `compact54-proof.md`, `h1868-full-soundness.md`, `h1868-peer-review.md`, `h1868-source-proof.md`, `latest-comparison.md`, `saturated-peer-review.md`, `saturated-proof.md`, `saturation-audit.md`
- `105-bootstrap-certificates/nine/licenses/`: `INHERITED_LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-radical-parent.md`
- `105-bootstrap-certificates/nine/parents/`: `compact2082.json`, `h1868.json`
- `105-bootstrap-certificates/nine/receipts/`: `normal.json`, `optimized.json`
- `105-bootstrap-certificates/nine/source/h1868/`: `code.json`, `kernels.json`
- `105-bootstrap-certificates/norms/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `LICENSE`, `MANIFEST.json`, `PORTABILITY.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build_and_check.py`, `normal-summary.txt`, `norms.py`, `optimized-summary.txt`
- `105-bootstrap-certificates/norms/equations/`: `norm13_crt_degree1088_short_norm.json`, `norm13_crt_guard_degree1072_short_norm.json`, `norm13_degree1392_short_norm.json`, `norm13_degree1408_short_norm.json`, `positive11_degree211_short_norm.json`
- `105-bootstrap-certificates/norms/proofs/`: `FACTORIAL_IMPLEMENTATION_PINS.json`, `FACTORIAL_RADIUS_CHECKS.json`, `FACTORIAL_RADIUS_CHECKS_OPTIMIZED.json`, `check_factorial_radius.py`, `factorial_bootstrap_audit.md`, `factorial_final_implementation_audit.md`, `factorial_square_radius.md`
- `105-bootstrap-certificates/norms/upstream/`: `compact_norms.py`, `exact_polynomial.py`, `positive11_111.json`
- `105-bootstrap-certificates/norms/upstream/positive11/`: `ADAPTIVE_PROOF.md`, `ALGEBRA_AUDIT.json`, `COEFFICIENT_REBUILD.json`, `DOUBLE_CENTER_CERTIFICATE.json`, `INDEPENDENT_AUDIT.json`, `INDEPENDENT_REVIEW.md`, `LICENSE.upstream`, `NOTICE.md`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `audit.py`, `build.py`, `p11_positive_degree211.json`, `rebuild_coefficients.py`, `section.tex`, `verify.py`
- `105-bootstrap-certificates/norms/upstream/positive11/coefficients/`: `ACTIVE_BINDING.json`
- `105-bootstrap-certificates/norms/upstream/positive11/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `105-bootstrap-certificates/norms/upstream/positive11/native_recipe/`: `NOTICE-upstream.md`
- `105-bootstrap-certificates/norms/upstream/positive11/upstream/`: `CENTERED_PROOF.md`, `PROOF112.md`, `degree277_PROOF.md`, `p11_positive_degree257.json`
- `105-bootstrap-certificates/norms/upstream/rootfusion/`: `LICENSE`, `README.md`, `REANCHORED_PROOF.md`, `build_equations.py`, `build_reanchored.py`, `build_reanchored_original.py`, `five_square_norm.py`, `norm13_crt_degree1088.json`, `norm13_crt_guard_degree1072.json`, `norm13_degree1392.json`, `norm13_degree1408.json`
- `105-bootstrap-certificates/norms/upstream/rootfusion/coefficients/`: `BINDING.json`
- `105-bootstrap-certificates/norms/upstream/rootfusion/report/`: `report.pdf`, `report.tex`
- `105-bootstrap-certificates/report/`: `compiler_contracts.tex`, `main.pdf`, `main.tex`, `metrics.tex`
- `106-compact-certificates-round13/`: `ConZFC_Compact_Proof_Certificates_Round13_2026-10-24.pdf`, `ConZFC_Compact_Proof_Certificates_Round13_2026-10-24.tex`, `MANIFEST.sha256.json`, `README.md`, `RELEASE_REPLAY.json`, `build_report.py`, `verify.py`
- `106-compact-certificates-round13/architecture/`: `BENCHMARKS.json`, `CHECKS.json`, `HEIGHT_CERTIFICATE.json`, `LICENSE.Mathlib`, `PELL_SOURCE_PIN.json`, `PROOF.md`, `PellMatiyasevic_reference.lean`, `README.md`, `RELEASE_WHITELIST.json`, `build_architecture_final.py`, `check_architecture.py`, `section.tex`
- `106-compact-certificates-round13/architecture/factorial_carrier/`: `BUILD.json`, `affine_restoration.json`, `circuit.json`, `equation.json`, `expanded_polynomial.json`
- `106-compact-certificates-round13/architecture/rounded_negative/`: `BUILD.json`, `affine_restoration.json`, `circuit.json`, `equation.json`, `expanded_polynomial.json`
- `106-compact-certificates-round13/architecture/rounded_positive/`: `BUILD.json`, `affine_restoration.json`, `circuit.json`, `equation.json`, `expanded_polynomial.json`
- `106-compact-certificates-round13/direct/`: `CLEAN_REBUILD.json`, `NOTICE.md`, `README.md`, `RELEASE_SHA256.json`, `RELEASE_WHITELIST.json`, `SOURCE_PINS.json`, `build_compact.py`, `build_direct.py`, `build_forward.py`, `build_integer.py`, `build_parametric.py`, `build_projected.py`, `build_radius.py`, `build_sign_normalized.py`, `projected_section.tex`, `section.tex`, `verify_rebuild.py`
- `106-compact-certificates-round13/direct/forward/`: `BUILD.json`, `affine_restoration.json`, `circuit.json`, `equation.json`, `expanded_polynomial.json`, `radius_certificate.json`
- `106-compact-certificates-round13/direct/projected/`: `BUILD.json`, `affine_restoration.json`, `circuit.json`, `equation.json`, `expanded_polynomial.json`, `projection_certificate.json`
- `106-compact-certificates-round13/direct/projected_guarded_integer/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `sign_certificate.json`
- `106-compact-certificates-round13/direct/projected_integer/`: `BUILD.json`, `equation.json`, `expanded_polynomial.json`, `normalization_certificate.json`
- `106-compact-certificates-round13/direct/projected_signed_template/`: `BUILD.json`, `affine_restoration.json`, `circuit.json`, `equation.json`, `expanded_polynomial.json`, `projection_certificate.json`
- `106-compact-certificates-round13/direct/sources/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FIXED_POWER_BOUND_PROOF.md`, `FactorialRepresentation.lean`, `INCOMING_PROJECTION_PROOF.md`, `INCOMING_SIGN_NORMALIZATION_PROOF.md`, `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`, `NOTICE.incoming_projection.md`, `NOTICE.shared_certificates.md`, `ORIENTATION_PROOF.md`, `PELL_SOURCE_PIN.json`, `PRIME_LIFT_PROOF.md`, `PellMatiyasevic_reference.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`, `wire_eliminated_source.json`
- `106-compact-certificates-round13/direct_audit/`: `FACTORED_SOURCE_CHECK.json`, `FORWARD_EXACT_CHECK.json`, `FORWARD_EXACT_CHECK.optimized.json`, `RELEASE_PROJECTED_WHITELIST.json`, `REPLAY_PROJECTED_COMMANDS.json`, `check_exact.py`, `check_factoring.py`
- `106-compact-certificates-round13/late_direct_audit/`: `DELTA_AUDIT.md`, `FINAL_AUDIT.json`, `FINAL_REPLAY.json`, `NEGATIVE_CONTROLS.json`, `NEGATIVE_CONTROLS.optimized.json`, `PROJECTED_CHECK.json`, `PROJECTED_CHECK.optimized.json`, `PROJECTED_INTEGER_CHECK.json`, `PROJECTED_INTEGER_CHECK.optimized.json`, `RELEASE_WHITELIST.json`, `REPLAY_COMMANDS.json`, `check_normalized.py`, `check_projected.py`, `negative_controls.py`, `run_release.py`
- `106-compact-certificates-round13/late_review/`: `LATE_ADDENDUM.md`, `LATE_LITERAL_AUDIT.json`, `LATE_SIGN_AUDIT.json`, `LATE_SOURCE_PINS.json`
- `106-compact-certificates-round13/norm/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `CLEAN_REPLAY.json`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `RELEASE_SHA256.json`, `RELEASE_WHITELIST.json`, `REPLAY_COMMANDS.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `independent_formula_short_guard.py`, `integer10_cubic.json`, `integer10_linear.json`, `integer10_polar.json`, `integer10_sixterm.json`, `section.tex`
- `106-compact-certificates-round13/norm/data/`: `code.json`, `kernels.json`
- `106-compact-certificates-round13/norm/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `106-compact-certificates-round13/norm/source/`: `BASELINE_PROOF.md`, `PROOF.md`, `README.md`, `ROOT_CERTIFICATES.json`, `SHORT_GUARD_PROOF.tex`, `cubic.json`, `integer10_polar.json`, `linear.json`, `sixterm.json`
- `106-compact-certificates-round13/norm_audit/`: `AUDIT_REVIEW.md`, `BUILD_REPLAY.txt`, `CHECK_REPLAY_NORMAL.json`, `CHECK_REPLAY_OPTIMIZED.json`, `INDEPENDENT_CHECKS.json`, `INDEPENDENT_CHECKS_OPTIMIZED.json`, `ISOLATED_REPLAY.json`, `RELEASE_SHA256.json`, `RELEASE_WHITELIST.json`, `REPLAY_COMMANDS.json`, `independent_checks.py`
- `106-compact-certificates-round13/radicals/`: `CENTER_IDENTITY.json`, `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `CLEAN_REPLAY.json`, `LICENSE`, `METRICS.json`, `PDF_QA.json`, `PROOF.md`, `README.md`, `RELEASE_SHA256.json`, `RELEASE_WHITELIST.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `check_center_identity.py`, `integer13_degree1072.json`, `integer14_degree378.json`, `integer15_degree172.json`, `integer15c_degree170.json`, `integer16_degree98.json`, `section.tex`, `standalone.pdf`, `standalone.tex`
- `106-compact-certificates-round13/radicals/coefficients/`: `BINDING.json`
- `106-compact-certificates-round13/radicals/inherited/`: `CALIBRATION_STATUS.md`, `CRT1088.tex`, `FORMALIZATION_BOUNDARY.md`, `NORMALIZED_NORMS_PROOF.md`, `PRIME_PACKAGE_SOURCE_PINS.json`, `PRIME_SEPARATION_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `SQUARED_MODULUS_PROOF.md`, `degree88_17.json`
- `106-compact-certificates-round13/radicals/inherited/pell_congruences/`: `LICENSE`, `NOTICE.md`, `RANK_REGISTER_REVIEW.md`
- `106-compact-certificates-round13/radicals/inherited/pell_congruences/inherited/determinant71/`: `NOTICE.md`
- `106-compact-certificates-round13/radicals/inherited/pell_congruences/report/`: `nine_section.tex`, `report.tex`
- `106-compact-certificates-round13/radicals/inherited/pell_congruences/transport/`: `PROOF.md`, `degree88_17.json`
- `106-compact-certificates-round13/radicals/inherited/pell_congruences/transport/parents/`: `crt_degree44_20.json`
- `106-compact-certificates-round13/radicals/inherited/upstream_ordinary/`: `SOURCES.json`
- `106-compact-certificates-round13/radicals/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `106-compact-certificates-round13/radicals12/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `CLEAN_REPLAY.json`, `LICENSE`, `METRICS.json`, `PDF_QA.json`, `PROOF.md`, `README.md`, `RELEASE_SHA256.json`, `RELEASE_WHITELIST.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `circuit.py`, `integer12_degree2048.json`, `section.tex`, `standalone.pdf`, `standalone.tex`
- `106-compact-certificates-round13/radicals12/coefficients/`: `BINDING.json`
- `106-compact-certificates-round13/radicals12/inherited/`: `INDEPENDENT_REVIEW_HILBERT.md`, `INDEPENDENT_TWELVE_AUDIT.md`, `INHERITED_FILES.json`, `INTERPOLATION12.md`, `LICENSE`, `NOTICE.md`, `REVIEWED_INCOMING.json`, `TRACE13_PROOF.md`
- `106-compact-certificates-round13/radicals12/inherited/root_fusion_provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `106-compact-certificates-round13/radicals12/inherited/root_fusion_provenance/upstream_ordinary/`: `SOURCES.json`
- `106-compact-certificates-round13/radicals12/inherited/signed_guards/`: `JOINT_GUARDS_PROOF.md`, `LICENSE`, `NOTICE.md`, `SOURCE.json`
- `106-compact-certificates-round13/radicals12/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `106-compact-certificates-round13/radicals12_audit/`: `AUDIT.normal.json`, `AUDIT.optimized.json`, `AUDIT_REVIEW.md`, `README.md`, `check_twelve.py`
- `106-compact-certificates-round13/radicals_audit/`: `AUDIT.normal.json`, `AUDIT.optimized.json`, `AUDIT_REVIEW.md`, `SOURCE_BINDINGS.json`, `check_radicals.py`
- `106-compact-certificates-round13/review/`: `C222_SOURCE_CHECK.json`, `C222_SOURCE_REVIEW.md`, `COMPARE.json`, `FETCH_LEDGER_UPDATED.json`, `INCOMING_ARCHIVE_PINS.json`, `LITERAL_COUNTS.json`, `ROUND13_REVIEW.md`
- `107-dyadic-pell/`: `INTEGRATION.md`, `LICENSE`, `MANIFEST.sha256`, `README.md`, `VERIFICATION.json`, `verify.py`
- `107-dyadic-pell/direct780/`: `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `parameters.json`, `verify.py`
- `107-dyadic-pell/direct780/certificates/`: `CHECK.json`, `INDEPENDENT_CHECK.json`, `VERIFY.json`, `VERIFY_OPTIMIZED.json`, `guard_changes.json`
- `107-dyadic-pell/direct780/equations/`: `METRICS.json`, `domain_certificate.json`, `equation.json`, `expanded_polynomial.json`, `projection.json`, `signed_source.json`
- `107-dyadic-pell/direct780/upstream/`: `LICENSE`, `NOTICE.md`, `README.md`
- `107-dyadic-pell/direct780/upstream/proofs/`: `integer_sign_inference.md`, `nonnegative_contraction.md`, `radix_and_pell.md`, `shared_indices.md`, `shared_powers.md`
- `107-dyadic-pell/direct780/upstream/source690/`: `equation.json`, `gate_ledger.json`, `index_derivations.json`, `interface.json`, `macro_inventory.json`
- `107-dyadic-pell/direct780/vendor/`: `terminal_elimination.py`
- `107-dyadic-pell/dyadic10/`: `CHECKS.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `audit.py`, `build.py`, `circuit.py`, `p10_dyadic_degree706.json`
- `107-dyadic-pell/dyadic10/upstream/`: `PROOF816.md`
- `107-dyadic-pell/provenance/`: `LICENSE.ProveIt`, `SOURCES.json`
- `107-dyadic-pell/report/`: `direct.tex`, `dyadic.tex`, `report.pdf`, `report.tex`
- `108-pell-residues/`: `LICENSE`, `NOTICE.txt`, `README.txt`, `RELEASE.json`, `metrics.tex`, `report.pdf`, `report.tex`, `reproduce.py`, `verify.py`
- `108-pell-residues/appendix/`: `integer_rows.tex`, `natural_rows.tex`, `small_rows.tex`
- `108-pell-residues/certificates/`: `INTEGER_LEDGER.json`, `integer_domain_bounds.json`
- `108-pell-residues/code/`: `build_modular.py`, `check_modular_structure.py`, `check_natural.py`, `check_signed_pell.py`, `modular_binomial.py`, `release_support.py`, `render_residuals.py`, `verify_modular_lemmas.py`
- `108-pell-residues/code/integer_domain/`: `audit_common_radix.py`, `bound_search.py`, `build_mixed.py`, `check_mixed.py`, `independent_polynomial.py`, `sign_inference_original.py`, `terminal_elimination.py`, `verify_projection.py`
- `108-pell-residues/equations/integer663/`: `INDEPENDENT_AUDIT.json`, `INDEPENDENT_AUDIT_OPTIMIZED.json`, `METRICS.json`, `domain_certificate.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `source.json`, `terminal_elimination_certificate.json`
- `108-pell-residues/equations/integer687/`: `INDEPENDENT_AUDIT.json`, `INDEPENDENT_AUDIT_OPTIMIZED.json`, `METRICS.json`, `domain_certificate.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `source.json`, `terminal_elimination_certificate.json`
- `108-pell-residues/equations/natural394/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `108-pell-residues/equations/natural395/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `108-pell-residues/equations/source655/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `label_majorant.json`, `local_majorant.json`, `macro_inventory.json`, `radix_certificate.json`, `raw_audit_input.json`
- `108-pell-residues/inherited/integer_domain/`: `PRIOR_GUARD_MINIMIZATION.md`, `SIGNED_INDEX_THEOREM.md`, `SOURCE_PINS.json`
- `108-pell-residues/proofs/`: `MIXED_DOMAIN_PROOF.md`, `independent_mathematical_review.txt`, `inherited_radix_and_pell.txt`, `modular_binomial.txt`
- `108-pell-residues/provenance/`: `PRIOR_SEARCH.json`, `SNAPSHOT.json`
- `108-pell-residues/receipts/`: `document_check.json`, `mathematical_review.json`, `modular_structure_normal.json`, `modular_structure_optimized.json`, `release_normal.json`, `release_optimized.json`, `reproduction.json`
- `108-pell-residues/supplemental/integer12/`: `CENTERING_CHECK.json`, `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `EXACT_NORM.json`, `EXACT_NORM_OPTIMIZED.json`, `LICENSE.UPSTREAM`, `PARENT_LICENSE`, `PARENT_NOTICE.md`, `README.md`, `README_CENTERING.txt`, `build_centered12.py`, `build_prime12.py`, `check_centered12.py`, `check_norm_exact.py`, `check_prime12.py`, `circuit.py`, `norm5.py`
- `108-pell-residues/supplemental/integer12/baselines/`: `monotone_intersective12_degree16000.json`, `monotone_intersective12_degree4832.json`
- `108-pell-residues/supplemental/integer12/equations/`: `centered12_integral2400.json`, `centered12_rational2368.json`, `prime_separated12_degree2400.json`, `prime_separated12_degree2912.json`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/`: `FUTURE_WORK.md`, `LICENSE`, `MANIFEST.json`, `README.md`, `RELEASE.json`, `build_equations.py`, `five_square_norm.py`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/coefficients/`: `BINDING.json`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/companions/quotient_fusion/`: `METRICS.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `quotient18_transport.json`, `quotient19_transport.json`, `quotient20.json`, `quotient20_transport.json`, `verify.py`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/equations/`: `METRICS.json`, `SCHEMA.md`, `norm13_crt_degree1088.json`, `norm13_degree1392.json`, `norm13_degree1408.json`, `norm14_degree696.json`, `norm14_degree792.json`, `norm15_degree344.json`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/provenance/upstream_ordinary/`: `SOURCES.json`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/report/`: `crt1088.tex`, `report.pdf`, `report.tex`
- `108-pell-residues/supplemental/integer12/inherited/root_fusion/verification/`: `CLEARED_EXACT_AUDIT.json`, `CRT_AUDIT.json`, `EXACT_AUDIT.json`, `INTEGRATED_AUDIT.json`, `INTEGRATED_AUDIT_OPTIMIZED.json`, `PDF_QA.json`, `RELEASE_AUDIT.json`, `RELEASE_AUDIT_OPTIMIZED.json`, `audit.py`, `audit_cleared.py`, `check_crt.py`, `check_integrated.py`, `exact_polynomial.py`, `five_square_norm_expanded.json`, `verify_release.py`
- `108-pell-residues/supplemental/integer12/proofs/`: `CENTERING_PROOF.txt`, `INDEPENDENT_REVIEW_HILBERT.md`, `INDEPENDENT_TWELVE_AUDIT.md`, `INTERPOLATION12.md`, `PRIME_TWELVE.md`, `TRACE13_PROOF.md`
- `108-pell-residues/supplemental/integer12/provenance/`: `CENTERING_PARENT_ARCHIVE.json`, `INHERITED_FILES.json`, `REVIEWED_INCOMING.json`
- `108-pell-residues/supplemental/integer12/provenance/signed_guards/`: `JOINT_GUARDS_PROOF.md`, `LICENSE`, `NOTICE.md`, `SOURCE.json`
- `109-valuations-centered/`: `MANIFEST.json`, `README.md`, `REVIEW.md`, `build_report.py`, `verify.py`
- `109-valuations-centered/direct_quartic/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PARENT_SHA256.json`, `PEER_REPLAY_CENTERED_FACTORIAL.json`, `PEER_REVIEW_CENTERED_FACTORIAL.md`, `PEER_REVIEW_POSITIVE718.md`, `PROVENANCE.json`, `README.md`, `centered_factorial_build.py`, `centered_factorial_proof.md`, `centered_verify.py`, `render_centered.py`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`, `README.md`, `report.pdf`, `report.tex`, `reproduce.py`, `verify.py`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/appendix/`: `integer888_rows.tex`, `integer917_rows.tex`, `natural407_rows.tex`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/code/`: `additive_index.py`, `audit_new.py`, `build.py`, `build_fused.py`, `build_projected.py`, `render_residuals.py`, `reuse_radix.py`, `source_identity.py`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/code/integer_pipeline/`: `audit_common_radix.py`, `build_integer.py`, `independent_polynomial.py`, `sign_inference.py`, `terminal_elimination.py`, `verify_integer.py`, `verify_projection.py`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/code/psd_contract/`: `check.py`, `contract.py`, `negative_controls.py`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/equations/integer888/`: `BUILD.json`, `INDEPENDENT_AUDIT.json`, `INDEPENDENT_AUDIT_OPTIMIZED.json`, `SOURCE_PINS.json`, `domain_conversion.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `source_natural.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/equations/integer917/`: `BUILD.json`, `INDEPENDENT_AUDIT.json`, `INDEPENDENT_AUDIT_OPTIMIZED.json`, `SOURCE_PINS.json`, `domain_conversion.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `source_natural.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/equations/natural407/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/equations/natural410/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/equations/source690/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `index_derivations.json`, `label_majorant.json`, `local_majorant.json`, `macro_inventory.json`, `radix_certificate.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/proofs/`: `integer_sign_inference.md`, `nonnegative_contraction.md`, `radix_and_pell.md`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/provenance/`: `COMPARISON.json`, `INDEPENDENT_PROJECTED_AUDIT.json`, `UPSTREAM_SHA256.json`, `incoming_index.json`, `prior_projection_proof.md`, `projected_raw_audit_input.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/receipts/`: `document_check.json`, `mathematical_review.md`, `verification_normal.json`, `verification_optimized.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`, `PROVENANCE.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/upstream/code/`: `affine_contract.py`, `audit_factored_source.py`, `audit_shared_power.py`, `audit_shared_product.py`, `direct_source.py`, `direct_source_factored.py`, `make_integer.py`, `release.py`, `shared_index_power.py`, `shared_power.py`, `shared_product_power.py`, `synchronized_builder.py`, `verify_synchronized.py`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/upstream/proofs/`: `contraction.md`, `factored_source.md`, `final_math_review.md`, `independent_mathematical_review.md`, `independent_structure_review.md`, `integer_guards.md`, `shared_indices.md`, `shared_powers.md`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `BUILD.json`, `LICENSE`, `NOTICE.md`, `README.md`, `audit_calculus.py`, `audit_source.py`, `build_equation.py`, `calculus.tex`, `crt.tex`, `direct_calculus.py`, `primitives.tex`, `wire_eliminated_source.json`
- `109-valuations-centered/direct_quartic/ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/`: `BoundedForallCertificate.lean`, `BoundedForallRepresentation.lean`, `Bridge.lean`, `CALIBRATION_PINS.json`, `COMMUTATIVE_CERTIFICATES.md`, `FactorialRepresentation.lean`, `PellRepresentation.lean`, `PowerRepresentation.lean`, `direct_flow_large_carrier_README.md`
- `109-valuations-centered/direct_quartic/appendix/`: `integer853_rows.tex`, `natural395_rows.tex`
- `109-valuations-centered/direct_quartic/centered_output/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `factorial_graphs.json`, `gate_ledger.json`, `index_derivations.json`, `label_majorant.json`, `local_majorant.json`, `macro_inventory.json`, `radix_certificate.json`, `raw_audit_input.json`
- `109-valuations-centered/direct_quartic/centered_output/integer_cap16/`: `BUILD.json`, `SOURCE_PINS.json`, `domain_conversion.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `source_natural.json`
- `109-valuations-centered/direct_quartic/centered_output/natural_cap16/`: `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `109-valuations-centered/direct_quartic/centered_output/natural_cap64/`: `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `109-valuations-centered/direct_quartic/receipts/`: `normal.json`, `optimized.json`, `parent_authentication.json`
- `109-valuations-centered/integer12/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `MANIFEST.json`, `PEER_REPLAY.json`, `PEER_REVIEW.md`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `REVIEW_FRONTIER_CHECKS.json`, `build.py`, `dag.py`, `five_square_norm.py`, `review_integer.py`, `verify.py`
- `109-valuations-centered/integer12/coefficients/`: `BINDING.json`
- `109-valuations-centered/integer12/equations/`: `prime_three_monotone31_centered_12_degree2304.json`, `prime_three_monotone31_integer_12_degree2848.json`, `prime_three_monotone31_rational_12_degree2336.json`, `prime_three_pure19_centered_12_degree2304.json`, `prime_three_pure19_integer_12_degree2848.json`, `prime_three_pure19_rational_12_degree2336.json`
- `109-valuations-centered/positive10/`: `CHECKS718.json`, `PROOF718.md`, `README.md`, `SOURCE_PIN.json`, `circuit718.py`, `equation718.json`, `verify718.py`
- `109-valuations-centered/positive10/licenses/`: `FETCH_MANIFEST.json`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.package44`, `LICENSE.root`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-package44.md`, `NOTICE-upstream-native44.md`, `NOTICE_K215.md`, `README.md`, `SOURCE_PINS-native44.json`
- `109-valuations-centered/positive10/provenance/compact44/`: `NOTICE-upstream.md`
- `109-valuations-centered/positive10/provenance/compact44/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `109-valuations-centered/positive10/provenance/parent816/`: `INDEPENDENT_REVIEW.md`, `PROOF.md`, `README.md`, `circuit.py`, `p10_positive_degree816.json`
- `109-valuations-centered/receipts/`: `pdf_qa.json`, `root_direct_normal.json`, `root_integer_normal.json`, `root_release_optimized.json`
- `109-valuations-centered/receipts/replays/`: `release-normal.json`
- `109-valuations-centered/report/`: `integer853_rows.tex`, `natural395_rows.tex`, `report.pdf`, `report.tex`
- `110-budget-interpolation/`: `DEPENDENCIES.md`, `PACKAGING_INVENTORY.json`, `README.md`, `REPLAY_PLAN.json`, `build_report.sh`, `check_sources.py`, `make_archive.py`, `verify.py`
- `110-budget-interpolation/alternative/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `FOUR_TILE_DAG.json`, `INDEPENDENT_PROOF_REVIEW.md`, `MANIFEST.sha256.json`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `SOURCES.md`, `THREE_POWERS_INTERFACE.json`, `TWO_POWERS_INTERFACE.json`, `build_dag.py`, `build_interfaces.py`, `check.py`, `core.py`, `prior_build_dag.py`, `section.tex`
- `110-budget-interpolation/baseline/`: `COMMITS_SINCE_55ca592.json`, `COMPARE_SINCE_55ca592.json`, `FETCH_LEDGER.json`, `PROPOSAL_REVIEW_FIXED_PRIME_RADICALS.md`, `PROPOSAL_REVIEW_LATEST.md`, `PROPOSAL_REVIEW_PARITY_FAMILIES.md`, `PROPOSAL_REVIEW_POLYNOMIAL_SHEARS_NORM10.md`, `PROPOSAL_REVIEW_PRIME_SEPARATION.md`, `PROPOSAL_REVIEW_ROOT_FUSION13.md`, `README.project.md`, `README.upstream.md`, `REPLAY_REVIEW.md`, `SOURCE_MAP.md`, `comparison.tex`, `download_extra.json`, `download_list.json`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/`: `FUTURE_WORK.md`, `LICENSE`, `MANIFEST.json`, `README.md`, `RELEASE.json`, `build_equations.py`, `five_square_norm.py`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/coefficients/`: `BINDING.json`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/companions/quotient_fusion/`: `METRICS.json`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `quotient18_transport.json`, `quotient19_transport.json`, `quotient20.json`, `quotient20_transport.json`, `verify.py`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/equations/`: `METRICS.json`, `SCHEMA.md`, `norm13_crt_degree1088.json`, `norm13_degree1392.json`, `norm13_degree1408.json`, `norm14_degree696.json`, `norm14_degree792.json`, `norm15_degree344.json`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/provenance/upstream_ordinary/`: `SOURCES.json`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/report/`: `crt1088.tex`, `report.pdf`, `report.tex`
- `110-budget-interpolation/baseline/ConZFC_13_Integer_Norms_2026-10-24/con-zfc-root-fusion-2026-10-24/verification/`: `CLEARED_EXACT_AUDIT.json`, `CRT_AUDIT.json`, `EXACT_AUDIT.json`, `INTEGRATED_AUDIT.json`, `INTEGRATED_AUDIT_OPTIMIZED.json`, `PDF_QA.json`, `RELEASE_AUDIT.json`, `RELEASE_AUDIT_OPTIMIZED.json`, `audit.py`, `audit_cleared.py`, `check_crt.py`, `check_integrated.py`, `exact_polynomial.py`, `five_square_norm_expanded.json`, `verify_release.py`
- `110-budget-interpolation/baseline/late/`: `DIRECT_EXPANSION_CHECK.json`, `FETCH_LEDGER.json`, `LATE_COMPARISON.md`, `STATIC_AUTHENTICATION.json`, `download_list.json`, `late_comparison.tex`
- `110-budget-interpolation/baseline/replay/`: `check_parity_identity.py`, `run_upstream_audits.py`
- `110-budget-interpolation/baseline/replay/results/`: `PARITY_IDENTITY.json`, `PARITY_IDENTITY_OPTIMIZED.json`, `REPLAY_SUMMARY.json`
- `110-budget-interpolation/baseline/replay/results/parity_normal/`: `release.json`, `release.stdout.txt`, `summary.json`
- `110-budget-interpolation/baseline/replay/results/parity_optimized/`: `AUDIT.json`, `COMPACT_INDEPENDENT_AUDIT.json`, `COMPACT_KERNEL_AUDIT.json`, `GRAPH_AUDIT.json`, `NORM_FAMILY_AUDIT.json`, `SHIFT_AUDIT.json`, `audit.stdout.txt`, `audit_compact_kernel.stdout.txt`, `audit_norm_family.stdout.txt`, `audit_shift.stdout.txt`, `driver_policy.stderr.txt`, `independent_checks.stdout.txt`, `independent_compact_audit.stdout.txt`, `independent_graph_audit.stdout.txt`, `summary.json`
- `110-budget-interpolation/baseline/replay/results/rootfusion_normal/`: `release.json`, `release.stdout.txt`, `summary.json`
- `110-budget-interpolation/baseline/replay/results/rootfusion_optimized/`: `release.json`, `release.stdout.txt`, `summary.json`
- `110-budget-interpolation/baseline/replay/tex_check/`: `comparison_check.tex`
- `110-budget-interpolation/eleven/`: `CHECK_NORMAL.json`, `CHECK_OPTIMIZED.json`, `DEGREE_CHECK.json`, `DEGREE_PROOF.md`, `METRICS.json`, `NORM_ORDER_SEARCH.json`, `PROOF.md`, `README.md`, `SEMANTIC_CUT_CHECK.json`, `SEMANTIC_CUT_CHECK_OPTIMIZED.json`, `SOURCE_PINS.json`, `budget_intersective11_degree2240.json`, `budget_intersective11_degree2272.json`, `budget_intersective11_degree2912.json`, `build.py`, `check.py`, `check_degree.py`, `check_semantic_cuts.py`, `section.tex`
- `110-budget-interpolation/eleven/licenses/`: `LICENSE-interpolation12`, `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-interpolation12.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `110-budget-interpolation/eleven/provenance/centered17/`: `BUDGET_PROOF.md`, `COEFFICIENT_BINDING.json`, `PROOF.md`, `SOURCE_PINS.json`, `normalized17_degree48.json`
- `110-budget-interpolation/eleven/provenance/centered17/upstream/`: `CENTERED_BUDGET_PROOF.md`, `WAVE11_GUARDS_PROOF.md`, `WAVE11_JOINT_PROOF.md`, `centered_budget18_degree48.json`, `joint19_degree88.json`
- `110-budget-interpolation/eleven/provenance/centered18/`: `COEFFICIENT_BINDING.json`, `PROOF.md`, `SOURCE_PINS.json`, `centered_budget18_degree48.json`
- `110-budget-interpolation/eleven/provenance/centered18/upstream/`: `WAVE11_GUARDS_PROOF.md`, `joint19_degree88.json`
- `110-budget-interpolation/eleven/provenance/interpolation12/`: `INTERPOLATION12.md`, `LICENSE`, `NOTICE.md`, `README.md`, `SCHEMA.md`, `build_twelve.py`, `check_twelve.py`, `monotone_intersective12_degree4832.json`
- `110-budget-interpolation/eleven/provenance/rootfusion/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `110-budget-interpolation/eleven/provenance/rootfusion/upstream_ordinary/`: `SOURCES.json`
- `110-budget-interpolation/eleven/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`, `README.md`, `TRACE13_PROOF.md`
- `110-budget-interpolation/finalizers/`: `ABSORPTION_CHECKS.json`, `ABSORPTION_METRICS.json`, `ABSORPTION_PROOF.md`, `README.md`, `absorbed15_degree176.json`, `absorbed15_degree176_dag.json`, `build_absorption.py`, `check_absorption.py`, `section.tex`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/`: `AUDIT.json`, `COMPACT_INDEPENDENT_AUDIT.json`, `COMPACT_KERNEL_AUDIT.json`, `COMPACT_METRICS.json`, `COMPACT_NORM_REVIEW.md`, `DEGREE_CERTIFICATES.json`, `GRAPH_AUDIT.json`, `LICENSE`, `NORM_FAMILY_AUDIT.json`, `NORM_FAMILY_METRICS.json`, `NOTICE.md`, `PARITY_MERGER_REVIEW.md`, `PDF_QA.json`, `PROOF.md`, `PROOF15.md`, `README.md`, `RELEASE_VERIFICATION.json`, `SHIFT_AUDIT.json`, `SOURCE_PROVENANCE.json`, `THIRTEEN_MATHEMATICAL_REVIEW.md`, `abstract_norm5_dag.json`, `audit.py`, `audit_compact_kernel.py`, `audit_norm_family.py`, `audit_shift.py`, `build.py`, `build_norm_family.py`, `centered16_sos.json`, `centered16_sos_dag.json`, `centered16_unit_product.json`, `centered16_unit_product_dag.json`, `compact_norm.py`, `independent_checks.py`, `independent_compact_audit.py`, `independent_graph_audit.py`, `independent_proof_audit.md`, `norm4_expanded.json`, `norm4_kernel.json`, `norm5_expanded.json`, `norm5_kernel.json`, `parity13_direct.json`, `parity13_direct_dag.json`, `parity13_shifted.json`, `parity13_shifted_dag.json`, `parity14_sos.json`, `parity14_sos_dag.json`, `parity14_unit_product.json`, `parity14_unit_product_dag.json`, `parity15_sos.json`, `parity15_sos_dag.json`, `parity15_unit_product.json`, `parity15_unit_product_dag.json`, `parity16_sos.json`, `parity16_sos_dag.json`, `parity16_unit_product.json`, `parity16_unit_product_dag.json`, `results.json`, `verify_release.py`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/coefficients/`: `BINDING.json`, `VERIFICATION.json`, `verify.py`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/parent/`: `degree88_17.json`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/provenance/`: `forms-README.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/report/`: `parity-norms.pdf`, `parity-norms.tex`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/`: `LICENSE`, `NOTICE.md`, `README.md`, `SOURCE_PROVENANCE.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `verify.py`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/certificates/`: `ALTERNATIVE_ROUTES_REVIEW.md`, `INDEPENDENT_INTEGER_AUDIT.json`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `INTEGER_CHECKS.json`, `NINE_INDEPENDENT_REVIEW.md`, `PDF_QA.json`, `RANK_REGISTER_REVIEW.md`, `crt_degree16_24_degree.json`, `crt_degree26_22_degree.json`, `crt_degree26_23_degree.json`, `crt_degree28_21_degree.json`, `crt_degree44_20_degree.json`, `degree10_25_degree.json`, `degree12_23_degree.json`, `degree20_22_degree.json`, `degree26_20_degree.json`, `degree32_19_degree.json`, `octic26_degree.json`, `quartic37_degree.json`, `quartic37_direct_degree.json`, `sextic31_degree.json`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/coefficients/`: `BINDING.json`, `VERIFICATION.json`, `verify.py`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/inherited/determinant71/`: `NOTICE.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/integer/`: `audit.py`, `build.py`, `crt_degree16_24.json`, `crt_degree26_22.json`, `crt_degree26_23.json`, `crt_degree28_21.json`, `crt_degree44_20.json`, `degree10_25.json`, `degree12_23.json`, `degree20_22.json`, `degree26_20.json`, `degree32_19.json`, `octic26.json`, `polynomial.py`, `quartic37.json`, `quartic37_direct.json`, `sextic31.json`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/`: `COEFFICIENT_RECONSTRUCTION.json`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `build_correction.py`, `check_laurent_cone.py`, `laurent9_positive.json`, `laurent_candidate.json`, `laurent_cone_certificate.json`, `laurent_correction_nopad_4JDbasis.json`, `laurent_symbolic.py`, `section.tex`, `verify.py`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/31-sun10/coefficients/licenses/`: `LICENSE`, `LICENSE.Wade`, `NOTICE-K215.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/nine_full_radical/upstream/71-determinant-guards/nine_positive/`: `LICENSE`, `NOTICE.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/`: `AUDIT11.json`, `AUDIT12.json`, `LICENSE`, `NATIVE_FETCH.json`, `NOTICE.md`, `PROOF.md`, `UPSTREAM_FETCH.json`, `VERIFICATION.json`, `build11.py`, `build12.py`, `p11_positive_degree269.json`, `p12_positive_degree78.json`, `positive_reductions.tex`, `verify.py`, `verify11.py`, `verify12.py`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/`: `NOTICE-upstream.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/positive/native/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/report/`: `nine_section.tex`, `report.pdf`, `report.tex`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/transport/`: `PROOF.md`, `README.md`, `build_transport.py`, `check_transport.py`, `degree10_24.json`, `degree16_22.json`, `degree20_20_rank_register.json`, `degree28_19.json`, `degree32_18.json`, `degree88_17.json`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/transport/certificates/`: `DOMINATED_TRANSPORT_PROBES.json`, `INDEPENDENT_TRANSPORT_AUDIT.json`, `TRANSPORT_CHECKS.json`, `degree10_24_degree.json`, `degree16_22_degree.json`, `degree20_20_rank_register_degree.json`, `degree28_19_degree.json`, `degree32_18_degree.json`, `degree88_17_degree.json`
- `110-budget-interpolation/finalizers/source/con-zfc-parity-norms-2026-10-23/upstream/pell-congruences-source/transport/parents/`: `crt_degree44_20.json`, `degree10_25.json`, `degree12_23.json`, `degree20_22.json`, `degree26_20.json`, `degree32_19.json`, `octic26.json`, `quartic37.json`, `quartic37_direct.json`, `sextic31.json`
- `110-budget-interpolation/guard/`: `CHECK_NORMAL.json`, `CHECK_OPTIMIZED.json`, `DEGREE_CHECK.json`, `DEGREE_PROOF.md`, `EARLY_CRT_LEMMA.md`, `METRICS.json`, `NORM_EVALUATOR_PROOF.md`, `PROOF.md`, `SEMANTIC_CUT_CHECK.json`, `SEMANTIC_CUT_CHECK_OPTIMIZED.json`, `SOURCE_PINS.json`, `audit_support.py`, `budget12_aux_centered.json`, `budget12_tau_centered.json`, `build.py`, `check.py`, `check_degree.py`, `check_exact_cuts.py`, `check_semantic_cuts.py`, `circuit.py`, `degree_section.tex`, `exact_polynomial.py`, `five_square_norm.py`, `formal_radicals.py`, `section.tex`
- `110-budget-interpolation/guard/coefficients/`: `BINDING.json`
- `110-budget-interpolation/guard/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `110-budget-interpolation/guard/provenance/centered17/`: `BUDGET_PROOF.md`, `COEFFICIENT_BINDING.json`, `PROOF.md`, `SOURCE_PINS.json`, `normalized17_degree48.json`
- `110-budget-interpolation/guard/provenance/centered17/upstream/`: `CENTERED_BUDGET_PROOF.md`, `WAVE11_GUARDS_PROOF.md`, `WAVE11_JOINT_PROOF.md`, `centered_budget18_degree48.json`, `joint19_degree88.json`
- `110-budget-interpolation/guard/provenance/centered18/`: `COEFFICIENT_BINDING.json`, `PROOF.md`, `SOURCE_PINS.json`, `centered_budget18_degree48.json`
- `110-budget-interpolation/guard/provenance/centered18/upstream/`: `WAVE11_GUARDS_PROOF.md`, `joint19_degree88.json`
- `110-budget-interpolation/guard/provenance/rootfusion/`: `CALIBRATION_STATUS.md`, `CON_ZFC_FORMS_README.md`, `FORMALIZATION_BOUNDARY.md`, `INDEPENDENT_CRT_ARITHMETIC_REVIEW.md`, `INDEPENDENT_INTEGER_NORM_AUDIT.md`, `JOINT_GUARD_AND_PROJECTIONS.md`, `NORMALIZED_NORMS_PROOF.md`, `RESIDUE_AND_DETERMINANT.md`, `REVIEWED_FRONTIER.md`, `SOURCE_EXTRACTION.json`, `SQUARED_MODULUS_PROOF.md`
- `110-budget-interpolation/guard/provenance/rootfusion/upstream_ordinary/`: `SOURCES.json`
- `110-budget-interpolation/guard/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`, `README.md`, `TRACE13_PROOF.md`
- `110-budget-interpolation/positive/ten_centered/`: `FUTURE_WORK.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `degree_specialization.py`, `independent_check.py`, `rebuild_coefficients.py`, `section.tex`, `verify.py`
- `110-budget-interpolation/positive/ten_centered/coefficients/`: `BINDING.json`, `UPSTREAM_BINDING.json`
- `110-budget-interpolation/positive/ten_centered/generated/`: `COEFFICIENT_CHECKS.json`, `DEGREE_SPECIALIZATIONS.json`, `INDEPENDENT_CHECKS.json`, `VERIFICATION_NORMAL.json`, `VERIFICATION_OPTIMIZED.json`, `normal_build.py.stdout.txt`, `normal_degree_specialization.py.stdout.txt`, `normal_independent_check.py.stdout.txt`, `normal_rebuild_coefficients.py.stdout.txt`, `optimized_build.py.stdout.txt`, `optimized_degree_specialization.py.stdout.txt`, `optimized_independent_check.py.stdout.txt`, `optimized_rebuild_coefficients.py.stdout.txt`, `p10_natural.json`, `p10_positive.json`
- `110-budget-interpolation/positive/ten_centered/upstream/`: `SOURCE_PINS.json`, `TEN_POSITIVE_PROOF.md`
- `110-budget-interpolation/positive/ten_centered/upstream/interfaces/`: `OBJECT_ZFC.md`, `SIZE_REDUCTION.md`, `STATUS.md`, `k215_transitions.json`
- `110-budget-interpolation/positive/ten_centered/upstream/interfaces/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `110-budget-interpolation/provenance/certificate_predecessor/`: `NOTICE.md`, `PROOF.md`, `TM_COMPILER_PROOF.md`, `build_dag.py`, `core.py`
- `110-budget-interpolation/provenance/certificate_predecessor/upstream/`: `NOTICE-K215.md`
- `110-budget-interpolation/report/`: `PDF_QA.json`, `coefficients.tex`, `report.pdf`, `report.tex`, `summary.tex`, `validation.tex`
- `110-budget-interpolation/report/qa/`: `before_layout_hashes.json`, `changed_pages.json`
- `110-budget-interpolation/review/budget/`: `RECEIPT_NORMAL.json`, `RECEIPT_OPTIMIZED.json`, `REVIEW.md`, `audit_budget.py`, `probe_norm.py`
- `110-budget-interpolation/review/eleven/`: `RECEIPT_NORMAL.json`, `RECEIPT_OPTIMIZED.json`, `REVIEW.md`, `independent_review.py`
- `110-budget-interpolation/review/positive/`: `REVIEW.md`, `REVIEW_NORMAL.json`, `REVIEW_OPTIMIZED.json`, `independent_review.py`
- `111-carriers-even-indices/`: `LICENSE.UPSTREAM`, `MANIFEST.json`, `README.md`, `SOURCE_LEDGER.json`, `check_sources.py`, `report.pdf`, `report.tex`, `verify_all.py`
- `111-carriers-even-indices/crt12/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `PROOF.md`, `build.py`, `check.py`, `integral.json`, `rational.json`
- `111-carriers-even-indices/crt12/source/`: `LICENSE.UPSTREAM`, `independent-peer-optimized.json`, `independent-peer.json`, `independent-peer.md`, `independent-peer.py`, `independent_norm_oracle.py`, `parent-equation.json`, `scalar-parent-integral.json`, `scalar-parent-proof.md`, `scalar-parent-rational.json`, `signed-quadratic-proof.md`
- `111-carriers-even-indices/direct566/`: `ADDITIONAL_CUT_REVIEW.json`, `CENSUS.json`, `INDEPENDENT_CHECK.json`, `INDEPENDENT_CHECK_OPTIMIZED.json`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `SOURCE.json`, `SOURCE_BYTE_REVIEW.json`, `build_even_index.py`, `check_even_index.py`, `frame_parent.json`, `frame_projection.json`, `independent_algebra.py`, `ledger.json`, `odd_index_negative_control.json`, `parent.json`
- `111-carriers-even-indices/direct566/proofs/`: `even_index_lemma.md`, `even_power_compiler.md`, `shared_signs.md`
- `111-carriers-even-indices/direct566/source/`: `call_certificate.json`, `raw_builder.json`
- `111-carriers-even-indices/direct566/source/signsharing/`: `domain.json`, `parent.json`
- `111-carriers-even-indices/direct566/source/signsharing/source/`: `SOURCE_THEOREM_README.md`, `domain.json`, `parent.json`
- `111-carriers-even-indices/direct566/support16_affine2/`: `equation.json`, `polynomial.json`, `projection.json`
- `111-carriers-even-indices/direct566/support8_affine2/`: `equation.json`, `polynomial.json`, `projection.json`
- `111-carriers-even-indices/direct566/support8_default/`: `equation.json`, `polynomial.json`, `projection.json`
- `111-carriers-even-indices/direct566/tools/`: `LICENSE`
- `111-carriers-even-indices/direct589/`: `CENSUS.json`, `INDEPENDENT_CHECK.json`, `INDEPENDENT_CHECK_OPTIMIZED.json`, `MANIFEST.json`, `PROOF.md`, `README.md`, `SOURCE.json`, `SOURCE_BYTE_REVIEW.json`, `build_equal_sum.py`, `check_equal_sum.py`, `domain.json`, `parent.json`
- `111-carriers-even-indices/direct589/source/`: `SOURCE_THEOREM_README.md`, `domain.json`, `parent.json`
- `111-carriers-even-indices/direct589/support16_affine2/`: `equation.json`, `polynomial.json`, `projection.json`
- `111-carriers-even-indices/direct589/support8_affine2/`: `equation.json`, `polynomial.json`, `projection.json`
- `111-carriers-even-indices/direct589/support8_default/`: `equation.json`, `polynomial.json`, `projection.json`
- `111-carriers-even-indices/direct589/tools/`: `LICENSE`
- `111-carriers-even-indices/height12/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `PROOF.md`, `build.py`, `centered.json`, `check.py`, `integral.json`, `rational.json`
- `111-carriers-even-indices/height12/source/`: `LICENSE.UPSTREAM`, `independent-peer-optimized.json`, `independent-peer.json`, `independent-peer.md`, `independent-peer.py`, `independent_norm_oracle.py`, `parent-equation.json`, `scalar-parent-integral.json`, `scalar-parent-proof.md`, `scalar-parent-rational.json`, `signed-quadratic-proof.md`
- `111-carriers-even-indices/inherited/`: `PROPOSAL_REVIEW_LATEST.md`
- `111-carriers-even-indices/inherited/direct/`: `ARCHIVE_MEMBER_PINS.json`, `ENDPOINT_AND_PROOF_CHAIN.md`, `LICENSE`, `MANIFEST.json`, `REPOSITORY_PINS.json`, `SIGNED_INDEX_PIN.json`
- `111-carriers-even-indices/inherited/direct/repository/`: `PROPOSAL_REVIEW_QUARTICS407888.md`, `PROPOSAL_REVIEW_SHARED_PELL1873_SIGNED.md`
- `111-carriers-even-indices/inherited/direct/repository/candidates/projected-factorial-radius/`: `PROOF.md`
- `111-carriers-even-indices/inherited/direct/repository/candidates/projected-radius-integers/`: `PROOF.md`, `README.md`
- `111-carriers-even-indices/inherited/direct/repository/candidates/projected-radius-mixed-bounds/`: `PROOF.md`, `README.md`
- `111-carriers-even-indices/inherited/direct/repository/candidates/projected-radius-mixed/`: `PROOF.md`
- `111-carriers-even-indices/inherited/direct/repository/candidates/synchronized-factorial-radius/`: `PROOF.md`
- `111-carriers-even-indices/inherited/direct/repository/research/comparison-base-sign/`: `README.md`
- `111-carriers-even-indices/inherited/direct/repository/research/factorial-radius-guard/`: `PROOF.md`
- `111-carriers-even-indices/inherited/direct/repository/research/factorial-radius-output-sign-profile/`: `README.md`, `SOURCE_PINS.json`
- `111-carriers-even-indices/inherited/direct/repository/research/factorial-radius-output-sign/`: `PROOF.md`
- `111-carriers-even-indices/inherited/direct/repository/research/guard-seed-consequences/`: `README.md`
- `111-carriers-even-indices/inherited/direct/repository/research/guard-sign-orbits/`: `README.md`
- `111-carriers-even-indices/inherited/direct/repository/research/main-root-and-modulus-signs/`: `README.md`, `SOURCE_PINS.json`
- `111-carriers-even-indices/inherited/direct/repository/research/paired-index-guards/`: `LOCAL_FACTORIAL.md`
- `111-carriers-even-indices/inherited/native/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-K215.md`, `PROVENANCE.json`, `README.md`, `check_provenance.py`
- `111-carriers-even-indices/inherited/scalar_parent/`: `README.md`, `SOURCE_PINS.json`
- `111-carriers-even-indices/peer/`: `CRT_CHECK.json`, `CRT_CHECK_OPTIMIZED.json`, `CRT_PEER_REVIEW.md`, `EVEN_INDEX_REPORT_REVIEW.md`, `FINAL_REPORT_REVIEW.md`, `REVIEW_RESOLUTION.md`, `peer_crt.py`
- `111-carriers-even-indices/verification/`: `PDF_QA.json`, `normal.json`, `optimized.json`
- `112-powered-saturation-round14/`: `ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.pdf`, `ENDPOINTS.json`, `LICENSE`, `MANIFEST_SHA256.json`, `NOTICE.md`, `README.md`, `verify.py`
- `112-powered-saturation-round14/architecture/`: `DERIVED_LABEL_RANGE_PROOF.md`, `FACTORIAL_CARRIER_PROOF.md`, `HYBRID_PROOF.md`, `README.md`, `RELEASE_WHITELIST.json`, `REPRODUCTION.json`, `SEMANTIC_CHECKS.json`, `SEMANTIC_CHECKS_OPTIMIZED.json`, `SOURCE_BINDING.json`, `build_derived_label_range.py`, `build_factorial_carrier.py`, `build_hybrid.py`, `check_semantics.py`, `section.tex`
- `112-powered-saturation-round14/architecture/carrier_hybrid_shell/raw/`: `equation.json`, `raw_audit_input.json`
- `112-powered-saturation-round14/architecture/derived16_cantor/`: `SUMMARY.json`
- `112-powered-saturation-round14/architecture/derived16_cantor/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `112-powered-saturation-round14/architecture/derived16_cantor/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `local_majorant.json`, `macro_inventory.json`, `raw_audit_input.json`
- `112-powered-saturation-round14/architecture/derived16_shell/raw/`: `equation.json`, `raw_audit_input.json`
- `112-powered-saturation-round14/architecture/factorial16_cantor/`: `SUMMARY.json`
- `112-powered-saturation-round14/architecture/factorial16_cantor/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `112-powered-saturation-round14/architecture/factorial16_cantor/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `local_majorant.json`, `macro_inventory.json`, `raw_audit_input.json`
- `112-powered-saturation-round14/direct/`: `NOTICE.md`, `REPRODUCTION.json`, `SELECTED_ARTIFACTS.json`, `SOURCE_PINS.json`, `bounded_label_source.py`, `build_signed.py`, `factor_horn.py`, `reproduce_integer519.py`, `residuals_integer519.tex`, `section.tex`, `translate_coordinates.py`
- `112-powered-saturation-round14/direct/derived16_centered_shell/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `translation_certificate.json`
- `112-powered-saturation-round14/direct/derived16_factored_shell/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projection_certificate.json`
- `112-powered-saturation-round14/direct/derived16_signed_shell/`: `METRICS.json`, `domain_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `mixed_source.json`, `projection_certificate.json`
- `112-powered-saturation-round14/direct/hybrid_noguard_signed_shell/`: `METRICS.json`, `domain_certificate.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `mixed_source.json`, `projection_certificate.json`
- `112-powered-saturation-round14/direct/integer519/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projection_certificate.json`
- `112-powered-saturation-round14/direct/integer519_centered/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `translation_certificate.json`
- `112-powered-saturation-round14/direct_audit/`: `DERIVED517_CENTERED_REPLAY.json`, `DERIVED517_REPLAY.json`, `DERIVED_LABEL_LITERAL_REPLAY.json`, `INTEGER519_CENTERED_REPLAY.json`, `INTEGER519_REPLAY.json`, `OPTIMIZED_REPLAY.json`, `UNIFIED_REVIEW.md`, `audit_literal_independent.py`, `audit_signed_independent.py`, `audit_translation_independent.py`
- `112-powered-saturation-round14/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `112-powered-saturation-round14/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/equations/integer553/`: `equation.json`, `expanded_polynomial.json`
- `112-powered-saturation-round14/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/equations/natural375/`: `equation.json`, `expanded_polynomial.json`
- `112-powered-saturation-round14/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/proofs/`: `AMPLIFIED_CRT_PROOF.md`, `INDEPENDENT_AMPLIFIED_CRT_REVIEW.md`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`, `README.md`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/code/`: `norm_transform.py`, `shared_radius.py`, `shell_source.py`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/equations/integer660/`: `equation.json`, `expanded_polynomial.json`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/equations/natural363/`: `equation.json`, `expanded_polynomial.json`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/equations/natural364/`: `equation.json`, `expanded_polynomial.json`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/proofs/`: `reciprocal_moduli_proof.md`, `shared_radius_proof.md`, `shell_encoding_proof.md`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/provenance/`: `INHERITED_FILES.json`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `112-powered-saturation-round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `112-powered-saturation-round14/norm/`: `CHECKS.json`, `CHECK_RUN.txt`, `CHECK_RUN_OPTIMIZED.txt`, `PROOF.md`, `README.md`, `RELEASE_SHA256.json`, `RELEASE_WHITELIST.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `equation.json`, `equation_reduced.json`
- `112-powered-saturation-round14/norm/provenance/`: `scalar_parent.json`, `scalar_parent_PROOF.md`
- `112-powered-saturation-round14/provenance/`: `NORM_LEGACY_IMPORT.json`
- `112-powered-saturation-round14/provenance/direct_licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `112-powered-saturation-round14/provenance/norm_legacy/`: `LICENSE`
- `112-powered-saturation-round14/provenance/norm_legacy/inherited/`: `LICENSE`, `NOTICE.md`
- `112-powered-saturation-round14/provenance/norm_legacy/inherited/signed_guards/`: `LICENSE`, `NOTICE.md`
- `112-powered-saturation-round14/provenance/norm_legacy/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `112-powered-saturation-round14/radicals/`: `CHECKS_NORMAL.json`, `CHECKS_OPTIMIZED.json`, `MANIFEST_SHA256.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `verify_arithmetic.py`
- `112-powered-saturation-round14/radicals/source/`: `MANIFEST.json`, `PROOF.md`, `README.md`, `source__signed-quadratic-proof.md`
- `112-powered-saturation-round14/radicals_audit/`: `AUDIT_RESULTS.json`, `AUDIT_SHA256.json`, `CLEAN_REPLAY.json`, `INDEPENDENT_REVIEW.md`, `audit_independent.py`
- `112-powered-saturation-round14/radicals_audit/fixtures/`: `pinned_integral_parent.json`
- `112-powered-saturation-round14/report/`: `comparison.tex`, `direct_arithmetic.tex`, `direct_signed.tex`, `main.tex`, `norm_proof.tex`, `reproducibility.tex`
- `112-powered-saturation-round14/report_audit/`: `FINAL_METRICS.json`, `PDF_QA.json`, `REVIEW.md`, `check_final_metrics.py`
- `112-powered-saturation-round14/review/`: `BASELINE_COMPARISON.md`, `CIRCUIT_AUDIT.json`, `COUNTEREXAMPLE_SCOPE.md`, `LITERAL_AUDIT.json`, `MANIFEST.json`, `RECENT_COMMITS.json`, `audit_circuit_counts.py`, `audit_literal_polynomials.py`, `comparison_fragment.tex`
- `112-powered-saturation-round14/review/sources/`: `PROPOSAL_REVIEW_LATEST.md`, `RECENT_INTAKE.md`, `active_README.md`, `factorial-radius-output-sign_PROOF.md`, `forms_README.md`, `hilbert_README.md`, `incoming_README.md`, `scalar-carrier12_SOURCE_PINS.json`, `source_independent-peer.md`, `ten-positive-zero-offset_README.md`
- `112-powered-saturation-round14/review/sources/factorial-radius-output-sign-profile/`: `CENSUS.json`, `README.md`
- `112-powered-saturation-round14/review/sources/public_support16_affine2/`: `equation.json`, `polynomial.json`
- `112-powered-saturation-round14/review/sources/public_support8_default/`: `equation.json`, `polynomial.json`
- `112-powered-saturation-round14/review/sources/scalar-carrier12/`: `PROOF.md`, `README.md`, `integral.json`, `rational.json`
- `112-powered-saturation-round14/review/sources/scalar-carrier12/source/`: `signed-quadratic-proof.md`
- `112-powered-saturation-round14/review/sources/ten-positive-direct-zero-offset/`: `PROOF.md`, `README.md`, `equation.json`
- `112-powered-saturation-round14/verification/`: `CLEAN_ARCHIVE_REPLAY.json`, `DEVELOPMENT_REPLAY.json`, `ROOT_ISOLATED_REPLAY.json`, `VISUAL_QA.json`
- `113-saturated-pell/`: `INTEGRATION.md`, `MANIFEST.json`, `README.md`, `RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `build_saturation.py`, `check_manifest.py`, `report.pdf`, `report.tex`, `verify.py`
- `113-saturated-pell/alternative/`: `relational_kernel.py`, `verification.json`
- `113-saturated-pell/audits/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`
- `113-saturated-pell/checks/`: `INTEGER12_OPTIMIZED.json`, `INTEGER12_ROOT_CHECK.json`, `INTEGER12_SATURATED_DEGREE_RAY.json`, `INTEGER12_SATURATED_OPTIMIZED.json`, `INTEGER12_SATURATED_ROOT_CHECK.json`, `PDF_LAYOUT_CHECK.json`, `SATURATED_FORMULA_BINDING.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `all_degree_verification.json`, `polynomial_ray.py`, `verify_all_degree_rays.py`, `verify_integer12_saturated_ray.py`, `verify_saturated_bindings.py`, `verify_saturated_degree_rays.py`
- `113-saturated-pell/coefficients/`: `recipe_compact44.py`
- `113-saturated-pell/coefficients/compact44_bfs/`: `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `113-saturated-pell/equations/`: `both_centers.json`, `direct_both_centers.json`, `direct_saturated_sharp.json`, `direct_saturated_upper.json`, `direct_strong_center.json`, `saturated_sharp.json`, `saturated_upper.json`, `strong_center.json`
- `113-saturated-pell/integer12/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `integral_centered.json`, `rational_centered.json`, `verify.py`
- `113-saturated-pell/integer12/parent/`: `PROOF.md`, `SOURCE_PINS.json`, `check_math.py`, `integral.json`, `rational.json`
- `113-saturated-pell/integer12/parent/source/`: `LICENSE.UPSTREAM`, `independent_norm_oracle.py`, `signed-quadratic-proof.md`
- `113-saturated-pell/integer12_saturated/`: `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `INDEPENDENT_SEMANTIC_AUDIT.md`, `INHERITED_SOURCE_PINS.json`, `PROOF.md`, `README.md`, `build.py`, `integral.json`, `rational.json`, `verify.py`
- `113-saturated-pell/integer12_saturated/parent/`: `PROOF.md`, `SOURCE_PINS.json`, `check_math.py`, `integral.json`, `rational.json`
- `113-saturated-pell/integer12_saturated/parent/source/`: `LICENSE.UPSTREAM`, `independent_norm_oracle.py`, `signed-quadratic-proof.md`
- `113-saturated-pell/report_parts/`: `appendix_relational_kernel.tex`, `centered_degree_proof.tex`, `complete_constants.tex`, `integer12.tex`, `integer12_saturated.tex`, `saturated_degree_proof.tex`, `saturation_semantics.tex`
- `113-saturated-pell/source/`: `LICENSE.UPSTREAM`, `README.md`, `incoming_archive_inventory.json`, `one_page_README.md`, `one_page_SOURCE_PINS.json`, `previous_complete_equation.tex`, `ten-positive-direct-zero-offset_SOURCE_PINS.json`, `ten-positive-zero-offset_SOURCE_PINS.json`
- `113-saturated-pell/source/parents/`: `one-page-short10.json`, `ten-positive-direct-zero-offset.json`, `ten-positive-zero-offset.json`
- `113-saturated-pell/source/proofs/`: `independent_three_root_centering.md`, `ten-positive-direct-zero-offset.md`, `ten-positive-quadratic-projection.md`, `ten-positive-short-projection.md`, `ten-positive-zero-offset.md`
- `114-signed-powers-height-two/`: `LICENSE.UPSTREAM`, `MANIFEST.json`, `README.md`, `check_projection_independent.py`, `generate_rows.py`, `report.pdf`, `report.tex`, `verify_all.py`
- `114-signed-powers-height-two/height_two/`: `PROOF.md`, `README.md`, `REPRODUCTION.json`, `build.py`, `verify.py`
- `114-signed-powers-height-two/height_two/anchored/`: `BUILD.json`, `VERIFY.json`, `VERIFY_OPTIMIZED.json`, `certificate.json`, `equation.json`, `expanded_polynomial.json`, `source.json`
- `114-signed-powers-height-two/quotient_frame/`: `CENSUS.json`, `FILTERED_PREFIX.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `SOURCE_VERIFY.json`, `SOURCE_VERIFY_OPTIMIZED.json`, `build.py`, `check_source.py`, `domain.json`, `parent.json`
- `114-signed-powers-height-two/quotient_frame/provenance/`: `INHERITED_SOURCE_MAP.json`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/candidates/projected-factorial-radius/`: `PROOF.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/candidates/projected-radius-comparison-base/`: `PROOF.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/candidates/projected-radius-mixed-bounds/`: `PROOF.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/candidates/projected-radius-mixed-orbits/`: `PROOF.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/candidates/retained-radius-comparison-base/`: `PROOF.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/research/comparison-base-sign/`: `README.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/research/factorial-radius-guard/`: `PROOF.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/research/factorial-radius-output-sign-profile/`: `CENSUS.json`, `README.md`, `SOURCE_PINS.json`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/research/factorial-radius-output-sign/`: `PROOF.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/research/main-root-and-modulus-signs/`: `README.md`
- `114-signed-powers-height-two/quotient_frame/provenance/later_proofs/research/paired-index-guards/`: `LOCAL_FACTORIAL.md`, `README.md`
- `114-signed-powers-height-two/quotient_frame/source/`: `arithmetic_interfaces.json`, `domain75.json`, `parent75.json`, `raw_builder.json`, `sign_certificate.json`
- `114-signed-powers-height-two/quotient_frame/support16_affine2/`: `equation.json`, `polynomial.json`, `projection.json`, `terminal_elimination_certificate.json`
- `114-signed-powers-height-two/quotient_frame/support8/`: `equation.json`, `polynomial.json`, `projection.json`, `terminal_elimination_certificate.json`
- `114-signed-powers-height-two/receipts/`: `output_projection_coefficients.json`, `quotient_projection_coefficients.json`
- `114-signed-powers-height-two/receipts/final_package/`: `SUMMARY.json`, `quotient_frame_projection.json`, `quotient_frame_source.json`, `signed_frame_projection.json`, `signed_frame_source.json`
- `114-signed-powers-height-two/review/`: `PEER_REVIEW.json`, `PEER_REVIEW_OPTIMIZED.json`, `QUOTIENT_PEER_REVIEW.json`, `QUOTIENT_PEER_REVIEW_OPTIMIZED.json`, `QUOTIENT_REVIEW.md`, `REVIEW.md`, `inspect_prefix.py`, `peer_check.py`
- `114-signed-powers-height-two/sections/`: `abstract.tex`, `calibration.tex`, `equation_rows.tex`, `height.tex`, `references.tex`, `research.tex`, `results.tex`, `signed.tex`, `verification.tex`
- `114-signed-powers-height-two/signed_frame/`: `CENSUS.json`, `FILTERED_PREFIX.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `SOURCE_VERIFY.json`, `SOURCE_VERIFY_OPTIMIZED.json`, `build.py`, `check_source.py`, `domain.json`, `parent.json`
- `114-signed-powers-height-two/signed_frame/source/`: `arithmetic_interfaces.json`, `domain75.json`, `parent75.json`, `raw_builder.json`, `sign_certificate.json`
- `114-signed-powers-height-two/signed_frame/support16_affine2/`: `equation.json`, `polynomial.json`, `projection.json`, `terminal_elimination_certificate.json`
- `114-signed-powers-height-two/signed_frame/support8/`: `equation.json`, `polynomial.json`, `projection.json`, `terminal_elimination_certificate.json`
- `115-synchronized-exponents/`: `LICENSE`, `README.md`, `SOURCE_PINS.json`, `report.pdf`, `report.tex`, `residuals.tex`
- `115-synchronized-exponents/checks/`: `ARITHMETIC_CONTROLS.json`, `FINAL_REPORT_REVIEW.json`, `INDEPENDENT_FINITE_REVIEW.json`, `LATENT_INDEX.json`, `PDF_REVIEW.json`, `PROTOTYPE_BINDING.json`, `RECONSTRUCTION.json`, `VERIFY.json`, `VERIFY_OPTIMIZED.json`
- `115-synchronized-exponents/code/`: `check_arithmetic.py`, `check_latent_index.py`, `construction.py`, `evaluate.py`, `render_residuals.py`, `verify.py`
- `115-synchronized-exponents/direct/`: `CENSUS.json`, `gate_ledger.json`, `integer_companion.json`, `interface.json`, `raw_complete.json`
- `115-synchronized-exponents/direct/natural358/`: `equation.json`, `polynomial.json`, `projection.json`
- `115-synchronized-exponents/direct/natural361/`: `equation.json`, `polynomial.json`, `projection.json`
- `115-synchronized-exponents/direct/source/`: `equation.json`, `polynomial.json`
- `115-synchronized-exponents/proofs/`: `incoming_comparison.md`, `independent_exponent_review.md`, `independent_finite_review.md`, `parent_407_review.md`, `parent_projected_factorial_radius.md`, `pinned_frontier.md`, `shared_square_and_latent_index.md`
- `115-synchronized-exponents/supplement/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `README.md`, `REPORT_SECTION.tex`, `SOURCE_PINS.json`, `check.py`, `fold_additional.py`, `fold_transport.py`
- `115-synchronized-exponents/supplement/circuits/`: `ADDITIONAL_CHECK.json`, `FOLD_TRANSPORT_CHECK.json`, `positive10_98_degree368.json`, `positive10_direct103_degree340.json`, `positive11_107_degree211.json`, `positive12_95_degree70.json`, `positive13_87_degree51.json`
- `115-synchronized-exponents/supplement/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `115-synchronized-exponents/supplement/coefficients/recipe/`: `NOTICE-upstream.md`
- `115-synchronized-exponents/supplement/inherited_proofs/`: `ten_direct_zero_offset.md`, `ten_zero_offset.md`, `twelve_polarized.md`
- `115-synchronized-exponents/supplement/parents/candidates/free-j-polarized-positive/`: `equation.json`
- `115-synchronized-exponents/supplement/parents/candidates/ten-positive-direct-zero-offset/`: `equation.json`
- `115-synchronized-exponents/supplement/parents/candidates/ten-positive-zero-offset/`: `equation.json`
- `115-synchronized-exponents/upstream/`: `AUTHENTICATED_COPY.json`
- `115-synchronized-exponents/upstream/engine/`: `LICENSE`, `NOTICE.md`
- `115-synchronized-exponents/upstream/engine/upstream/`: `LICENSE`, `NOTICE.md`
- `115-synchronized-exponents/upstream/engine/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `116-coprime-projection/`: `DEPENDENCIES.md`, `MANIFEST.json`, `README.md`, `REPLAY_SUMMARY.json`, `REPRODUCE_CHECK.json`, `RESULTS.json`, `reproduce.py`
- `116-coprime-projection/alternative/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `FOUR_CORNER_21NAT.json`, `FOUR_CORNER_22NAT.json`, `MANIFEST.sha256.json`, `METRICS.json`, `POWER_ONE_9AUX.json`, `POWER_TWO_13AUX.json`, `POWER_TWO_14AUX.json`, `PROOF.md`, `README.md`, `SOURCES.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `section.tex`, `standalone.pdf`, `standalone.tex`
- `116-coprime-projection/alternative/prior/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`
- `116-coprime-projection/baseline/`: `BASELINE_COMPARISON.md`, `CALIBRATION_CITATIONS.md`, `FETCH_LEDGER.json`, `FRONTIER_SOURCE_AUDIT.json`, `INCOMING_METRIC_INDEX.json`, `LATE_BASELINE_NOTE.json`, `LATE_BASELINE_NOTE.md`, `check_late_evidence.py`
- `116-coprime-projection/baseline/late_head_evidence/`: `PROPOSAL_REVIEW_LATEST.md`
- `116-coprime-projection/baseline/late_head_evidence/research/encoded-index-sign-profile/`: `README.md`
- `116-coprime-projection/baseline/late_head_evidence/research/historical-archives-compat/`: `README.md`
- `116-coprime-projection/baseline/late_head_evidence/research/incoming-e13c748234/`: `README.md`
- `116-coprime-projection/baseline/late_head_evidence/research/pow2-output-sign/`: `PROOF.md`
- `116-coprime-projection/baseline/late_head_evidence/research/ten-positive-expanded-transport/`: `PROOF.md`, `README.md`, `direct103.json`, `zero98.json`
- `116-coprime-projection/baseline/late_head_evidence/reviews/`: `incoming-e13-root-peer.md`
- `116-coprime-projection/integer/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `REBUILD.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `fused11_integral.json`, `fused11_rational.json`, `guard_fused11_aux.json`, `guard_fused11_direct.json`, `section.tex`
- `116-coprime-projection/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `116-coprime-projection/integer/source/`: `LICENSE.UPSTREAM`, `scalar12-proof.md`, `signed-quadratic-proof.md`
- `116-coprime-projection/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `116-coprime-projection/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `116-coprime-projection/lowdegree/`: `DEPENDENCIES.md`, `LICENSE.ProveIt`, `MANIFEST.json`, `METRICS.json`, `PROOF.md`, `README.md`, `REPRODUCE_PLAN.json`, `SOURCE_PINS.json`, `build.py`, `circuit.py`, `equation.json`, `section.tex`, `section12.tex`, `section13.tex`, `specification.json`
- `116-coprime-projection/lowdegree/fourteen/`: `PROOF.md`, `build.py`, `centered_equation.json`, `centered_specification.json`, `equation.json`, `specification.json`
- `116-coprime-projection/lowdegree/fourteen/review/`: `CENTERED_EVALUATOR_REVIEW.md`, `CHECK.json`, `CHECK_CENTERED.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`
- `116-coprime-projection/lowdegree/review/`: `CHECK.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`
- `116-coprime-projection/lowdegree/source/`: `SIGNED_QUADRATIC_PROOF.md`
- `116-coprime-projection/lowdegree/thirteen/`: `PROOF.md`, `build.py`, `equation.json`, `horner_equation.json`, `horner_specification.json`, `specification.json`
- `116-coprime-projection/lowdegree/thirteen/review/`: `CHECK.json`, `GENERIC_NORM_CERTIFICATE.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`
- `116-coprime-projection/lowdegree/twelve/`: `PROOF.md`, `build.py`, `equation.json`, `specification.json`
- `116-coprime-projection/lowdegree/twelve/review/`: `CHECK.json`, `DIRECT_NORM_CERTIFICATE.json`, `GENERIC_CENTERED_NORM_CERTIFICATE.json.gz`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`
- `116-coprime-projection/positive/`: `BUILD_CHECK.json`, `BUILD_CHECK_OPTIMIZED.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `PROOF.md`, `README.md`, `build.py`, `check.py`, `equation.json`, `section.tex`
- `116-coprime-projection/positive/coefficients/`: `BINDING.json`
- `116-coprime-projection/positive/source/`: `BFS_SOURCE_PINS.json`, `BFS_SOURCE_TRANSFER.md`, `DIRECT_PROOF.md`, `EXPANDED_TRANSPORT_SOURCE_PROOF.md`, `FREE_J_PROOF.md`, `FUSION98_PROOF.md`, `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`, `QUADRATIC_PROOF.md`, `SHORT_PROOF.md`, `WEIGHTED_PROOF.md`, `ZERO_PROOF.md`, `fusion98_equation.json`, `parent_equation.json`
- `116-coprime-projection/report/`: `baseline.tex`, `build_report.sh`, `coefficients.tex`, `common.tex`, `references.tex`, `report.pdf`, `report.tex`, `results.tex`, `summary.tex`, `validation.tex`
- `116-coprime-projection/report/qa/`: `FINAL_QA.json`, `FINAL_QA.txt`
- `116-coprime-projection/report/sections/`: `alternative.tex`, `integer.tex`, `lowdegree.tex`, `positive.tex`, `thirteen.tex`, `twelve.tex`
- `116-coprime-projection/review/alternative/`: `AUDIT_CHECK.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.json`, `OPTIMIZED_RECEIPT.json`, `PORTABILITY.patch`, `PORTABILITY_CHECK.json`, `SOURCE_CHECK.json`, `audit_power_graph.py`
- `116-coprime-projection/review/alternative/provenance/`: `AUDIT_CHECK.original.json`, `audit_power_graph.original.py`
- `116-coprime-projection/review/integer/`: `AUDIT_RESULTS.json`, `AUDIT_RUN.txt`, `AUDIT_RUN_OPTIMIZED.txt`, `INDEPENDENT_REVIEW.md`, `PREDECESSOR_BINDINGS.json`, `README.md`, `independent_audit.py`
- `116-coprime-projection/review/lowdegree/`: `CHECK.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`, `carrier_lemma.txt`
- `116-coprime-projection/review/lowdegree12/`: `CHECK.json`, `DIRECT_NORM_CERTIFICATE.json`, `GENERIC_CENTERED_NORM_CERTIFICATE.json.gz`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`
- `116-coprime-projection/review/lowdegree13/`: `CHECK.json`, `GENERIC_NORM_CERTIFICATE.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`, `audit_horner.py`
- `116-coprime-projection/review/lowdegree14/`: `CHECK.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`, `audit_centered.py`
- `116-coprime-projection/review/positive/`: `AUDIT.md`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `EXPANDED_CARRIER_AUDIT.md`, `PORTABILITY_CHECK.json`, `PRODUCER_REPLAY.json`, `SOURCE_PINS.json`, `audit.py`
- `116-coprime-projection/review/positive/provenance/`: `FUSION98_PORTABLE_AUDIT.md`, `FUSION98_PORTABLE_CHECK.json`, `FUSION98_PORTABLE_CHECK_OPTIMIZED.json`, `FUSION98_PORTABLE_PORTABILITY_CHECK.json`, `FUSION98_PORTABLE_audit.py.txt`, `ORIGINAL_AUDIT.md`, `ORIGINAL_CHECK.json`, `ORIGINAL_audit.py.txt`
- `117-quadratic-frames/`: `LICENSE`, `MANIFEST.sha256`, `METRICS.json`, `NOTICE.md`, `PDF_QA.json`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `constant_recipe.tex`, `direct_section.tex`, `report.pdf`, `report.tex`, `verify.py`
- `117-quadratic-frames/direct/`: `INDEPENDENT_REVIEW.md`, `INDEPENDENT_SOURCE.json`, `INDEPENDENT_SOURCE_OPTIMIZED.json`, `MANIFEST.sha256`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `direct_section.tex`, `independent_source_check.py`
- `117-quadratic-frames/direct/source/`: `LICENSE.ProveIt`, `LICENSE.Source407`, `LICENSE.Source888`, `NOTICE.Source407.md`, `NOTICE.Source888.md`, `domain75.json`, `factorial_guard76_proof.md`, `first_output_sign_certificate.json`, `local_factorial_certificate.json`, `local_factorial_proof.md`, `original_source_certificate.json`, `output_guard75_proof.md`, `paired_guard77_proof.md`, `parent75.json`, `raw104_guard_certificate.json`, `raw_builder.json`, `signed_comparison_base_proof.md`
- `117-quadratic-frames/direct/variants/63/`: `CENSUS.json`, `CHECKS.json`, `CHECKS_OPTIMIZED.json`, `domain.json`, `parent.json`
- `117-quadratic-frames/direct/variants/63/support16_affine2/`: `equation.json`, `polynomial.json`, `projection.json`
- `117-quadratic-frames/direct/variants/63/support32/`: `equation.json`, `polynomial.json`, `projection.json`
- `117-quadratic-frames/ten_positive/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `COEFFICIENT_CHECK.json`, `PROOF.md`, `SEED.txt`, `algebra.py`, `build.py`, `build_integer.py`, `check.py`, `equation.json`, `integer30.json`, `rebuild_coefficients.py`
- `117-quadratic-frames/ten_positive/coefficients/`: `BINDING.json`, `K.bin.gz`, `MC.bin.gz`, `MF_source.bin.gz`, `beta.bin.gz`
- `117-quadratic-frames/ten_positive/review/`: `review.md`, `ten_saturation_review.json`, `ten_saturation_review.py`, `ten_saturation_review_optimized.json`
- `117-quadratic-frames/ten_positive/upstream/`: `BFS_PAGE_VERIFY.json`, `BFS_SOURCE_TRANSFER.md`, `BFS_VERIFY.json`, `FREE_J_PROOF.md`, `LICENSE.ProveIt`, `LICENSE_SOURCE61`, `NINE_SATURATION_PRIOR.md`, `PARENT_PROOF.md`, `QUADRATIC_PROOF.md`, `SHORT_PROOF.md`, `SOURCE_PINS.json`, `WEIGHTED_PROOF.md`, `coefficient_constructor.py`, `parent_equation.json`, `printed_parent.tex`
- `118-structural-compression/`: `LICENSE.UPSTREAM`, `PDF_QA.json`, `POSITIVE_PROOF_PINS.json`, `PROVENANCE.json`, `README.md`, `VERIFICATION_SUMMARY.json`, `constants.tex`, `export_quartic_text.py`, `positive_proofs.tex`, `quartic_and_appendices.tex`, `reconstruct_constants.py`, `report.pdf`, `report.tex`, `verify_all.py`
- `118-structural-compression/integer/`: `AUXILIARY_GROWTH_CARRIER_PEER_REVIEW.md`, `COMPACT_NORM_ADDENDUM.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `UNWEIGHTED_PEER_REVIEW.md`, `VERIFICATION.json`, `build_compact_norms.py`, `build_symmetric_scalar12.py`, `build_symmetric_trace13.py`, `compact_scalar12_integral.json`, `compact_scalar12_rational.json`, `compact_trace13.json`, `norm_identity.py`, `scalar12_integral_parent.json`, `scalar12_rational_parent.json`, `symmetric_scalar12_integral.json`, `symmetric_scalar12_rational.json`, `symmetric_trace13.json`, `trace13_parent.json`, `verify_symmetric_norms.py`
- `118-structural-compression/integer/source/candidates/integer13-quadratic-trace/`: `PROOF.md`, `README.md`
- `118-structural-compression/integer/source/candidates/integer13-quadratic-trace/source/`: `LICENSE`, `SIGNED_QUADRATIC_PROOF.md`, `TRACE_SOURCE_PINS.json`
- `118-structural-compression/integer/source/candidates/scalar-carrier12/`: `PROOF.md`
- `118-structural-compression/integer/source/candidates/scalar-carrier12/source/`: `LICENSE.UPSTREAM`
- `118-structural-compression/positive/`: `CHECKS.json`, `CHECK_OUTPUT.txt`, `CHECK_OUTPUT_OPTIMIZED.txt`, `PROOF.md`, `build.py`, `equation102.json`, `equation104.json`, `equation96.json`, `equation98.json`, `verify.py`
- `118-structural-compression/positive/bfs/`: `equation102.json`, `equation104.json`, `equation96.json`, `equation98.json`
- `118-structural-compression/positive/bfs/source/`: `README_SCALED10.md`, `README_SHORT10.md`, `SEED.txt`, `SOURCE_PINS.json`, `equation.tex`, `polynomial.json`
- `118-structural-compression/positive/coefficients_bfs/`: `K.bin.gz`, `RECONSTRUCTION.json`
- `118-structural-compression/positive/source/`: `DIRECT_ZERO_OFFSET_PROOF.md`, `FREE_J_PROOF.md`, `QUADRATIC_PROJECTION_PROOF.md`, `SHIFTED_PROOF.md`, `SHORT_PROJECTION_PROOF.md`, `WEIGHTED_ROOTS_PROOF.md`, `ZERO_OFFSET_PROOF.md`, `direct105.json`, `zero99.json`
- `118-structural-compression/quartic/`: `CALIBRATION_DEPENDENCIES.md`, `CENSUS.json`, `CHECK_FUSED68.json`, `CHECK_PAIR_GUARDS.json`, `EXTRA_CENSUS.json`, `FUSED_CENSUS.json`, `PAIR_GUARD_CERTIFICATE.json`, `PROOF_FUSED68.md`, `PROOF_PAIR_GUARDS.md`, `README.md`, `SOURCE_PROVENANCE.json`, `build_fused68.py`, `build_pair_guards.py`, `check_fused68.py`, `check_pair_guards.py`, `extra_profiles.py`, `factorial-radius-output-sign-profile_compact_domain.json`, `factorial-radius-output-sign-profile_compact_parent.json`, `factorial-radius-output-sign-profile_raw_domain.json`, `factorial-radius-output-sign-profile_raw_parent.json`, `research_factorial-radius-guard_PROOF.md`, `research_factorial-radius-output-sign-profile_check.py`, `research_factorial-radius-output-sign_PROOF.md`
- `118-structural-compression/quartic/fused68/`: `domain.json`, `parent.json`
- `118-structural-compression/quartic/fused68/support16_affine2/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/fused68/support32_quadratic_first/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/fused68/support8/`: `equation.json`, `polynomial.json`, `polynomial.txt`, `projection.json`, `residuals.txt`
- `118-structural-compression/quartic/old75/support16/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/old75/support32/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/old75/support8/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/old75_compact/support32/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/pair69/`: `domain.json`, `parent.json`
- `118-structural-compression/quartic/pair69/support16/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/pair69/support16_affine2/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/pair69/support32/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/pair69/support32_quadratic_first/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/pair69/support8/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/pair69_compact/`: `domain.json`, `parent.json`
- `118-structural-compression/quartic/pair69_compact/support32/`: `equation.json`, `polynomial.json`, `projection.json`
- `118-structural-compression/quartic/upstream/`: `LICENSE`, `PROPOSAL_REVIEW_QUARTICS407888.md`, `SOURCE_PINS75.json`, `profile_build.py`
- `118-structural-compression/verification/`: `bfs_constants.txt`, `integer_norms.txt`, `positive_algebra.txt`, `positive_build.txt`, `quartic_final.txt`, `quartic_pairs.txt`, `quartic_plaintext.txt`
- `119-cofinal-witnesses/`: `LICENSE.UPSTREAM`, `MANIFEST.sha256`, `NOTICE.md`, `README.md`, `RELEASE.json`, `SOURCE_LEDGER.json`, `verify_all.py`
- `119-cofinal-witnesses/checks/`: `check_cofinal_semantics.py`
- `119-cofinal-witnesses/direct/`: `MANIFEST.json`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build.py`, `equation512.json`, `metrics512.json`, `polynomial512.json`, `specialization_certificate.json`, `verify.py`
- `119-cofinal-witnesses/direct/principal/`: `COFINAL_PROOF.md`, `COMPARISON.json`, `MANIFEST.json`, `METRICS.json`, `PROOF.md`, `PROVENANCE.json`, `README.md`, `REPRODUCTION.json`, `SEED_AND_BOOTSTRAP_CERTIFICATE.json`, `VARIANT_COMPARISON.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build.py`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization.json`, `print_residuals.py`, `projection2.json`, `raw_audit_input.json`, `residuals508.tex`, `signed_source.json`, `source_transformation.json`, `translation.json`, `untranslated_equation.json`, `verify.py`
- `119-cofinal-witnesses/inherited/direct/`: `NOTICE.md`
- `119-cofinal-witnesses/inherited/direct/upstream/ConZFC_407_888_Quartics/`: `NOTICE.md`
- `119-cofinal-witnesses/inherited/direct/upstream/ConZFC_407_888_Quartics/upstream/`: `NOTICE.md`
- `119-cofinal-witnesses/inherited/direct/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `NOTICE.md`
- `119-cofinal-witnesses/positive/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `verify.py`
- `119-cofinal-witnesses/positive/equations/`: `direct_sharp.json`, `direct_uncentered.json`, `direct_upper.json`, `sharp.json`, `uncentered.json`, `upper.json`
- `119-cofinal-witnesses/positive/provenance/saturation_source/`: `LICENSE.UPSTREAM`
- `119-cofinal-witnesses/proofs/`: `COFINAL_PROOF.md`, `CONSECUTIVE_MODULUS_PROOF.md`
- `119-cofinal-witnesses/report/`: `coupled_factorial.tex`, `generate_residuals.py`, `main.pdf`, `main.tex`, `positive_companions.tex`, `residuals.tex`, `results_table.tex`, `verification.tex`
- `119-cofinal-witnesses/review/`: `ASSEMBLED_MATH_REVIEW.md`, `ConsecutiveModulusREVIEW.md`, `PDF_AND_RELEASE_QA.json`, `RELEASE_VERIFICATION.json`, `RELEASE_VERIFICATION_OPTIMIZED.json`
- `120-height-one-degree464/`: `ConZFC_Height_One_and_Degree_464.pdf`, `LICENSE`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `RELEASE_MANIFEST.json`, `verify_all.py`
- `120-height-one-degree464/eleven/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `powered_coprime11_aux.json`, `powered_coprime11_direct.json`
- `120-height-one-degree464/eleven/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `120-height-one-degree464/eleven/source/`: `LICENSE.UPSTREAM`
- `120-height-one-degree464/eleven/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `120-height-one-degree464/eleven/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `120-height-one-degree464/height_one/`: `MANIFEST.json`, `PROOF.md`, `README.md`, `build.py`, `verify.py`
- `120-height-one-degree464/height_one/output/`: `METRICS.json`, `VERIFY.json`, `VERIFY_OPTIMIZED.json`, `certificate.json`, `polynomial.json`, `polynomial.txt`
- `120-height-one-degree464/height_one/source/`: `LICENSE.UPSTREAM`, `NOTICE.UPSTREAM.md`, `PROVENANCE.json`
- `120-height-one-degree464/height_one/source/reading/`: `AUDIT_AND_READING_ORDER.md`, `SOURCE_INDEX.json`
- `120-height-one-degree464/height_one/source/reading/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.Round14`, `LICENSE.incoming_signed`, `NOTICE.407_888.md`, `NOTICE.Direct519.md`, `NOTICE.DirectOriginal.md`, `NOTICE.PrimePower.md`, `NOTICE.Round14.md`, `NOTICE.Shell.md`, `NOTICE.Synchronized.md`
- `120-height-one-degree464/report/`: `artifacts.tex`, `calibration.tex`, `eleven.tex`, `height_one.tex`, `report.tex`
- `120-height-one-degree464/review/`: `HEIGHT_ONE_REVIEW.md`, `INDEPENDENT_PROOF_AUDIT.md`, `REVIEW_RESOLUTIONS.md`, `height_one_read_audit.json`, `source_pins.json`
- `120-height-one-degree464/verification/`: `PDF_REVIEW.json`, `RELEASE_CHECK.json`
- `121-paired-guards-centered/`: `CODE_REVIEW.json`, `CODE_REVIEW.md`, `COEFFICIENT_CHECK.json`, `DEPENDENCIES.md`, `LICENSES.md`, `MANIFEST.json`, `README.md`, `REPLAY_SUMMARY.json`, `RESULTS.json`, `make_release_zip.py`, `rebuild_coefficients.py`, `reproduce.py`, `requirements.txt`, `seal_release.py`
- `121-paired-guards-centered/alternative/`: `CALIBRATION.md`, `COMPONENT_CHECK.json`, `COMPONENT_CHECK_OPTIMIZED.json`, `FINAL_SEAL.json`, `MANIFEST.sha256.json`, `PAIRED_BUILD.json`, `PROOF.md`, `README.md`, `REPRODUCE_PLAN.json`, `SQUARED_BUILD.json`, `VISUAL_QA.json`, `build_pairguards.py`, `check_components.py`, `section.tex`, `standalone.pdf`, `standalone.tex`
- `121-paired-guards-centered/alternative/inherited_proofs/`: `NOTICE.md`
- `121-paired-guards-centered/alternative/inherited_proofs/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/alternative/inherited_proofs/late/`: `SOURCE.json`, `shared-remainder-product-guards-root-peer.md`
- `121-paired-guards-centered/alternative/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `121-paired-guards-centered/alternative/paired/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `pair_certificate.json`, `paired_source.json`, `presemantic_certificate.json`, `projection_certificate.json`, `terminal_elimination_certificate.json`
- `121-paired-guards-centered/alternative/squared_paired/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `pair_certificate.json`, `paired_source.json`, `presemantic_certificate.json`, `projection_certificate.json`, `terminal_elimination_certificate.json`
- `121-paired-guards-centered/baseline/`: `BASELINE_CHECKS.json`, `BASELINE_REVIEW.md`, `SELECTED_EVIDENCE.json`, `arrival_git_blobs.json`, `arrivals_paths.json`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/`: `CURRENT_EQUATION.json`, `RECENT_INTAKE_2026_10_24.md`, `SHORT_FRONTIER.md`, `SIZE_REDUCTION.md`, `STATUS.md`, `equation.tex`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/indexed-tile-enumeration/`: `PEER_REVIEW.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `equation.tex`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/power0-output-square-frame/`: `FULL_SOURCE.md`, `PEER_REVIEW.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/power0-output-square-frame/source/`: `LICENSE.bootstrap`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/power3-output-square-frame/`: `FULL_SOURCE.md`, `PEER_REVIEW.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/power3-square-frame-source-prototype/`: `PEER_REVIEW.md`, `README.md`, `SOURCE_PINS.json`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/ten-positive-index-weight/`: `PEER_REVIEW.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/`: `PEER_REVIEW.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/research/ten-positive-square-weight-tradeoff/parents/`: `PROOF.md`
- `121-paired-guards-centered/baseline/Computability/DiophantineConsistency/reviews/`: `power0-square-frame-root-peer.md`, `power3-square-frame-root-peer.md`, `ten-index-weight-root-peer.md`, `ten-square-weight-root-peer.md`
- `121-paired-guards-centered/baseline/arrivals/ConZFC_Carriers_and_Even_Indices_2026-10-24/ConZFC_Carriers_and_Even_Indices_2026-10-24/`: `LICENSE.UPSTREAM`
- `121-paired-guards-centered/baseline/arrivals/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/baseline/arrivals/ConZFC_Signed_Powers_Height_Two_2026-10-24/ConZFC_Signed_Powers_Height_Two_2026-10-24/`: `LICENSE.UPSTREAM`
- `121-paired-guards-centered/baseline/arrivals/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/`: `LICENSE`
- `121-paired-guards-centered/baseline/arrivals/con-zfc-quadratic-frames-2026-10-24/con-zfc-quadratic-frames/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/baseline/arrivals/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/`: `LICENSE.UPSTREAM`
- `121-paired-guards-centered/baseline/late/`: `LATE_COMPARISON.md`, `LATE_REVIEW_SOURCES.json`, `ONE_WORD_WINDOW.md`, `SOURCE.json`, `TRIAGE.md`, `latest_commits.json`, `shared-remainder-product-guards-root-peer.md`
- `121-paired-guards-centered/integer/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `METRICS.json`, `METRICS_OPTIMIZED.json`, `PROOF.md`, `README.md`, `REPLAY_OPT_STDOUT.json`, `REPLAY_STDOUT.json`, `RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `build_prior_optimized.py`, `check.py`, `optimized_fused11_integral.json`, `optimized_fused11_rational.json`, `optimized_guard_fused11_aux.json`, `optimized_guard_fused11_direct.json`, `pair_fused11_integral.json`, `pair_fused11_rational.json`, `pair_fused11_rational_sharp.json`, `pair_fused11_rational_strong.json`, `section.tex`
- `121-paired-guards-centered/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `121-paired-guards-centered/integer/source/`: `LICENSE.UPSTREAM`
- `121-paired-guards-centered/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/lowdegree/`: `DEPENDENCIES.md`, `FINAL_REBRACKETING_CERTIFICATE.json`, `MANIFEST.json`, `METRICS.json`, `PROOF.md`, `README.md`, `REPRODUCE_PLAN.json`, `SOURCE_PINS.json`, `build.py`, `equation.json`, `section.tex`, `section12.tex`, `specification.json`, `standalone.pdf`, `standalone.tex`
- `121-paired-guards-centered/lowdegree/review/`: `CHECK.json`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`
- `121-paired-guards-centered/lowdegree/twelve/`: `PROOF.md`, `SOURCE_PINS.json`, `build.py`, `equation.json`, `specification.json`
- `121-paired-guards-centered/lowdegree/twelve/review/`: `CHECK.json`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `audit.py`
- `121-paired-guards-centered/lowdegree/twelve/source/`: `LICENSE.UPSTREAM`
- `121-paired-guards-centered/positive/`: `BUILD_CHECK.txt`, `BUILD_CHECK_OPTIMIZED.txt`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `CHECK_ORDINARY.json`, `CHECK_ORDINARY_OPTIMIZED.json`, `MANIFEST.json`, `PDF_QA.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `check_ordinary.py`, `ordinary_sharp.json`, `ordinary_uncentered.json`, `ordinary_upper.json`, `render.sh`, `section.tex`, `sharp.json`, `standalone.pdf`, `standalone.tex`, `uncentered.json`, `upper.json`
- `121-paired-guards-centered/positive/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/alternative/prior/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/integer/`: `NOTICE.md`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/integer/source/`: `LICENSE.UPSTREAM`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/lowdegree/`: `LICENSE.ProveIt`
- `121-paired-guards-centered/prior/ZFC_Diophantine_Coprime_Projection/positive/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `121-paired-guards-centered/report/`: `QA_RECEIPT.json`, `QA_RECEIPT.md`, `build_report.sh`, `references.tex`, `report.pdf`, `report.tex`, `scope.tex`, `section_copy_provenance.json`, `summary.tex`, `validation.tex`
- `121-paired-guards-centered/report/qa/`: `check_editorial_math.py`, `editorial_math_check.json`, `editorial_math_check_optimized.json`
- `121-paired-guards-centered/report/sections/`: `centered_fifteen.tex`, `compact_twelve.tex`, `direct_quartics.tex`, `integer_family.tex`, `positive_family.tex`
- `121-paired-guards-centered/review/alternative/`: `PAIRED_OPTIMIZED_RUN.txt`, `README.txt`, `REVIEW.md`, `audit_paired_independent.py`, `check_negative_controls.py`
- `121-paired-guards-centered/review/alternative/attribution/`: `SOURCE.json`, `upstream_six_pair_review.md`
- `121-paired-guards-centered/review/alternative/paired/`: `GUARD_LEDGER.json`, `INDEPENDENT_REPLAY.json`, `NEGATIVE_CONTROLS.json`, `NEGATIVE_RUN.txt`, `PRESEMANTIC_BOUNDS.json`, `REPLAY.txt`
- `121-paired-guards-centered/review/alternative/paired_optimized/`: `INDEPENDENT_REPLAY.json`, `PRESEMANTIC_BOUNDS.json`
- `121-paired-guards-centered/review/alternative/squared_paired/`: `GUARD_LEDGER.json`, `INDEPENDENT_REPLAY.json`, `NEGATIVE_CONTROLS.json`, `NEGATIVE_RUN.txt`, `PRESEMANTIC_BOUNDS.json`, `REPLAY.txt`
- `121-paired-guards-centered/review/alternative/squared_paired_optimized/`: `INDEPENDENT_REPLAY.json`, `PRESEMANTIC_BOUNDS.json`, `REPLAY.txt`
- `121-paired-guards-centered/review/integer/`: `INDEPENDENT_CHECK.json`, `INDEPENDENT_CHECK_OPTIMIZED.json`, `REVIEW.md`, `check_independent.py`
- `121-paired-guards-centered/review/lowdegree/`: `INDEPENDENT_CHECK.json`, `INDEPENDENT_REVIEW.md`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `independent_audit.py`
- `121-paired-guards-centered/review/positive/`: `INDEPENDENT_CHECK.json`, `INDEPENDENT_CHECK_OPTIMIZED.json`, `INDEPENDENT_REVIEW.md`, `independent_audit.py`
- `122-residue-compiler/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `SOURCE_LEDGER.json`, `equation-332.pdf`, `equation-332.tex`, `equation-333.pdf`, `equation-333.tex`, `equation-typesetting-check.json`, `report.pdf`, `report.tex`, `residuals-332.tsv`, `residuals-333.tsv`, `variables-332.tsv`, `variables-333.tsv`, `verify_all.py`
- `122-residue-compiler/code/`: `audit_parity_interface.py`, `check_independent.py`, `check_parity_structure.py`, `check_transform.py`, `even_architecture.py`, `generate_equation_tex.py`, `modular_factorial.py`, `release_332.py`
- `122-residue-compiler/equations/natural332/`: `DEPENDENCIES.json`, `SUMMARY.json`, `TRANSFORM.json`
- `122-residue-compiler/equations/natural332/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `122-residue-compiler/equations/natural332/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `122-residue-compiler/equations/natural333/`: `INDEPENDENT_CHECK.json`, `INDEPENDENT_CHECK_OPTIMIZED.json`, `PARITY_CHECK.json`, `PARITY_CHECK_OPTIMIZED.json`, `SUMMARY.json`
- `122-residue-compiler/equations/natural333/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `122-residue-compiler/equations/natural333/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `parity_interface.json`, `raw_audit_input.json`
- `122-residue-compiler/proofs/`: `MATHEMATICAL_REVIEW.md`, `MODULAR_NUMERATORS_PROOF.md`, `PARITY_PROOF.md`
- `122-residue-compiler/vendor/round14/`: `LICENSE`
- `122-residue-compiler/vendor/round14/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `122-residue-compiler/vendor/round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `122-residue-compiler/vendor/round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `122-residue-compiler/vendor/round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `122-residue-compiler/vendor/round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `122-residue-compiler/verification/`: `CALIBRATION_PINS_CHECK.json`, `FINAL_CHECKS.json`, `INDEPENDENT_CHECK_332_H12.json`, `OPTIMIZED_CHECKS.json`, `PARITY_INTERFACE_INITIAL.json`, `PDF_QA.json`, `TRANSFORM_CHECK_332_H12.json`
- `123-shared-binomial/`: `MANIFEST_SHA256.json`, `NOTICE.md`, `PDF_REVIEW.json`, `PROVENANCE.json`, `README.md`, `VERIFICATION.json`, `report.pdf`, `verify_all.py`
- `123-shared-binomial/direct/`: `COMPARISON.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `REPRODUCTION.json`, `REPRODUCTION_OPTIMIZED.json`, `SEMANTIC_CHECKS.json`, `SEMANTIC_CHECKS_OPTIMIZED.json`, `SOURCE_LEDGER.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build_modular_factorial.py`, `check_semantics.py`, `report_section.tex`, `reproduce.py`, `verify.py`
- `123-shared-binomial/direct/equation319/`: `SUMMARY.json`
- `123-shared-binomial/direct/equation319/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `polynomial.txt`, `residuals.txt`
- `123-shared-binomial/direct/equation319/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `123-shared-binomial/direct/equation320/`: `SUMMARY.json`
- `123-shared-binomial/direct/equation320/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `polynomial.txt`, `residuals.txt`
- `123-shared-binomial/direct/equation320/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `local_majorant.json`, `raw_audit_input.json`
- `123-shared-binomial/direct/frozen_round14/`: `LICENSE`, `NOTICE.md`
- `123-shared-binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `123-shared-binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `123-shared-binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `123-shared-binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `123-shared-binomial/direct/provenance/`: `LICENSE.108`, `NOTICE.108.txt`
- `123-shared-binomial/lowops/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `METRICS.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `exact_poly.py`, `product11_degree882.json`, `product11_degree966.json`, `section.tex`
- `123-shared-binomial/norm/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `METRICS.json`, `PROOF.md`, `README.md`, `build.py`, `check.py`, `scalar11_original_center.json`, `scalar11_original_center_reduced.json`, `scalar11_original_direct.json`, `scalar11_q4_center.json`, `scalar11_q4_center_reduced.json`
- `123-shared-binomial/norm/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `123-shared-binomial/norm/source/`: `LICENSE.UPSTREAM`
- `123-shared-binomial/norm/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `123-shared-binomial/norm/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `123-shared-binomial/report/`: `direct_section.tex`, `lowops_section.tex`, `norm_section.tex`, `report.tex`, `validation_section.tex`
- `123-shared-binomial/reviews/`: `DIRECT319_INDEPENDENT_REVIEW.md`, `LOWOPS11_INDEPENDENT_REVIEW.md`, `SYNTHESIS11_INDEPENDENT_REVIEW.md`
- `124-shared-pell-bound261/`: `LICENSE`, `MANIFEST.json`, `README.md`, `verify_release.py`
- `124-shared-pell-bound261/code/`: `check_affine_export.py`, `check_cap_independent.py`, `check_self_radix.py`, `evaluate_equation.py`, `generate_report_inputs.py`
- `124-shared-pell-bound261/equations/integer/`: `README.md`, `recipe.json`
- `124-shared-pell-bound261/portable/`: `CAP_THEOREM.md`, `LICENSE`, `PORTABLE_REPLAY.json`, `ProveIt_LICENSE`, `README.md`, `SOURCE_MAP.json`, `build.py`, `verify.py`
- `124-shared-pell-bound261/portable/equations/primary/`: `SUMMARY.json`, `equation.txt`
- `124-shared-pell-bound261/portable/equations/primary/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `124-shared-pell-bound261/portable/equations/primary/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `124-shared-pell-bound261/portable/equations/sparse/`: `SUMMARY.json`, `equation.txt`
- `124-shared-pell-bound261/portable/equations/sparse/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `124-shared-pell-bound261/portable/equations/sparse/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `124-shared-pell-bound261/portable/source/custom/`: `build_radix_R.py`, `build_self_radix.py`, `capped_pell.py`, `frame_environment.py`
- `124-shared-pell-bound261/proofs/`: `CAP_AUDIT.md`, `SELF_RADIX_PROOF.md`
- `124-shared-pell-bound261/provenance/`: `SNAPSHOT.json`
- `124-shared-pell-bound261/provenance/arithmetic_interfaces/`: `PROVENANCE.json`
- `124-shared-pell-bound261/provenance/logical_interfaces/`: `README.md`
- `124-shared-pell-bound261/report/`: `metrics.tex`, `report.pdf`, `report.tex`, `residuals.tex`
- `124-shared-pell-bound261/verification/`: `REPORT_QA.json`, `affine_export_certificate.json`, `independent_affine_export.json`, `independent_affine_export_optimized.json`, `independent_cap.json`, `independent_cap_optimized.json`, `independent_radix.json`, `independent_radix_optimized.json`, `release_normal.json`, `release_optimized.json`
- `125-unified-binomial-round15/`: `ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.pdf`, `ENDPOINTS.json`, `LICENSE`, `MANIFEST_SHA256.json`, `NOTICE.md`, `README.md`, `REPLAY_RECEIPT.json`, `SOURCE_INVENTORY.json`, `VALIDATION.json`, `build_report.sh`, `verify.py`
- `125-unified-binomial-round15/architecture/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `README.md`, `REPRODUCTION.json`, `REPRODUCTION_OPTIMIZED.json`, `SOURCE_BINDING.json`, `UNIFIED_PRODUCT_PROOF.md`, `build_unified_product.py`, `check_unified_product.py`, `reproduce_unified_product.py`
- `125-unified-binomial-round15/architecture/unified_derived_cantor/`: `SUMMARY.json`
- `125-unified-binomial-round15/architecture/unified_derived_cantor/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `125-unified-binomial-round15/architecture/unified_derived_cantor/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `125-unified-binomial-round15/architecture/unified_derived_shell/`: `SUMMARY.json`
- `125-unified-binomial-round15/architecture/unified_derived_shell/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `125-unified-binomial-round15/architecture/unified_derived_shell/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `local_majorant.json`, `macro_inventory.json`, `raw_audit_input.json`
- `125-unified-binomial-round15/architecture/unified_slack_cantor/`: `SUMMARY.json`
- `125-unified-binomial-round15/architecture/unified_slack_cantor/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `125-unified-binomial-round15/architecture/unified_slack_cantor/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `125-unified-binomial-round15/architecture/unified_slack_shell/`: `SUMMARY.json`
- `125-unified-binomial-round15/architecture/unified_slack_shell/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `125-unified-binomial-round15/architecture/unified_slack_shell/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `local_majorant.json`, `macro_inventory.json`, `raw_audit_input.json`
- `125-unified-binomial-round15/architecture/unified_square_derived_cantor/`: `SUMMARY.json`
- `125-unified-binomial-round15/architecture/unified_square_derived_cantor/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `125-unified-binomial-round15/architecture/unified_square_derived_cantor/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `125-unified-binomial-round15/architecture/unified_square_slack_shell/`: `SUMMARY.json`
- `125-unified-binomial-round15/architecture/unified_square_slack_shell/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `125-unified-binomial-round15/architecture/unified_square_slack_shell/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `local_majorant.json`, `macro_inventory.json`, `raw_audit_input.json`
- `125-unified-binomial-round15/direct/`: `DELIVERY_WHITELIST.json`, `NOTICE.md`, `PROOF.md`, `ROUND14_NOTICE.md`, `SOURCE_AND_ARTIFACT_PINS.json`, `build_residue.py`, `center_integer.py`
- `125-unified-binomial-round15/direct/integer442/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `125-unified-binomial-round15/direct/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `125-unified-binomial-round15/direct/unified_reparam_derived_shell/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `positive_seed_certificate.json`, `projected.json`, `projection_certificate.json`, `pruned_source.json`, `pruning_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `125-unified-binomial-round15/direct_audit/`: `CHECK_ALL.json`, `CHECK_ALL_OPT.json`, `MATH_AUDIT.md`, `check_direct.py`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/direct/`: `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/provenance/direct_licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/provenance/norm_legacy/`: `LICENSE`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/provenance/norm_legacy/inherited/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/provenance/norm_legacy/inherited/signed_guards/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/provenance/norm_legacy/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `125-unified-binomial-round15/intake/ConZFC_Signed_Powers_Height_Two_2026-10-24/ConZFC_Signed_Powers_Height_Two_2026-10-24/`: `LICENSE.UPSTREAM`
- `125-unified-binomial-round15/intake/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/`: `LICENSE`
- `125-unified-binomial-round15/intake/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/supplement/coefficients/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE_K215.md`
- `125-unified-binomial-round15/intake/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/supplement/coefficients/recipe/`: `NOTICE-upstream.md`
- `125-unified-binomial-round15/intake/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/upstream/engine/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/upstream/engine/upstream/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/upstream/engine/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/alternative/prior/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/integer/`: `NOTICE.md`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/integer/source/`: `LICENSE.UPSTREAM`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/lowdegree/`: `LICENSE.ProveIt`
- `125-unified-binomial-round15/intake/ZFC_Diophantine_Coprime_Projection_2026-10-24/ZFC_Diophantine_Coprime_Projection/positive/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `125-unified-binomial-round15/intake/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/`: `LICENSE.UPSTREAM`
- `125-unified-binomial-round15/intake/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/integer/source/candidates/integer13-quadratic-trace/source/`: `LICENSE`
- `125-unified-binomial-round15/intake/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/integer/source/candidates/scalar-carrier12/source/`: `LICENSE.UPSTREAM`
- `125-unified-binomial-round15/intake/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/quartic/upstream/`: `LICENSE`
- `125-unified-binomial-round15/norm/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `DEGREE_PROOF.md`, `ISOLATED_REPLAY.json`, `README.md`, `RELEASE.json`, `build_norm.py`, `check_norm.py`, `integral_centered.json`, `integral_centered_expandedcut.json`, `integral_centered_paired.json`, `integral_direct.json`, `integral_direct_paired.json`
- `125-unified-binomial-round15/norm_weak/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `DEGREE_PROOF.md`, `ISOLATED_REPLAY.json`, `README.md`, `RELEASE.json`, `build_norm.py`, `check_norm.py`, `weak_integral_centered_paired.json`, `weak_integral_direct_paired.json`
- `125-unified-binomial-round15/report/`: `architecture_full.tex`, `comparison.tex`, `crt_full.tex`, `direct_full.tex`, `equations.tex`, `main.tex`, `norm_full.tex`, `overview.tex`, `questions.tex`, `reproducibility.tex`, `scalar_full.tex`, `weak_degree_full.tex`
- `125-unified-binomial-round15/report_audit/`: `COEFFICIENTS.json`, `METRICS.json`, `PDF_AUDIT.json`, `PROOF_COVERAGE.json`, `REPORT_REVIEW.md`, `check_proof_coverage.py`, `check_report_metrics.py`
- `125-unified-binomial-round15/review/`: `ROUND15_REVIEW.md`, `SOURCE_PINS.json`, `check_new_payloads.py`, `independent_payload_metrics.json`, `new_archive_acquisition.json`, `public_main_commit.json`, `recent_commits.json`, `replay_incoming.py`
- `125-unified-binomial-round15/root_qa/`: `ROOT_ISOLATED_REPLAY.json`
- `125-unified-binomial-round15/scalar/`: `CRT_CARRIER_PROOF.md`, `CRT_CHECKS.json`, `CRT_CHECKS_OPTIMIZED.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `RELEASE.json`, `RELEASE_WHITELIST.json`, `SEMANTIC_CHECKS.json`, `SEMANTIC_CHECKS_OPTIMIZED.json`, `SOURCE_PINS.json`, `verify_coefficients.py`, `verify_crt_carrier.py`, `verify_semantics.py`
- `125-unified-binomial-round15/scalar/coefficients/`: `RECIPE_REPLAY.json`
- `125-unified-binomial-round15/scalar/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `125-unified-binomial-round15/scalar/source/`: `LICENSE.UPSTREAM`
- `125-unified-binomial-round15/scalar/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/scalar/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `125-unified-binomial-round15/scalar_audit/`: `AUDIT_RESULTS.json`, `AUDIT_RESULTS_OPTIMIZED.json`, `CRT_AUDIT_RESULTS.json`, `CRT_AUDIT_RESULTS_OPTIMIZED.json`, `CRT_CARRIER_AUDIT.md`, `INTERPOLATION_CONTROLS.json`, `MANIFEST_SHA256.json`, `README.md`, `REVIEW_BINDINGS.json`, `SEMANTIC_AUDIT.md`, `audit_crt_graphs.py`, `check_interpolation.py`, `independent_audit.py`
- `126-weak-carriers-shared-signs/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `SOURCE_SNAPSHOT.json`, `report.pdf`, `report.tex`, `verify_all.py`
- `126-weak-carriers-shared-signs/direct/`: `INDEPENDENT_CHECK.json`, `INDEPENDENT_CHECK_OPTIMIZED.json`, `INDEPENDENT_GUARD_AUDIT.json`, `INDEPENDENT_GUARD_AUDIT_OPTIMIZED.json`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `METRICS.json`, `PROOF.md`, `README.md`, `REPLAY.json`, `SOURCE_LEDGER.json`, `budget_certificate.json`, `build.py`, `equation.json`, `evaluate.py`, `expanded_polynomial.json`, `fused_source.json`, `fusion_certificate.json`, `independent_guard_audit.py`, `projection_certificate.json`, `residuals.txt`, `section.tex`, `transform.py`, `translation_certificate.json`, `uncentered_equation.json`, `verify.py`
- `126-weak-carriers-shared-signs/direct/source/`: `LICENSE`, `NOTICE.md`, `PROVENANCE_README.md`
- `126-weak-carriers-shared-signs/inherited/norm/source/`: `LICENSE.UPSTREAM`
- `126-weak-carriers-shared-signs/inherited/norm/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `126-weak-carriers-shared-signs/inherited/norm/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `126-weak-carriers-shared-signs/norm/`: `AUDIT_INDEPENDENT.json`, `AUDIT_INDEPENDENT_OPTIMIZED.json`, `COEFFICIENT_REPLAY.json`, `COEFFICIENT_REPLAY_OPTIMIZED.json`, `METRICS.json`, `MIXED_PROOF.md`, `PROOF.md`, `audit_independent.py`, `build.py`, `dag.py`, `integer11_cubic_centered.json`, `integer11_cubic_direct.json`, `integer11_mixed_centered.json`, `integer11_mixed_direct.json`, `verify_coefficients.py`
- `126-weak-carriers-shared-signs/verification/`: `CALIBRATION_SCOPE_REVIEW.md`, `INHERITED_FILES.json`, `MAIN_PAPER_REVIEW.md`, `PDF_QA.json`, `RELEASE_REPLAY.json`, `UPSTREAM_FILE_ORIGINS.json`
- `127-graph-certificates/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `README.md`, `RELEASE.json`, `verify.py`
- `127-graph-certificates/direct/`: `LICENSE`, `PROOF.md`, `README.md`, `REBUILD.json`, `SIGNED_CAP_PROOF.md`, `SOURCE_FILES.json`, `VERIFICATION.json`, `build.py`, `build_signed_cap.py`, `check_capped_modular.py`, `check_signed_cap.py`, `reproduce.py`, `verify.py`
- `127-graph-certificates/direct/equation239/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `127-graph-certificates/direct/equation240/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `127-graph-certificates/direct/equation240/raw/`: `cap_certificate.json`, `equation.json`, `raw_audit_input.json`
- `127-graph-certificates/direct/inherited/`: `LICENSE`, `MODULAR_NOTICE.md`
- `127-graph-certificates/direct/integer381/`: `INDEPENDENT_CHECK.json`, `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `mixed_source.json`, `projection_certificate.json`, `sign_certificate.json`, `source_certificate.json`
- `127-graph-certificates/direct/integer391/`: `INDEPENDENT_CHECK.json`, `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `mixed_source.json`, `projection_certificate.json`, `sign_certificate.json`, `source_certificate.json`
- `127-graph-certificates/direct/vendor/modular/frozen_round14/`: `LICENSE`, `NOTICE.md`
- `127-graph-certificates/direct/vendor/modular/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `127-graph-certificates/direct/vendor/modular/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `127-graph-certificates/direct/vendor/modular/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `127-graph-certificates/direct/vendor/modular/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `127-graph-certificates/direct/vendor/signed/`: `NOTICE.md`, `ROUND14_NOTICE.md`
- `127-graph-certificates/direct/vendor/signed/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `127-graph-certificates/direct/verification/`: `ALL_REPLAYS.json`, `integer381_normal.json`, `integer381_normal.stdout.txt`, `integer381_optimized.json`, `integer381_optimized.stdout.txt`, `integer391_normal.json`, `integer391_normal.stdout.txt`, `integer391_optimized.json`, `integer391_optimized.stdout.txt`, `natural_normal.json`, `natural_optimized.json`, `natural_optimized.stdout.txt`, `rebuild_normal.json`, `rebuild_normal.stdout.txt`, `rebuild_optimized.json`, `rebuild_optimized.stdout.txt`
- `127-graph-certificates/graph/`: `PROFILES.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `compress_aliases.py`, `rebuild.py`, `verify_graph.py`
- `127-graph-certificates/graph/matched519/`: `COMPRESSION.json`, `certificate.json`, `metrics.json`, `polynomial.json`
- `127-graph-certificates/graph/matched519_no_square/`: `COMPRESSION.json`, `certificate.json`, `metrics.json`, `polynomial.json`
- `127-graph-certificates/graph/principal/`: `COMPRESSION.json`, `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `127-graph-certificates/graph/receipts/`: `CHECK_442_H128_C4.json`, `CHECK_442_H128_C4_OPTIMIZED.json`, `CHECK_519_H256_C4.json`, `CHECK_519_H256_C4_OPTIMIZED.json`, `CHECK_519_H256_QUADRATIC_C4.json`, `CHECK_519_H256_QUADRATIC_C4_OPTIMIZED.json`, `REBUILD.json`
- `127-graph-certificates/inherited/source442/`: `044_NOTICE.md`, `132_NOTICE.md`, `134_NOTICE-K215.md`, `135_NOTICE-source25.md`, `136_NOTICE-source34.md`, `137_NOTICE-source57.md`, `138_NOTICE.source68.md`, `139_NOTICE.source71.md`, `182_NOTICE.md`
- `127-graph-certificates/inherited/source519/`: `025_NOTICE.PrimePower.md`
- `127-graph-certificates/low_variable/`: `LICENSE`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `REPRODUCTION.json`, `SOURCE_LEDGER.json`, `UPSTREAM_NOTICE.md`, `VERIFY.json`, `VERIFY_OPTIMIZED.json`, `build.py`, `linear_multiplier11_centered412.json`, `linear_multiplier11_direct440.json`, `section.tex`, `verify.py`
- `127-graph-certificates/low_variable/source/`: `LICENSE.UPSTREAM`
- `127-graph-certificates/low_variable/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `127-graph-certificates/low_variable/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `127-graph-certificates/provenance/`: `INHERITED_SOURCES.json`, `REPOSITORY_SNAPSHOT.json`
- `127-graph-certificates/report/`: `additional.tex`, `alias_compression.tex`, `artifact_map.tex`, `check_residuals.py`, `direct.tex`, `direct_residuals.tex`, `main.pdf`, `main.tex`, `metrics.tex`, `provenance.tex`, `results_table.tex`, `verification.tex`
- `127-graph-certificates/reviews/`: `DIRECT_SIGNED_CAP_381_NORMAL.json`, `DIRECT_SIGNED_CAP_381_OPTIMIZED.json`, `DIRECT_SIGNED_CAP_391_NORMAL.json`, `DIRECT_SIGNED_CAP_391_OPTIMIZED.json`, `DIRECT_SIGNED_CAP_REVIEW.md`, `DIRECT_SIGNED_CAP_SOURCE_IDENTITIES.json`, `DIRECT_SOURCE_NORMAL.json`, `FINAL_REVIEW.md`, `INHERITED_BUNDLE_CHECK.json`, `LOW_VARIABLE_NORMAL.json`, `LOW_VARIABLE_OPTIMIZED.json`, `LOW_VARIABLE_REVIEW.md`
- `127-graph-certificates/verification/`: `PDF_QA.json`, `RELEASE_CHECK.json`
- `128-one-row-pell/`: `DOCUMENT_CHECK.json`, `DOCUMENT_CHECK_OPTIMIZED.json`, `LICENSE`, `NOTICE.md`, `README.md`, `verify_document.py`
- `128-one-row-pell/baselines/`: `PROVENANCE.json`
- `128-one-row-pell/diagnostics/`: `FINAL_ONE_ROW_CHECK.json`, `FINAL_ONE_ROW_CHECK_OPTIMIZED.json`, `ONE_ROW_FINITE_CHECK.json`, `ONE_ROW_SIGNED_PELL_CAP.md`, `check_one_row_cap.py`
- `128-one-row-pell/portable/`: `CLAIMS.json`, `COMPONENT_README.md`, `FINAL_FINITE_CHECK.json`, `FINAL_FINITE_CHECK_OPTIMIZED.json`, `FINITE_CHECK.json`, `FINITE_CHECK_OPTIMIZED.json`, `GUARD_TABLE.tsv`, `SIGNED_CONSTRUCTION_PROOF.md`, `SOURCE_LEDGER.json`, `build_capped_modular.py`, `build_signed_merged.py`, `verify_release.py`
- `128-one-row-pell/portable/audits/`: `INTERFACE_INTEGER378.json`, `INTERFACE_NATURAL242.json`, `MATH_REVIEW.md`, `SIGNED378_AUDIT.json`, `audit_interfaces.py`, `audit_signed.py`
- `128-one-row-pell/portable/incoming/cap261/portable/`: `LICENSE`, `ProveIt_LICENSE`
- `128-one-row-pell/portable/incoming/shared319/direct/`: `LICENSE`, `NOTICE.md`
- `128-one-row-pell/portable/incoming/shared319/direct/frozen_round14/`: `LICENSE`, `NOTICE.md`
- `128-one-row-pell/portable/incoming/shared319/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `128-one-row-pell/portable/incoming/shared319/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `128-one-row-pell/portable/incoming/shared319/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `128-one-row-pell/portable/incoming/shared319/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `128-one-row-pell/portable/incoming/shared319/direct/provenance/`: `LICENSE.108`, `NOTICE.108.txt`
- `128-one-row-pell/portable/integer378/`: `METRICS.json`, `PROJECTION_METRICS.json`, `equation.json`, `expanded_polynomial.json`, `guarded.json`, `projected.json`, `projection_certificate.json`, `residuals.txt`, `signed_certificate.json`, `source.json`, `translation_certificate.json`, `variables.tsv`
- `128-one-row-pell/portable/integer378/natural_raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `128-one-row-pell/portable/natural242/`: `SUMMARY.json`
- `128-one-row-pell/portable/natural242/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `variables.tsv`
- `128-one-row-pell/portable/natural242/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `128-one-row-pell/report/`: `PDF_QA.json`, `comparison.tex`, `integer_construction.tex`, `integer_residuals.tex`, `metrics.tex`, `one_row_theorem.tex`, `report.pdf`, `report.tex`, `reproduction.tex`, `verification.tex`
- `129-semantic-pell-anchor/`: `LICENSE`, `README.md`, `report.pdf`, `report.tex`, `residuals233.tex`, `residuals234.tex`
- `129-semantic-pell-anchor/code/`: `build_combined.py`, `check_affine_export.py`, `check_consecutive_ordinates.py`, `check_new_arithmetic.py`, `check_semantics.py`, `evaluate.py`, `render_equations.py`, `verify_release.py`
- `129-semantic-pell-anchor/equations/integer/`: `integer699.json`, `integer702.json`
- `129-semantic-pell-anchor/equations/natural233/`: `SUMMARY.json`, `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `equation.txt`, `expanded_polynomial.json`
- `129-semantic-pell-anchor/equations/natural234/`: `SUMMARY.json`, `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `equation.txt`, `expanded_polynomial.json`
- `129-semantic-pell-anchor/equations/source/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `semantic.json`
- `129-semantic-pell-anchor/proofs/`: `ANCHOR_REUSE_PROOF.md`, `COMPOSITION_REVIEW.md`, `CONSECUTIVE_ORDINATES.md`, `INDEPENDENT_REVIEW.md`, `REJECTED_COFINAL_RADIX.md`
- `129-semantic-pell-anchor/provenance/`: `BASELINE_METRICS.json`, `LOGICAL_INTERFACE_IDENTITIES.json`, `SOURCE_PINS.json`
- `129-semantic-pell-anchor/upstream/shared_binomial/direct/`: `LICENSE`, `NOTICE.md`
- `129-semantic-pell-anchor/upstream/shared_binomial/direct/frozen_round14/`: `LICENSE`, `NOTICE.md`
- `129-semantic-pell-anchor/upstream/shared_binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `129-semantic-pell-anchor/upstream/shared_binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `129-semantic-pell-anchor/upstream/shared_binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `129-semantic-pell-anchor/upstream/shared_binomial/direct/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `129-semantic-pell-anchor/upstream/shared_binomial/direct/provenance/`: `LICENSE.108`, `NOTICE.108.txt`
- `129-semantic-pell-anchor/verification/`: `PDF_QA.json`, `README.md`, `final_small_normal_semantic_receipt.json`, `final_small_optimized_semantic_receipt.json`, `final_sparse_normal_semantic_receipt.json`, `final_sparse_optimized_semantic_receipt.json`, `release_normal_with_rebuild.json`, `release_optimized.json`
- `130-shared-index/`: `LICENSE`, `MANIFEST.json`, `README.md`, `REPORT_BINDING.json`, `SOURCE_SNAPSHOT.json`, `build_report_support.py`, `package_release.py`, `verify_all.py`
- `130-shared-index/center246/`: `LICENSE.UPSTREAM`, `MANIFEST.json`, `PROOF.md`, `README.md`, `RESULTS.json`, `build_verify.py`, `center_defect.json`, `equation.json`, `sparse_polynomials.py`
- `130-shared-index/center246/source/`: `parent94.json`, `parent_proof.md`
- `130-shared-index/direct/`: `INDEPENDENT_REVIEW.md`, `LICENSE`, `MANIFEST.json`, `PROOF.md`, `README.md`, `SOURCE_LEDGER.json`, `build.py`, `evaluate.py`, `verify.py`
- `130-shared-index/direct/code/`: `audit_combined.py`
- `130-shared-index/direct/equations/dense239/`: `SUMMARY.json`
- `130-shared-index/direct/equations/dense239/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`
- `130-shared-index/direct/equations/dense239/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `130-shared-index/direct/equations/principal241/`: `SUMMARY.json`
- `130-shared-index/direct/equations/principal241/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`
- `130-shared-index/direct/equations/principal241/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `130-shared-index/direct/source/shared_binomial/frozen_round14/`: `LICENSE`, `NOTICE.md`
- `130-shared-index/direct/source/shared_binomial/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `130-shared-index/direct/source/shared_binomial/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `130-shared-index/direct/source/shared_binomial/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `130-shared-index/direct/source/shared_binomial/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `130-shared-index/direct/verification/`: `affine_certificate32.json`, `affine_verify32.json`, `release_normal.json`, `release_optimized.json`, `semantic_audit.json`
- `130-shared-index/integer964/`: `README.md`, `equation.json`, `expanded_polynomial.json`
- `130-shared-index/licenses/native_sources/`: `FETCH_MANIFEST.json`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.package44`, `LICENSE.root`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-package44.md`, `NOTICE-upstream-native44.md`, `NOTICE_K215.md`, `README.md`, `SOURCE_PINS-native44.json`
- `130-shared-index/positive/`: `PROOF.md`, `README.md`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build.py`, `quotient.json`, `quotient_absorbed.json`, `quotient_absorbed_sharp.json`, `quotient_sharp.json`, `verify.py`
- `130-shared-index/positive/inherited/gap_fusion/`: `CHECKS.json`, `INDEPENDENT_REVIEW.md`, `PROOF.md`, `README.md`, `build.py`, `verify.py`
- `130-shared-index/positive/inherited/gap_fusion/equations/`: `gap_fusion_direct.json`, `gap_fusion_direct_lower_centre.json`, `gap_fusion_direct_sharp_centre.json`, `gap_fusion_scaled.json`, `gap_fusion_scaled_lower_centre.json`, `gap_fusion_scaled_sharp_centre.json`
- `130-shared-index/report/`: `centering.tex`, `metrics.tex`, `report.pdf`, `report.tex`, `residuals.tex`, `variables.tex`
- `130-shared-index/reviews/`: `AUDIT_CENTER246.md`, `AUDIT_COMBINED_241.json`, `AUDIT_COMBINED_241.md`, `AUDIT_POSITIVE.md`, `README.md`
- `130-shared-index/verification/`: `RELEASE_CHECKS.json`, `REPORT_QA.json`
- `131-shared-pell-caps-round16/`: `CLOSURE_MAP.md`, `ConZFC_Shared_Pell_Caps_Round16_2026-10-25.pdf`, `ENDPOINTS.json`, `ISOLATED_REPLAY.json`, `LICENSE`, `MANIFEST_SHA256.json`, `NOTICE.md`, `README.md`, `REPLAY.json`, `SOURCE_INVENTORY.json`, `VALIDATION.json`, `build_report.sh`, `verify.py`
- `131-shared-pell-caps-round16/architecture/`: `NEGATIVE_RECIPROCAL_NOTE.md`, `PRIMARY_AND_SPARSE_CHECK.json`, `PRIMARY_AND_SPARSE_CHECK_OPTIMIZED.json`, `README.md`, `REPRODUCTION.json`, `REPRODUCTION_OPTIMIZED.json`, `SEMANTIC_PINS_CHECK.json`, `SOURCE_CLOSURE.json`, `UNIFIED_CAP_PROOF.md`, `build_unified_cap.py`, `check_cap_variants.py`, `check_unified_cap.py`, `reproduce_unified_cap.py`
- `131-shared-pell-caps-round16/architecture/portable/`: `LICENSE`, `ProveIt_LICENSE`
- `131-shared-pell-caps-round16/architecture/unified_cap_h12/`: `SUMMARY.json`
- `131-shared-pell-caps-round16/architecture/unified_cap_h12/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `131-shared-pell-caps-round16/architecture/unified_cap_h12/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `131-shared-pell-caps-round16/architecture/unified_cap_sparse_h12/`: `SUMMARY.json`
- `131-shared-pell-caps-round16/architecture/unified_cap_sparse_h12/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `131-shared-pell-caps-round16/architecture/unified_cap_sparse_h12/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `gate_ledger.json`, `macro_inventory.json`, `raw_audit_input.json`
- `131-shared-pell-caps-round16/cap_audit/`: `FINAL_AUDIT.md`, `FINAL_ENDPOINT_CHECK.json`, `FINAL_ENDPOINT_CHECK_OPTIMIZED.json`, `ODD_ANCHOR_CHECK.json`, `REVIEW_PINS.json`, `SIGNED_CAP_AUDIT.md`, `SIGNED_CAP_CHECK.json`, `check_compiled_cap.py`, `check_odd_anchor.py`, `check_signed_cap.py`
- `131-shared-pell-caps-round16/dependencies/cofinal/`: `LICENSE.UPSTREAM`, `NOTICE.md`
- `131-shared-pell-caps-round16/direct/`: `COMPARISON.json`, `DELIVERY_WHITELIST.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `REPRODUCTION_CHECK.json`, `ROUND14_NOTICE.md`, `ROUND15_NOTICE.md`, `SOURCE_AND_ARTIFACT_PINS.json`, `build_cap.py`, `center_integer.py`
- `131-shared-pell-caps-round16/direct/cap_cofinal_self/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `input_raw.json`, `projected.json`, `projection_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `131-shared-pell-caps-round16/direct/cap_sparse/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `input_raw.json`, `projected.json`, `projection_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `131-shared-pell-caps-round16/direct/integer324/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `131-shared-pell-caps-round16/direct/integer338/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `131-shared-pell-caps-round16/direct/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `131-shared-pell-caps-round16/packaging/`: `render_proofs.py`
- `131-shared-pell-caps-round16/positive/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `PROOF.md`, `README.md`, `RELEASE_WHITELIST.json`, `SOURCE_PINS.json`, `build.py`, `verify.py`
- `131-shared-pell-caps-round16/positive/equations/`: `direct_single_square.json`, `direct_single_square_lean.json`, `single_square.json`, `single_square_lean.json`
- `131-shared-pell-caps-round16/positive/provenance/`: `PUBLIC_GAP_FUSION_PROOF.md`
- `131-shared-pell-caps-round16/positive/provenance/saturation_source/`: `LICENSE.UPSTREAM`
- `131-shared-pell-caps-round16/report/`: `architecture_full.tex`, `comparison.tex`, `direct_full.tex`, `equations.tex`, `main.tex`, `overview.tex`, `positive_full.tex`, `questions.tex`, `reproducibility.tex`, `scalar_full.tex`, `signed_lemma_full.tex`, `two_root_full.tex`
- `131-shared-pell-caps-round16/report_audit/`: `ARCHIVE_PROVENANCE_RECHECK.json`, `COMPACT44_COEFFICIENT_REPLAY.json`, `COMPACT44_COEFFICIENT_REPLAY_OPTIMIZED.json`, `DELIVERY_STRUCTURE.json`, `FINAL_REPORT_REVIEW.json`, `FRESH_BUILD_RASTER_CHECK.json`, `PROOF_COVERAGE.json`, `PROOF_FIDELITY.json`, `REPORT_METRICS.json`, `REPORT_METRICS_OPTIMIZED.json`, `SOURCE34_COEFFICIENT_REPLAY.json`, `SOURCE34_COEFFICIENT_REPLAY_OPTIMIZED.json`, `check_delivery_structure.py`, `check_proof_fidelity.py`, `check_report_metrics.py`
- `131-shared-pell-caps-round16/review/`: `HEIGHT_ONE_BINDING.json`, `INCOMING_COMPARISON.json`, `INDEPENDENT_METRICS.json`, `PUBLIC_PIN.json`, `ROUND16_REVIEW.md`, `archive_acquisition.json`
- `131-shared-pell-caps-round16/review/source/`: `CURRENT_EQUATION.json`, `candidates__ten-positive-gap-fusion__PROOF.md`, `candidates__ten-positive-gap-fusion__README.md`, `research__ten-positive-uncentered-b-weight__PROOF.md`, `research__ten-positive-uncentered-b-weight__README.md`
- `131-shared-pell-caps-round16/root_math/`: `SIGNED_POOLED_CAP.md`
- `131-shared-pell-caps-round16/scalar/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `COEFFICIENT_RECIPE_CHECK.json`, `COEFFICIENT_RECIPE_CHECK_OPTIMIZED.json`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `RELEASE.json`, `RELEASE_WHITELIST.json`, `SOURCE_PINS.json`, `TWO_ROOT_PROOF.md`, `build.py`, `build_two.py`, `build_two_weak.py`, `check.py`, `product11_degree882.json`, `product11_degree966.json`
- `131-shared-pell-caps-round16/scalar/inherited/`: `LICENSE.UPSTREAM`
- `131-shared-pell-caps-round16/scalar/inherited/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `131-shared-pell-caps-round16/scalar/inherited/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `131-shared-pell-caps-round16/scalar/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `131-shared-pell-caps-round16/scalar/two_root/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `METRICS.json`, `check.py`, `two_root11_degree810.json`
- `131-shared-pell-caps-round16/scalar/two_root_weak/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `METRICS.json`, `check.py`, `two_root_weak11_degree654.json`
- `131-shared-pell-caps-round16/scalar_audit/`: `INDEPENDENT_NORMAL.json`, `INDEPENDENT_OPTIMIZED.json`, `REVIEW_BINDINGS.json`, `SEMANTIC_REVIEW.md`, `audit_product.py`
- `131-shared-pell-caps-round16/small_audit/`: `NORMAL.json`, `OPTIMIZED.json`, `POSITIVE_BUILD.json`, `POSITIVE_BUILD_OPTIMIZED.json`, `POSITIVE_COEFFICIENT_REPLAY.json`, `POSITIVE_COEFFICIENT_REPLAY_OPTIMIZED.json`, `REVIEW_BINDINGS.json`, `SCALAR_BUILD.json`, `SCALAR_BUILD_OPTIMIZED.json`, `SEMANTIC_REVIEW.md`, `WEAK_BUILD.json`, `WEAK_BUILD_OPTIMIZED.json`, `check_small.py`
- `132-signed-caps-free-scales/`: `CODE_REVIEW.json`, `COMPONENT_SEALS.json`, `DEPENDENCIES.md`, `LICENSES.md`, `MANIFEST.json`, `PRIOR.json`, `README.md`, `REPLAY_SUMMARY.json`, `REPRODUCE_PLAN.json`, `RESULTS.json`, `make_release_zip.py`, `reproduce.py`, `seal_release.py`
- `132-signed-caps-free-scales/alternative/`: `BUILD355.txt`, `CHECK355_NORMAL.txt`, `CHECK355_OPTIMIZED.txt`, `CHECK_NORMAL.txt`, `CHECK_OPTIMIZED.txt`, `DELIVERY_WHITELIST.json`, `FINAL_SEAL.json`, `MANIFEST.json`, `MUTATIONS_NORMAL.txt`, `MUTATIONS_OPTIMIZED.txt`, `MUTATION_CHECKS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `REBUILD_CHECK.json`, `SIGNED_CAP_FINITE_CHECKS.json`, `SIGNED_CAP_ODD_QUOTIENT_CHECKS.json`, `SIGNED_CAP_REVIEW.md`, `SOURCE_LEDGER.json`, `build_signed_cap.py`, `check_mutations.py`, `check_signed_cap.py`, `section.tex`
- `132-signed-caps-free-scales/alternative/inherited_proofs/`: `NOTICE.md`
- `132-signed-caps-free-scales/alternative/inherited_proofs/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/alternative/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `132-signed-caps-free-scales/alternative/odd_cap/`: `CHECK.json`, `METRICS.json`, `POWER_COVERAGE.json`, `PRESEMANTIC_BOUNDS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`
- `132-signed-caps-free-scales/alternative/signed_cap/`: `CHECK.json`, `METRICS.json`, `POWER_COVERAGE.json`, `PRESEMANTIC_BOUNDS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`
- `132-signed-caps-free-scales/baseline/`: `BASELINE_CHECKS.json`, `ELEVEN416_REVIEW.md`, `FRONTIER.md`, `INCOMING_CHECKS.json`, `INDEPENDENT_INCOMING_DATA_AUDIT.json`, `MATHEMATICAL_OPPORTUNITIES.md`, `RECENT_COMMITS.json`, `SELECTED_EVIDENCE.json`
- `132-signed-caps-free-scales/baseline/late/`: `12a6f5a037-PROPOSAL_REVIEW_LATEST.md`, `12a6f5a037-ROUND15_DIRECT_REVIEW.md`, `12a6f5a037-round15-direct-root-peer.md`, `LATEST_HEAD.json`
- `132-signed-caps-free-scales/baseline/selected/Computability/DiophantineConsistency/`: `CURRENT_EQUATION.json`, `NATIVE_QUARTIC_SIZE.md`, `README.md`, `RECENT_INTAKE_2026_10_24.md`, `STATUS.md`
- `132-signed-caps-free-scales/baseline/selected/Computability/DiophantineConsistency/candidates/ten-positive-gap-fusion/`: `CHECKS.json`, `INDEPENDENT_REVIEW.md`, `PROOF.md`, `README.md`
- `132-signed-caps-free-scales/baseline/selected/Computability/DiophantineConsistency/candidates/ten-positive-gap-fusion/equations/`: `gap_fusion_direct.json`, `gap_fusion_direct_lower_centre.json`, `gap_fusion_direct_sharp_centre.json`, `gap_fusion_scaled.json`, `gap_fusion_scaled_lower_centre.json`, `gap_fusion_scaled_sharp_centre.json`
- `132-signed-caps-free-scales/integer/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `METRICS.json`, `PROOF.md`, `README.md`, `RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `free_main_saturated11_none.json`, `free_main_saturated11_sharp.json`, `free_main_saturated11_simple.json`, `main_saturated11_none.json`, `main_saturated11_sharp.json`, `main_saturated11_simple.json`, `section.tex`
- `132-signed-caps-free-scales/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `132-signed-caps-free-scales/integer/source/`: `FREE_SCALE_PROOF.md`, `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/integer_lowops/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `METRICS.json`, `PROOF.md`, `README.md`, `RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `product_main_guard11_native.json`, `product_main_guard11_short.json`, `section.tex`
- `132-signed-caps-free-scales/integer_lowops/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `132-signed-caps-free-scales/integer_lowops/source/`: `FREE_SCALE_PROOF.md`, `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/integer_lowops/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/integer_lowops/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/lowdegree/`: `DEPENDENCIES.md`, `MANIFEST.json`, `METRICS.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `equation.json`, `section.tex`, `specification.json`, `standalone.pdf`, `standalone.tex`
- `132-signed-caps-free-scales/lowdegree/review/`: `BASELINE_FACTORING_CHECK.json`, `CHECK.json`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `PDF_QA.json`, `audit.py`
- `132-signed-caps-free-scales/positive/`: `BUILD_CHECK.txt`, `BUILD_CHECK_OPTIMIZED.txt`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `check.py`, `first.json`, `second.json`, `section.tex`
- `132-signed-caps-free-scales/positive/prior/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `132-signed-caps-free-scales/prior/wave15/`: `LICENSES.md`
- `132-signed-caps-free-scales/prior/wave15/alternative/inherited_proofs/`: `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/alternative/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `132-signed-caps-free-scales/prior/wave15/baseline/Computability/DiophantineConsistency/research/power0-output-square-frame/source/`: `LICENSE.bootstrap`
- `132-signed-caps-free-scales/prior/wave15/baseline/arrivals/ConZFC_Carriers_and_Even_Indices_2026-10-24/ConZFC_Carriers_and_Even_Indices_2026-10-24/`: `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/prior/wave15/baseline/arrivals/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/baseline/arrivals/ConZFC_Signed_Powers_Height_Two_2026-10-24/ConZFC_Signed_Powers_Height_Two_2026-10-24/`: `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/prior/wave15/baseline/arrivals/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/`: `LICENSE`
- `132-signed-caps-free-scales/prior/wave15/baseline/arrivals/con-zfc-quadratic-frames-2026-10-24/con-zfc-quadratic-frames/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/baseline/arrivals/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/`: `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/prior/wave15/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `132-signed-caps-free-scales/prior/wave15/integer/source/`: `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/prior/wave15/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/lowdegree/twelve/source/`: `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/prior/wave15/positive/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/alternative/prior/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/`: `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/source/`: `LICENSE.UPSTREAM`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/lowdegree/`: `LICENSE.ProveIt`
- `132-signed-caps-free-scales/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/positive/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `132-signed-caps-free-scales/prior/wave15/review/alternative/attribution/`: `SOURCE.json`, `upstream_six_pair_review.md`
- `132-signed-caps-free-scales/report/`: `EDITORIAL_MATH_CHECK.json`, `QA_RECEIPT.json`, `build_report.sh`, `check_report.py`, `positive_definitions.tex`, `references.tex`, `report.pdf`, `report.tex`, `scope.tex`, `section_copy_provenance.json`, `summary.tex`, `validation.tex`
- `132-signed-caps-free-scales/report/sections/`: `direct.tex`, `direct_full_proof.tex`, `integer.tex`, `integer_lowops.tex`, `lowdegree.tex`, `positive.tex`
- `132-signed-caps-free-scales/report/sources/`: `direct_full.tex`
- `132-signed-caps-free-scales/review/alternative/`: `INDEPENDENT_CAP_REPLAY.json`, `OPTIMIZED_RUN.txt`, `PROVENANCE.json`, `REVIEW.md`, `audit_cap_independent.py`
- `132-signed-caps-free-scales/review/alternative/optimized/`: `INDEPENDENT_CAP_REPLAY.json`
- `132-signed-caps-free-scales/review/integer/`: `AUDIT.json`, `FINITE_AUDIT_MANIFEST.json`, `FROZEN_INPUTS.json`, `NORMAL_OUTPUT.json`, `OPTIMIZED_OUTPUT.json`, `ORDINARY_REVIEW.md`, `REVIEW.md`, `check_independent.py`, `independent_audit.py`, `receipt-normal.json`, `receipt-optimized.json`
- `132-signed-caps-free-scales/review/integer_lowops/`: `FINITE_AUDIT_MANIFEST.json`, `FROZEN_INPUTS.json`, `REVIEW.md`, `check_independent.py`, `receipt-normal.json`, `receipt-optimized.json`
- `132-signed-caps-free-scales/review/lowdegree/`: `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `root_normal.txt`, `root_optimized.txt`
- `132-signed-caps-free-scales/review/lowops/`: `AUDIT.json`, `NORMAL_OUTPUT.json`, `OPTIMIZED_OUTPUT.json`, `REVIEW.md`, `independent_audit.py`
- `132-signed-caps-free-scales/review/positive/`: `AUDIT.json`, `NORMAL_OUTPUT.json`, `OPTIMIZED_OUTPUT.json`, `REVIEW.md`, `independent_audit.py`
- `132-signed-caps-free-scales/review/replay/`: `REPRODUCE_CHECK.json`
- `132-signed-caps-free-scales/review/replay/REPRODUCE_CHECK_logs/`: `normal_01.txt`, `normal_02.txt`, `normal_03.txt`, `normal_04.txt`, `normal_05.txt`, `normal_06.txt`, `normal_07.txt`, `normal_08.txt`, `normal_09.txt`, `normal_10.txt`, `normal_11.txt`, `normal_12.txt`, `normal_13.txt`, `normal_14.txt`, `normal_15.txt`, `normal_16.txt`, `normal_17.txt`, `normal_18.txt`, `normal_19.txt`, `normal_20.txt`, `normal_21.txt`, `normal_22.txt`, `optimized_01.txt`, `optimized_02.txt`, `optimized_03.txt`, `optimized_04.txt`, `optimized_05.txt`, `optimized_06.txt`, `optimized_07.txt`, `optimized_08.txt`, `optimized_09.txt`, `optimized_10.txt`, `optimized_11.txt`, `optimized_12.txt`, `optimized_13.txt`, `optimized_14.txt`, `optimized_15.txt`, `optimized_16.txt`, `optimized_17.txt`, `optimized_18.txt`, `optimized_19.txt`, `optimized_20.txt`, `optimized_21.txt`, `optimized_22.txt`
- `132-signed-caps-free-scales/review/report/`: `DATA_CHECK.json`, `DATA_CHECK_OPTIMIZED.json`, `EDITORIAL_CHECK_REPLAY.json`, `EDITORIAL_CHECK_REPLAY_OPTIMIZED.json`, `PORTABILITY.json`, `REPORT_REVIEW.json`, `REPORT_REVIEW.md`, `check_report_data.py`, `check_report_data_original.py`
- `133-staged-certificates/`: `LICENSE`, `MANIFEST.sha256`, `PROVENANCE.json`, `README.md`, `RESULTS.json`, `build_report.sh`, `evaluate.py`, `integer_companion.json`, `verify_release.py`
- `133-staged-certificates/compact/`: `PROOF.md`, `README.md`, `REVIEW.md`, `REVIEW_PINS.json`, `equation_84.json`, `equation_85.json`, `parent-equation.json`, `report_section.tex`, `verification-optimized.json`, `verification.json`, `verify.py`
- `133-staged-certificates/compact/coefficients/`: `K.bin.gz`
- `133-staged-certificates/compact/provenance/`: `SOURCE_LEDGER.json`, `parent_printed_equation.tex`, `saturated_parent_proof.md`, `uncentered_parent_proof.md`
- `133-staged-certificates/direct/`: `INDEPENDENT_DOMINANT_RECEIPT.json`, `INDEPENDENT_DOMINANT_RECEIPT_OPTIMIZED.json`, `INDEPENDENT_REVIEW.md`, `PROOF.md`, `README.md`, `REPLAY.json`, `REPLAY_OPTIMIZED.json`, `SOURCE_LEDGER.json`, `build.py`, `builder.py`, `review_staged_independent.py`, `verify.py`
- `133-staged-certificates/direct/equations/`: `RESULTS.json`
- `133-staged-certificates/direct/equations/minimum237/`: `RECIPE.json`
- `133-staged-certificates/direct/equations/minimum237/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `variables.tsv`
- `133-staged-certificates/direct/equations/minimum237/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `133-staged-certificates/direct/equations/principal239/`: `RECIPE.json`
- `133-staged-certificates/direct/equations/principal239/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `variables.tsv`
- `133-staged-certificates/direct/equations/principal239/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `133-staged-certificates/direct/equations/small_support255/`: `RECIPE.json`
- `133-staged-certificates/direct/equations/small_support255/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `variables.tsv`
- `133-staged-certificates/direct/equations/small_support255/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `133-staged-certificates/direct/equations/sparse240/`: `RECIPE.json`
- `133-staged-certificates/direct/equations/sparse240/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `variables.tsv`
- `133-staged-certificates/direct/equations/sparse240/raw/`: `METRICS.json`, `cap_certificate.json`, `equation.json`, `expanded_polynomial.json`, `raw_audit_input.json`
- `133-staged-certificates/direct/upstream/`: `LICENSE`, `NOTICE.md`
- `133-staged-certificates/direct/upstream/binomial_provenance/`: `LICENSE.108`, `NOTICE.108.txt`
- `133-staged-certificates/direct/upstream/frozen_round14/`: `LICENSE`, `NOTICE.md`
- `133-staged-certificates/direct/upstream/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `133-staged-certificates/direct/upstream/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `133-staged-certificates/direct/upstream/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `133-staged-certificates/direct/upstream/frozen_round14/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `133-staged-certificates/report/`: `constants.tex`, `generate_residuals.py`, `product_square.tex`, `report.pdf`, `report.tex`, `residuals.tex`
- `133-staged-certificates/review/`: `PDF_QA.json`, `PRINTED_RESIDUALS.json`, `REPORT_REVIEW.json`
- `134-certificate-reductions/`: `INTEGRATION.md`, `LICENSE`, `METRICS.json`, `PROVENANCE.json`, `README.md`, `verify.py`
- `134-certificate-reductions/compact/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `equation78.json`, `equation79.json`, `rebuild_coefficients.py`, `section.tex`, `verify.py`
- `134-certificate-reductions/compact/coefficients/`: `K.bin.gz`
- `134-certificate-reductions/compact/licenses/`: `LICENSE.ProveIt`, `LICENSE.Wade`, `NOTICE-native44.md`, `NOTICE-normalized-source.txt`, `NOTICE-original245.txt`, `NOTICE-package44.md`, `NOTICE-source61.md`, `NOTICE_K215.md`
- `134-certificate-reductions/direct/`: `README.md`, `check.json`, `equation.json`, `expanded_polynomial.json`, `metrics.json`, `optimized_check.json`, `projected.json`, `projection.json`, `projection_check.json`, `proof.md`, `replay.json`, `residuals.tex`, `residuals.txt`, `review.md`, `section.tex`, `source.json`, `source_change.json`, `source_pins.json`, `translation.json`, `variables.tsv`
- `134-certificate-reductions/direct/code/`: `build.py`, `check.py`, `print_equation.py`
- `134-certificate-reductions/direct/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`, `parent131_notice.md`, `round14_notice.md`, `round15_notice.md`
- `134-certificate-reductions/direct/proofs/`: `INDEX.md`, `fixed_center.md`, `signed_scale.md`
- `134-certificate-reductions/natural/`: `ENGINE_MAP.json`, `INDEPENDENT_REPLAY.json`, `LICENSE`, `METRICS.json`, `NOTICE.md`, `README.md`, `REPLAY.json`, `REVIEW.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `build.py`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `render_equation.py`, `residuals.tex`, `residuals.txt`, `review_arithmetic_controls.py`, `variables.tsv`, `verify.py`
- `134-certificate-reductions/natural/engine/direct/`: `NOTICE.md`, `build_modular_factorial.py`
- `134-certificate-reductions/natural/engine/direct/r14/`: `NOTICE.md`
- `134-certificate-reductions/natural/engine/direct/r14/architecture/`: `build_derived_label_range.py`, `build_hybrid.py`
- `134-certificate-reductions/natural/engine/direct/r14/intake/shell/shell/`: `NOTICE.md`
- `134-certificate-reductions/natural/engine/direct/r14/intake/shell/shell/code/`: `norm_transform.py`
- `134-certificate-reductions/natural/engine/direct/r14/intake/shell/shell/upstream/q407/`: `NOTICE.md`
- `134-certificate-reductions/natural/engine/direct/r14/intake/shell/shell/upstream/q407/upstream/`: `NOTICE.md`
- `134-certificate-reductions/natural/engine/direct/r14/intake/shell/shell/upstream/q407/upstream/provenance/upstream/`: `NOTICE.md`
- `134-certificate-reductions/natural/provenance/`: `README.md`, `check_pins.py`
- `134-certificate-reductions/natural/source/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `semantic.json`
- `134-certificate-reductions/report/`: `compact_constants.tex`, `natural_section.tex`, `report.pdf`, `report.tex`
- `134-certificate-reductions/verification/`: `PDF_QA.json`, `README.md`, `normal_with_rebuild.json`, `optimized_with_rebuild.json`
- `135-cofinal-anchors-round17/`: `CLOSURE_MAP.md`, `ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.pdf`, `ENDPOINTS.json`, `ISOLATED_REPLAY.json`, `LICENSE`, `MANIFEST_SHA256.json`, `NOTICE.md`, `README.md`, `VERIFY_PLAN.json`, `build_report.sh`, `verify.py`
- `135-cofinal-anchors-round17/architecture/`: `README.md`, `RELEASE_WHITELIST.json`, `SOURCE_CLOSURE.json`, `build_strict_anchor.py`, `contract_reordered.py`, `verify_architecture.py`
- `135-cofinal-anchors-round17/architecture/portable/`: `LICENSE`, `ProveIt_LICENSE`
- `135-cofinal-anchors-round17/architecture/portable/source/custom/`: `build_modular_factorial.py`, `build_strict_budget.py`
- `135-cofinal-anchors-round17/architecture/proofs/`: `ONE_ROW_SEMANTIC_ANCHOR_PROOF.md`
- `135-cofinal-anchors-round17/architecture/strict_natural228/`: `SUMMARY.json`
- `135-cofinal-anchors-round17/architecture/strict_natural228/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `135-cofinal-anchors-round17/architecture/strict_natural228/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `semantic.json`
- `135-cofinal-anchors-round17/architecture/strict_natural229/`: `SUMMARY.json`
- `135-cofinal-anchors-round17/architecture/strict_natural229/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `135-cofinal-anchors-round17/architecture/strict_natural229/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `semantic.json`
- `135-cofinal-anchors-round17/architecture/strict_natural230/`: `SUMMARY.json`
- `135-cofinal-anchors-round17/architecture/strict_natural230/natural/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`
- `135-cofinal-anchors-round17/architecture/strict_natural230/raw/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `semantic.json`
- `135-cofinal-anchors-round17/architecture/verification/`: `FINAL_NORMAL.json`, `FINAL_OPTIMIZED.json`, `strict_natural228_affine_normal.json`, `strict_natural228_affine_optimized.json`, `strict_natural228_contraction_normal.json`, `strict_natural228_contraction_optimized.json`, `strict_natural229_affine_normal.json`, `strict_natural229_affine_optimized.json`, `strict_natural229_contraction_normal.json`, `strict_natural229_contraction_optimized.json`, `strict_natural230_affine_normal.json`, `strict_natural230_affine_optimized.json`, `strict_natural230_contraction_normal.json`, `strict_natural230_contraction_optimized.json`
- `135-cofinal-anchors-round17/cap_audit/`: `CAP_COMPOSITION_REVIEW.md`, `FROZEN_HASHES.json`, `STRICT_NATURAL_AUDIT.json`, `STRICT_NATURAL_AUDIT_OPTIMIZED.json`, `STRICT_SIGNED282_AUDIT.json`, `STRICT_SIGNED282_AUDIT_OPTIMIZED.json`, `STRICT_SIGNED287_AUDIT.json`, `STRICT_SIGNED287_AUDIT_OPTIMIZED.json`, `STRICT_SIGNED309_AUDIT.json`, `STRICT_SIGNED309_AUDIT_OPTIMIZED.json`, `check_natural.py`, `check_signed.py`
- `135-cofinal-anchors-round17/direct/`: `ARITHMETIC_CONTROLS_NORMAL.json`, `ARITHMETIC_CONTROLS_OPTIMIZED.json`, `CHECK_FINAL_NORMAL.json`, `CHECK_FINAL_OPTIMIZED.json`, `CLOSURE.json`, `DELIVERY_WHITELIST.json`, `NOTICE.md`, `ORIENTATION_FIRST_PROOF.md`, `PROOF.md`, `PROOF_315.md`, `README.md`, `REPRODUCE_NORMAL.json`, `REPRODUCE_OPTIMIZED.json`, `SOURCE_AND_ARTIFACT_PINS.json`, `STRICT_BUDGET_PROOF.md`, `build_cap.py`, `check_arithmetic_controls.py`, `check_compiled_cap.py`, `reproduce.py`
- `135-cofinal-anchors-round17/direct/constructor_sources/`: `SHA256.json`
- `135-cofinal-anchors-round17/direct/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `135-cofinal-anchors-round17/direct/strict_dimension/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `input_raw.json`, `projected.json`, `projection_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `135-cofinal-anchors-round17/direct/strict_dimension_centered/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `135-cofinal-anchors-round17/direct/strict_grouped/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `input_raw.json`, `projected.json`, `projection_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `135-cofinal-anchors-round17/direct/strict_grouped_centered/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `135-cofinal-anchors-round17/direct/strict_sparse/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `input_raw.json`, `projected.json`, `projection_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `135-cofinal-anchors-round17/direct/strict_sparse_centered/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `135-cofinal-anchors-round17/height_one/`: `CONFIG.json`, `ENDPOINTS.json`, `MANIFEST_SHA256.json`, `NOTICE.md`, `README.md`, `SOURCE_BINDINGS.json`, `WHITELIST.json`, `check.py`, `check_factor.py`, `compare_matched.py`, `contract.py`, `factor_source.py`, `independent_audit.py`, `literal.py`, `verify.py`
- `135-cofinal-anchors-round17/height_one/comparison/`: `COMPARISON.json`
- `135-cofinal-anchors-round17/height_one/endpoints/balanced806/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `135-cofinal-anchors-round17/height_one/endpoints/compact793/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `135-cofinal-anchors-round17/height_one/endpoints/sparse994/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `135-cofinal-anchors-round17/height_one/receipts/`: `MATCHED_NORMAL.json`, `MATCHED_OPTIMIZED.json`, `REPLAY_BOTH.json`
- `135-cofinal-anchors-round17/height_one/report/`: `proof_body.tex`, `results.tex`
- `135-cofinal-anchors-round17/height_one/sources/`: `original287.json`, `original309.json`
- `135-cofinal-anchors-round17/height_one/sources/refactored287/`: `factor_certificate.json`, `selection.json`, `source.json`
- `135-cofinal-anchors-round17/height_one/sources/refactored309/`: `factor_certificate.json`, `selection.json`, `source.json`
- `135-cofinal-anchors-round17/height_one/vendor/`: `GRAPH_NOTICE.md`, `LICENSE`
- `135-cofinal-anchors-round17/packaging/`: `render_proofs.py`
- `135-cofinal-anchors-round17/report/`: `PROOF_INPUTS.json`, `abstract.tex`, `architecture_full.tex`, `comparison.tex`, `direct_foundation_full.tex`, `direct_orientation_full.tex`, `direct_strict_full.tex`, `endpoint_tables.tex`, `equations.tex`, `height_one_full.tex`, `height_one_results.tex`, `main.tex`, `overview.tex`, `questions.tex`, `reproducibility.tex`, `scalar_full.tex`
- `135-cofinal-anchors-round17/report_audit/`: `CLOSURE_CHECK.json`, `CLOSURE_CHECK_OPTIMIZED.json`, `DOCUMENT_ONLY_DELTA.json`, `FRESH_BUILD_RASTER_CHECK.json`, `INDEPENDENT_DOCUMENT_CLOSURE.json`, `INDEPENDENT_DOCUMENT_REVIEW.json`, `INDEPENDENT_LITERAL_METRICS.json`, `PRESENTATION_MUTATIONS.json`, `PROOF_COVERAGE.json`, `PROOF_FIDELITY.json`, `PROOF_FIDELITY_OPTIMIZED.json`, `REPORT_METRICS.json`, `REPORT_METRICS_OPTIMIZED.json`, `check_closure.py`, `check_proof_fidelity.py`, `check_report_metrics.py`
- `135-cofinal-anchors-round17/review/`: `ARCHIVE_AUTHENTICATION.json`, `CONTRACTION_REPLAY.json`, `CONTRACTION_REPLAY_OPTIMIZED.json`, `HEIGHT_ONE_FINAL_AUDIT.json`, `HEIGHT_ONE_FINAL_AUDIT_OPTIMIZED.json`, `HEIGHT_ONE_FINAL_MATHEMATICAL_AUDIT.md`, `INCOMING_MANIFEST_REPLAY.json`, `INDEPENDENT_INCOMING_METRICS.json`, `PIN.json`
- `135-cofinal-anchors-round17/review/final_height_one_audit/`: `README.md`, `audit_affine_factor.py`, `audit_height_one.py`, `verify_final.py`
- `135-cofinal-anchors-round17/scalar/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `CLOSURE_MAP.md`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `RELEASE_WHITELIST.json`, `REPLAY.json`, `RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `free_cofactor11_none.json`, `free_cofactor11_sharp.json`, `free_cofactor11_simple.json`, `replay.py`, `weak_cofactor11_none.json`, `weak_cofactor11_sharp.json`, `weak_cofactor11_simple.json`
- `135-cofinal-anchors-round17/scalar/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `135-cofinal-anchors-round17/scalar/source/`: `LICENSE.UPSTREAM`
- `135-cofinal-anchors-round17/scalar/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `135-cofinal-anchors-round17/scalar/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `135-cofinal-anchors-round17/scalar_audit/`: `ALL_GATE_MUTATIONS.json`, `ALL_GATE_MUTATIONS_OPTIMIZED.json`, `AUDIT.json`, `AUDIT_MANIFEST.json`, `AUDIT_OPTIMIZED.json`, `CLEAN_REPLAY.json`, `SEMANTIC_AUDIT.md`, `audit_mutations.py`, `audit_scalar.py`, `replay_release.py`
- `136-local-certificates/`: `EQUATION_IDENTITIES.json`, `LICENSE`, `MANIFEST.sha256`, `NOTICE.txt`, `README.txt`, `build_report_data.py`, `direct_residuals.tex`, `evaluate.py`, `metrics.tex`, `provenance_section.tex`, `report.pdf`, `report.tex`, `results_table.tex`, `signed_section.tex`, `verification_section.tex`, `verify.py`
- `136-local-certificates/direct/`: `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build.py`, `signed_section.tex`, `verify.py`
- `136-local-certificates/direct/integer306/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `transformation_certificate.json`, `variables.tsv`
- `136-local-certificates/direct/review/`: `REVIEW306.md`, `REVIEW306_CHECK.json`, `REVIEW306_CHECK_OPTIMIZED.json`, `review306.py`
- `136-local-certificates/graph/`: `HUB_COMPARISON.json`, `LIFT_CHECKS.json`, `PROFILES.json`, `README.txt`, `REBUILD_VERIFICATION.json`, `REBUILD_VERIFICATION_OPTIMIZED.json`, `SOURCE_PINS.json`, `VERIFICATION.json`, `evaluate.py`, `optimize_aliases.py`, `verify.py`, `verify_local.py`
- `136-local-certificates/graph/inherited/`: `LICENSE`, `NOTICE.md`
- `136-local-certificates/graph/matched1252/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`, `verification.json`, `verification_optimized.json`
- `136-local-certificates/graph/parents/principal985/`: `certificate.json`, `metrics.json`, `polynomial.json`
- `136-local-certificates/graph/parents/sparse1122/`: `certificate.json`, `metrics.json`, `polynomial.json`
- `136-local-certificates/graph/principal985/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`, `verification.json`
- `136-local-certificates/graph/sources/`: `source306.json`
- `136-local-certificates/graph/sparse1122/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`, `verification_optimized.json`
- `136-local-certificates/provenance/`: `NOTICE_131.md`, `ROOT_SOURCE_PINS.json`
- `136-local-certificates/verification/`: `PDF_QA.json`, `RELEASE_CHECK.json`, `RELEASE_CHECK_OPTIMIZED.json`
- `137-odd-helpers-saturated-carriers/`: `CODE_REVIEW.json`, `COMPONENT_SEALS.json`, `DEPENDENCIES.md`, `MANIFEST.json`, `PRIOR.json`, `README.md`, `REPLAY_SUMMARY.json`, `REPRODUCE_PLAN.json`, `RESULTS.json`, `SOURCE_LOCATION_MAP.json`, `flatten_report.py`, `make_release_zip.py`, `prepare_source_map.py`, `record_replay_summary.py`, `reproduce.py`
- `137-odd-helpers-saturated-carriers/baseline/`: `AUDIT_OPTIMIZED_STDOUT.json`, `AUDIT_STDOUT.json`, `COEFFICIENT_DOWNLOAD_MANIFEST.json`, `DOWNLOAD_MANIFEST.json`, `FRONTIER.md`, `HISTORICAL_LOWDEGREE_CHECK.json`, `INDEPENDENT_DATA_AUDIT.json`, `LATE_COMMITS.json`, `RECENT_COMMITS.json`, `audit_downloaded_data.py`
- `137-odd-helpers-saturated-carriers/baseline/con-zfc-diophantine-forms/129-semantic-pell-anchor/`: `LICENSE`
- `137-odd-helpers-saturated-carriers/baseline/con-zfc-diophantine-forms/130-shared-index/`: `LICENSE`
- `137-odd-helpers-saturated-carriers/baseline/con-zfc-diophantine-forms/131-shared-pell-caps-round16/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/baseline/con-zfc-diophantine-forms/133-staged-certificates/`: `LICENSE`
- `137-odd-helpers-saturated-carriers/baseline/late/`: `FETCH_MANIFEST.json`, `METRICS.json`, `one-page-shared-odd9-root-peer.md`, `signed-pell-cap-nine-factor-projections-root-peer.md`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-helper-reflection/`: `PROOF.md`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-nine-factor-projections/`: `BOUNDARY.json`, `PROOF.md`, `README.md`, `build.py`, `check.py`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-nine-factor-source/`: `MANIFEST.json`, `PROOF.md`, `RESULTS.json`, `SOURCE_PINS.json`, `domain.json`, `guarded.json`, `source.json`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-refined-product-projections/`: `RESULTS.json`, `RESULTS.md`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-refined-product-projections/data/centered/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-refined-source/`: `PROOF.md`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-support-pair-products/`: `BINDING.json`, `MANIFEST.json`, `PROPOSAL.md`, `SOURCE_PINS.json`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap-unoriented/`: `PROPOSAL.md`
- `137-odd-helpers-saturated-carriers/baseline/research/signed-pell-cap/`: `PROPOSAL.md`
- `137-odd-helpers-saturated-carriers/baseline/research/ten-positive-qcube-normalization/`: `PROOF.md`, `build.py`, `zero86.json`
- `137-odd-helpers-saturated-carriers/baseline/reviews/`: `signed-pell-cap-refined-product-projections-root-peer.md`, `ten-qcube-normalization-root-peer.md`
- `137-odd-helpers-saturated-carriers/direct/`: `CACHE_FIX.json`, `CACHE_INVENTORY_CHECK.json`, `CACHE_INVENTORY_CHECK_OPTIMIZED.json`, `CENTER307_LOG.txt`, `CENTER308_LOG.txt`, `CENTER310_LOG.txt`, `CHECK_NORMAL.json`, `CHECK_OPTIMIZED.json`, `CODE_REVIEW.json`, `DIAGNOSTICS.json`, `LICENSE.ProveIt`, `LICENSES.md`, `MANIFEST.json`, `PROJECTION_SEARCH.json`, `PROOF.md`, `README.md`, `REBUILD_NORMAL.json`, `REBUILD_NORMAL_LOG.txt`, `REBUILD_OPTIMIZED.json`, `REBUILD_OPTIMIZED_LOG.txt`, `REPORT_FORMULA_CHECK.json`, `REPORT_FORMULA_CHECK_OPTIMIZED.json`, `REPRODUCE_PLAN.json`, `RESULTS.json`, `SOURCE_BINDING.json`, `SOURCE_COPY_AUTHENTICATION.json`, `SOURCE_PINS.json`, `build.py`, `center.py`, `check.py`, `check_diagnostics.py`, `check_inventory.py`, `check_report.py`, `full_proof.tex`, `reproduce.py`, `seal.py`, `section.tex`
- `137-odd-helpers-saturated-carriers/direct/centered307/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `SOURCE_PARENT.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/centered308/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `SOURCE_PARENT.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/centered310/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `SOURCE_PARENT.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/odd_t/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/odd_y/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/self_radix/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/self_radix_min/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/self_radix_qf/`: `ENGINE.json`, `METRICS.json`, `SOURCE_BINDING.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `projected.json`, `projection_certificate.json`, `raw_equation.json`, `terminal_elimination_certificate.json`, `transformation_certificate.json`, `translation_certificate.json`
- `137-odd-helpers-saturated-carriers/direct/source/`: `CALIBRATION_BINDING.json`, `FUSED_FULL_PROOF.md`, `MANIFEST.json`, `NATIVE_CLOSURE.md`, `NATIVE_CLOSURE_PLAN.json`, `POWER_INTERFACE.json`, `PROOF.md`, `SIGNED_TARGET_CAP.md`, `SUPPORT_PAIR_PRODUCTS.md`, `TRANSFORM.json`, `UPSTREAM_SOURCE_PINS.json`, `domain.json`, `guarded.json`, `source.json`
- `137-odd-helpers-saturated-carriers/integer/`: `BUILD.txt`, `CHECK.json`, `CHECK_NORMAL.txt`, `CHECK_OPTIMIZED.json`, `CHECK_OPTIMIZED.txt`, `MANIFEST.json`, `METRICS.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `REBUILD_CHECK.json`, `RESEARCH_BOUNDARY.md`, `RESULTS.json`, `SOURCE_PINS.json`, `build.py`, `check.py`, `free_product11_none.json`, `free_product11_simple.json`, `section.tex`, `weak_product11_none.json`, `weak_product11_simple.json`
- `137-odd-helpers-saturated-carriers/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `137-odd-helpers-saturated-carriers/integer/source/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/lowdegree/`: `DEPENDENCIES.md`, `MANIFEST.json`, `METRICS.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `build.py`, `equation.json`, `section.tex`, `specification.json`, `standalone.pdf`, `standalone.tex`
- `137-odd-helpers-saturated-carriers/lowdegree/review/`: `CHECK.json`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `PDF_BUILD.txt`, `PDF_QA.json`, `audit.py`
- `137-odd-helpers-saturated-carriers/lowdegree/thirteen/`: `BUILD.txt`, `METRICS.json`, `PROOF.md`, `SOURCE_PINS.json`, `build.py`, `equation.json`, `section.tex`, `specification.json`, `standalone.pdf`, `standalone.tex`
- `137-odd-helpers-saturated-carriers/lowdegree/thirteen/review/`: `CHECK.json`, `NORMAL_RECEIPT.txt`, `OPTIMIZED_RECEIPT.txt`, `PDF_BUILD.txt`, `PDF_QA.json`, `audit.py`
- `137-odd-helpers-saturated-carriers/positive/`: `BUILD_CHECK.txt`, `BUILD_CHECK_OPTIMIZED.txt`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `PROOF.md`, `README.md`, `SOURCE_PINS.json`, `VERIFY.txt`, `VERIFY_OPTIMIZED.txt`, `build.py`, `equation_81.json`, `equation_82.json`, `section.tex`, `verify.py`
- `137-odd-helpers-saturated-carriers/positive/coefficients/`: `BINDING.json`, `REPACKING.json`
- `137-odd-helpers-saturated-carriers/positive/source/`: `QCUBE_PROOF.md`, `ten-qcube-normalization-root-peer.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/`: `LICENSES.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/`: `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/inherited_proofs/`: `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/inherited_proofs/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/alternative/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer/source/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer_lowops/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer_lowops/source/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer_lowops/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/integer_lowops/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/positive/prior/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/`: `LICENSES.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/alternative/inherited_proofs/`: `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Prime_Power_375_553_2026-10-23/ConZFC_Prime_Power_375_553/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/alternative/inherited_proofs/intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/alternative/licenses/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`, `LICENSE.incoming_signed`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/baseline/Computability/DiophantineConsistency/research/power0-output-square-frame/source/`: `LICENSE.bootstrap`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/baseline/arrivals/ConZFC_Carriers_and_Even_Indices_2026-10-24/ConZFC_Carriers_and_Even_Indices_2026-10-24/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/baseline/arrivals/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/baseline/arrivals/ConZFC_Signed_Powers_Height_Two_2026-10-24/ConZFC_Signed_Powers_Height_Two_2026-10-24/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/baseline/arrivals/ConZFC_Synchronized_Exponents_2026-10-24/ConZFC_Synchronized_Exponents_2026-10-24/`: `LICENSE`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/baseline/arrivals/con-zfc-quadratic-frames-2026-10-24/con-zfc-quadratic-frames/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/baseline/arrivals/con-zfc-structural-compression-2026-10-24/con-zfc-structural-compression-2026-10-24/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/integer/source/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/lowdegree/twelve/source/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/positive/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/alternative/prior/`: `LICENSE.Mathlib`, `LICENSE.ProveIt`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/`: `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/source/`: `LICENSE.UPSTREAM`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/integer/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/lowdegree/`: `LICENSE.ProveIt`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/positive/source/`: `LICENSE_SOURCE61`, `NOTICE_SOURCE61.md`
- `137-odd-helpers-saturated-carriers/prior/wave16/prior/wave15/review/alternative/attribution/`: `SOURCE.json`, `upstream_six_pair_review.md`
- `137-odd-helpers-saturated-carriers/report/`: `DATA_CHECK.json`, `PRIOR_INTEGRITY.json`, `QA_RECEIPT.json`, `SELF_CONTAINED_TEX.json`, `STANDALONE_BUILD_CHECK.json`, `TEX_SOURCE_MAP.json`, `build_report.sh`, `calibration.tex`, `check_report.py`, `constructions.tex`, `frontier.tex`, `references.tex`, `report.pdf`, `report.tex`, `report_self_contained.tex`, `scope.tex`, `section_copy_plan.json`, `section_copy_provenance.json`, `summary.tex`, `summary_table.tex`, `validation.tex`
- `137-odd-helpers-saturated-carriers/report/sections/`: `direct.tex`, `integer.tex`, `lowdegree.tex`, `positive.tex`, `thirteen.tex`
- `137-odd-helpers-saturated-carriers/review/`: `INTEGER_LOWDEGREE_VERDICT.json`, `independent_norm_audit.py`
- `137-odd-helpers-saturated-carriers/review/direct/`: `CACHE_FREE_CHECK.json`, `CACHE_FREE_CHECK_OPTIMIZED.json`, `CACHE_FREE_RECHECK.md`, `CACHE_FREE_REPLAY.json`, `CHECK.json`, `CHECK_OPTIMIZED.json`, `FINAL_REVIEW.json`, `FINAL_SEAL.json`, `NATIVE_PROVENANCE.json`, `ORDINARY_AUDIT.md`, `PRE_CACHE_FIX_FINAL_REVIEW.json`, `PRE_CACHE_FIX_FINAL_SEAL.json`, `RELEASE_INVENTORY_CHECK.json`, `SIGNED_HELPER_DIAGNOSTICS.json`, `SIGNED_HELPER_DIAGNOSTICS_OPTIMIZED.json`, `independent_check.py`, `signed_helper_diagnostics.py`
- `137-odd-helpers-saturated-carriers/review/integer/`: `INDEPENDENT_NORMAL.json`, `INDEPENDENT_NORMAL.txt`, `INDEPENDENT_OPTIMIZED.json`, `INDEPENDENT_OPTIMIZED.txt`, `LEMMAS_NORMAL.json`, `LEMMAS_NORMAL.txt`, `LEMMAS_OPTIMIZED.json`, `LEMMAS_OPTIMIZED.txt`, `PRODUCER_NORMAL.json`, `PRODUCER_NORMAL.txt`, `PRODUCER_OPTIMIZED.json`, `PRODUCER_OPTIMIZED.txt`, `REVIEW.md`, `lemma_diagnostics.py`, `producer_replay.py`
- `137-odd-helpers-saturated-carriers/review/lowdegree/`: `INDEPENDENT_NORMAL.json`, `INDEPENDENT_NORMAL.txt`, `INDEPENDENT_OPTIMIZED.json`, `INDEPENDENT_OPTIMIZED.txt`, `REVIEW.md`
- `137-odd-helpers-saturated-carriers/review/lowdegree/thirteen/`: `INDEPENDENT_NORMAL.json`, `INDEPENDENT_NORMAL.txt`, `INDEPENDENT_OPTIMIZED.json`, `INDEPENDENT_OPTIMIZED.txt`, `REVIEW.md`
- `137-odd-helpers-saturated-carriers/review/packaging/`: `PRODUCTION_REPLAY.json`, `ROOT_STATIC_REVIEW.json`
- `137-odd-helpers-saturated-carriers/review/positive/`: `CHECK_NORMAL.json`, `CHECK_OPTIMIZED.json`, `MANIFEST.json`, `REPRODUCE.txt`, `REVIEW.md`, `independent_check.py`
- `137-odd-helpers-saturated-carriers/review/report/`: `ASSEMBLED_CLOSURE_CHECK.json`, `ASSEMBLED_DATA_CHECK.json`, `ASSEMBLED_PRESENTATION_CHECK.json`, `CACHE_PIN_SCAN.json`, `FINAL_VERDICT.json`, `PDF_QA_FINAL.json`, `PRIOR_CHECK.json`, `REPORT_DATA_CHECK.json`, `REPORT_DATA_CHECK_OPTIMIZED.json`, `REVIEW.md`, `SELF_CONTAINED_CHECK.json`, `STANDALONE_RENDER_CHECK.json`, `verify_release_closure.py`, `verify_report_data.py`
- `137-odd-helpers-saturated-carriers/review/root/`: `ORDINARY_REVIEW.json`
- `138-semantic-signs/`: `ENDPOINTS.json`, `INTEGRATION.md`, `LICENSE`, `MANIFEST_SHA256.json`, `NOTICE.md`, `README.md`, `SOURCES.json`, `VERIFICATION_ALL.json`, `build_report.sh`, `verify_all.py`
- `138-semantic-signs/integer11/`: `CHECK.json`, `CHECK_OPTIMIZED.json`, `METRICS.json`, `PROOF.md`, `README.md`, `RESTORED_DEPENDENCIES.json`, `REVIEW.md`, `build.py`, `parity_saturated11_native.json`, `parity_saturated11_short.json`, `verify.py`
- `138-semantic-signs/integer11/licenses/`: `LICENSE-source57`, `LICENSE.ProveIt`, `LICENSE.Wade`, `LICENSE.source71`, `NOTICE-K215.md`, `NOTICE-centered-compression.md`, `NOTICE-normalized-source.txt`, `NOTICE-source25.md`, `NOTICE-source34.md`, `NOTICE-source57.md`, `NOTICE.source68.md`, `NOTICE.source71.md`
- `138-semantic-signs/integer11/source/`: `LICENSE.UPSTREAM`
- `138-semantic-signs/integer11/source/provenance/interpolation12/`: `LICENSE`, `NOTICE.md`
- `138-semantic-signs/integer11/source/provenance/trace_precursor/`: `LICENSE`, `NOTICE.md`
- `138-semantic-signs/integer286/`: `INDEPENDENT_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `PROOF_ORIENTED.md`, `README.md`, `RELEASE_FILES.json`, `REVIEW_COMPACT_AGENT.json`, `REVIEW_COMPACT_AGENT.md`, `SOURCE_PROVENANCE.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build.py`, `evaluate.py`, `verify.py`
- `138-semantic-signs/integer286/generated/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `projected.json`, `projection_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `138-semantic-signs/integer286/generated/centered/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `138-semantic-signs/integer286/inherited/`: `LICENSE.Mathlib`, `NOTICE.112.md`, `NOTICE.125.md`, `NOTICE.131.md`, `NOTICE.131_package.md`
- `138-semantic-signs/integer286/principal/`: `METRICS.json`, `PROJECTION_CHECK.json`, `equation.json`, `expanded_polynomial.json`, `factored_source.json`, `factorization_certificate.json`, `guarded.json`, `projected.json`, `projection_certificate.json`, `source.json`, `transform_certificate.json`, `translation_certificate.json`
- `138-semantic-signs/integer286/principal/centered/`: `METRICS.json`, `equation.json`, `expanded_polynomial.json`, `projected.json`, `translation_certificate.json`
- `138-semantic-signs/natural235/`: `LICENSE`, `MANIFEST_SHA256.json`, `NOTICE.md`, `README.md`, `REPLAY.json`, `REPLAY_OPTIMIZED.json`, `SOURCE_LEDGER.json`, `build.py`, `evaluate.py`, `verify.py`
- `138-semantic-signs/natural235/code/`: `build_linear_cofinal.py`, `build_single_row.py`, `build_staged_rows.py`
- `138-semantic-signs/natural235/equations/natural235/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `variables.tsv`
- `138-semantic-signs/natural235/equations/natural235/raw/`: `equation.json`, `transformation.json`
- `138-semantic-signs/natural235/equations/natural236_sparse/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `expanded_polynomial.json`, `residuals.txt`, `variables.tsv`
- `138-semantic-signs/natural235/equations/natural236_sparse/raw/`: `equation.json`, `transformation.json`
- `138-semantic-signs/natural235/inherited/`: `NOTICE_100.md`, `NOTICE_128.md`, `NOTICE_133.md`
- `138-semantic-signs/natural235/proofs/`: `COMPACT_PEER_REVIEW.md`, `PROOF.md`
- `138-semantic-signs/positive10/`: `CUTS.json`, `INDEPENDENT_MATH_REVIEW.md`, `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `SOURCE_LEDGER.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, `build.py`, `equation_80_750.json`, `equation_81_560.json`, `equation_83_436.json`, `verify.py`
- `138-semantic-signs/positive10/coefficients/`: `BINDING.json`
- `138-semantic-signs/positive10/inherited/`: `indexed_native_certificate.json`, `indexed_tiles.json`, `package61_LICENSE`, `package61_NOTICE.md`, `prior_LICENSE`, `qcube_normalization_proof.md`
- `138-semantic-signs/report/`: `compact_constants.tex`, `compact_section.tex`, `generate_tables.py`, `integer_residuals.tex`, `natural_section.tex`, `report.pdf`, `report.tex`, `signed_section.tex`, `verification_section.tex`
- `139-graph-digits/`: `LICENSE`, `MANIFEST.sha256`, `NOTICE.md`, `PROVENANCE.json`, `README.md`, `RESULTS.json`, `build_report.sh`, `generate_report_inputs.py`, `report.pdf`, `report.tex`, `verify_all.py`
- `139-graph-digits/compact/`: `LICENSE`, `NOTICE.md`, `PROOF.md`, `README.md`, `VERIFICATION.json`, `build.py`, `construct_coefficients.py`, `equation_87_degree323.json`, `equation_88_degree318.json`, `verify.py`
- `139-graph-digits/compact/coefficients/`: `K.bin.gz`
- `139-graph-digits/compact/provenance/`: `SOURCE_PINS.json`
- `139-graph-digits/compact/review/`: `INDEPENDENT_CENTER_REVIEW.md`, `independent_lower_center.json`, `independent_lower_center.py`, `independent_upper_center.json`
- `139-graph-digits/compact/upstream133/`: `LICENSE`
- `139-graph-digits/direct/`: `LICENSE`, `MANIFEST.json`, `NOTICE.md`, `PROOF.md`, `README.md`, `RESULTS.json`, `UPSTREAM_PINS.json`, `evaluate.py`, `verify.py`
- `139-graph-digits/direct/code/`: `build.py`, `render_equations.py`
- `139-graph-digits/direct/equations/`: `integer678.json`
- `139-graph-digits/direct/equations/natural226/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `equation.txt`, `expanded_polynomial.json`, `residuals.tex`, `variables.tsv`
- `139-graph-digits/direct/equations/natural227/`: `VERIFICATION.json`, `elimination_certificate.json`, `equation.json`, `equation.txt`, `expanded_polynomial.json`, `residuals.tex`, `variables.tsv`
- `139-graph-digits/direct/equations/source/`: `equation.json`, `expanded_polynomial.json`, `transform.json`
- `139-graph-digits/direct/reviews/`: `HISTORICAL_RAW_ROW_REVIEW.json`, `INDEPENDENT_MATHEMATICAL_REVIEW.md`, `RAW_ROW_REVIEW.json`, `independent_raw_rows.py`
- `139-graph-digits/direct/upstream/100-quartics407-888/`: `LICENSE`
- `139-graph-digits/direct/upstream/129-semantic-pell-anchor/`: `LICENSE`
- `139-graph-digits/direct/verification/`: `normal.json`, `optimized.json`
- `139-graph-digits/graph/`: `INDEPENDENT_REVIEW.md`, `LICENSE`, `README.md`, `SECOND_MATH_REVIEW.md`, `SOURCE_PINS.json`, `build.py`, `evaluate.py`, `independent_verify.py`, `paired_graph.py`, `profiles.json`, `quartic_equalities.py`, `quotient_aliases.py`, `verify.py`
- `139-graph-digits/graph/equations/matched1137/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `139-graph-digits/graph/equations/unit1050/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `139-graph-digits/graph/equations/unit951/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `139-graph-digits/graph/equations/unit984/`: `certificate.json`, `metrics.json`, `polynomial.json`, `polynomial.txt`
- `139-graph-digits/graph/verification/`: `NORMAL.json`, `OPTIMIZED.json`
- `139-graph-digits/report_inputs/`: `compact_registers.tex`, `constant_recipe.py`, `natural226_residuals.tex`
- `139-graph-digits/verification/`: `FINAL_MATHEMATICAL_REVIEW.md`, `PDF_REVIEW.json`, `normal.json`, `optimized.json`
