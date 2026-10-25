# Ten positive unknowns in 89 operations: coprime fusion with the gap majorant (independent derivation)

Six complete equations N = 0 in ten strictly positive integers, each with an
ordinary proof (PROOF.md) that it has no solution if and only if the
inherited syntactic refutation calculus derives no contradiction from ZFC.
The fixed coefficients are the whole original compact44 tuple in
`coefficients/` (the tuple of wave-12 package 116).

| Equation | Coordinate | Centre | Operations | ×/+/− | Exact degree |
|---|---|---|---:|---|---:|
| `equations/gap_fusion_scaled.json` | X = w·q | none | **89** | 53/18/18 | 288 |
| `equations/gap_fusion_scaled_lower_centre.json` | X = w·q | (A−1)·D·E | 91 | 54/19/18 | 283 |
| `equations/gap_fusion_scaled_sharp_centre.json` | X = w·q | A·D·E | 92 | 54/20/18 | 278 |
| `equations/gap_fusion_direct.json` | X = q + x | none | 94 | 56/19/19 | 262 |
| `equations/gap_fusion_direct_lower_centre.json` | X = q + x | (A−1)·D·E | 96 | 57/20/19 | 258 |
| `equations/gap_fusion_direct_sharp_centre.json` | X = q + x | A·D·E | 97 | 57/21/19 | **254** |

All six are on the operations/degree Pareto frontier of ten-positive
equations. The 89-operation equation ties for the fewest operations: the
research session found the same polynomial independently and concurrently
(`research/ten-positive-uncentered-b-weight/zero89.json`, commit 90d8b714f9,
16:29). The three direct-coordinate circuits are each one row shorter than
the research session's evaluators of the same or the same-profile
polynomials.

## Priority, as established at intake

These six equations were built in this repository on 24 October 2026 between
16:00 and 16:45 (commit 18a04bee9e). Earlier work already contains them:

- wave-13 package **121** (`con-zfc-diophantine-forms/121-paired-guards-centered`,
  built 15:58, delivered at 16:35) has the **same polynomials** as
  `gap_fusion_scaled` (89/288), `gap_fusion_scaled_sharp_centre` (92/278),
  `gap_fusion_direct` (94/262) and `gap_fusion_direct_sharp_centre` (97/254),
  on the same original tuple and at the same operation counts;
- wave-13 package **119** has all six profiles on the BFS tuple, identical
  to the research session's polynomials;
- the research session's `zero89`, reused-b and direct-carrier packets have
  the same or same-profile polynomials (see below).

Only the two lower-centre circuits (91/283 and 96/258, centre (A−1)·D·E) are
polynomials not found elsewhere, and they match existing profiles exactly.
This packet therefore adds **no new frontier point**. It is kept as an
independent derivation with its own proof (PROOF.md) and checks, which
confirm those points. It is not a priority claim.

## How they are made

Each is a literal row edit of package 116's 96-row schedule
(`con-zfc-diophantine-forms/116-coprime-projection/positive/equation.json`,
pinned by SHA-256 in `build.py`), combining three published devices:

1. **Coprime fusion** (packages 116 and 113, found independently): the first
   and strong Pell radicands are multiplied into one radical sqrt(D·F_s),
   F_s = 1 + Δ·D·E², which is coprime to D. The norm becomes a quartic in two
   radicals.
2. **The transport weight W = 1 + g·b.** With a centre above tau·f this
   weight is package 117's (sharp centre, no gap lemma needed). Without a
   centre, b must dominate tau·f itself; that follows from package 118's
   auxiliary-index gap (section 6 there: the auxiliary Pell index is at least
   5, so V > 8Q²). PROOF.md section 3 checks that the gap argument survives
   the extra factor D in Q and F_s; the uncentred forms and the lower centre
   (A−1)·D·E need it, only the sharp centre does not. Either way the two rows
   computing 116's L = H·D·E + b disappear.
3. **Coordinate and centre.** The scaled zero-offset coordinate X = w·q saves
   five more rows of direct-carrier bookkeeping. An optional second centre
   (A−1)·D·E or A·D·E (package 113's "upper and sharp centres") costs two or
   three rows and cancels the top of the norm, lowering the degree.

The degree is set by the cross term of the quartic: with Z = M·(V + Γ) + Z0,

    N = 4·δ²·M⁴·V²·(Γ² − a) + (strictly lower terms),

and Γ² − a is −Δ·D²·E² − D, −(2A − 2)·D²·E² − D or D²·E² − D for the three
centres (PROOF.md section 6).

## Comparison

Ten-positive equations, operations / exact degree:

| Equation | Profile | Relation to this packet |
|---|---|---|
| research canonical page `candidates/one-page-index-weight10` | 98 / 360 | dominated by all six |
| package 118 | 96 / 360, 102 / 332 | dominated |
| package 116 | 96 / 266 | dominated by 94 / 262 |
| package 113 | 92 / 283, 93 / 278, 98 / 258, 99 / 254 | dominated by 91 / 283, 92 / 278, 96 / 258, 97 / 254 |
| package 117 | 93 / 278 (sharp centre, W = 1 + (q−1)b) | the same polynomial as `gap_fusion_scaled_sharp_centre`, here in 92 operations (expanded transport) |
| research `research/ten-positive-reused-b-weight` (fc77fcd31a, 16:14) | 91 / 283, 92 / 278, 97 / 258, 98 / 254 | see below |
| research `research/ten-positive-uncentered-b-weight` (90d8b714f9, 16:29) | 89 / 288, 95 / 262 | see below |

The research session reached the same b-weight on package 113's four centred
equations independently, minutes earlier. Evaluated with the same whole
ports:

- `gap_fusion_scaled_sharp_centre` is the same polynomial as its
  `saturated_sharp` (92 / 278), which is package 117's polynomial;
- `gap_fusion_direct_sharp_centre` is the same polynomial as its
  `direct_saturated_sharp`, here in 97 operations instead of 98 (116's
  direct schedule is one row leaner than 113's);
- `gap_fusion_scaled_lower_centre` (91 / 283) is a different polynomial with
  the same profile as its `saturated_upper` (centre (A−1)·D·E instead of
  (A+1)·D·E);
- `gap_fusion_direct_lower_centre` (96 / 258) is a different polynomial, one
  operation below its 97 / 258;
- `gap_fusion_scaled` (89 / 288) is the same polynomial as the research
  session's `zero89`, found concurrently with the same fifth-index argument;
- `gap_fusion_direct` (94 / 262) is the same polynomial as its `direct95`,
  here in 94 operations instead of 95.

The wave-12 intake dossier also found the uncentred profiles as counts and
degrees. Net new points of this packet: 94 / 262, 96 / 258 and 97 / 254 (one
operation below the research session's evaluators), and the lower-centre
polynomials 91 / 283 and 96 / 258.

## A measured remark, not part of the claim

Replacing the free unknown Y by Y = q³·s (s a new free unknown) in
`gap_fusion_scaled` turns the term Y/q³ of the centre into the integer s and
saves one more row: 88 operations at measured exact degree 478 (Y now has
degree 4 and enters A, D and E). Its proof would have to re-check every
inherited step that treats Y as a free coordinate; it is not written here,
so this point is recorded only as a measurement.

## Files and checks

- `PROOF.md`: the complete ordinary proof (sections 2–5) and the exact-degree
  proof (section 6).
- `build.py`: derives the six schedules from 116's pinned file;
  `py -I build.py --check` rebuilds and compares.
- `verify.py`: coefficient binding and port box; counts and liveness; exact
  degree along random lines modulo 2^127 − 1 and 2^89 − 1; the leading forms
  of section 6 against the top coefficient along rays; the expansion identity;
  Pell trace values. `py -I verify.py` writes `CHECKS.json`.
- `INDEPENDENT_REVIEW.md`: the adversarial review and its resolution.

Scope: the equivalence is relative to exactly the calibration of the
parents (the source61/native/controller theorem with the whole original
tuple). No Lean theorem, internal-ZFC certificate, consistency claim or
minimality claim is made.
