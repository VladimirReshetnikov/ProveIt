# Independent review and its resolution

An independent adversarial reviewer (a separate agent, read-only, given the
package files, the parents and the research proofs but not the author's
conclusions) reviewed the first version of this package on 24 October 2026.
It found the mathematics sound and nothing fatal. Its findings and their
resolution are below, followed by the review as written, with its headings
one level lower and its local scratch path removed.

| Finding | Rating | Resolution |
|---|---|---|
| The research session's code-free proposal `research/ten-positive-qcube-doubled` (`a576e152f4`, 22:07) has the same polynomials, schedules and leading forms; the "New here" claim did not hold | GAP | README "Priority" and PROOF section 0 credit it as first committed; this package is described as the materialized circuits and checks |
| Degree upper bound not computed in the package | MINOR | `verify.py` now checks that the syntactic degree bound of N equals 750 and 560 |
| PROOF section 3 omitted the equal-degree linear sums and the explicit leading coefficient | MINOR | Added the four linear forms and both leading monomials, with coefficients 2¹⁴β⁵⁰⁶ and −2¹⁰β³⁸⁴ as the reviewer computed |
| Transfer identity checked at 4 points modulo one prime; no mutation rejection | MINOR | Now 16 points over two primes, 30 exact-integer points with small ports (18 with n′ − s ≤ 0), and two mutations rejected |
| Equation JSONs carry no hashes | MINOR | `CHECKS.json` records the SHA-256 of each emitted equation; the coefficients stay bound by `coefficients/BINDING.json` and the port box |
| `INDEPENDENT_REVIEW.md` listed but missing | EDITORIAL | This file |
| Row accounting omitted the deletion of P1 | EDITORIAL | Now 84 + 1 − 1 − 8 + 5 = 81 in README and PROOF |
| Lower-degree frontier points listed incompletely | EDITORIAL | README lists 89 / 288 to 97 / 254, 102 / 253, 104 / 252 and 121 / 246 |
| Register `P1mu2` holds hμ² | EDITORIAL | Renamed `hmu2` in `build.py` and both circuits |
| "Fewest operations" sentence ignored the 22:07 proposal | EDITORIAL | Replaced by the Priority section |

## The review, as written: Adversarial review: candidates/ten-positive-qcube-product-square

Reviewer: independent, read-only (no edits or commits in the repository, no Lean/Lake).
Date: 2026-10-24, about 22:00 to 22:20 PDT.

### Verdict

**The mathematics is sound. Two things are missing: credit for prior work, and package-level verification.**

The transfer identity, the positive-domain soundness without assuming n' - s > 0,
the completeness with the repaired R > 3q canonical family, the operation counts
and the exact degrees 750 and 560 all check out. My checks used exact integer
arithmetic, a gate-wise top-form certificate and closed-form leading forms. I found
no FATAL issue.

There is one GAP. The candidate's "New here" claim is not supported.
`research/ten-positive-qcube-doubled/PROPOSAL.md` (commit a576e152f4, 22:07:06)
proposes the same polynomials, with the same 81/750 and 82/560 schedules and the
same proof structure. It already has an approved ordinary peer review.
`reviews/ten-positive-qcube-doubled-ordinary-peer.md` says: "APPROVED ... This
does not accept an 81/750 or 82/560 finite endpoint". Neither package cites the
other. The candidate's files were created at 22:01-22:05, so the two efforts are
concurrent. The candidate's real contribution is the **materialized** circuits plus
build/verify. That is exactly the "separate finite packet" the research review says
is still missing.

Files reviewed (current bytes). README.md and PROOF.md were edited by their author
during this review, at 22:04:58 and 22:05:05. I re-read and reviewed the final
versions.

| File | SHA-256 |
|---|---|
| README.md | 0051239a7e20cad1de4125a910355dae8aad99e59a9fbdfa4df5532255e137b1 |
| PROOF.md | db8d0366678f23003bd927380882e15a9eb33d6b4257c4f435591cd460dd4c9e |
| build.py | c90f211b5780f708158ffce31a8bb82d12b5189bd04541ecf458a25e8e5d083c |
| verify.py | c544a5a7712859815023eb85ffab69507432f403e702cd770c18eef01d6e0a5e |
| equations/qcube_product_square_81.json | 8a2a371b97fb5fc1898f811a20280b6d41808b68a6a844c28af94f74cf956dd7 |
| equations/qcube_product_square_82.json | 2b8e9f38a05583a0750e0f894b7cbb728416714271ad430d777d4cecb97d6c81 |
| coefficients/BINDING.json | 5689a32ec5ea92c99bcf1f09a3363ccc32e70f7a764590cd66f0f7a07d768998 |

### Findings

#### GAP 1: novelty and priority (README "How they are made"; PROOF section 0, "New here")

- **Problem.** The PROOF says: "New here: applying q-cube normalization to the
  product-square kernel, the transfer ... and the exact degrees". All three are
  already in the repository:
  - `research/ten-positive-qcube-doubled/PROPOSAL.md`, sections 2, 4-6 and 8,
    covers them.
  - It also gives the leading forms 2^14 i^20 q0^506 w^46 s^108 k0^64 T0^4 C0^2
    and -2^10 i^14 q0^384 w^34 s^80 k0^46 T0^2.
  - Its section 7 has a manual schedule that is gate-for-gate the candidate's
    build.py edit: delete P1, qm1Y, q3Bt, inner; replace P1mu2 by bJ*mu2,
    mu2inner by mu2*Bt and P1e by bJ*e; turn brk into a sum and Znum into a
    difference.
  - The proposal has root and peer reviews and appears in SIZE_REDUCTION.md
    ("Next cost tradeoff: q-cube normalization after doubling").
- **Evidence.** Its formula (1) is the candidate's Z', M', RG' and N, symbol for
  symbol. I checked that the candidate's polynomial is the unique match: I
  evaluated it against all 197 ten-input straight-line circuits in
  `Computability/DiophantineConsistency`, by name, up to sign, and under the
  (Y = q^3 s, n = n' - s, divide by q^6) transfer. The only matches are the
  intended transfers to 133's equation_84/85 and their byte-identical copies in
  `research/ten-positive-doubled-product-square`. No ten-input circuit of total
  degree 750 or 560 exists elsewhere, and total degree does not change under
  coordinate translation. So the candidate is the first *materialized* form of the
  proposal, not a new combination.
- **Fix.** Credit and pin `research/ten-positive-qcube-doubled` (MANIFEST
  8051545c..., PROPOSAL 93c14910...) and its two reviews. Restate "New here" as
  "the materialized circuits, build and finite checks for the proposal". The
  research review lists what the finite packet must do: "bind every actual row,
  all ten free inputs and all four ports, and reject meaningful mutations". The
  candidate does the first three. It does not reject mutations (MINOR 3).

#### MINOR 1: the degree upper bound is not machine-checked (verify.py check 3; PROOF section 3)

- verify.py measures degree on random lines modulo two Mersenne primes, using
  802 points. A nonzero t^750 coefficient proves degree >= 750. The vanishing
  finite differences above 750 are only probabilistic evidence for <= 750.
- PROOF section 3 says the register degrees are "measured, and matching the
  syntactic bounds", but nothing in the package computes the syntactic bounds.
- I closed this independently (rev.py):
  - Gate-wise syntactic degree propagation gives exactly 750 and 560.
  - Propagating the homogeneous top component gives a nonzero value at the
    syntactic degree. The check ran modulo 2^61-1, 2^127-1, 10^18+3 and
    2^64-59, with the actual 590,069-bit ports.
  - That is a rigorous exact-degree certificate: the syntactic bound plus a
    nonzero top form.
  - The only equal-degree +/- gates are four nonzero linear forms: qmF, C, k and
    Tp, i.e. beta J - F, beta J - F - alpha, eta + zeta and T + alpha.
- Suggest adding the syntactic bound and the top-form propagation to verify.py.

#### MINOR 2: the PROOF section 3 domination argument is incomplete in wording

- "sums dominated by one summand" leaves out the four equal-degree linear sums
  above. Their leading forms are nonzero, but they are not dominated by one
  summand.
- No explicit leading monomial or coefficient is given. 133 and the research
  proposal both give one.
- Correct values, verified at random points mod 2^127-1 against the propagated
  top form (lead.py):
  - **81:** 2^14 i^20 w^46 s^108 q0^506 k0^64 (T+alpha)^4 (q0-F-alpha)^2. The
    coefficient 2^14 beta^506 sits at J^506 w^46 s^108 i^20 eta^64 T^4 F^2.
  - **82:** -2^10 i^14 w^34 s^80 q0^384 k0^46 (T+alpha)^2. The coefficient is
    -2^10 beta^384.
- In 82 the leading form no longer contains F: b0 = k0 q0^3 s (T+alpha) replaces
  133's b0 = -q0^3(q0-F).

#### MINOR 3: verify.py coverage is thin

- **Transfer identity.** Only 4 points, all modulo 2^127-1, with the actual
  ports only.
- **Binding.** BINDING.json is checked against itself. It is not compared with
  the parent equation JSON's coefficient_binding, and the equation JSONs carry
  no coefficient hashes; the parents' JSONs did.
- **Mutations.** No mutation rejection; 133's verifier rejected five gate
  mutations per equation.
- **Topology.** No explicit check that every reference is defined before use;
  an undefined name would raise a KeyError rather than give a clean FAIL. No
  check that all four ports are live.
- I checked all of these by hand or with scripts, and all pass:
  - BINDING hashes equal 133's equation_84.json coefficient_binding (gzip and
    raw, all four ports).
  - K.bin.gz is byte-identical to 133's compact/coefficients/K.bin.gz.
  - All four .gz files are byte-identical to the accepted
    research/ten-positive-doubled-product-square/coefficients.
  - The raw hashes match the table in the 133 review.
  - Topology is strict, there are no dead gates, and all ten inputs and four
    ports are live.

#### EDITORIAL

1. README "Files and checks" lists `INDEPENDENT_REVIEW.md: the adversarial
   review and its resolution`. That file does not exist.
2. PROOF section 1, last paragraph, and README: the row accounting does not add
   up as written.
   - "one added row ... and the replacement of the eight low-bracket rows by
     five" gives 84 + 1 - 8 + 5 = 82, not 81.
   - The ninth deletion, P1 = q3*bJ, which becomes dead, is not counted.
   - README's "eight rows to five for one new row: three operations fewer" has
     the same omission.
   - The actual edit, recounted: 9 rows deleted (P1, qm1Y, q3Bt, inner,
     mu2inner, P1e, brk, Zpart2, Znum) and 6 added (Y, mu2Bt, bJe, lowsum,
     Zpart2, Znum). That gives 84 → 81 and 85 → 82, with breakdowns 48/19/14
     and 49/19/14.
3. README: "the lower-degree points 84/436, 85/328 and 89/288 remain" is an
   incomplete list of the Pareto frontier. Lower-degree ten-positive points
   include 91/283, 92/278, 94/262, 96/258, 97/254, 102/253 and 104/252. These
   are on different tuples or charts, so "remain" should not read as "only
   these".
4. The register name `P1mu2` now holds h*mu^2, not P1*mu^2. A rename or a
   comment would avoid confusion. The name `G` is the mask factor
   [h(q-F)+alpha], while 133's G = E*F0 is `Dg`. This is inherited, but worth a
   note given PROOF's use of G.
5. README's "fewest operations ... were 84" is still true for *accepted* points.
   It should add that an unmaterialized 81/82 proposal was committed 22:07
   (GAP 1).

### Detailed attack results

#### 1. Transfer identity (T) and homogeneity

**Algebra.** With P = q^3 h, Y = q^3 s and n = n' - s:

    Z133 = q^3 h mu^2 [H(n' - s - LB) + Kpos] + H[mu^2(h q^3 s - q^3 B) - q^3 h e]
         = q^3 { h mu^2[H(n' - LB) + Kpos] - h mu^2 H s + h mu^2 H s - H[mu^2 B + h e] }
         = q^3 Z'

M133 = q^3 h mu^2 H = q^3 M'. H, L, B, Kpos and e do not depend on n, and they
are evaluated at the same Y. N133 = Q Z^2 - Q M^2 G V^2 + M^2 G - Z^2: every term
contains Z^2 or M^2, so it is homogeneous of degree 2 in (Z, M). Hence
q^6 N = N133 identically.

**Exact checks on the actual circuits (rev.py):**
- 60 exact-integer trials with small box-satisfying ports (beta in
  {31, ..., 63}, random K0, MC, MF) and random positive inputs. 33 of them had
  n' - s <= 0.
- Each trial checked q^6 N_new = N_133, Znum_133 = q^3 Znum_new and
  Mtot_133 = q^3 Mtot_new, all exactly, with 0 failures.
- The centre identity (C) also held exactly as a Fraction equality,
  Z'/M' = n' - LB + Kpos/H - B/h - e/mu^2, with 0 failures.
- 20 further trials modulo random 160-bit primes, half with the actual ports and
  half with random ports. That is a Schwartz-Zippel test over all 14 variables:
  0 failures.

#### 2. Soundness when n = n' - s may be <= 0

I went through 133's sections 2-7 and the inherited saturated and uncentered parent
proofs (compact/provenance/) for every use of n:

- **Sections 2-4** (positivity, coprimality via Q ≡ 0 mod G, valuation argument,
  adjacent-Pell descent, folding c = psi_A(p), first-index exclusion, mask
  bound, b > c, V > 0, kappa > 0) never use n. Y = q^3 s >= q^3 only
  strengthens Y >= 1.
- **Equation (8)** is a rational identity for every integer n.
- **Section 5 (weight V^2).** The only use of n's sign is the final step:
  "n = eps g y - kappa - s + Wt + rho < V^2/2 - V^2 + V/mu^2 < 0, contrary to
  n > 0". The upper bound discards -kappa - s, using only kappa > 0 and s > 0.
  With n' = eps g y - kappa + Wt + rho, the same chain needs only kappa >= 0:
  - g y < V^2/2 (from V > 3g and y < 3V/2);
  - Wt <= -L - 1/h when B <= -1 (W > 0 since L = V^2 > 0);
  - rho < b/mu^2 < V/mu^2;
  - so n' < 0, contradicting n' >= 1.
  No lower bound on n, s or kappa is used anywhere.
- **Section 6 (weight bV).** The same applies with W = 1 + h b V > 0 (b, V > 0
  from section 4), g y < L/2 (from V > 8Q^2 and b > 4g), and
  n' < L/2 - L + b/mu^2 = b(1/mu^2 - V/2) < 0.
- **Section 7 and the parents' section 4 chain.** This covers rank p = R, q even,
  mu^2 | e, n0 = (R+1)/2, H | P Kpos, the whole-product projection, q^3 | Y,
  h | B, and source reconstruction. It uses n only as an integer addend of the
  integral centre. "n0" there is the first Pell index, not the unknown.
  - Under (C): mu^2 | h H e, then H | h Kpos, which implies the weaker parent
    premise H | q^3 h Kpos.
  - The remaining fraction -B/h gives h | B, and q^3 | Y holds literally.
  - The research packet's peer review proves the same thing. I found no use of
    n > 0 or n >= 1 after the transport step.

PROOF section 2 states this correctly, if briefly.

#### 3. Completeness

The research session's accepted repair
(research/ten-positive-doubled-product-square/PROOF.md, section 8 and (11);
R > 3q >= 96, hence R >= 7, V* >= 9Q^2 and T* > 9S > alpha) supplies the canonical
tuple of 133:
- q^3 | Y, so s = Y/q^3 is a positive integer;
- t >= 0, rho >= 0 and kappa > 0 are integers;
- g = tau f0 > kappa + s.

Then n' = g y + W t + rho - kappa = n133 + s >= 1, and N = N133/q^6 = 0. The
q^3 cancellation does not touch the witness construction: the new witness tuple is
the canonical old one under Y = q^3 s and n = n' - s, and q > 0.

An earlier draft of the PROOF said rho >= 1. That is true here (e > 0 because
k > 8q^5 > R + 1, and mu^2 | e), but it was not argued. The current version says
rho >= 0, which is fine.

#### 4. Exact degrees

These are syntactic degrees, with exactness certified by a nonzero top form:

| | c | Y | cT | R | b | Q | V | M' | RG' | LB | Z' | N |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 81 | 5 | 4 | 6 | 4 | 6 | 152 | 142 | 13 | 124 | 286 | 299 | 750 |
| 82 | 5 | 4 | 6 | 4 | 6 | 152 | 142 | 13 | 124 | 150 | 163 | 560 |

- **Final summands, 81:** QZ'^2 = 750, QRG'V^2 = 560, RG' = 124, Z'^2 = 598.
- **Final summands, 82:** 478, 560, 124, 326.

These match the PROOF table. The dominant terms are as follows:
- b = c(T+alpha) - R: 6 against 4.
- Z': the term -h mu^2 H L B (299 or 163) dominates. The low bracket
  H(mu^2 B + h e) has degree 14, n' has 1 and Kpos has 7.
- inside = Z'^2 - RG V^2: 598 against 408 for 81, and 326 against 408 for 82.

The leading forms are given in MINOR 2. Both are nonzero, so the degrees are
exactly 750 and 560. The parents re-measured at 436 and 328.

#### 5. build.py

- `py -I -B build.py --check` gives "ok" for both files, and the parent SHA-256
  pins match.
- My own row diff against 133's equation_84/85:
  - removed: P1, qm1Y, q3Bt, inner, mu2inner, P1e, brk;
  - added: Y = q3*s, mu2Bt, bJe, lowsum;
  - changed: P1mu2 (P1 → bJ), Zpart2 (brk → lowsum), Znum (+ → -).
- The counts are 81 = 48/19/14 and 82 = 49/19/14.
- Strict topology holds, there are no dead gates, all 10 inputs and 4 ports are
  live, and N is the last row.
- There is no gate on constants only.
- The reordering moves q2/q3/R/mask rows before Y, which is valid.
- `py -I -B verify.py --output <scratch>` passed all 21 checks. The package's own
  CHECKS.json was not touched.

#### 6. Novelty

These were evaluated with the actual ports, at random points modulo 2^127-1, under
three tests: identity, sign flip, and the q-cube transfer. The set was all 197
ten-input circuits in Computability/DiophantineConsistency, including:
- 130-shared-index positive/quotient*.json (86/466, 87/466, 89/450, 90/450) and
  the inherited gap_fusion controls;
- 131 single_square 87/436 and single_square_lean 88/380, plus direct 92/384
  and 93/334;
- 132 positive first (102/253) and second (104/252);
- 133 compact 84/85 and parent 89;
- research/ten-positive-qcube-normalization zero86 and parents;
- one-page-qcube86;
- research/ten-positive-doubled-product-square (accepted at a223b3e174);
- every other candidates/ and research/ ten-input JSON.

Results:
- **Identity and sign flip:** no match.
- **Transfer:** matches exactly 133's equation_84/85 and their byte-identical
  research copies, as intended.
- **Degree:** no other circuit has degree 750 or 560, so no coordinate shift of an
  existing circuit equals either candidate.
- **Text search:** turned up no other prior 81/750 or 82/560.
- **The one exception** is the code-free proposal in GAP 1, which has no
  circuit file. Its formulas define the same polynomial.

### Coverage

- **Read in full:**
  - the candidate's README, PROOF (both versions), build.py, verify.py, both
    equation JSONs and BINDING.json;
  - 133 compact PROOF.md and both parent circuits;
  - compact/provenance uncentered_parent_proof.md and saturated_parent_proof.md;
  - research/ten-positive-qcube-normalization PROOF.md and README;
  - reviews/staged-certificates-compact-ordinary-peer.md;
  - reviews/ten-positive-qcube-doubled-ordinary-peer.md;
  - research/ten-positive-qcube-doubled PROPOSAL.md: sections 1-3 and 7-9 read,
    section headings and MANIFEST checked.
- **Partly read:** research/ten-positive-doubled-product-square/PROOF.md (R > 3q
  repair lines, section 8 and (11)).
- **Run:** build.py --check, verify.py --output (scratch), and my own rev.py,
  novelty.py and lead.py. All were kept in
  the reviewer's scratch directory.
- **Not done:**
  - exact-integer evaluation with the full 590k-bit ports; N is about 4·10^8
    bits, so I used modular checks with the actual ports and exact checks with
    small ports instead;
  - re-verification of the inherited native, source61 and calibration theorems,
    which are retained by scope;
  - mutation testing.
