# A strict output bound completes the 589-variable quartic

This is an additional exact reduction of the 69-predicate system proved in
`PROOF_PAIR_GUARDS.md`. It gives a complete polynomial in **589 unrestricted
integer variables**, exact degree four, with **8,156 monomials** and height
**2,445,790,974,704**. It is supplied both as 371 quadratic residuals and as
all collected quartic coefficients in `fused68/support8/`.

## 1. Two existing guards are one lower bound

The original raw coordinates have the following literal relations:

    v_7=v_6^2, v_8=v_7^2, ..., v_28=v_27^2,
    v_29=v_3+1, v_28=v_29.

There are exactly 22 square transitions, at original body rows 2 through
23. Rows 24 and 25 give v_28=v_3+1. Neither this statement nor its proof
interprets v_6 as a power, or v_3 as a computation carrier.

On these integer row equations,

    (v_3>=0 and v_6>=0)  <->  v_6>=1.

If v_6>=1, induction through the 22 squares gives v_28>=1, hence
v_3=v_28-1>=0. Conversely v_6>=0 is an integer, and v_6=0 would make
every displayed square zero and therefore v_3=-1, contradicting v_3>=0.
Thus the two old scalar guards are exactly equivalent to the one affine
predicate v_6-1>=0. This covers the boundary v_6=1, v_3=0.

The replacement guard is the quadratic row

    v_6-1-a^2-b^2-c(c+1)=0,

using three new unrestricted integer coordinates. The same three-square
lemma used by every old guard supplies witnesses for all v_6>=1.
Keep the other 67 predicates and every original body row. There are now
68 predicates in total.

## 2. Both directions, before inherited semantics

A new 68-predicate zero implies v_6>=1 and therefore both omitted scalar
signs. Supply fresh triples for v_3 and v_6 to obtain the full
69-predicate parent at the same body tuple. Its six shared-remainder
arguments then restore all 75 predicates of the accepted ordinary source.
Only after these restorations is the inherited C222 interpretation used.

An old 69-predicate zero implies v_6>=1 by the same exact row chain.
Forget its two scalar triples, choose a triple for v_6-1, and retain every
other body and guard value. This gives a new zero. Thus, once again, the
two systems have exactly the same body-coordinate projections.

Combining with the proof in `PROOF_PAIR_GUARDS.md` and the named ordinary
source/refutation calibration gives the same ZFC-formalizable equivalence
between absence of integer zeros and Con(ZFC). No new encoded internal-ZFC
or Lean certificate is asserted.

## 3. Literal equations and measured comparisons

The new unprojected system has 1,259+204=1,463 integer coordinates and
1,177+68=1,245 quadratic rows. The principal exact monic projection
removes 874 coordinates and rows, leaving 589 coordinates and 371 rows.
Every deleted coordinate has a unique integral restoration. Every guard
undergoes the same complete substitutions as every source row.

| Equation | Integer variables | Quadratic rows | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|
| Matched parent75 support8 | 604 | 372 | 4 | 9676 | 2445790974704 |
| Six pair guards, parent69 support8 | 592 | 372 | 4 | 8167 | 2445790974704 |
| Pair guards + strict output, source68 support8 | **589** | **371** | **4** | **8156** | **2445790974704** |
| Source68 quadratic-first support32 | 595 | 377 | 4 | 7595 | 6956012 |
| Source68 support16/affine2 | 600 | 382 | 4 | 7075 | 964213 |

Compared with the matched 604-variable source, the principal result saves
15 variables and 1,520 monomials without changing degree or coefficient
height. The 600-variable point keeps every coefficient below one million.
The listed profiles do not establish a global minimum.

The full equation is

    P_589(z_0,...,z_588)=sum_{j=0}^{370} E_j(z)^2=0,
    (z_0,...,z_588) in Z^589.

The `equation.json` file supplies every E_j, and `polynomial.json` supplies
every coefficient of P_589. These are actual finite integer polynomials,
not templates with undetermined coefficient ports. The proof does not
use numerical searches for zeros.

## 4. Reproduction

The previous six-pair profiles are built by `build_pair_guards.py` and
`extra_profiles.py`. Then run

    python3 -B build_fused68.py
    python3 -B check_fused68.py

The latter imports neither producer nor optimizer. It independently
rechecks all shared-remainder row identities, every predicate cut, all
22 literal square rows and the exact carrier identity. It then replays
every signed monic inverse for each of the three new profiles and
reconstructs their complete quartic coefficients. `CHECK_FUSED68.json`
records the finite algebraic verification. The preceding integer proof
establishes the unbounded witness equivalences.

The inherited endpoint theorem is the composition of
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The direct arithmetic
compilation is reviewed at
`Computability/DiophantineConsistency/PROPOSAL_REVIEW_QUARTICS407888.md`.
The main explicit proof chain and its boundary are recorded in
`CALIBRATION_DEPENDENCIES.md`.
