# Independent review of the signed Pell-cap integer quartics

## Verdict and scope

**Accept the new ordinary signed-cap and sequential-power transformation, relative to the retained natural C222 source and its explicitly inherited refutation calibration.** I found no circular use of a power output's intended value or sign in the new source-order argument, and no unresolved mathematical obstruction in the changed rows. This review does not claim a new end-to-end proof-assistant derivation, an object-language ZFC proof term, a global minimum, or independent re-verification of the entire inherited metamathematical development.

The reviewed files are the `direct_capped_modular` construction, especially `SIGNED_CAP_PROOF.md`, its natural companion `PROOF.md`, `inherited/MODULAR_PROOF.md`, and the actual raw metadata, sign certificates and coefficient artifacts. `DIRECT_SIGNED_CAP_SOURCE_IDENTITIES.json` records the reviewed snapshots. One editorial correction was requested: the 61 exempt coordinates are excluded from the set whose signs must be established by elementary closure, rather than absent from all closure steps. Four power-output signs are in fact derived from digit-remainder rows. This does not introduce an assumption or invalidate the proof; those derivations are exact polynomial consequences and are not required to interpret the six powers sequentially.

## Mathematical audit

### Signed index recovery

For each principal norm solution, signed Pell classification gives independent signs and an index `j>=0`. The aggregate equation with a nonnegative slack gives `y_i^2<Y_W(A)`, and hence `|y_i|<Y_W(A)`. This remains valid for `y_i=0`. Monotonicity implies `j_i<W` without assuming a sign for either principal coordinate.

Modulo `A-1`, the two squared errors have residues

    (delta_i*j_i-k_i)^2 + (epsilon_i-1)^2.

Their nonnegative sum is at most `m[4(W-1)^2+4]`, strictly less than `4W^3<A-1` for the stated `W>=4` and `m<=W-2`. Divisibility therefore forces every error to vanish. Because every requested index is positive, this recovers the index, positive ordinate and positive abscissa. In particular, the abscissa error is necessary: an ordinate-only error would not distinguish negative abscissas. No sign of the pooled quotient is used.

For completeness, the square frame supplies `2k_i<=W-1`. The addition identity `Y_(2k)=2X_kY_k>Y_k^2`, together with the growth recurrence and `A>W+1`, supplies the aggregate slack. The error quotient is integral since each individual difference is divisible by `A-1`. All witnesses can be constructed after choosing the common parameter `A`.

### Actual source ordering

I inspected the literal 23 frame atoms, the fifteen distinct seed-exponent ports, the explicit single-cap witnesses, and the exact six-power metadata. The fifteen indices are positive from guarded source witnesses and positive arithmetic gates, before any power interpretation. The literal `t=t0+16` gives the stronger lower bound `W>=258`. The squared frame bounds the absolute value of every semantic atom even while outputs and quotients are allowed to be signed.

The lower-scale norm has natural `L`, nonnegative slack and `Z>=1`, independently supplied by the finite sign certificate. Pell classification at base `W+1`, followed by the congruence `Y_e(W+1)=e (mod W)`, proves `e>=W` and `A>=(W+1)^W`. Thus the inequality `A-1>4W^3` is obtained before interpreting any principal pair. Every witness used by the one inherited indexed-cap criterion is natural at this stage, and its missing index margin follows from the aggregate row. The cap does not depend on unproved principal signs.

After the principal pairs are interpreted, the exact power row implies

    T_n divides m-n^k,   T_n=2An-n^2-1.

For positive `n<W`, `T_n>=2A-2>W^W+W`. The square frame gives `|m|<W`, while `0<n^k<W^W`, so the only possible multiple is zero. This proof uses an absolute-value bound for the initially signed output; it does not presume that output is already a nonnegative residue.

The metadata has exactly the required dependency order:

1. `V0=(F^2+1)^t`, whose base is positive directly;
2. `N=B^K`, where `B=b0+2>=2` is a literal shift;
3. `q=N^K`, using the already recovered positive `N`;
4. the three powers of `q`, using the already recovered positive `q`.

All exponents have been established positive before step 1. The sign certificate's incidental proof of four output signs from digit rows is harmless and not a replacement for this order.

### Remaining quotients and inherited arithmetic

The common-root and modular-digit equations are used as integer congruences, so their quotients need no sign premise. After powers and principal pairs are interpreted, the relevant moduli are positive and the selected remainders are least nonnegative residues. The canonical Pell expression is positive, giving the usual nonnegative quotient when needed for comparison with the inherited natural construction. The CRT index quotient and local-evaluation quotient likewise need no sign premise for divisibility; their natural signs follow afterward from the decoded positive divisor and nonnegative dividend.

The original independent radix bound precedes the interpretation of the factorial binomial. Then the square-radius factorial fixed point, reciprocal prime-power CRT, range-digit bounds and Horn-flow argument apply in the inherited order. The unchanged prefix and retained source proof are essential to this conclusion. The review accepts that explicitly identified source calibration; the finite coefficient checks alone do not establish it.

Completeness fixes all semantic refutation, factorial, beta, CRT and power data first, computes the enlarged square frame, and only then selects a sufficiently large member of the soluble common-root residue class. This avoids fixing incompatible old Pell witnesses. The canonical pairs and signed-cap slacks can all be supplied at that new parameter. The 52 private nonnegativity graphs represent every required natural coordinate by Legendre's three-square theorem.

## Exact finite replay

I ran fresh checker processes in both ordinary and optimized Python for both frozen integer endpoints. All four executions passed. The checker imports neither the source constructor nor the sign-inference producer or coordinate optimizer. I inspected its finite sign rules: every derivation is reproduced from an actual residual, its target does not occur on its right side, every odd-factor sign dependency is already established, and an affine-square derivation is verified by exact expansion.

| Endpoint | Integer variables | Quadratic rows | Exact degree | Collected monomials | Coefficient height | Integral restorations |
|---|---:|---:|---:|---:|---:|---:|
| `integer381` | 381 | 225 | 4 | 13,179 | 2,445,790,974,704 | 124 |
| `integer391` | 391 | 235 | 4 | 10,764 | 80,496,640 | 114 |

Both runs verify 52 explicit guard graphs, 174 exact elementary sign consequences, 15 positive indices before powers, the ordered positive-base schedule, all three changed source rows, and every coefficient of the collected quartic. Each run also rejects corruptions of the square frame, a guard, a sign proof, an integral restoration, and the final coefficient map. No unconstrained coordinate is deleted.

I additionally replayed the natural construction's independent verifier. It confirms the unchanged 468-row prefix on 491 original coordinates, all 60 semantic suffix identities, all 428 affine restorations from the 777-coordinate graph to the 349-coordinate raw graph, and both natural endpoint polynomials. Although those affine restorations were originally selected for nonnegative values, their exact monic polynomial identities remain valid over the integers; the signed construction supplies the particular source signs it actually needs separately.

Receipts are:

- `DIRECT_SIGNED_CAP_381_NORMAL.json`
- `DIRECT_SIGNED_CAP_381_OPTIMIZED.json`
- `DIRECT_SIGNED_CAP_391_NORMAL.json`
- `DIRECT_SIGNED_CAP_391_OPTIMIZED.json`
- `DIRECT_SOURCE_NORMAL.json`
- `DIRECT_SIGNED_CAP_SOURCE_IDENTITIES.json`

The 381-variable form uses fewer variables and rows than the inspected 442-variable direct predecessor, at a cost in support and coefficient height. The 391-variable companion makes a different height/support tradeoff. Neither is described as a universal minimum or as dominating the predecessor in every measure.
