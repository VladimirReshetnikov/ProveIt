# Final one-gate reduction: a squared budget residual

This note proves the final two single-polynomial variants. The ordinary
variant has **16 strictly positive integer unknowns, 74 arithmetic gates
(41 multiplications and 33 additions/subtractions), and exact degree 101**.
The normalized variant has **16 strictly positive integer unknowns,
72 arithmetic gates (41 multiplications and 31 additions/subtractions),
and exact degree 157**. Their five fixed numeral ports, compiled machine,
and arithmetic input are unchanged.

These variants are equivalent to the seven-equation, 63-gate ordinary
system **at the level of existence of positive solutions**. They do not
have the same positive zero tuples as that system. The zero-budget
63-gate system remains the recommended transparent system and the source
of the nonnegative quadratic-gate lift.

## 1. Literal source change

Use every definition from `FIXED_INPUT73_PROOF.md` and, for the ordinary
strong variant, `FIXED_INPUT75_ORDINARY_PROOF.md`. In particular,

    C = Z + W0,
    r0 = q - F - Z - alpha - C,
    W0 = 2^u,                 u = 2d+b,
    q = (B-1)J+1,             B = 2^d.

All sixteen unknowns are strictly positive. The native compiler supplies
the admissible fixed numerals, with d >= 4 and b a positive odd integer.
Arithmetic input 1 denotes the normalized machine's raw input 2.

Replace the former marker factor `1+r0^2` by `r0^2`. Thus the final
polynomials are

    P72 = N0 N1 Na Nk Nt Ns r0^2 - Delta,
    P74 = N0 N1 Na0 Nk Nt Ns0 r0^2 - 1.

Here `Ns = Delta*(f^2-Delta*i^2*c^4)` is the normalized strong factor.
For the ordinary variant,

    I = i*c^2,
    A0 = Delta*(f^2-1),
    Na0 = A0*(V^2-y^2)+y^2,
    Ns0 = 1+I^2-A0.

The complete literal sources are `fixed_input72_square_marker.json` and
`fixed_input74_ordinary_square_marker.json`. Each deletes only the
`marker_unit = marker_square+1` row from its parent and changes the
final marker multiplication to use `marker_square`. The old source
rows otherwise remain in their old order. The variable alpha occurs
only in the budget residual r0.

## 2. A zero supplies enough of the budget

For P72, cancel the positive integer Delta. For P74, no cancellation is
needed. In either case a product of integer factors equals 1, and one
factor is the square r0^2. Consequently

    r0^2 = 1,                 r0 = epsilon in {-1,1}.

The resulting budget is

    q = W0+F+2Z+alpha+epsilon.                 (1)

Because alpha >= 1, its effective slack alpha+epsilon is nonnegative.
The other coordinates are strictly positive, so (1) implies

    q-C = F+Z+alpha+epsilon >= 2,
    q-F-Z = W0+Z+alpha+epsilon > 0,
    q > W0.

In particular, C > 0, C < q, F+Z < q, and W0 < q. These are precisely
the budget consequences used before dyadicity in the parent proofs.
Their norm signs, main Pell index, auxiliary positivity, strong rank,
signed target recovery, and no-wrap argument therefore apply without
change. None of those steps requires alpha+epsilon to be strictly
positive, or uses alpha outside the displayed budget margins.

The no-wrap estimate remains the asymmetric estimate

    E >= q^4 > R+2.

Indeed, after the signed target step gives p=R, a positive wrap would
give 2n >= R-1+E > 2R+1 > 2p, contradicting n<p. No stronger estimate
such as E>2(R+2) is required or asserted.

The parent proofs consequently recover the same positive core,
including X=2^R, q=2^ell, R>3ell, and the exact input endpoint W0.

## 3. Strictly positive raw slack is recovered after dyadicity

Although the effective slack alpha+epsilon can be zero, the raw75
compiler slack can still be chosen strictly positive. Since both q and
W0 are powers of 2 and W0<q, one has q >= 2W0. Equation (1) gives

    q-C = (q-W0+F+alpha+epsilon)/2.

The integer F+alpha+epsilon is at least 1. Hence

    q-C > W0/2 >= 2d,

where the last inequality follows from
W0/2=2^(2d+b-1), d>=4, and b>=1. Thus

    alpha_raw = q-C-2d

is a strictly positive integer. The raw75 bound is now restored
exactly. The remaining restoration formulas are unchanged:

    w_raw = X/q^3 > 0,
    z_raw = t-1+wC > 0,
    kappa = psi_(a+2)(u),
    mu = chi_(a+2)(u),
    delta = (kappa-u)/Delta > 0,
    phi = c-kappa > 0,
    rho = (mu-a*kappa-W0)/H > 0.

The positivity, integrality, and input identities for these formulas
are proved in the parent notes; they use u<R and the recovered core,
which this argument preserves. The auxiliary coordinates o,j are
likewise restored by the parent construction. The ordinary variant
uses i_raw=i; the normalized variant uses i_raw=Delta*i.

Therefore every positive zero of P72 or P74 yields a positive solution
of the full raw75 equations, and the pinned compiler theorem proves
acceptance at raw input 2. For the fixed machine in the deliverable,
this is equivalent to the K215 halting predicate and to the existence
of a ZFC proof of contradiction.

## 4. Completeness and the precise equivalence claim

Start with a positive zero of the corresponding parent polynomial
(P73 for the normalized source, P75 for the ordinary source). Its old
budget residual is zero and its old marker is 1. Retain all
coordinates except set

    alpha_new = alpha_old+1.

The new residual is -1, its square is 1, and every retained norm factor
is unchanged. The new tuple is strictly positive and is a zero of the
new polynomial. Parent completeness therefore proves completeness
of each new variant.

Combining this direction with the explicit raw75 soundness restoration
above gives equivalence of **existence of positive solutions** with the
63-gate ordinary system, its quartic lift, and the fixed machine's
acceptance. A supplied new zero need not itself satisfy the old budget
equation. In particular, replacing alpha by alpha+epsilon would give
zero when alpha=1 and epsilon=-1, which is not an allowed positive
coordinate in the old system. No pointwise conversion by that formula
and no equality of positive zero sets is claimed.

## 5. Operation counts, degree, and executable checks

Exactly one addition is removed. Thus the normalized count becomes
72=41M+31A, and the ordinary count becomes 74=41M+33A. All gates,
unknowns, and fixed numeral ports remain live. Both old and new marker
factors have the same leading homogeneous form r0_top^2. The leading
forms proved in the parent notes are therefore unchanged, so the
degrees remain exactly 157 and 101 respectively.

`verify_square_marker.py` first replays both parent validations. It
then reconstructs the literal one-row deletion and rewire, verifies
the gate ledgers and liveness, checks 64 signed whole-source algebraic
fixtures for each variant, and evaluates the exact coefficient arrays
for the degree and nonzero leading coefficient. Its diagnostic
constants are not asserted to be a compiled ZFC program. The checked
receipt is `square_marker_validation.json`.

The executable arithmetic checks do not replace the semantic proof
above or constitute an end-to-end Lean/Rocq formalization. The new
variants use the same pinned and explicitly identified compiler and
Pell interfaces as their parent constructions.

