# Independent arithmetic audit: signed horizons and divisibility-forced Pell growth

This note audits the combination of the supplied incoming Pell Growth 210
package with the signed affine horizons and oriented pooling package. It is
a proof of the new arithmetic interface; it does not replace the inherited
C222/ZF/ZFC logical calibration or claim an end-to-end formal proof.

## 1. Literal new source and the preliminary estimate

Put d=2^19. Replace the quadratic horizon by

    t = 2 + 4z, z in Z,

and retain the independent standalone growth rows

    Z = tF,
    X^2 - 16Z^2 - 8ZF = 1,
    F = d t (2u+1).

All variables are unrestricted integers. The growth quotient u and beta
multiplier v are independent. Let T=|t|. Then T>=2 and |t+1|>=1. The
last row alone proves that F is nonzero and even, with

    |F| >= d T > T.

No Pell classification or sign of t is needed for this preliminary estimate.
This avoids accidentally applying the positive-center growth bound on a
negative branch. That bound is invoked only after a retained exact-power
certificate proves t positive.

## 2. Main Pell certificates and pooling before sign recovery

Keep the predecessor's full signed square frame, even CRT anchor C, main
Pell norm equations, cap and orientation equations, except for deleting the
obsolete exact-growth request and its own pair. Every actual remaining base,
nominal index, and output is included in the frame. In particular t and F
remain frame atoms; D below must be included by its actual affine expression.
Since the actual frame contains F^2 and |F|>=2d, the same square-frame identity gives W>=258. Its square-based anchor theorem
does not need the sign of t or F. It yields canonical signed Pell pairs and
the usual large-center hypothesis before arithmetic sign recovery.

The new standalone pair X,F at center |4t+1| is independent of this common
Pell frame. It does not need inclusion in the common family.

There are fifteen remaining exact-power requests in thirteen principal
common-frame pairs, at the four bases B,D,q,q+1. There is no exact-power
request at base t any more. Use either an oriented weighted pool for all four
bases, or a weighted pool for B,D and an unweighted reciprocal pool for q,q+1.
The inherited oriented-pooling proof applies to any subfamily of its former
at-most-five bases and at-most-seventeen requests, with unchanged strict
error bounds.

The following sign ordering handles the fact that a zero base in an oriented
pool is initially unconstrained. Keep the literal CRT identity

    B eta = C+F+1,  C even,

and replace the old self-radix base by

    D=2(C+F+1).

Because C and F are even, C+F+1 is odd, so B is odd and nonzero, eta is odd
and nonzero, and D is 2 modulo 4. In particular |D|>=2. Thus both B and D
blocks are active in an oriented pool before any requested power is used.
The D request gives

    x>=0, q=D^x.

It follows that q is neither 0 nor -1: x=0 gives q=1, and x>0 gives |q|>=2.
Thus q and q+1 are nonzero and have the same sign. Their unweighted reciprocal
pool, if that partition is selected, is now legitimate. Every one of the
remaining power requests is exact. No binomial interpretation is used here.

## 3. Sign bootstrap in a noncircular order

The retained endpoint rows, with their literal source meanings, are

    y = F(2v+1),
    g = 1+(t+1)y,
    x = 1+g u_t,
    x = F+1+(y+1)u_0.

The already proved bound gives |y|>=|F|>T. Also |t+1|>=T-1>=1. Therefore

    |g| >= |F|-1 > 1.

If x=0 then g u_t=-1, impossible. Hence x>=1 and |q|>=2.
The literal request at base q has exponent t (not t+1). Its signed-power
conclusion forces t>=0; the affine progression excludes zero, hence t>=2.

At this point the positive-center growth theorem from the parent applies
without alteration: with L=8^(d-1)t^d it gives |F|>=L^t>t.

The q request with exponent y+1 gives y+1>=0. A negative y would satisfy
y<=-|F|<-1, so y>0 and y>=|F|. If x=1 the initial endpoint would give
(y+1)u_0=-F, impossible since 0<|F|<=y<y+1. Therefore x>=2, whence
|q|>=4 and |q+1|>=3.

The (q+1) request with exponent F+t gives F+t>=0. If F<0, then
F+t=t-|F|<0, contradiction. Thus F>0. The same base certifies all CRT
representatives as nonnegative, with C>0 by the anchor's nonvanishing.
Consequently D>2C, and all the parent's binomial-digit, B-positivity,
N|q, local-bound, beta-CRT, and Horn-flow arguments have their established
hypotheses. This proves soundness of the combined arithmetic source.

The possible negative values of q cause no problem: x>=2 was used through
|q|, before (q+1)-powers force C>=0. Then D=2(C+F+1)>0, so q=D^x>0.

## 4. Why the lower bound t>=2 suffices

The positive-center Pell proof is elementary. Eliminating Z gives
X^2-((4t+1)^2-1)F^2=1. For the standard ordinate sequence Y_n(a),
classification gives |F|=Y_n(4t+1) with n>=1. Specialization of the recurrence
at a=1 gives Y_n(a)=n modulo a-1. Thus 4t|F implies 4t|n. At an odd center,
Y_(2m)=2X_mY_m with X_m odd gives v_2(Y_n)=v_2(n). Hence
v_2(n)=19+v_2(t), and n>=dt. The elementary growth estimate
Y_n(a)>=(2a-1)^(n-1) now gives

    |F| >= (8t)^(dt-1) >= (8^(d-1)t^d)^t = L^t.

The last ratio is exactly 8^(t-1)/t>=1 for every t>=1.

The constructor-depth proof uses only local leaves strictly below t and the
fixed codes 0 and 1. At t>=2 both constants are below t. For a child bound m,
E(m,m)+1<=8(m+1)^2, so depth19 gives L=8^(d-1)t^d with no t>=16 premise.
The finite-product label-separation theorem requires L>=t>=1 and F>=L^t,
which now hold.

For the factorial-free binomial-CRT theorem, the actual premise is
F>=lcm(1,...,t)^2 and t>=1. Since d>=2, L>=t^2. Hence the elementary
factorial bound gives

    F>=L^t>=t^(2t)>=(t!)^2>=lcm(1,...,t)^2.

This replaces an older sufficient comparison t^t>=lcm(1,...,t)^2 that was
only used in the former t>=16 range. No estimate for the asymptotic size
of the least common multiple is needed.

The remaining local-value estimate requires x>2^32. In the new range,

    F>=L^t >= (8^(d-1)2^d)^2 = 2^(8d-6) > 2^32.

The retained endpoint inequalities give x>=2+(t+1)y with y>=F. They imply
2+t+x+y+F<2x because (t-1)y>t for t>=2 and y>=F. The unchanged finite
local-polynomial bound therefore gives Local<(2x)^(2^23)<2^x. The final
inequality holds at x>=2^32 and becomes stronger as x increases.
All radix digit estimates depend on this large x, not on the older lower
bound t>=16. The range compiler itself allows every integer t>=1.

No independent requirement 4|t is used by the signed main-Pell theorem,
whose nominal indices may be arbitrary integers. The older use of 4|t
was a sufficient way of obtaining binomial parity and large growth; both
properties now have their separate proofs.

## 5. Cofinal completeness, including the parity condition

Choose t in the cofinal progression

    t = 2 modulo 2^23,  t>0.

This progression is contained in t=2+4z (choose z divisible by 2^21).
It retains v_2(t)=1 and makes bit 20 of t zero. All horizon lower bounds can
be met because the progression is cofinal.

Set n_0=dt, y_0=Y_(n_0)(4t+1), a_0=X_(n_0)(4t+1), and
b_0=y_0/(dt). The recurrence congruence modulo 4t and the valuation identity
show b_0 is an odd integer. The even index n_0 gives a_0=1 modulo 4.

Choose ell>23 with 2^ell>t. Because s -> Y_s(a_0) permutes residues modulo
each power of two, one can choose an arbitrarily large positive odd s with

    (t/2) b_0 Y_s(a_0) = 1 modulo 2^(ell-20).

Put n=n_0s and F=Y_n(4t+1)=y_0Y_s(a_0). Then F/(dt) is odd, all three
growth rows have integral witnesses, and F=2^20 modulo 2^ell. The binary
supports of F and t are disjoint, so binom(F+t,t) is odd.

For beta coding it is enough to choose the odd multiplier 2v+1 divisible by
all odd primes <=t and large enough for all states. The old stronger demand
t! | y is unnecessary and generally incompatible with the chosen fixed
v_2(F)=20. Prime support suffices to make the numbers 1+iy pairwise coprime.

Then apply the parent's acyclic witness construction: choose beta data and
N=B^x; the nonanchor CRT representatives; an arbitrarily large permitted even
anchor C; D; actual q=D^x and power outputs; and finally the common Pell
frame and its private comparison witnesses. The old exact private quotients
give the new pooled quotients integrally. The affine horizon parameter is
integral by construction. Thus every finite calibrated refutation produces
an integer zero of the combined source.

The residue permutation used above has a short elementary proof. If a=1
modulo 4 then X_s(a)=1 modulo 4 and Y_s(a)=s modulo 2. With h=2^r the
duplication valuation gives v_2(Y_h)=r, and the Pell norm gives X_h=1
modulo 2^(2r+2). The addition identity therefore implies

    Y_(s+h)-Y_s = (X_h-1)Y_s + X_s Y_h = 2^r modulo 2^(r+1).

The two lifts of each index class give the two lifts of its output class.
Periodicity modulo 2^r follows from the same identity. Thus each residue
is attained once modulo 2^r, positive lifts are cofinal, and an odd output
residue has an odd index.

## 6. Exact algebraic elimination

After the semantic change, replacing every occurrence of t by 2+4z and
deleting the horizon row and t coordinate is an exact integer-polynomial
zero-set bijection. The inverse restores t=2+4z. Since the substitution is
affine, it preserves residual degree at most two wherever it was quadratic.
This saves one coordinate and one residual in the standalone quartic branch.
It also commutes with any later acyclic unit-pivot substitution provided the
literal source binding is checked. Counts for pooled projected equations
must be obtained from their actual emitted circuits; they are not inferred
only from the semantic proof.

This is not a pointwise zero-set bijection with the original 210-variable
quartic, whose horizon is constrained by a different quadratic progression.
The two sources have the same refutability predicate by their separate
soundness and cofinal completeness arguments. The exact polynomial
restorations apply after the signed horizon source has been specified.

## 7. Literal source coordinates and restoration maps

The complete starting point is source/pell216.json, the uncontracted
affine-radix stage of the supplied Pell Growth 210 package. Its SHA-256 is
2a8ee90a0d11eccba1956ac31d12992807a6cd2db8ef3d06cd2226d30dc196b9.
Every index in this section is zero-based. The semantic coordinates are:

| Semantic quantity | Literal source expression |
|---|---|
| t, x, F, B | x_0, x_1, x_2, x_3 |
| y, u_0, u_t, g | x_4-1, x_5, x_6, x_7 |
| A_1 | x_8-1 |
| A_2,...,A_8 | x_9,...,x_15 |
| C, N, eta | 2x_16, x_17, x_18 |
| q, q+1 | x_100-1, x_100 |
| W, common Pell center A | x_136, x_137+1 |
| horizon z, beta multiplier v | x_184, x_212 |
| standalone X, Z, u | x_213, x_214, x_215 |
| D | 2+2x_2+4x_16 |

Only source row131 is changed: t-16-4z^2 becomes t-2-4z. The main frame
is row130, signed orientation is row142, and the dominant-anchor cap is
row145. The endpoint rows are 0,1,2; the parity/CRT selector is row3; beta
spacing is row152; and the standalone growth rows are 153,154,155.

The fifteen actual power requests are:

| Base | Nominal exponent | Output |
|---|---|---|
| x_3 | x_1 | x_17 |
| D | x_1 | x_100-1 |
| x_100-1 | x_0 | x_102 |
| x_100-1 | x_4 | x_119 |
| x_100-1 | x_1 | x_126 |
| x_100 | x_2+x_0 | x_101 |
| x_100 | x_8-1 | x_106 |
| x_100 | x_9 | x_109 |
| x_100 | x_10 | x_112 |
| x_100 | x_11 | x_115 |
| x_100 | x_12 | x_118 |
| x_100 | x_13 | x_122 |
| x_100 | x_14 | x_125 |
| x_100 | x_15 | x_130 |
| x_100 | 2x_16 | x_133 |

The independent checker reconstructs the 34 actual frame atoms, the thirteen
principal norms and AY wires including their two historical offsets, the
complete signed orientation row, and the anchor cap. It checks each request's
base, index, and output in that frame. No nominal sign is assumed during this
finite binding check.

Pooling deletes eight private coordinates 144,145,146,147,208,209,210,211
and eight rows 102,103,104,105,148,149,150,151. The two singleton moduli
are T_B=2AB-B^2-1 and T_D=2AD-D^2-1. Their deltas are

    delta_B=N-x_175-B*x_176,
    delta_D=q-x_175-D*x_176.

Here x_175=X_x-A Y_x, x_176=Y_x, and the shifted AY wire is x_177+1=A Y_x.
For either singleton define

    E=(m-(X_x-A Y_x))^2-Y_x^2-2bY_x(m-X_x).

Modulo the retained AY wire the exact identity is E=delta^2+T_bY_x^2.
The old quotient restores as -delta/T_b; its integrality follows from the
exact power congruence recovered by the oriented-pooling theorem.

For the q and q+1 blocks, let H=sum Y_i(m_i-X_i) and
E=sum((m_i-(X_i-A Y_i))^2-Y_i^2)-2bH. Their old private rows are

    K-2H-(2A-b)L=0,
    E-T_b L=0  (after adding b times the first row to the old norm row).

Restore L=E/T_b and K=2H+(2A-b)L. These values are integral on a zero of
the new source. Conversely each old private certificate makes E/T_b integral,
so each weighted pool has the integral witness z=sum bE/T_b, or sum E/T_b
for the unweighted q,q+1 block. Every T_b is nonzero by the main frame bound.
These are exact quotient restorations on the zero set; they are not claimed
to be polynomial functions on arbitrary integer tuples. The final defining
polynomials themselves contain only integer constants and +,-,*.

The emitted source partitions are staged, with blocks (B,D) weighted by
their bases and (q,q+1) unweighted, and all4, with all four bases weighted
by their bases. The final acyclic certificates then select unit-linear rows
epsilon*v+f=0, epsilon in {1,-1}, and restore v=-epsilon*f. These last
restorations are integer polynomials on all tuples. The independent circuit
checker verifies their acyclic order and every retained residual exactly.

The matched-degree profiles are:

| Profile | Integer variables | Squared residuals | Exact degree | Binary operations | Bound on collected coefficient height |
|---|---:|---:|---:|---:|---:|
| integer130_degree12_staged | 130 | 70 | 12 | 2475 | <2^54 |
| integer116_degree16_staged | 116 | 56 | 16 | 2433 | <2^84 |
| integer107_degree32_all4 | 107 | 47 | 32 | 2419 | <2^107 |

The largest literal integer constant is 2^20 in every circuit. This must not
be confused with the height of the expanded polynomial. The listed height
bounds are rigorous propagated l1 bounds, not claims of exact height.

Nonzero top homogeneous specializations modulo 1000000007 certify residual
degrees 6,8,16 respectively; their squares cannot cancel in a real sum of
squares. Exact modular derivative witnesses certify actual occurrence of
every quantified variable. The checkers run with and without Python -O.

## 8. Scope of the conclusion

Composed with the named inherited C222/ZF and ZF/ZFC refutation equivalences,
the argument is ordinary mathematics formalizable internally in ZFC and
proves the desired equivalence for every completely emitted equivalent
polynomial. It assumes neither consistency nor a standardness restriction on
proof codes. This note supplies no new kernel-checked proof term and makes no
claim of global minimality or historical priority.
