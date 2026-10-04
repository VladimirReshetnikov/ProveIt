# Exact input-quotient dichotomy in independent-gamma83

On every positive zero of the actual independent-gamma83 polynomial, on its inherited valid fixed-program compiler slice, the input quotient has exactly two possible ranges:

    0 < rho < gamma < c,      or      0 < gamma < c < rho.

The first range is exactly the image of the positive parent84 zero set under the literal map gamma=rho+sigma_parent. Its input Pell index is the intended ordinary index u=2d*x+b. In the second range that index is at least A*u if even, and at least u+2Delta if odd. Here A=a+2 is the Pell parameter, c=psi_A(R), and Delta=A^2-1 is the source register named `A`.

This is a theorem about all full positive zeros of the unchanged83 source, not merely the fixed-history shifts of parent zeros. **It does not resolve the ordinary-input language.** The second range already contains infinitely many known completions at accepted, unchanged inputs. No new source or operation saving is claimed. The authenticated circuit remains83=47M+36A, eighteen positive witnesses and exact degree187.

## 1. Authenticated source and domain

The helper reads eight pinned dependencies as bytes or JSON only. The immediate circuit and proof anchors are:

| File | SHA-256 |
|---|---|
| complete83_independent_gamma_scout.py | b67ee981d5475a745094924d6ec3cbe72dfb38e3d28d9bd2c144ff0c2a59dc18 |
| complete83_independent_gamma_scout.json | ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20 |
| complete83_independent_gamma_scout.md | bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41 |
| complete84_scaled_strong_output.json | 8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf |
| complete84_scaled_strong_output.md | 01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade |

The other three dependencies, with exact hashes saved in the helper and receipt, are [the normalized85 proof](review_complete85_auxiliary_bezout_math.md), [the asymmetric native-kernel proof](review_complete74_asymmetric_scale_math.md), and [the actual modified compiler recipe](complete75_half_binomial_compiler.md). Their pre-input arguments, rather than the parent ordinary-input theorem, supply Section2 below.

In the child the supplied port `sigma` means independent gamma. The only edit from the full84 array is deletion of `gamma_sum=rho+sigma` and replacement of that wire by the supplied `sigma` in `gam`. All other rows and the full paid finalizer remain literal. In particular:

    q=(B-1)J+1, X=wq, Y=sq^3,
    k=eta+zeta, c=kY+eta, a=Y(X+1),
    A=a+2, Delta=a^2+4a+3, H=4a+3=4A-5,
    D=X+ac+gamma*H,
    C=q-F-Z-alpha-2d*x, W=C-Z,
    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.

The discriminant witness multiplier `delta` is distinct from Delta. All eighteen supplied witnesses and ordinary x are strictly positive. Fixed numerals satisfy the complete compiler recipe, including B=2^d, positive odd b, the actual shifted MF, and the original slack definition. Arbitrary numerical diagnostics are not asserted to be valid compiler slices.

The complete polynomials obey, over every commutative ring,

    P83(gamma)=P84(sigma_parent=gamma-rho).                (1)

The inverse in (1) is initially signed. Its positivity is a conclusion of the first branch, not a premise of the native bootstrap. The helper independently reconstructs the entire literal deletion, checks every input/native boundary row and all-row/all-port liveness, and authenticates the full83 packet without re-emitting it. Its canonical packet SHA-256 is recorded in the receipt. It also verifies that delta and rho occur in no noninput factor.

## 2. Full native bootstrap before input decoding

Take an arbitrary full positive child zero. Positive X,Y give a>0 and Delta>0 before using its equation. The inherited all-ring scaled-strong identity gives Delta times a normalized product-minus-one. Cancelling Delta makes all seven normalized integer factors units; it would be invalid to infer units directly from the scaled product equaling Delta.

The normalized85 proof, Sections2–6, uses the main quotient only through D>0. That positivity still holds because gamma is supplied positive. The five norm signs are +1: the main/input/strong exclusions use their residues modulo4, the auxiliary exclusion uses its square coefficient in the explicit Pell form, and the first norm uses its strict descent. At this stage index and transport have a common unknown sign. The transport magnitude and positive quotient give C>=0 and F+Z<q. Hence

    -q<W<q,  0<R,  R+2<q^4<=XY<a.

The normalized strong norm, auxiliary root gap and two auxiliary congruences then restore positive auxiliary coordinates and give main rank p=R. The first ratio fixes both remaining signs at +1. None of these steps compares rho and gamma or invokes accepted-input soundness.

The asymmetric native-kernel proof, Section2, likewise needs a positive independent gamma but no decoded input. Its ratio and main congruence recover X=2^R, dyadic q, the exact half-binomial Y, and R=3 modulo4. Consequently the actual seven scaled factors are

    1,1,1,1,1,1,Delta,

and D=chi_A(R), c=psi_A(R). This is the native conclusion of the frozen83 scout, Section2; it is not an assertion that x has already been decoded.

The inequalities needed here are especially elementary once these conclusions hold. The repunit definition gives q>=B=2^d>b. Since C>=0 and F,Z,alpha>0, 2d*x<q. Thus

    3<=u<q+b<2q<R<a<A<Delta.                            (2)

Here the inherited native bound R>=3q+1 supplies the middle inequality. Also c=kY+eta>=2Y+1>q and H>3. From u<=A-1 we obtain

    0<A*u<=A(A-1)<2(A^2-1)=2Delta.                     (3)

The input root is positive without a quotient comparison: mu>-q+a*kappa+rho*H>0. Its norm +1 therefore gives a unique positive integer index v with

    kappa=psi_A(v), mu=chi_A(v).

All subsequent arguments are on this fully justified native domain.

## 3. Exact quotient threshold at c

Write c_j=psi_A(j), D_j=chi_A(j), and

    E_j=D_j-(A-2)c_j=2c_j-c_(j-1)  (j>=1).

The sequence E has E_0=1,E_1=2 and recurrence E_(j+1)=2A*E_j-E_(j-1). It is positive and strictly increasing. The input and main projections are

    rho*H=E_v-W,  gamma*H=E_R-X.                       (4)

If v<=R, then E_v<=E_R<2c. Since |W|<q<c,

    rho*H<2c+q<3c<Hc.

Thus rho<c. In the opposite direction the Pell recurrence gives the exact identity

    E_(R+1)-Hc = 4c-2c_(R-1).                          (5)

If v>=R+1, strict c_(R-1)<c and q<c imply

    E_v-W >= E_(R+1)-W > Hc+4c-2c_(R-1)-q > Hc.

Therefore rho>c. In particular rho=c never occurs, and

    rho<c  iff  v<=R.                                  (6)

This comparison is independent of multiplicative orders and does not use the missing gamma>rho hypothesis. Separately, the positive supplied gamma satisfies gamma*H=E_R-X<2c, so

    0<gamma<c.                                         (7)

## 4. The input congruence leaves one small index

Modulo Delta=A^2-1, the Pell coefficient has the exact residues

    psi_A(v)=v         for odd v,
    psi_A(v)=A*v       for even v.

A is even, Delta is odd, and u is odd. The equation kappa=u+delta*Delta and the parity of v strengthen these to

    odd v:  v=u modulo 2Delta;
    even v: v=A*u modulo 2Delta.                        (8)

The second line uses A^2=1 modulo Delta and the evenness of A*u. Equations(2)–(3) give the least positive representatives. Every possible input index is therefore of exactly one of the forms

    v=u+2Delta*j,       j>=0  (odd branch),
    v=A*u+2Delta*j,     j>=0  (even branch).             (9)

The even representative A*u exceeds R, and the next odd representative u+2Delta also exceeds R. Hence the complete small-index classification is

    v<=R  iff  v=u.                                    (10)

No assertion is made that every index in (9) meets the second, H-modulus congruence; the frozen order criterion supplies that additional restriction. For any noncanonical completion (9) gives the rigorous lower bounds v>=A*u or v>=u+2Delta. These bounds concern all full zeros, including any that might lie over false inputs.

## 5. Positive parent restoration and the unresolved branch

Suppose v=u. The recurrence gives E_u=2^u modulo H, and (4) gives W=2^u modulo H. Because u<R and X=2^R<a,

    0<2^u<X<a,  -q<W<q,  a+q<H.

The congruent representatives therefore differ by less than H in absolute value, so W=2^u. In particular 2^u<q is recovered rather than assumed.

Both u and R are odd and u<R, so R>=u+2. Monotonicity of E gives

    E_R-E_u >= E_(u+2)-E_u
             =2A*E_(u+1)-2E_u
             >(2A-2)E_u > A > X.

It follows from (4) that

    H*(gamma-rho)=E_R-E_u-X+2^u>0.                     (11)

Thus sigma_parent=gamma-rho is a strictly positive integer. Equation(1) now restores an actual full positive parent84 zero at the same input, with every other supplied coordinate unchanged. Only after this restoration is the parent ordinary-input theorem invoked.

Conversely, any positive parent84 zero maps to this child with gamma=rho+sigma_parent>rho. By(7), rho<gamma<c, and (6),(10) identify its index v=u. Consequently the following conditions are equivalent on the full child zero set:

    rho<c;  v=u;  rho<gamma;  the literal inverse is positive.

The complementary branch has rho>c>gamma and the index bounds in Section4. This locates all noncanonical completions beyond the entire forbidden interval [gamma,c]. It does not identify that branch with false inputs: the frozen83 CRT construction supplies infinitely many v>R completions above every genuine parent zero while leaving its accepted ordinary input unchanged. A rejected-input zero, if one exists, must be in this branch, but proving its existence still requires authentic outer data and the full order compatibility condition.

Enforcing rho<c by an additional coordinate relation would be a further source change whose paid cost must be counted. This note does not add that relation, lower any universal bound, or normalize the complementary branch into parent zeros.

## 6. Fresh checks and scope

The standard-library helper authenticates all eight dependencies and reads them only as inert data. It checks the full literal83/84 substitution, nineteen exact boundary rows, all83 gates and25 free ports, and the absence of the two input witnesses from all six other factors. Twenty-four signed/rational whole-array pullbacks check1,992 retained-register equalities. These all-ring checks make no positive-zero claim for their diagnostic assignments.

Independent Pell recurrence checks cover648 quotient-threshold comparisons, including negative representatives of W and both sides of v=R. Twelve positive intended-index components check rho<gamma<c, the positive input modulus, and the index representatives. Seventeen complete modular periods give68,442 checks of the two residues in (8). These are small Pell/congruence components; none is a compiler history or full83 zero. No predecessor helper, compiler builder, or historical suite executes, and no enormous native tuple is materialized.

The unchanged full source packet is authenticated rather than duplicated. The new receipt includes its canonical hash and the new helper's own SHA-256. Use `--root` for the absolute native-stream-queue directory and `--expect` for this receipt; `--output` writes a deterministic receipt. Checks use explicit exceptions and canonical type-sensitive JSON comparison in both ordinary and optimized Python. Fresh normal and optimized exact replays from `/` both pass.
