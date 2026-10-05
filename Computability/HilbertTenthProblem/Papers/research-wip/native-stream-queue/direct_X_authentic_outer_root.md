# Authentic outer restrictions on the direct-X83 proposal

On every positive zero of the unchanged direct-X83 source on an admissible
fixed-program slice, the scale q is **even**, the repunit coordinate J and
marker Z are odd, and the input Pell index is one of **u or A*u**. The latter
alternative requires A*u<=R. On the branch with no first-index wrap, the
ordinary input is already decoded: **W=2^u<q**. The remaining divisibility
obligation there concerns even scales with an odd factor, not arbitrary
odd scales.

These are necessary conditions and a partial decoding theorem for the
existing83=46M+37A source. They do not prove q|X, exclude every wrapped
zero, or improve the established universal84 bound. No source array is
changed. The companion arithmetic work by Pascal independently noticed
the odd-index parity obstruction used below.

## 1. Exact inherited setting

Use `complete83_direct_X_boundary_pascal.md` and its authenticated source
metadata. Its full positive-zero bootstrap proves, without q|X,

    q=(B-1)J+1, U=q-F, C=U-Z-alpha-2d*x, W=C-Z,
    R=(q*U-Z)(q^2-1)+(MC+q*MF_source)J,
    X>0, Y=s*q^3, a=Y(X+1), A=a+2,
    Delta=A^2-1, H=4a+3=4A-5,
    c=psi_A(R), D=chi_A(R), gamma=rho+sigma,
    D=X+a*c+gamma*H,
    kappa=u+delta*Delta, u=2d*x+b,
    mu=W+a*kappa+rho*H, mu^2-Delta*kappa^2=1.

All supplied witnesses, including rho,sigma,delta, are strictly positive.
Here delta is distinct from Delta. The authentic modified compiler has
B=2^d, positive odd b and d, MC even, and
MF_source=MF_native+B-1 with MF_native even. In particular B is even and
MF_source is odd. Arbitrary mask values do not constitute a valid compiler.
The same bootstrap gives

    C>=0, -q<W<q, 3<=u<q+b<2q,
    (2q-1)(q^2-1)<R<q^4-q^3,
    q>=16, c>RY>2R, Delta>4q^6>R.

The bound on u follows directly from C>=0 and positive F,Z,alpha:
2d*x<q and b<B<=q. The positivity mu>0 follows from W>-q,
a>=2q^3 and kappa,rho>=1, before classifying its input Pell index.

The normalized strong equation supplies a positive index m with

    f=chi_A(m), psi_A(m)=i*c^2, R*c divides m.

The positive auxiliary solution has an odd index ell and the inherited
signed step-down argument gives ell=+R or -R modulo m. These are precisely
the pre-input conclusions established in the direct-X83 note, not a use
of the parent universal theorem after deleting its divisibility premise.

## 2. Parity excludes every odd scale on the authentic slice

The Pell coefficient recurrence

    psi_A(0)=0, psi_A(1)=1,
    psi_A(j+2)=2A*psi_A(j+1)-psi_A(j)

shows psi_A(j)=j modulo2 for every integer A. If R were even, c would be
even, and c|m would make m even. The congruence ell=+R or -R modulo m
would then contradict the oddness of ell. Thus **R is odd**.

If q were odd, the equation q=(B-1)J+1 with B even would make J even.
Then q^2-1 and J are both even, so the displayed exact formula for R
would make R even. This contradiction proves q is even. Consequently
J is odd; MC+q*MF_source is even and q^2-1 is odd. The same formula now
gives R=Z modulo2, so Z is odd. In particular

    8 divides Y, A=2 modulo8, H=3 modulo32,
    Delta=3 modulo32.                                  (1)

No interpretation of J as a geometric repunit or of q as a power of
two was used. The earlier q=27 kernel example remains valid at its
explicitly weaker interface; this theorem explains an additional exact
reason it cannot extend to authentic outer rows.

## 3. Only two possible input indices remain

Positive mu and kappa classify a unique positive input index v with
kappa=psi_A(v), mu=chi_A(v). Write

    E_j=chi_A(j)-(A-2)psi_A(j)
       =2psi_A(j)-psi_A(j-1), j>=1.

The sequence E is positive and increasing. Its main and input projections
are gamma*H=E_R-X and rho*H=E_v-W. Since X>0 and E_R<2c,

    0<rho<gamma<c.                                     (2)

For v>=R+1, the Pell recurrence gives

    E_(R+1)-H*c=4c-2psi_A(R-1)>2c.

With W<q<c, this would give rho*H>H*c, contrary to (2). Hence v<=R.
This threshold proof uses the paid positive split gamma=rho+sigma; it
would not be valid for the separate independent-gamma83 proposal.

Reduction of the Pell binomial expansion modulo Delta gives

    odd v:  psi_A(v)=v modulo Delta,
    even v: psi_A(v)=A*v modulo Delta.

Since A^2=1 modulo Delta and kappa=u+delta*Delta, it follows that
v=u modulo Delta on the odd branch, and v=A*u modulo Delta on the even
branch. We have 0<v<=R<Delta. Also 0<u<A and
0<A*u<=A*(A-1)<Delta. Thus there is no modular ambiguity:

    v=u, or v=A*u<=R.                                  (3)

A is even by (1) and u is odd, so these alternatives have the required
parities. They are necessary conditions only: no claim is made that
both alternatives can satisfy every remaining equation.

## 4. No wrap already restores the ordinary input loader

On the branch with no first-index wrap, the direct-X83 proof gives
X=2^R and H>2^R. Then A>X>R, so the second alternative in (3) is
impossible and v=u. In particular u<R, since u<2q<R.
The projection recurrence E_j=2^j modulo H gives

    W=2^u modulo H.

Here 2^u<=2^(R-1)<H/2, and q<H/2 because H>=8q^3+3. Together with
-q<W<q, these bounds make the difference W-2^u strictly between -H and H.
Therefore **W=2^u**, and the outer bound then gives **2^u<q**.

This restores the actual ordinary exponential input loader on this whole
branch, not just at constructed canonical tuples. For the inherited
compiler u=2d*x+b it is the intended marker 2^b*B^(2x). This still does
not turn q into B^N: with q even, an odd divisor of q could remain.
If q is proved dyadic, then R>q makes q|2^R=X and the already-proved
conditional inverse restores the complete positive parent84 zero.

## 5. An even nondyadic kernel boundary

**Remark 1 (evenness alone does not recover the missing divisibility).**
The stronger kernel-only inference obtained by adding "q is even" to
the previous weak size, canonical half-binomial and q^3|Y hypotheses is
still false. Retain R=1223, r=611 and X=2^1223, but set q=54. Define

    Y=(1/2)*sum_(j=0..611) binom(1222,611+j)*X^j.

The previously recorded exact 3-adic residue is reproduced independently:
Y=452709=23*3^9 modulo3^12. The central coefficient has
v2(binom(1222,611))=pc(611)=5. Every noncentral term after halving is
divisible by 2^(1223-1), so **v2(Y)=4**, while **v3(Y)=9**. Thus

    q^3=2^3*3^9 divides Y, but X=14 modulo54.

The weak bounds q>=16, 3q+1<=R<q^4 and R=3 modulo4 still hold. The
canonical positive first/main/input/index/normalized strong/auxiliary
completion in `unscaled_x_odd_kernel_root.md` depends only on X,Y,R,
with s changed to Y/54^3. All its coordinates remain positive integers.
This does not restore authentic outer rows: R violates their stronger
lower bound, and q-1=53 is not divisible by the minimal allowed B-1=31.
The example is **not a full compiler zero** or a refutation of direct-X83.
It proves that parity plus the weakened kernel conditions still cannot
supply the missing divisibility theorem.

## 6. Evidence and remaining questions

The full direct-X83 note and its root review, the full earlier kernel
counterexample, and the compiler mask/parity definitions were read as
proof text. The source metadata is bound as bytes; no array is evaluated.
The fresh handwritten helper checks1,056 Pell parity identities,1,056
input-index residue identities,1,152 outer parity instances and the
single even-scale half-binomial residue. Its outer diagnostic mask
values test the parity identity only; they are not compiler exports.
The half-binomial numerator is computed modulo twice the desired modulus
before exact halving, so no inverse of2 modulo an even modulus is used.

Fresh writer, normal comparison and optimized comparison from `/` pass
before freezing. No supplied, committed, archived or frozen program was
executed or imported. No complete native Pell tuple was materialized.
The receipt and dependency metadata distinguish these finite scalar
checks from the all-size arguments above.

The direct-X83 proposal remains open, with its source and original
argument credited in Section1: exclude the nonzero first-index wrap,
and exclude even nondyadic q on the no-wrap branch. The new input
classification and parity restrictions narrow these obligations; the
q=54 counterexample records why the kernel-only parity shortcut fails.
No unproved claim is promoted to a universal theorem.
