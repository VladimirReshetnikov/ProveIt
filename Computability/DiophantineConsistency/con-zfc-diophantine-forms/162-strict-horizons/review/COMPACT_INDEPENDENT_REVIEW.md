# Independent mathematical review: free quotient with a Pell scale

## Verdict and scope

I independently reviewed the two constructions in
../compact/PROOF.md, with particular
attention to equation_89_degree278.json. I found no mathematical gap in the
new argument, conditional on the explicitly inherited universal Pell
classification/folding, ratio, native half-binomial, and C222/refutation
calibration theorems identified there.

The two polynomials have ten strictly positive integer variables. The
83-operation chart has exact degree 312; the 89-operation chart has exact
degree 278. Their coefficients remain the full bound four-integer BFS943
radix67 tuple. This review does not claim a new end-to-end proof-assistant
check or a global minimum.

The separate check_compact_independent.py was written without importing
the producer or supplied verifier. It checks topology, use of every gate
and input, the degree upper bounds, and 80 direct-formula evaluations per
chart modulo 2^127-1. Those evaluations are finite regression checks,
not replacements for the algebraic identity proof or arithmetic theorem.

## 1. Why freeing Y does not remove a needed divisibility hypothesis

The new input is Y=s, with lambda=q in

    A=qY(X+1)+1,             v=Xq^2Y^2.

At the start q need not divide Y. The proof does not assume it. The
initial lower bound c>4q^4 follows instead from the folded odd Pell index:
c>=psi_A(3)=4A^2-1, and A>q^2. This works even at Y=1.

The retained shift T+alpha is important. From the unconditional mask
upper bound R<q^4+(alpha+2)q^2, T>=1 and alpha>=1 give

    b-c >= alpha*c-R > c-q^4-3q^2 >0.

This establishes b>c and V>0 before determining B or C. It replaces
the old argument which depended on q dividing Y; it is not a tacit
reuse of that old argument.

## 2. Root extraction and auxiliary growth

The identity Q=4 Delta^2 U^2 G makes every prime divisor of G coprime
to Q-1 and QV^2-1. Taking valuations of the rational-square identity
forces G to be an integer square. Since F0=1+Delta U^2 E,
gcd(E,F0)=1, so E and F0 are separately positive squares.

The rational adjacent-Pell descent is valid. For a reduced rational
y=r/m satisfying Qv^2-(Q-1)y^2=1 with integer v>1, m^2 divides Q-1.
The transformed integer

    v'=(2Q-1)v-2(Q-1)y

satisfies 0<|v'|<v. The transformed numerator of y modulo m is
congruent to r, because 2Q-1=1 modulo m. Thus the denominator
cannot disappear during descent; reaching v=1 forces m=1.

The all-index folding theorem is used before V is assumed positive,
with exactly its signed hypotheses. The later estimate b>c gives

    V>c(f^2-1)>4Q.

In the adjacent Pell sequence, this excludes indices one and three.
The resulting index at least five gives

    V>8Q^2,       b>4 Delta^3 I^2>4g,       gy<3bV/8.

All these bounds survive at Y=1 and require no early q-adic property
of Y.

## 3. Negative transport cases in the corrected chart

For R>=1 other than the two sign exceptions, the cubic correction has
the favorable sign. When R=-r<=-4, the exact mask decomposition

    R=(hC+q alpha)(q^2-1)+Pmask,    Pmask>0,

gives C<0 and |C|>r/q^3. Thus the extra negative transport term has
magnitude greater than w|C|L, whereas the adverse cubic correction is
less than w*s^2*r^3/(6q^4). Since b>r and
L>(Fs-1)r^2>s^2 r^2, the former strictly dominates the latter.

For R=0, one has C<=-1, the adverse correction is
w*s^2/(2q^4), and L>Fs-1>s^2, again giving a strict margin.
These are the complete integer ranks at which the correction can
hurt the proof. Therefore B>=0, then C>0, is established without
an omitted sign case.

Only after that recovery are the mask bounds 3q<R<q^4-2 used.
Together with the normalized strong-rank and signed auxiliary-index
lemmas, they give p=R before any first-index or quotient divisibility
claim is made.

## 4. The corrected first-index recovery handles both 2 and 3

The exact expansion is

    2 psi_(1+2v)(m)
      =2m+8v binom(m+1,3)+32v^2 Z_m,       Z_m>=0.

For odd R, r0=(R+1)/2 gives
(R+1)(R-1)(R+3)=48 binom(r0+1,3), so the corrected ebar is an
integer before clearing its denominator.

The carrier gives q^7|(ebar-q^4s), hence q^4|ebar. The recurrence
first gives q^3|d, d=2n0-R-1. The displayed exact difference
identity then gives q^6|6(ebar-d). At a prime ell dividing q,
with a=v_ell(q)>=1,

    v_ell(ebar-d)>=6a-v_ell(6)>=6a-1>=4a.

This argument explicitly covers ell=2 and ell=3. It does not
invert six modulo q. The bound |d|<R<q^4 consequently forces d=0.

The whole q^7 quotient is deliberately postponed. The proof first
gets the exact index n0=(R+1)/2, then derives X=2^R, then uses the
new q-adic divisibility of X to prove q^7|ebar. This is acyclic.

## 5. Projection and the delayed divisibility of Y

The modulus H=4A-5 is odd and equals -1 modulo q. The corrected
carrier yields H|6hK. Only powers of q are cancelled; six and h
need not be invertible modulo H.

The universal Pell projection therefore yields

    H | 6h (X-2^R)(2^R X+1).

The proof bounds the complete product rather than either factor
separately. With R=2r+1, r>=48, X>=q>=32, its sufficient upper
bound divided by X^(r+1) is

    4*4^r/X^(r-5)+8*16^r/X^(r-4)
      <=2^(-117)+2^(-25)<1.

The uniform ratio lemma holds for lambda=q and Y>=1 and supplies
X^(r+1)<H. Hence the product vanishes and X=2^R.

Since q|X, q is a power of two. The inequality R>3q then gives
q^6|X, whence q^8|v. It now supplies the full integral
nonnegative rho in both charts.

The final denominator argument is exact: after z,n,kappa,rho
are integral,

    Y/q^3-WB/h is an integer.

Reduction after multiplying by hq^3 gives q^3|Y and h|B, because
gcd(q,h)=1 and W=1 modulo h. This obtains the condition removed
from the original input parameterization.

## 6. Positive completeness at the new bases

The copied uniform_ratio.md proves its ratio estimate for every
lambda>=1, so using lambda=q is licensed. Canonical native outer
data satisfy q^3|Y and X=2^R. They provide positive new w:
w=X/q^2 in the plain chart and w=X/q in the corrected chart.

The new c,k,tau are computed at the new bases, rather than identified
with the old unscaled witnesses. The ratio/half-binomial theorem
gives 0<eta<k. A fresh Pell period modulo c^2*tau gives i>0 and
the doubled strong witnesses in the exact literal chart.

The universal auxiliary reconstruction is applicable to that doubled
strong solution: it requires only c|I, the positive strong norm,
R>=3, and R=3 modulo 4. Its explicit solution at index R>=97
satisfies b>4g, so T_*>4g/c>q>alpha. Therefore T=T_*-alpha>0.
No positive-domain inverse of an arbitrary old witness is presumed.

Finally g>2Xc, while kappa<Xc and Y/q^3<=Y<Xc.
The defined n is thus strictly positive. This closes all ten
positive-coordinate obligations.

## 7. Exact degree check independent of the producer

For the corrected chart write q0=beta*J and k0=eta+zeta. Leading
terms give

    Delta: q0^4 w^2 s^2,
    G: q0^16 w^6 s^14 i^2 k0^8,
    Fs: 4 q0^20 w^8 s^20 i^4 k0^12,
    Q: 4 q0^24 w^10 s^22 i^4 k0^12,
    V: -4 q0^23 w^8 s^20 i^4 k0^12 (q0-F),
    M: 24 q0^10 w s.

The unique highest-degree finalizer term is -Q M^2 G V^2. It is

    -36864 q0^106 w^34 s^78 i^14 k0^44 (q0-F)^2,

of total degree 278. The other finalizer terms have degrees at most
244, 172, and 70. Choosing eta^44 and F^2 gives a nonzero
coefficient at the actual positive beta.

The analogous plain leading terms give

    -1024 q0^140 w^34 s^78 i^14 k0^44 (q0-F)^2

of total degree 312, again uniquely dominant. Expanding k0^44 and
(q0-F)^2 produces 45*3=135 distinct monomials in either leading
form. Thus the claimed degrees are attained, not merely propagated
upper bounds.

## 8. Limits

The finite checks do not solve the polynomial or decide consistency.
The proof uses the inherited native tuple calibration and ordinary
Pell lemmas exactly as identified in the source. The claims of
comparison with earlier frontier points must remain tied to the
inspected repository snapshot and domain; the result is not a
literature-wide optimality statement.

