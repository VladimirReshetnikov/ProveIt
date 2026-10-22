# Final lower-degree weights and the twenty-six-integer extension

This is an independent continuation of `RATIONAL_AUXILIARY_PELL_SATURATION.md`.
It audits the final scaled-auxiliary-root construction, including its zero
branches and its signed domain. Arithmetic circuit counts and exact degrees
are separate claims to be checked against the final emitted circuit.

## 1. Final separation weights

Let W be a positive integer strict bound for every conjugate of
`rho=d y`. Put

    P=H W, K=P+1, M=6W, u=HM=6P,
    Z=Ht+K(X+ac).

Only u needs to be evaluated for the resultant; M is a proof abbreviation.
The correspondence is `t=M tau+K gamma+rho`.

When X>0, the source geometry gives `A2<16A1`, as proved in the earlier
audit. With `P>=14`,

    u sqrt(A1)-K sqrt(A2)
      > [6P-4(P+1)]sqrt(A1)
      = (2P-4)sqrt(A1) > P=H W.

The last inequality uses `sqrt(A1)>=1` and P>4. Also

    K sqrt(A2)>K>P=H W.

Thus the two required conjugate separations hold with these lower-degree
weights. This is not a heuristic degree estimate; the inequalities are
strict on the full intended domain. The change does not add a supplied
unknown, since M is the computed expression 6W.

## 2. Exact mixed domain and a sign-safe bound

Only the following seven supplied ports must be positive:

    J,F,alpha,z,s,eta,zeta.

The other five coordinates are unrestricted integers

    h,r,T,w0,t,

with the polynomial substitutions `i=2r+1` and `w=w0^2`. In particular
i is a nonzero odd integer, whereas w may initially be zero. All old
gamma, f, tau and y coordinates are eliminated. Before any root recovery,
q,Y,k,c,a,H,Delta are positive even at w=0, since a=(X+1)Y.

Use the normalized abbreviations

    I=i c^2, S=Delta I, Q=S^2, d=Q-1,
    D=1+I S=1+Delta i^2 c^4,
    v=cT, b=c+RD, e=Q(Dv^2+b^2)-1, B=2Qvb.

For the system assume Nk=Nt=1. For the product, its already audited
mod-four guard gives Res=0 and Nk=Nt=epsilon in {+1,-1}. In either case
the weak transport argument gives Cword>=0 and R>0 without requiring
X>0. Hence b>0. Also |i|>=1, c>1 and Delta>1 give

    |S|>1, Q>2, d>0, D<S^2.

Define the sign-safe polynomial bound

    W=2d*((S*i)*(v*T)+b).

This is positive on the whole mixed domain. Indeed

    S*i=Delta i^2 c^2>=|S|,
    v*T=cT^2>=|v|.

For each real root f' with (f')^2=D, one has |f'|<|S|. If
`rho'^2=d(e-Bf')`, then

    rho'^2=d[Q(vf'-b)^2-1]
       < dQ(|S||v|+b)^2
       < 2d^2(|S||v|+b)^2
       < W^2.

Thus |rho'|<W. This proof explicitly covers negative i and T. It is not
valid to retain the cheaper positive-domain expression `2d(Sv+b)` in
this mixed-domain polynomial, because Sv can have either sign.

If B=0, then b,Q are positive so v=0 and T=0. The resultant branch is
`rho'^2=de=d(Qb^2-1)`, and the same strict bound follows directly. Thus
the bound remains available before T is known nonzero.

## 3. The resultant branch when B may vanish

Choose real tau,g with tau^2=A1, g^2=A2 for a vanishing formal factor and
put

    rho=(Z-u tau-Kg)/H.

The defining factor gives

    (rho^2-de)^2=d^2 B^2 D.

If B is nonzero, define

    f=(de-rho^2)/(dB).

Then f belongs to the totally real multiquadratic field Q(tau,g),
f^2=D, and rho^2=d(e-Bf). Every field conjugate satisfies the strict
bound in Section 2. If B=0, one instead has rho^2=de and the same bound
for every conjugate without ever defining or dividing by f.

## 4. Exclude w0=0 before using the first separation inequality

Assume w0=0. Then X=E=Lfirst=0 and A1=1, so tau is already the integer
+1 or -1. The first separation inequality is unnecessary and must not
be invoked, since A2<16A1 need not hold at this boundary.

The second inequality always holds: K sqrt(A2)>HW. Therefore any
automorphism changing the sign of g would change Kg by more than the
maximum possible change 2HW of H rho, while u tau is fixed. This
contradicts the rational equation Z=u tau+Kg+H rho. Thus g is rational,
hence integral, and rho is rational.

If B is nonzero, f is now rational and f^2=D is integral, so f is integral.
Then rho^2=d(e-Bf) is integral, which makes rational rho integral. If B=0,
rho^2=de is integral directly and gives the same conclusion.

Set gamma=(g-X-ac)/H. Its denominator divides H. The linear relation is

    K gamma=t-M tau-rho,

whose right side is integral. Because K=1 modulo H, gamma is integral.
But at X=0 the main equation now reads

    (ac+H gamma)^2-(a^2+H)c^2=1.

Reduction modulo H gives 0=1 modulo H, impossible since H>1. Therefore
w0 is nonzero and w=w0^2>0. This closes the zero-square branch without
assuming an unavailable first-root growth estimate or dividing by B.

## 5. Recover the outer roots and exclude T=0

With w>0, X>=q>=16 and the source weak packing inequalities apply:

    0<R<E-2, a>R+2, Delta>R.

Now both separation inequalities in Section 1 hold. They force tau and
g to be rational, hence integral. Then rho is rational. The B=0 and
B!=0 arguments from Section 4 show that rho is integral in either case,
and the same linear congruence proves gamma integral.

Suppose T=0, so v=B=0. Then y=rho/d is rational and

    Qb^2-(Q-1)y^2=1.

Since Q=S^2, the rational auxiliary Pell saturation lemma applies with
the positive integer |S|>1 and V=b, proving that y is an integer.

The expression b satisfies 1<b<Q before any strong Pell classification:

    Q-b=(Delta-R)D-Delta-c
       >=D-Delta-c
       =1+Delta(i^2 c^4-1)-c>0.

Here Delta-R>=1, |i|>=1 and c>1. Rearranging the auxiliary equation gives

    (Q-1)(y^2-b^2)=b^2-1>0.

Thus |y|>=b+1, and consequently

    b^2-1 >= (Q-1)(2b+1) >= b(2b+1) > b^2-1,

a contradiction. Hence T!=0 and B!=0. This exclusion uses rational Pell
saturation first, not an unjustified assertion that rational y must
already be an integer.

## 6. Final reconstruction and soundness

The now valid formula `f=(de-rho^2)/(dB)` gives an integer f with f^2=D.
Set y=rho/d and V=vf-b. The factor equation gives

    S^2 V^2-(S^2-1)y^2=1.

Since y is rational and |S|>1, saturation again proves y integral. Thus
all six normalized source equations are restored, with seven positive
ports, nonzero odd i, square w, and otherwise signed f,h,T,tau,y,gamma.

This is exactly the enlarged domain proved in
`integers/upstream/14-integer29/proofs/signed_domain_proof.md`, not merely
the earlier nine-positive-port domain. Its signed rank, no-wrap and main
root arguments establish the correct compiler predicate and, for the
product, force epsilon=+1. No sign of any eliminated root is silently
inserted into an affine relation.

## 7. Completeness and coefficient compatibility

Package 14 provides canonical witnesses with odd normalized i and square
w. Its proofs are existence-preserving choices, not claims about every
old witness tuple:

- Choose the auxiliary index m=cR. Canonical c and R are odd, and the
  binomial expansion of the Pell unit at index R to the c-th power gives
  c^2|psi_A(cR). Since A=a+2 is even on the canonical dyadic witnesses,
  psi_A(m) is odd for odd m; hence i=psi_A(m)/c^2 is odd and positive.
- The canonical space/time dimensions can both be powers of five, making
  their product N odd. The fixed cell-bit exponent dcell is also a power
  of five. Thus q=2^ell with ell=dcell*N odd. Since canonical R is odd,
  w=2^(R-ell) is a positive integer square.

The new four-site coefficient recipe changes the source cell-bit exponent
from 5^67 to 5^28, but it remains odd. Its coefficient-reduction proof
explicitly preserves the five-adic correction, native mask low bits, and
the original completeness hypotheses. Therefore the square-w and odd-i
completeness restrictions remain compatible with that recipe; no claim
that the old numerical exponent 5^67 was retained is necessary.

Keep these canonical witnesses and set

    t=M tau+K gamma+d y.

It is an integer (indeed positive on the canonical positive witnesses),
and the defining resultant factor vanishes. No period or further index
restriction is introduced by this final construction.

## 8. Why the unrestricted integer count is twenty-six

For each of the seven positive ports substitute a separate three-integer
surjection

    Pos(x,y,z)=1+x(x+1)+y^2+z^2.

This is positive for all integer triples and represents every positive
integer by the standard three-square argument. Leave h,r,T,w0,t free.
The total is therefore `7*3+5=26` unrestricted integers. Every such tuple
produces the audited mixed domain; every positive-port solution has a
preimage under the seven independent surjections. This proves both
directions of the variable-count conversion, not only positivity.

## Verdict

The final lower-degree weights, sign-safe bound, w0=0 boundary argument,
T=0 exclusion, and twenty-six-integer conversion are valid, conditional
on the cited exact compiler and package-14 signed-domain theorems. The
explicit divisibility and parity arguments above identify the needed
completeness assumptions. Circuit degrees and operation counts must
still refer to the final generated JSON and its independent checks.
