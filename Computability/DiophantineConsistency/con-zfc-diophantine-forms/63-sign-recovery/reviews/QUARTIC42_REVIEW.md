# Independent arithmetic audit of the 42-integer quartic adapter

This is an internal AI-assisted mathematical review, not an external peer review or a proof-assistant certificate. Reviewed against ProveIt snapshot `beb0192cb8` and the literal source `57-separated-degrees/quartic/quartic45.json`.

## Exact proposed change

In the literal 45-variable source, replace the residual `w-u**2` by `w-4*u**2`. Delete the two residuals representing eta and zeta separately as positive numbers and their six private positivity variables. Introduce three new free integers a_eta, b_eta, t_eta and the single quadratic residual

    eta*zeta - (1+a_eta^2+b_eta^2+t_eta*(t_eta+1)).

Retain every other residual. This gives 42 unrestricted integer variables and 27 quadratic residuals. Their sum of squares has exact total degree four: the monomial tau^4 has coefficient one, since tau occurs only quadratically in its single source residual.

## Guard consequences

The retained dyadic guard `beta*J+1=2*q_half_root^2`, with beta>=3, forces J>0 and q=beta*J+1>=16. The two retained simplex guards F*alpha>0 and F*(q-F-alpha)>0 give F, alpha, C=q-F-alpha>0: all three have a common sign and sum to q>0.

The new product guard gives eta*zeta>0. Put delta=sign(eta)=sign(zeta), eta0=abs(eta), zeta0=abs(zeta), K=eta0+zeta0>=2. Thus k=eta+zeta=delta*K and 0<eta0<K. Retain s=2*v_scale+1 and i=2*r+1, both odd and nonzero.

The source's constant bounds and these simplex facts imply q*(q^2-1)<R<q^4-2 independently of the sign of the literal transport coordinate z. All four coefficients must be bound together to the authentic source tuple.

## Zero scale and strengthened modulus

Set X=w*q, Y=s*q^3, E=X*Y, a=(X+1)*Y, H=4*a+3 and Delta=(a+2)^2-1. Initially w=4*u^2>=0. If w=0, X=0 and D=a*c+gamma*H. The retained main norm D^2-Delta*c^2=1 reduces modulo H to 0=1. But abs(Y)>=q^3 and H=4*Y+3 has abs(H)>1, a contradiction. Hence w>=4 and X>=4*q.

Let M=abs(E)=X*abs(Y). Then

    M>=4*q^4>3*R+1.

The strict last inequality follows from R<q^4-2. This is the new numerical margin needed to remove the common negative sign.

## Uniform Pell recovery before fixing signs

Write Z=abs(Y), B=abs(a+2), P0=2*X*Y^2+1, c0=abs(c). In either sign of Y, B>=2, Delta=B^2-1 and B>M>R.

If Y>0, c=delta*(K*Y+eta0), so K*Z<c0<K*(Z+1). If Y<0, c=delta*(-K*Z+eta0), so K*(Z-1)<c0<K*Z. Consequently c0>K in both cases. Also P0>B, by direct expansion using X>=4*q and Z>=q^3.

The first Pell equation is tau^2-X*Y^2*(X*Y^2+1)*k^2=1. Its fundamental unit gives

    abs(k)=K=2*psi_P0(n), n>=1.

The main Pell equation gives c0=psi_B(p), abs(D)=chi_B(p), p>=1. Since P0>B and c0>K, monotonicity gives p>n.

The retained index equation gives k=R+1+h*E. Since P0=1 modulo M, psi_P0(n)=n modulo M. Hence

    2*delta*n = R+1 modulo M.

For delta=+1 this implies n>=(R+1)/2. For delta=-1 it implies n>=(M-R-1)/2>R. In either case n>=24 and p>=25. In particular:

    c0>B*Delta^2, c0>2*p, c0>2*R.

For the first two bounds, the elementary estimate psi_B(p)>=(2*B-1)^(p-1), with B>=2 and p>=25, is more than sufficient. For the third, c0>=psi_B(2)=2*B>2*R.

## Signed ordinary-rank recovery is unaffected by sign(c)

The unchanged quadratic rows assert rho^2=Delta*(f^2-1), rho=abs(i)*c0^2, and

    rho^2*V^2-(rho^2-1)*y^2=1,
    V=o*f-c=j*c-R.

The relaxed ordinary-Pell-rank lemma applies with the positive pair (B,c0), because c0>B*Delta^2. It yields f0=abs(f)=chi_B(m), p|m, c0|m and m>2*p. These hypotheses do not require c>0.

The two exposed-quotient rows give V=-c modulo f0 and V=-R modulo c0. The auxiliary odd-index quotient argument squares the first congruence, so replacing c by -c has no effect. It yields ell=+p or -p modulo m, while the second gives ell=+R or -R modulo c0. Hence R=+p or -p modulo c0. Since 0<R,p<c0/2, this forces p=R.

Thus delta=-1 is impossible: that branch had n>R while p>n and p=R. We conclude eta,zeta>0 before invoking any theorem that requires their positivity.

## Recover the remaining source domain

Once eta,zeta>0, the exact inherited negative-odd-scale proof applies unchanged to exclude s<0. It uses the same first and main Pell equations, exposed V congruences, and outer packing bounds, all now established. The new scale restriction w=4*u^2 is stronger than its required nonzero square condition.

Positive-scale signed recovery then supplies the usual positive main-root choice and X=2^R. Consequently w=2^R/q>q>F.

CAUTION: the literal source transport residual is

    (K0+w)*C-F-z*(q-1)=0,

not `(K0+w)*C-F-(z-1)*(q-1)=0`. The source QUARTIC45_PROOF.md states the latter, apparently carrying over an unshifted coordinate convention. Direct expansion of row 14 of quartic45.json proves the former. Our proof must use the literal shifted coordinate. Since (K0+w)*C>F and q-1>0, the literal equation now gives z>0. Its unshifted transport counterpart is z_old=z+1.

Thus every original guarded coordinate is positive, and the arithmetic variables satisfy the original source system with old square witness 2*u. Supply positive ternary representations for eta and zeta to obtain a source quartic45 zero. The inherited native compiler/refutation calibration then applies. No assumption that ZFC is consistent is used.

## Completeness

Use the canonical positive source witness supplied by the inherited compiler. Its q=2^t has t odd, its rank R is odd (indeed R=3 mod4), and w=2^(R-t). The packing bound gives R>t+2. Therefore R-t-2 is a nonnegative even integer and

    u_new=2^((R-t-2)/2)

is an integer satisfying w=4*u_new^2. All other arithmetic coordinates are unchanged. Since eta*zeta>0, its value is represented by Pos(a_eta,b_eta,t_eta)=1+a_eta^2+b_eta^2+t_eta*(t_eta+1), by the same Legendre three-square argument used in the source. This supplies the new three guard variables. The dyadic and simplex guard witnesses are retained. All 27 new residuals vanish.

## Audit conclusion and boundary

The new arithmetic reduction is valid, provided the exact inherited ordinary-rank, signed auxiliary step-down, negative-odd-scale and compiler results are used with their stated hypotheses. Every additional sign hypothesis has been established before the respective theorem is invoked. The weakened eta/zeta guard is compensated by the strictly stronger square scale w=4*u^2, which is complete on canonical witnesses.

The conclusion is an ordinary mathematical existence equivalence, internalizable in ZFC. Finite symbolic checks certify residual transcriptions, degree and counts; they cannot certify Con(ZFC), and this audit is not a new end-to-end Lean/Rocq proof.
