# Provisional positive-index bootstrap, 2026-10-03

Status: independently unreviewed mathematical partial result. This is not a proof that the restored index is positive, not a counterexample, and not a new universal bound. No upstream code was executed. Only targeted public text/JSON was read.

## Source pin

All links below use repository VladimirReshetnikov/ProveIt at commit `2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`.

Let Q denote `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` and H denote `Computability/HilbertTenthProblem/Papers/1980/`.

1. Q/review_complete74_nonlinear_index_projection.md: exact child graph identity, intended strictly positive supplied domains, remaining R positivity obligation
2. Q/complete74_factored_first_norm.json: literal three parent schedules, equations, witness lists; its recorded source SHA256 is `7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908`
3. Q/complete74_nonlinear_index_projection_scout.md: substitution R=actual_k-h*UM-1 in packing and auxiliary argument, paid retained gates
4. Q/complete75_signed_projection_elimination101.md, Sections 1–2: exact signed definitions and mask remainder
5. Q/pell_kernel_half_binomial42.md, Sections 3–4: first-norm classification and retained rank/step-down use
6. H/PELL_RELAXED_AUXILIARY_PROOF.md, “The relaxed norm forces an integral Pell solution at A” and “Recovering the required divisibility of the auxiliary index”: generic strong-rank argument
7. H/HALF_PARAMETER_PELL_92_PROOF.md, Sections 3–4: odd-quotient polynomial identities and signed step-down
8. H/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md, Sections 2–3: stronger plus-sign step-down and sign retention
9. Q/complete75_asymmetric_scale_tradeoffs.md, Sections 1–3: comparison only; its F+Z<q hypothesis is NOT available here

Pinned root URL: https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/

## Exact common equations on a positive child zero

Every complete SOS zero over the integers makes each retained residual zero. The reviewed graph identity restores an integer parent zero at R=k-hE-1, with no assertion about the sign of R. In all modes the retained equations then imply:

    q=(B-1)J+1 >= B >=16
    X=w*q^3, Y=s*q^3, E=X*Y
    k=eta+zeta, c=kY+eta, a=Y(X+1)
    A=a+2, Delta=A^2-1=a^2+4a+3, H=4a+3
    D=X+ac+gamma*H, D^2-Delta*c^2=1
    tau^2-XY^2(XY^2+1)*k^2=1
    k=R+1+hE
    Qaux=i*c^2, Qaux^2=Delta*(f^2-1)
    U=j*c-R=o*f-c
    Qaux^2*(U^2-y^2)=1-y^2

All of q,X,Y,E,k,c,a,A,Delta,H,D,tau,eta,zeta,i,f,h,j,o,y,gamma are strictly positive. R and U have not yet been assumed positive. In raw30, q,a,c,D,k,gamma are supplied and the retained comparisons establish these identities. In positive22/signed20, the relevant triangular definitions compute the same values. Signed20 has gamma=rho+sigma>0; the other modes use supplied ga>0. Mathematical A is a+2; the source register named A is Delta. Qaux is not the outer repunit J, input rho, or restored index R.

## Proposed lemma 1: main projection supplies a large index without R>0

The main positive Pell norm has c=psi_A(p), D=chi_A(p), p>=1. (The fundamental unit of Delta=A^2-1 is A+sqrt(Delta).)

Put z_p=chi_A(p)-a*psi_A(p). Its initial values are z_0=1,z_1=2 and it has recurrence z_(p+2)=2A*z_(p+1)-z_p. The sequence 2^p satisfies that recurrence modulo H because 4A-1=H+4. Thus

    X = z_p mod H = 2^p mod H.

Since 0<X<a<H, there is an integer ell>=0 such that 2^p=X+ell H. In particular p>=ceil(log_2 X). As X>=q^3>=4096, p>=12. This argument uses no packing, no first-index representative bound, no R positivity, and no exponent no-wrap conclusion. It does NOT assert ell=0.

## Proposed lemma 2: all generic strong-rank hypotheses now hold

For A>=2, ordinary Pell growth gives c=psi_A(p)>=(2A-1)^(p-1). With p>=12, this is greater than A*Delta^2 and greater than 2p. The strict c>A*Delta^2 requirement is the numerical hypothesis used in source 6's generic rank argument; its old a+4 convention plays no role in that argument once A and Delta=A^2-1 are given.

Together with Qaux=i*c^2>0, f>0, and Qaux^2=Delta(f^2-1), that argument yields

    f=chi_A(m), p|m, c|m, Qaux=Delta*psi_A(m), m>=c>2p.

Then f>=chi_A(2p)=1+2Delta*c^2>2c. Consequently the actual retained linear equation proves

    U=of-c>=f-c>c>0.

This supplies auxiliary-root positivity without assuming R>0 or c>R.

## Proposed lemma 3: rank congruence and odd p, without an index bound

Qaux>1 and the auxiliary norm give a positive index s with

    Qaux*U=chi_Qaux(s), y=psi_Qaux(s).

Since Qaux divides the root, s is odd. Write s=2b+1. The integer polynomial identity from source 7 is

    U=Q_b(Qaux^2)
    Q_b(0)=(-1)^b*s
    Q_b(1-A^2)=(-1)^b*psi_A(s).

Modulo f, use Qaux^2=1-A^2 and U=-c. Squaring and the Pell doubling identity gives chi_A(2s)=chi_A(2p) mod f. The stronger plus-sign step-down (source 8, Section 2) applies because 0<2p<m, f=chi_A(m), A>=2. It gives

    2s=+/-2p mod 4m, hence s=+/-p mod 2m.

Therefore p is odd, strengthening p>=12 to p>=13. Since c|m and Qaux is divisible by c, the first Q_b identity and U=-R mod c imply

    R=+/-p mod c.

No bound on R was used. This congruence alone does not imply R=p or R>0.

## Proposed lemma 4: first/main index interval independent of R

Put P=2XY^2+1. First-norm classification gives k=2psi_P(n), n>=1. P>A, and c>k, imply n<p. Also set P2=chi_A(2)=2A^2-1. One has P2>P and A>Y+1. If p>=2n then

    c>=psi_A(2n)=2A*psi_P2(n)>=2A*psi_P(n)=A*k>k(Y+1),

contrary to c=kY+eta and 0<eta<k. Thus

    (p+1)/2 <= n <= p-1.

The first-index identity only supplies 2n=R+1 mod E. It cannot be replaced by equality without a fresh no-wrap argument.

## Scope of the remaining obstruction

The packing remainder still proves R<q^4 and R!=0, without R>0. It gives no lower bound on R in signed20 because supplied Z may be arbitrarily large before the input-root sign is controlled. The new bootstrap proves that the retained rank machinery is available, but negative representatives R=+/-p-t*c have not been excluded.

For raw30/positive22, W>0 and C=Z+W<q give Z<q, while transport gives F<(K0+X)q. Hence one has the safe rough bound -R<q^3+(K0+X)q^4 when R<0. Further use of a claimed K0<B^2 bound requires checking the exact compiler export; no such bound is assumed in the proposed common lemmas above.

The asymmetric-scale proof starts from C=q-F-Z-alpha-2dx and obtains F+Z<q. Its conclusion R>0 must not be imported to the current C=q-alpha-2dx source.

No full positive child zero with R<=0 has been constructed.
