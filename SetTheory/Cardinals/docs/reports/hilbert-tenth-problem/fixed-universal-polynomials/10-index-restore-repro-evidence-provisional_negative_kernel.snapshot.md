# Provisional negative-index kernel family

Status: independently unreviewed proof proposal. This concerns the ENTIRE TEN-EQUATION PELL KERNEL with a signed index R. It does NOT satisfy or purport to satisfy the complete source's outer packing, compiler, or input equations. It is not a positive reduced child zero and not a universal-theorem counterexample. No upstream code was executed and no giant witness was materialized.

Source pin for all imported Pell constructions: VladimirReshetnikov/ProveIt, commit `2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff`, `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/pell_kernel_half_binomial42.md`, Sections 1, 3, 6; and `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md`, Sections 2–3. The kernel equations and conventions are also written in `provisional_bootstrap.md` in this directory.

## Claim

There are infinitely many assignments with q=16, X=wq^3, Y=sq^3, and every supplied kernel coordinate OTHER THAN R strictly positive, satisfying all ten retained kernel equations, with R<0. X,Y may be held fixed throughout this family. Therefore the ten-equation kernel and the common scale hypotheses alone cannot imply R>0. Any proof for the complete reduced child must use additional outer/input equations.

## 1. Fix a small exact common-scale context

Take q=16, p0=15, X=2^15=32768 and Y=2^12=4096. Then q^3=2^12 divides both X and Y; the actual positive scale witnesses are w=8 and s=1. Set

    E=XY, a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    P=2XY^2+1.

Here E=2^27, a=134221824, A=134221826, H=536887299 and P=2^40+1. Thus A is even, H is odd, and X<H. Also P>A and P<chi_A(2)=2A^2-1.

No compiler constants, outer words, or ordinary input are claimed in this construction. The choices above only provide actual common-scale kernel parameters.

## 2. Two genuinely independent Pell growth rates

Let

    alpha=log(A+sqrt(A^2-1)), beta=log(P+sqrt(P^2-1)).

Delta is odd. In contrast

    P^2-1=4XY^2(XY^2+1)

has odd 2-adic valuation 2+15+24=41. Thus the squarefree parts of Delta and P^2-1 are different. The two real quadratic fields are distinct and intersect in Q. If alpha/beta were rational, positive integer powers of their two norm-one units would agree. The common value would be rational; a positive rational norm-one unit is 1, contradicting growth. Therefore alpha/beta is irrational.

Let T=lcm(4,2E,ord_H(2)) and L=E/2. Choose n0=L-7=67108857, so

    2n0 = 1-p0 mod E.

Consider p=p0+T*u and n=n0+L*v. For all these pairs,

    p=3 mod4,
    2^p=X mod H,
    2n=1-p mod E.

The quotient T*alpha/(L*beta) is irrational. Density of an irrational rotation therefore gives infinitely many arbitrarily large positive u, with corresponding positive integer v, for which

    psi_A(p)/(2psi_P(n)) lies strictly between Y and Y+1.

For completeness, use an open interval strictly inside (log Y,log(Y+1)). The logarithm of this quotient differs by a quantity tending to zero from

    p*alpha-n*beta+log(sqrt(P^2-1)/(2sqrt(Delta))).

Reduce that affine expression modulo L*beta. Irrational rotation of u hits the chosen interval infinitely often; v is the corresponding integer translate. Since both alpha,beta>0, v grows positively with u. Taking sufficiently large hits absorbs the vanishing Binet-form error. This is an existence proof using density, not a claim that a finite search found such pairs.

## 3. First/main equations and negative index

For any sufficiently large pair from Section 2, put

    c=psi_A(p), D=chi_A(p),
    k=2psi_P(n), tau=chi_P(n),
    eta=c-kY, zeta=k-eta,
    gamma=(D-ac-X)/H,
    R=-p, h=(k+p-1)/E.

The strict quotient interval makes eta,zeta positive integers. The main projection recurrence gives D-ac=2^p mod H, so gamma is integral. It is positive because D-ac=2c-psi_A(p-1)>c>X for sufficiently large p.

Since P=1 mod E, psi_P(n)=n mod E. The chosen congruence 2n=1-p mod E makes h integral and positive. It gives exactly k=R+1+hE with R=-p<0. The first norm is tau^2-XY^2(XY^2+1)k^2=1, and the main norm is D^2-Delta*c^2=1. Thus all first/main equations, both positive ratio slacks, and the main projection equation hold.

## 4. All strong auxiliary equations, with positive witnesses

Because p is odd, c=psi_A(p) is odd. Put m=c*p, which is odd, and define

    f=chi_A(m), Qaux=Delta*psi_A(m), i=Qaux/c^2.

The binomial expansion of (D+c*sqrt(Delta))^c shows c^2 divides psi_A(pc): its linear term is c^2*D^(c-1), and all higher odd terms contain at least c^3. Thus i is a positive integer and Qaux=i*c^2. The strong norm Qaux^2=Delta(f^2-1) is immediate.

Choose an odd positive auxiliary index saux=p+2m. Since p=3 mod4 and m is odd, saux=1 mod4. Let baux=(saux-1)/2, which is even, and put

    U=chi_Qaux(saux)/Qaux, y=psi_Qaux(saux).

The odd-quotient polynomial identity makes U a positive integer. Modulo c, its constant-term identity gives U=saux=p mod c. Modulo f, the identity at 1-A^2 and the 2m shift give

    U=psi_A(saux)=-psi_A(p)=-c mod f.

Therefore

    j=(U-p)/c, o=(U+c)/f

are integers. They are strictly positive by elementary Pell growth (U>c>p). Since R=-p, their equations are precisely U=jc-R=of-c. The Pell norm at Qaux gives Qaux^2(U^2-y^2)=1-y^2. This verifies every remaining kernel equation and every supplied auxiliary positivity condition.

## Limitation that must remain explicit

The complete74 reduced source also requires an actual compiler packing equation, transport, and input norm. None of those have been supplied here. The construction is a theorem about a subsystem and identifies where a complete positivity proof must obtain extra information. It is not a full positive zero of raw29, positive21, or signed19, and establishes no false acceptance or change in universal bounds.
