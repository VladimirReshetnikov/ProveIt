# Free-coefficient 83: a weakened rank condition and an infinite nonnative inner family

## Status and source boundary

This is a rigorous reduction and an inner-kernel counterfamily, **not a counterexample to the ordinary-input language**. No unchanged genuine compiler is shown to accept a rejected input. The established bound remains 84. The candidate here is the free-coefficient 83=46M+37A, degree-111, 18-positive-witness source at commit `0d9d1e0174df30d82d80d758e9ba8e793203126e`, not Report 41's first-index deletion.

The exact upstream scout and its saved source were read as data; no upstream Python or saved arithmetic schedule was executed. A targeted file-history read found no later change to this scout on 2026-10-03. The essential source meanings are

    q=(B-1)J+1, X=wq, Y=sq^3, E=XY,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    k=eta+zeta, c=kY+eta,
    D=X+ac+(rho+sigma)H,
    R=(q^2-Z-qF)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    C=q-F-Z-alpha-ell*x, W=C-Z,
    Nt=(K+w)C+q-F-t(q-1),
    V=c(Tf-1)-Rf^2,
    Na=S^2(V^2-y^2)+y^2, Ns=Delta*f^2-S^2.

Here `ell=twice_cell_bits`, `K=Kconstant`, and `MF` is the **shifted source numeral**. The complete output is N0*N1*N2*Na*Nk*Nt*Ns-Delta. Its five unchanged factors N0,N1,N2,Nk,Nt are the first, main, input, index and transport factors. A generic zero has not been normalized into these intended factor values.

## 1. A general auxiliary-completion theorem

**Theorem.** Let A>=2, let p>=3 be odd, and put c=psi_A(p), D=chi_A(p), Delta=A^2-1. For any R>0 satisfying

    gcd(c,p) | R,                                      (1)

there are positive integers f,S,T,y such that the literal new auxiliary and strong factors satisfy Na=1 and Ns=Delta. This does not require p=R.

**Proof.** Set

    f=chi_A(2p), b=psi_A(2p)=2Dc, S=Delta*b.

Then f^2-Delta*b^2=1, so Ns=Delta, f^2=1 modulo c, and gcd(c,f)=1. Also c|S. The parity recurrence gives c odd. Set j=3 if p=1 modulo4, and j=1 if p=3 modulo4. Solve

    z=j*p modulo 8p,     z=R modulo c.                (2)

The gcd of these moduli is gcd(c,p), and j*p is divisible by that gcd. Thus (1) is exactly the compatibility condition for this CRT pair. Choose a positive solution z. It is 3 modulo4. Put v=(z-1)/2, which is odd, and

    V=chi_S(z)/S=Q_v(S^2), y=psi_S(z).

The integer quotient polynomial satisfies

    Q_v(0)=(-1)^v z, Q_v(1-A^2)=(-1)^v psi_A(z).

Consequently V=-R modulo c. In the quadratic ring modulo f, Pell duplication gives (chi_A(4p),psi_A(4p))=(-1,0) and (chi_A(8p),psi_A(8p))=(1,0). Hence psi_A(z)=psi_A(jp) modulo f. For j=1 this is c; for j=3 it is (2f+1)c, also c modulo f. Since S^2=Delta(f^2-1)=1-A^2 modulo f and v is odd, V=-c modulo f.

It follows that

    T=(V+c+R*f^2)/(c*f)                               (3)

is a positive integer. Its numerator is divisible by f using V=-c modulo f, and by c using V=-R modulo c and f^2=1 modulo c. The moduli c,f are coprime. Formula (3) is precisely the supplied-witness identity V=c(Tf-1)-Rf^2. Finally the Pell norm at S gives S^2 V^2-(S^2-1)y^2=1. This is Na=1. All divisions define existential witnesses and are not new circuit instructions. QED.

The forced inverse of the deleted row is i=S/(Delta*c^2)=2D/c. This is nonintegral because c is odd, c>1, and gcd(c,D)=1. Unlike the upstream extensions at p=R, this theorem also supplies the auxiliary block when p differs from R, provided (1) holds. It does not itself produce a full zero: the five untouched factors must still be supplied.

## 2. An infinite family with all the inner constraints, including the retained first-index equation

Let j>=0 and define

    u=11^(12j+1), p=247u, n=208u, R=416u-1,
    X=2^p, Y=2^(57u-1), E=XY,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    P=2XY^2+1,
    D=chi_A(p), c=psi_A(p), tau=chi_P(n), k=2psi_P(n).

Here R>p and 2n=R+1 exactly. Both Pell norms are 1:

    D^2-Delta*c^2=1,
    tau^2-XY^2(XY^2+1)*k^2=1.

### Strict ratio

Write L0=2XY and M0=4XY^2. Direct exponent arithmetic gives

    L0^(p-1)=2Y*M0^(n-1),                            (4)

because p(p-n)=(57u)(2n-p). Also

    2A-1=L0*(1+1/X+3/(2XY)),
    2A=L0*(1+1/X+2/(XY)),
    2P=M0*(1+1/(2XY^2)), 2P-1>M0.

For r>=3 the standard bounds (2A-1)^(r-1)<=psi_A(r)<(2A)^(r-1) imply c/(kY)>1: the numerator perturbation base exceeds the denominator perturbation base and p>n. For the upper bound put epsilon=1/X+2/(XY)<2/X. Since (p-1)epsilon<1/2,

    c/k-Y < 4pY/X = 494u*2^(-190u) < 1.              (5)

The geometric-series estimate (1+epsilon)^h<=1/(1-h*epsilon)<1+2h*epsilon justifies the bound. The final inequality follows, for example, from u<=2^(u-1). Therefore

    eta=c-kY>0, zeta=k-eta>0,
    k=eta+zeta, c=kY+eta.

Since P=1 modulo E, psi_P(n)=n modulo E. Thus

    h=(k-2n)/E=(k-R-1)/E

is a strictly positive integer, and the **retained** index factor Nk=1. This is not a first-index deletion.

### Main projection

Let z_r=chi_A(r)-a*psi_A(r). Then z_0=1,z_1=2, and z_r obeys the Pell recurrence. Since 4A=H+5, the sequence 2^r obeys that same recurrence modulo H. Therefore z_r=2^r modulo H. In particular

    gamma=(z_p-X)/H

is integral and positive. Positivity follows from p>=3 and the elementary growth z_(r+1)>(2A-1)z_r for r>=1, together with A=Y(X+1)+2. Hence the literal main projection D=X+ac+gamma H also holds.

### Coprimality for every parameter

The only prime divisors of p=247*11^(12j+1) are 11,13,19. Let

    L=lcm(12,18,13*(13^2-1),19*(19^2-1))=622440.

Direct integer arithmetic gives 11^12=1 modulo L, so u=11 modulo L. For l=13,19, this fixes both A modulo l (through the exponents defining X,Y) and p modulo l(l^2-1). The Pell companion matrix has determinant 1 and its order divides |SL2(F_l)|=l(l^2-1). At u=11 the exact residues are

    modulo13: A=4,  psi_A(p)=1;
    modulo19: A=11, psi_A(p)=18.

They persist for every j. For l=11, u=1 modulo10, so A=8 and Delta=8 modulo11. The quadratic-ring Frobenius identity is

    psi_A(11r)=Delta^5*psi_A(r) modulo11.

Here Delta^5=-1 and psi_8(247)=10 modulo11. Since 12j+1 is odd, psi_A(p)=1 modulo11. Thus gcd(c,p)=1 for every j. Section 1 supplies positive f,S,T,y at the actual R=416u-1, completing the auxiliary and strong factors with p different from R.

This is an infinite **inner-kernel** counterfamily. R is a target port at this stage; it has not yet been identified with an actual compiler's packed expression. X,Y are positive dyadic scales; a compatible q can be selected only subject to the remaining outer constraints below.

## 3. Input loading does not add a new inner obstruction

Fix any genuine compiler and ordinary x>=1. Put I=ell*x+b and W=2^I, where b=inner_bits is odd. For any member of Section 2 with p>I, take

    kappa=psi_A(I), mu=chi_A(I),
    delta=(kappa-I)/Delta,
    rho=(z_I-W)/H, sigma=gamma-rho.

The odd-index congruence psi_A(I)=I modulo Delta makes delta integral; it is positive for I>=3. The projection recurrence makes rho integral and positive. Because p>I and z grows by a factor greater than 2A-1 at each step of index at least 1,

    z_p-z_I > X,

so sigma=(z_p-z_I-X+W)/H is positive. These values satisfy the exact input norm and its shared rho/sigma projection. This uses no accepted input, no native history and no mask decoding.

It remains necessary to realize the register W as C-Z with the actual positive F,Z,alpha and to satisfy both outer equations. The next section states those conditions exactly.

## 4. A two-integer genuine-compiler interface

Keep **all six genuine fixed numerals unchanged**, and fix x. Let u be from Section 2. Choose t=dN with N>=1, q=2^t=B^N, and require

    3t<=57u-1, p>I.

Then w=2^(p-t), s=2^(57u-1-3t) are positive integers and X=wq,Y=sq^3. Write

    J=(q-1)/(B-1), Q=q^2-1, M=(MC+q MF)J,
    e=p mod t, 0<=e<t.

The construction realizes its prescribed packed R and intended transport factor Nt=1 with positive remaining outer witnesses if and only if F,Z satisfy

    R=M modulo Q,                                    (6)
    G=(R-M)/Q=q^2-Z-qF,
    F=(K+2^e)(W+Z) modulo q-1,                       (7)
    F>=1, Z>=1, F+2Z+W+ell*x<q.                     (8)

In particular Z is the unique integer in 1,...,q-1 congruent to -G modulo q, if such a nonzero residue exists; F=(q^2-Z-G)/q is then forced. Set

    alpha=q-F-2Z-W-ell*x,
    transport_quotient=1+((K+w)(W+Z)-F)/(q-1).

Condition (7) makes this quotient integral, because w=2^e modulo q-1. It is positive: the scale inequality implies p>2t and w>q, while 0<F<q and W+Z>=1. Equation (8) makes alpha positive. All 18 supplied source coordinates are now specified and positive, all six unchanged/unit factors are 1, Ns=Delta, and hence the complete 83 polynomial is zero.

Conversely, any realization of the Section 2 family with these chosen q and W, the prescribed value R=416u-1, and Nt=1 must satisfy (6)--(8), since these are literal rewritings of packing, transport and alpha positivity. Thus this is an exact residual interface for the intended-factor completion of this family, not a heuristic simplification. It is not asserted to classify accidental product zeros obtained by abandoning the prescribed R or Nt value.

**Unresolved:** no pair (j,N) satisfying (6)--(8) has been proved for a known rejected input under a genuine fixed compiler. The divisibility and congruences are real restrictions. For example J|R follows from (6). For the inherited d an odd power of5 with 5|d, an even N gives 11|J, whereas R=416u-1=-1 modulo11; hence even N is impossible for this particular family. Also B has order3 modulo7 because d is a power of5, so 3|N implies 7|J. But u=4 modulo7 and R=4 modulo7. Thus 3|N is impossible too: every completion in this family must have gcd(N,6)=1. These obstructions must not be hidden by replacing the mask ports with arbitrary numerals.

## 5. What this changes, and what it does not

The free-coefficient branch cannot recover p=R from the first/main/index/auxiliary/strong inner block alone: Section 2 is an explicit infinite counterfamily, even with the main projection and with ordinary input loading available. A soundness proof must use the genuine outer packing/transport arithmetic in a substantially new way, or rule out the family through those constraints. The generic product-divisor/sign branches remain a separate open task.

The residual interface (6)--(8) gives a concrete, finite-modular target for the next stage. Proving one solution at a rejected x completes a language counterexample. Proving it impossible only for this family would not establish language soundness. No new universal operation bound, full positive compiler zero, or rejection certificate is claimed here.

## 6. Why a simple prime-existence shortcut does not close the interface

Replacing the power-of-11 parameter by suitable primes u can simplify the local gcd condition, but it does not presently prove outer completion. The packing congruence (6) is

    416u = M+1 modulo q^2-1.

After removing gcd(416,q^2-1), its modulus is of order q^2, rather than the smaller repunit J. The genuine packing interval has R<q^4, so this supplies only a range quadratic in that modulus. Ignoring the factor q^2-1 would give a misleadingly favorable prime-progression estimate.

Transport further restricts candidates. On the unwrapped branch F=L(W+Z), with L=K+2^e fixed after selecting e, packing is

    R = Q*(q^2-qLW-(1+qL)Z)+M.

Thus the progression step as Z varies is Q*(1+qL), of order q^3 or larger, inside a range below q^4. No applicable prime-existence theorem has been established at these actual moduli. This is a diagnosed obstruction to that shortcut, not a proof that (6)--(8) are insoluble.
