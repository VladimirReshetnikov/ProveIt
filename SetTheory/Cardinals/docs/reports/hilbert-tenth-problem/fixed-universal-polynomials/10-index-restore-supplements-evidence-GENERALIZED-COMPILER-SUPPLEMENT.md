# Supplement: powers-of-five compiler widths are unnecessary

Status: mathematical supplement submitted for independent audit, 2026-10-03. The already approved main proof and its hash remain unchanged. This supplement strengthens its algebraic parameter range; it makes no new universal-bound claim.

## Statement

The theorem of `FULL-SIGNED-COUNTEREXAMPLE.md` remains true for the same complete signed19 equation interface under the following broader fixed-numeral hypotheses:

- d is any integer with d>=1 and B=2^d
- b is any positive odd integer
- K0 is any nonnegative integer
- MC and MFsrc are arbitrary fixed integers

For every positive integer ordinary input x, that interface has infinitely many strictly positive supplied-witness zeros with restored R=k-hXY-1<0. Actual compiler exports are a special case; no powers-of-five condition on d or the selected repunit exponent N is needed. The arbitrary mask extension is solely an algebraic statement about the stated interface, not a claim that arbitrary masks implement a compiler.

## 1. Replace only the initial exponent selection

Choose any positive integer N large enough that

    q=B^N>2d*x+1,
    t=dN,
    J=(q-1)/(B-1)>0.

Write

    t=2^a*3^b0*t0, with gcd(t0,6)=1.

The exponents a,b0 here are factorization exponents, and b0 is unrelated to the fixed input-offset numeral b. Since gcd(t0,12)=1, elementary CRT gives an integer p0 satisfying

    p0=7 (mod12),
    p0=1 (modt0).

When t0=1, the second condition is vacuous. Add a sufficiently large positive multiple of 12t0 so that p0>3t. Set

    X=2^p0, w=X/q^3=2^(p0-3t)>0,
    Q=q^2-1, D0=4q^3*(X+1)/3.

Every prime divisor of t is either2,3 or divides t0. The first congruence makes p0 odd and nonzero modulo3, while the second makes it coprime to t0. Hence

    gcd(p0,2t)=1,
    p0=3 (mod4),
    p0=1 (mod6).

These are exactly the arithmetic properties required of the original choice p0=12t+7. No remaining step uses that particular formula.

## 2. The coprime scale lemma still holds

For completeness, let g=gcd(2^p0+1,2^(2t)-1). It is odd. Choose Bezout integers r,s with rp0+2st=1; reducing this equality modulo2 shows r is odd. Since2 is invertible modulo g, negative exponents cause no difficulty, and

    2 = (2^p0)^r*(2^(2t))^s = (-1)^r = -1 (modg).

Thus g divides3. Both binary powers in the gcd are divisible by3, so g=3. Also p0=1 modulo6 gives 2^p0=2 modulo9, whence v3(X+1)=1. Therefore

    gcd(D0,Q)=1.

Choose s0 with both s0 and 1+D0*s0 units modulo Q by excluding the two forbidden residues at each odd prime divisor of Q, exactly as in the approved proof. The progression

    ell=1+D0*s0 (mod D0*Q)

is primitive, so Dirichlet's theorem supplies a sufficiently large prime ell>3. Put

    s=(ell-1)/D0>0,
    Y=s*q^3,
    H=4Y(X+1)+3=3ell,
    E=XY.

The original special case had D0=2 modulo3. That identity must **not** be imported here: now

    D0=(-1)^t (mod3),

which can be1 or2. Nothing requires a particular one. Because3 divides Q and both s and D0 are units modulo Q, ell-1=D0*s is a unit modulo3. Since ell is also a unit modulo3 by the primitive residue choice, ell is neither0 nor1 modulo3. Therefore ell=2 modulo3 in either case.

All decisive coprimalities follow unchanged:

    gcd(QH,2E)=1,
    ord_H(2) | 2(ell-1),
    gcd(QH,ord_H(2))=1,
    gcd(QH,T)=1, where T=lcm(4,2E,ord_H(2)).

Their proof uses only gcd(Q,D0*s)=1, ell-1=D0*s, ell=2 modulo3, and Xq being a power of two. None depends on t being odd or a power of five.

## 3. Every subsequent definition and sign is unchanged

Set

    C=1, alpha=q-1-2d*x>0,
    z=1, F=K0+X-q+1>0,
    u=2d*x+b,
    M=(MC+q*MFsrc)*J.

The fixed input index u is odd and at least3. No bound on b beyond positive oddness was needed: the input slack delta=(psi_A(u)-u)/Delta is a positive integer for every such u.

With the newly selected p0, impose exactly the original two progressions

    p=p0 (mod T),
    p=-M-Q*(q^2-qF+E_A(u)-1) (mod QH).

Their moduli remain coprime. They form a free arithmetic progression, and the original first-index progression `n=(1-p0)/2 (mod E/2)` is compatible. The fixed outer variables Z and rho remain affine functions of p with positive slopes, so fixed mask values of either sign affect only their constant terms and not eventual positivity.

The distinct-quadratic-field argument also persists: q and Y are even, so A=Y(X+1)+2 is even and Delta=A^2-1 is odd; p0 is odd, so v2(P^2-1)=2+p0+2v2(Y) is odd. Irrational-rotation density therefore provides the same infinite positive ratio family.

All main, first, input, projection and strong auxiliary equations in Sections 4–7 of the approved proof now follow verbatim. The signs use only the properties already checked: p=3 modulo4, p and n unbounded, alpha,F,s,w,J positive, positive odd u>=3, affine positive rho, and exponential gamma. Thus all nineteen supplied child coordinates are positive eventually, while R=-p<0. The input root is positive and the computed W is eventually negative.

## Conclusion

The actual compiler's powers-of-five convention is sufficient but unnecessary for this failure of positive restoration. The broader algebraic theorem holds for every d>=1 with B=2^d and the fixed-numeral hypotheses above. The audited actual-compiler theorem, its original proof, and all limitations concerning raw29/positive21 remain unchanged.
