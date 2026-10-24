# Independent audit: twelve integers, degree 2048, 233 operations

## Verdict

The frozen `radicals12/integer12_degree2048.json` passes the independent exact circuit and degree audit. The new arithmetic synthesis is sound relative to the explicitly inherited ordinary normalized signed-kernel/native/compiler/K215 proofs. No essential new lemma remains unproved in this review. This is not a new proof-assistant compilation, encoded ZFC derivation, or independent reconstruction of the entire inherited calibration.

The circuit has twelve unrestricted integer coordinates, exact degree 2048, and 233 live binary operations: 148 multiplications, 53 additions and 32 subtractions. The coherent six coefficient payloads are unchanged. This improves the authenticated incoming twelve-integer point of degree 4832 and 248 operations, without changing the earlier five frozen round-13 radical packets.

The checker uses its own earlier independent universal-norm recurrence, not the construction builder or any upstream executable code. It expands the full five-root norm with 20,349 monomials and verifies every prefix, carrier, radicand and output register over the integers. It separately verifies the quintic split, positive B identity, zero-I specialization, auxiliary-centering cancellation and exposed quotient formulas. Twelve deliberately altered algebraic registers are rejected. Normal and Python -O execution retain every check.

## 1. Nonvanishing before division, including v=0 and I=0

The actual beta is odd and 1 modulo 3, and J=6j+1 is odd and 1 modulo 3. Thus q is even, nonzero, and 2 modulo 3. W=12w+4 is nonzero and 1 modulo 3, so X=qW is 2 modulo 3. With Y=qv, the integer a=(X+1)Y is a multiple of 6. Therefore

    Delta=(a+1)(a+3)>=3,
    H=4a+3 is odd, nonzero, and divisible by 3.

These facts include v=0, where a=0 and Delta=H=3. Set M=2q^2 and L=MH. Since H=3 modulo q and q is coprime to 3, gcd(H,M)=1. In particular L is nonzero. Dm=1+Delta*c^2 is positive, and Dtilde=M^2*Dm is positive.

Let pi(x)=(x^2+31)(x^3+x+1), Phi_L(x)=L^5*pi(x/L). The quadratic factor has no real zero. The cubic has no rational root and is irreducible of degree three, so it has no root in a real field of degree one or two. Therefore neither Phi_L(u+sqrt(Dtilde)) nor Phi_L(u-sqrt(Dtilde)) vanishes.

The exact split Phi_L(u+dtilde)=A+B*dtilde, dtilde^2=Dtilde, is checked from the factored polynomial. Its odd coefficient also satisfies

    B=5u^4+10u^2*Dtilde+Dtilde^2+32L^2*Dtilde
       +95L^2*u^2+L^2*(u+L)^2+30L^4>0.

If I=0, then S=I*L^5=0. All four non-main radicands vanish, Z=-A, and the norm is exactly

    (A^2-B^2*Dtilde)^16,

which is nonzero. The checker verifies this specialization of the universal norm exactly. Thus every polynomial zero has I,S,s0,r,c nonzero before any factor is divided by S or any auxiliary root is divided by delta. Q=(Delta I)^2 is never one even off the zero set, and at a zero Q>1. This addresses both zero-I and zero-scale branches without a positivity assumption from the missing guard.

## 2. The quintic coefficient is a 3-adic unit

Modulo 3 we have L=0, M=2, b0=2, u=-M*b0=2 and Dtilde=1. Consequently

    B=5u^4+10u^2*Dtilde+Dtilde^2=1 modulo 3.

Also Dm,Df,Dt,Da,Dg are all 1 modulo 3. For Dt, write b=XY^2, so Dt=1+b(b+1)k^2 with b=0 or 2 modulo 3. For Da, Q=0 modulo 9 implies delta=Cy=-1 modulo 3. For Dg, use the deliberate s=3s0 substitution.

After the nonzero-I bootstrap, divide a vanishing norm factor by S. The weighted roots are

    BM*d/S, 2*ytilde, 6*f, 18*tau, 54*g.

Their squared rational orders at 3 are respectively

    -2*v_3(S), 0, 2, 4, 6.

Here B and M are units, Dm is a unit, and v_3(S)>0. Every subset of at least two roots has a unique even minimum square order. The sign-product argument modulo 3 excludes any vanishing signed subset. Subtracting a Galois conjugate of the rational factor equality therefore shows every root is rational, including when the squareclasses are dependent or a radicand was initially negative. The five original radicands are integers, so d,f,tau,g,ytilde are integers. This uses no magnitude weights and no prior guard positivity.

The rational y=ytilde/delta satisfies QV^2-(Q-1)y^2=1. For Q>1, the adjacent-Pell descent proves y integral: a reduced denominator m satisfies m^2|(Q-1), the standard transformation preserves m and decreases |V|, and |V|=1 gives y=+/-1. The transformation and denominator argument require no sign hypothesis on the initial V or y.

## 3. Guard recovery and the s divisible by 3 condition

Rationality gives Dg>=0. Since s is a nonzero integer, P<=0 would force

    Dg=(3P-4)s^2+1<=-3,

a contradiction. Thus P>0. The nearest-square joint guard then implies det>0 and eta*zeta>0: if both factors were negative, the subtracted square would exceed their product.

The possible P=1 completeness obstruction disappears for an exact parity reason, not a heuristic size bound. Both authenticated cone coefficients are divisible by 4, q is even, and hence det is divisible by 4 on every integer assignment. Therefore

    P=det*eta*zeta-(t^2-det-eta*zeta+1)^2
      is 0 or 3 modulo 4.

Positive P is at least 3. Thus D=3P-4 is positive and 2 modulo 3, hence nonsquare. A positive Pell unit g1+s1*sqrt(D) exists. Its image in the finite quadratic ring modulo 3 is a norm-one unit, so a positive power is 1 modulo 3. That power has positive s divisible by 3. This supplies s=3s0 without changing any native data or the chosen t. The exceptional incoming P=1 construction is never needed.

## 4. The coprime quintic really restores both carriers

The factor equality implies S divides A+BM*d. Since S=I*L^5,

    L^5 divides Phi_L(Md-btilde+LT).

For any prime p with p^e exactly dividing L, if the argument had valuation b<e, its monic fifth-power term would have valuation 5b. Every other term, 32L^2*x^3, L^3*x^2, 31L^4*x and 31L^5, would have larger valuation. The unique smallest term cannot cancel. Therefore L divides the argument, with no assumption about gcd(I,L) and no restriction on the sign of L.

Using btilde=Mb0+H(v-q^2), this becomes

    L divides M(d-b0)-H(v-q^2).

Reduction modulo M and H, using gcd(M,H)=1, gives

    M divides v-q^2, H divides d-b0.

Hence v=q^2(2v_old+1), Y=(2v_old+1)q^3, and gamma=(d-b0)/H is an integer. In particular v is nonzero after root recovery, even though the circuit allowed v=0 initially.

## 5. The exact signed-kernel interface is normalized, not source17 parity

With rho=Delta I, the recovered equations include

    f^2-Delta I^2=1,
    rho^2 V^2-(rho^2-1)y^2=1,
    d=X+ac+gamma H,
    d^2-Delta c^2=1,
    tau^2-XY^2(XY^2+1)k^2=1.

The exposed quotients have exact integer polynomial restorations

    o=f(c-R+4IT),
    j_aux=Delta*s^2*r^2*c^3*(c-R)+4*s*r*c*Df*T,
    V=f*o-c=c*j_aux-R.

These identities are checked independently. The first/main rank argument from the signed residue proof applies after the recovered scale and guards. It gives c0=|c|=psi_B(p), p>n>=24 and c0>2p,2R, for B=|a+2|.

The normalized strong equation classifies |I|=psi_B(m), |f|=chi_B(m). Since c^2|I, strong divisibility of the Pell sequence gives p|m. Writing m=p*k, the multiplication formula gives

    psi_B(pk)/c0=k*chi_B(p)^(k-1) modulo c0.

The left side is divisible by c0 and the first Pell coordinate is coprime to c0, so c0|k. Thus m is divisible by both p and c0 and exceeds 2p. These are the actual inputs needed by the signed auxiliary step-down.

The auxiliary Pell index is odd for every integer |rho|>1, not only odd rho: an even index has first coordinate chi_|rho|(2k)=(-1)^k modulo |rho| and therefore cannot be divisible by |rho|. The exposed congruences, step-down and interval bounds then give p=R. The first index unwraps to 2n=R+1, the signed main-root congruence gives X=sign(c)*2^R, and X=2 modulo 3 selects the positive sign. The existing post-power native decoder applies.

This is not literal restoration of the old odd-multiplier source17 coordinate. In general (Delta*s*r-1)/2 is not integral. The review checks the incoming direct normalized signed proof instead. The ordinary compiler and K215 endpoint remain inherited mathematical results; this audit does not silently replace them by finite diagnostics.

## 6. Full residue interpolation, with the corrected period

The imported lemma fixes a positive strong Pell pair I=psi_A(n0), f=chi_A(n0) before the target residue for T is selected. Here A>1 is even, Delta=A^2-1, R=3 modulo 4, and c=psi_A(R)=R modulo 4.

For any positive N, the norm-one Pell recurrence matrix is invertible modulo 4N*c^2. Its finite order gives a positive n0 with I divisible by 4N*c^2. Taking a positive even multiple keeps that divisibility and makes I even and f odd. This provides arbitrarily large eligible indices, so no bounded or accidentally isolated strong witness is assumed.

For each prime p dividing I, the valuation bound v_p(I)>=v_p(n0) is valid. At odd p, the rank of appearance is p when p divides Delta and otherwise divides p-1 or p+1; binomial lifting supplies the bound. At p=2 with even A and even n0, the doubling identity gives v_2(I)=v_2(n0)+v_2(A).

Write alpha=A+sqrt(Delta). The norm-one relation for alpha^n0=f+I*sqrt(Delta) yields

    alpha^(4n0)=1-4f*alpha^n0 modulo f^2,
    alpha^(4n0 f)=1 modulo f^2.

The period is lambda=4n0f, not 4n0. Since gcd(f,I)=1 and the valuation bound holds,

    gcd(lambda,4I^2) divides 4I.

Therefore, for every residue a modulo I, CRT permits a positive L0 with

    L0=R modulo lambda,
    L0=R-4Ia modulo 4I^2.

It is 3 modulo 4. Let S0=Delta I, V0=chi_S0(L0)/S0 and y=psi_S0(L0). The odd Chebyshev recurrence proves both

    V0=-c modulo f^2,
    V0=-L0 modulo 4S0^2.

The second modulus includes the necessary factor 4. Since c-R is divisible by 4 and f^2=1+Delta I^2,

    N0=V0+c-f^2(c-R)

is divisible by f^2 and equals 4Ia modulo 4I^2. The oddness of f and gcd(f,I)=1 make T=N0/(4If^2) integral. Dividing by 4I and using f^2=1 modulo I proves T=a modulo I. Rearrangement gives V0=f^2(c-R+4IT)-c and the desired auxiliary norm.

The checker includes a concrete counterexample to replacing 4n0f by 4n0, but that finite test is not the proof of this lemma. The unbounded recurrence, valuation and CRT argument above is the proof.

## 7. Complete witness order and the shifted residue

Start with the canonical native outer coordinates and the canonical main root d. Set v=q^2(2v_old+1), preserving the physical Y. Choose t with P>0, then the guard Pell witness with 3|s. Apply interpolation with N=s; it fixes I,f with 4s*c^2|I. Set r=I/(s*c^2).

Let e0=(v-q^2)/M. The quintic carrier satisfies exactly

    A+BM*d=L^5*pi(T+gamma-e0).

The intersective quintic has a root modulo every positive integer. Briefly, at odd primes other than 31 a root comes either from the cubic or from its discriminant -31; the chosen roots are simple. At 31, the cubic has the simple root 3. At 2, -31=1 modulo 8 lifts as a square. Prime-power lifting and CRT supply a root modulo I.

Choose a residue for T so I divides pi(T+gamma-e0), then use the full interpolation lemma with the already fixed I,f. No later choice changes I. Set ytilde=delta*y and finally

    n=(A+BM*d)/S+2*ytilde+6*f+18*tau+54*g-(2Q-1)V.

Every term is integral and one norm factor vanishes. The dependency order is outer data, t, guard s, strong I/f/r, intersective residue, T/y, then n. The shared T causes no cycle precisely because interpolation covers every residue for the same strong witness.

## 8. Exact degree, not naive propagation

Naive propagation through the supplied DAG gives only 2528. The exact cancellation is essential. Put Caux=(2Q-1)V and pair the two auxiliary signs first. If Bother contains Sn-A and the other four signed radical terms, then the paired factor is exactly

    Bother^2+2S*Caux*Bother+S^2*(V^2+4Q-4),

because Caux^2-4Da=V^2+4Q-4. The checker verifies this identity universally, including specializations off the zero set.

The prefix bounds are S:34, Caux:45, V:21, Q:24. The four other root weights are main35, strong42, first45 and guard49. Thus Bother has weight at most 49, and the three paired terms have weights at most 98,128,110. Multiplying the sixteen remaining conjugates gives degree at most 2048.

The unique highest paired contribution is 2S*Caux times the signed guard term 54S*sqrt(Dg). Its sixteen-conjugate product has leading form

    108^16*S_top^32*Caux_top^16*Dg_top^8,

which is nonzero. More explicitly, put

    q0=6beta*j, a0=12w*v*q0^2, I0=3s0*r*c^2,
    L0=8q0^2*a0, S0=I0*L0^5,
    Caux0=2a0^6*I0^4*(4I0*T-R0),
    Dg0=-27s0^2*(q0*v*k0)^4, k0=R0+h*a0.

The coefficient of

    j^928*w^288*v^320*h^32*s0^128*r^112*c^224*T^16

is exactly 2^2064*3^1400*beta^928, which is positive. The exponents sum to 2048. The highest h power forces every k0 selection to h*a0; T^16 then forces every remaining bracket selection to 4I0*T. These choices are unique. The checker independently adds all factor exponents and verifies the stated coefficient.

Actual-coefficient polynomial specializations in independent directions give leading coefficient 49438 modulo 65521 and 35643 modulo 65519, at degree 2048. They agree with the derived leading-form expression. These are additional exact lower certificates, not substitutes for the universal upper bound or the unbounded source reduction.
