# Final independent audit: the 15-variable Start-only construction

Audit date: 22 October 2026.

## Verdict

The final Start-only construction passes this mathematical audit. It has:

- 15 strictly positive integer unknowns and four fixed integer coefficients;
- one polynomial of exact degree 155, evaluated by 67 binary arithmetic operations, comprising 39 multiplications and 28 additions/subtractions;
- an equivalent six-equation system evaluated by 61 operations, comprising 34 multiplications and 27 additions/subtractions;
- a sum-of-squares version of that system of degree 120 and 78 operations.

The literal audited files have SHA-256 hashes:

- `start_only_polynomial67.json`: `585eb8ea2292debe157e53a046e845be4bb3ba4a3c928a8e65ff9070c7e6ad38`.
- `start_only_system61.json`: `627254270ea72dae657510b7c7c88a3b14dff58f5ea95fcb05ea2404248d31f2`.

The main report's displayed expressions agree with these circuits. Its positivity, rank, sign, scale, packing, and degree arguments agree with the proof below. The separate independent compiler audit, `diophantine_zfc_compiler/INDEPENDENT_AUDIT.md`, establishes the needed Start-only finite-tableau semantics, including arbitrary reconstructed periodic planes and multiple Starts. That audit and this one have complementary scopes.

This is a mathematical audit with identified imported theorems, not an end-to-end proof-assistant build, a proof of global minimality, or a decision of Con(ZFC). The machine-to-ZFC endpoint is a separately identified pinned dependency.

## 1. Exact construction and coefficient contract

Use the new Start-only coefficient recipe, whose executable definition is `start_only_constants.py`, importing the total transition/window predicate and layout routines from `explicit_constants.py`. The historical Start/End enumerator in the latter module is not the final coefficient ordering.

The new ordering has the actual Start at selector 0 and the allowed but noncanonical homogeneous window `(7,7,7,7,7,7,7,7,7)` at selector 1. The old End remains an ordinary allowed window. Every other allowed window follows lexicographically. The actual modified75 masks, clause bands, anchors, ignored dummy position, enlarged radix margin and modular correction are retained with this ordering.

Write the native radix as B=2^d, with B>=16. The valid constants satisfy

    0<MC,MF_native<B-1,
    MC=2 mod4, MF_native=4 mod8,
    popcount(MC)+popcount(MF_native)=d.

The four source ports are beta=B-1, K=DC+B DR, MC, and MFstar=MF_native+B-1. These inequalities alone are not a replacement for the complete fixed coefficient recipe.

The positive unknowns are

    J,F,alpha,z,f,h,i,o,s,w,tau,eta,zeta,y,gamma.

Define

    q=beta J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, H=4a+3, Delta=A^2-1,
    D=X+ac+gamma H,
    C=q-F-alpha,
    G=(q-1)(q-F)+alpha=q^2-C-qF,
    R=G(q^2-1)+(MC+q MFstar)J,
    V=c(of-1)-Rf^2, L=(Delta i c^2)^2.

The six factors are

    N1=tau^2-(EkY)(EkY+k),
    N2=D^2-Delta c^2,
    NA=L(V^2-y^2)+y^2,
    NI=k-hE-R,
    NT=(K+w)C+q-F-z(q-1),
    NS=Delta f^2-L.

The final polynomial is

    P=N1 N2 NA NI NT NS-Delta.

The comparison system is N1=N2=NA=NI=NT=1 and NS=Delta. Every displayed abbreviation is computed, not an additional witness.

## 2. Correct cancellation and unit recovery

Let S=f^2-Delta i^2c^4. The exact polynomial identity is

    P=Delta(N1 N2 NA NI NT S-1).

Positive inputs give Delta=(a+1)(a+3)>0. Therefore P=0 implies a product of six integer units, after cancellation of Delta. It is invalid to infer units directly from the literal product equal to Delta.

Delta is 0 or 3 modulo 4, so neither N2 nor S can equal -1. L is a square, so NA modulo 4 is either y^2 or V^2 and cannot equal -1. Finally, N1 is

    tau^2-V0(V0+1)k^2, V0=XY^2>1.

The negative Pell equation at V0(V0+1) has no solution. For a least positive negative-norm coefficient k, multiplication by the inverse of 2V0+1+2sqrt(V0(V0+1)) gives coefficient (2V0+1)k-2tau strictly between 0 and k, a contradiction.

Thus

    N1=N2=NA=S=1,
    NI=epsilon, NT=nu, epsilon,nu in {+1,-1}, epsilon nu=1.

## 3. The potentially zero computed C

The supplied positivity does not itself prove C>0. Since

    q-F-z(q-1)=1-F-(z-1)(q-1)<=0,

a transport unit cannot have C<0. Thus C>=0 and F+C=q-alpha<q.

If C>=1, direct estimation gives

    2q-1<=G=q^2-C-qF<=q^2-q-1.

If C=0, the transport unit must be -1 and

    F+(z-1)(q-1)=2.

Because q>=16, this forces F=2,z=1. Then G=q^2-2q satisfies exactly the same bounds. Consequently the actual native-mask inequalities yield, in both cases,

    (2q-1)(q^2-1)<R<q^4-q^3,
    E>=q^4>R+q^3, a>R+2, q>=16.

This resolves the bootstrap without assuming a positive R witness or prematurely excluding C=0.

## 4. Restore positive auxiliary coordinates

The normalized strong equation gives

    f^2=1+Delta i^2c^4, f>c^2>2c, c>2.

Since Delta>R,

    L-(Rf^2+c)=(Delta-R)f^2-Delta-c
      >=1+Delta(i^2c^4-1)-c>0.

The auxiliary norm excludes V=0. For v=|V|>1,

    v^2-1=(L-1)(y^2-v^2),

so y>=v+1, forcing v>=2L-1. But V>-(Rf^2+c)>-L; therefore such a V cannot be negative. V=+1 and V=-1 are impossible from V=-c modulo f and f>2c>4. Hence V>1.

Define

    o_old=co-Rf,
    j_old=of-R Delta i^2c^3-1.

They are integers, and the strong identity gives

    o_old f=V+c>0, j_old c=V+R>0.

Thus o_old,j_old are positive, and V=o_old f-c=j_old c-R. No rank conclusion is needed for these signs.

## 5. Exact rank and index sign

The first and main Pell equations classify as

    tau=chi_P0(n), k=2psi_P0(n), P0=2XY^2+1,
    D=chi_A(p), c=psi_A(p), n,p>=1.

P0>A and c>k imply p>n. Since P0=1 modulo E,

    2n=R+epsilon modulo E.

The outer bounds give n>=(R-1)/2>=24, c>2p, and c>2R.

The normalized strong equation directly gives f=chi_A(m) and psi_A(m)=i c^2. Reducing m modulo p in (A+sqrt(Delta))^p=D+c sqrt(Delta), using gcd(D,c)=1 and 0<=psi_A(r)<c for 0<=r<p, proves p|m. Write m=pv. Expanding (D+c sqrt(Delta))^v gives

    psi_A(m)/c = v D^(v-1) modulo c.

Therefore c|v, so pc|m and m>2p. This avoids an unjustified division of an ordinary, unnormalized strong witness.

Put S0=Delta i c^2. From the auxiliary Pell equation, its positive index lambda is odd. For lambda=2r+1, the standard integer polynomials Q_r satisfy

    chi_S0(2r+1)=S0 Q_r(S0^2),
    Q_r(1-A^2)=(-1)^r psi_A(2r+1),
    Q_r(0)=(-1)^r(2r+1).

As S0^2=Delta(f^2-1)=1-A^2 modulo f and V=-c modulo f, squaring the resulting psi congruence gives

    chi_A(2lambda)=chi_A(2p) modulo chi_A(m).

The signed chi step-down lemma applies with 0<2p<m, yielding lambda=+p or -p modulo m, hence modulo c. Reduction of Q_r(S0^2)=V=-R modulo c then gives R=+p or -p modulo c. As 0<R,p<c/2, p=R.

Write 2n=R+epsilon+vE with v>=0. If v>=1, then 2n>2R, contradicting n<p=R. Hence 2n=R+epsilon. If epsilon=-1, then p=2n+1. Pell duplication, chi_A(2)>P0 and A>Y+1 imply

    c=psi_A(2n+1)>Ak>k(Y+1),

contrary to c=kY+eta with 0<eta<k. Therefore epsilon=nu=1, p=R, and 2n=R+1. The case C=0 had NT=-1 and is now excluded. In particular C>0.

This proves equality of the positive zero sets of P and the six-equation system.

## 6. Recover the power, symmetric scale and native word

Let r=(R-1)/2. The lower half-binomial Pell ratio estimate gives

    c/(k/2)>(X+1)^(2r)/X^r.

Together with c/k<Y+1, it implies Y>X^r/3 and a>X^(r+1)/3>2^R; X>=16 and r>=1 suffice for the last comparison. The main projection and recurrence give X=2^R modulo H=4a+3. Both positive representatives are below a, so X=2^R exactly.

Because q|X, q=2^t for t>=4. Since R>3q>3t, q^3|X. Thus w_old=X/q^3 is a positive integer. Together with i_old=Delta i and the positive coordinates restored above, all ten equations of the original symmetric half-binomial kernel hold. Its external bounds q>=16 and 3q+1<=R<q^4 have already been proved. The kernel therefore gives popcount(R)>=3t+2.

The repunit relation and the multiplicative order of 2 modulo 2^d-1 imply d|t, hence q=B^N. Put

    S'=(C-1)+qF,
    T'=MC J+1+q(MF_native J-1).

The exact shifted packing identity is R=(q^2-S')(q^2-1)+T'. Here C>0 and F+C<q provide the required positive range for S'. The inverse population argument yields

    (C-1) AND (MC J+1)=0,
    F AND (MF_native J-1)=0.

Thus C is native-typed with a Start at the origin and without selector 1. The source's bit manipulations occur only in the proof, not in the final polynomial.

Restore z_old=z-1+wC>0. Then

    (K+X)C=F+z_old(q-1).

The modified compiler's quarter-radix coefficient bound, duplicated clean bands, anchor parity and unique anchor-difference argument synchronize X to a whole-cell temporal shift. The retained copy and occupancy tests reconstruct a valid periodic tile plane containing Start.

## 7. Semantic soundness and completeness

The separate compiler audit proves that any such periodic valid plane containing a Start yields a finite initialized halting rectangle. Its proof does not assume h|N, a canonical layout, or uniqueness of Start. Around the initialized Q head, the acyclic phase graph and horizontal periodicity force nearest vertical boundaries; the H above it and a first later H give a finite rectangle. Exact no-escape updates preserve its unique initial head, and the final-row condition forces that head to halt.

The normalized machine erases its finite unary input and then exactly simulates the hashed blank K215 machine. Thus every positive polynomial zero gives a blank K215 halt.

Conversely, a blank halt has finite duration and space. The compiler audit constructs a canonical helical tableau with one Start, no forbidden homogeneous window, and independently sufficiently large five-power width and height. The unique Start and nonzero intended stride ensure the exceptional origin field-mask test; this is a canonical completeness choice, not a soundness assumption.

The ignored Boolean dummy adjustment sets the actually packed R to the desired temporal residue without changing the computation or masks. Canonical native digits are Boolean, and aligned field digits have the quarter-radix margin. Therefore C+F<q and alpha=q-C-F>0. The half-binomial converse supplies positive main and ratio witnesses. For normalized auxiliary witnesses take m=2cR; the binomial expansion of (chi_A(R)+c sqrt(Delta))^(2c) gives c^2|psi_A(m). The canonical minus construction supplies positive f,i,o_old,j_old,y, and the positive quotient o=(o_old+Rf)/c is integral because f^2=1 modulo c and o_old f+R=0 modulo c. This gives the supplied Bezout coordinate and all six equations.

No old input Pell loader or End-distance condition is required. Completeness is existential and may use fresh padding and auxiliary witnesses; no bijection with all old universal-certificate tuples is claimed.

## 8. Consequence, domains and trust limits

The combined result is

    exists a positive zero of P iff blank K215 halts.

The pinned machine endpoint identifies the right side with existence of a finite syntactic ZFC refutation. All finite coding, integer, Pell, compiler and proof-translation arguments are formalizable in ZFC, giving the requested equivalence between no positive zeros and Con(ZFC). The compiler and this audit do not substitute model existence for proof existence and do not require a stronger-model consistency assumption.

The positive domain is essential: signed values can make Delta=0 and introduce unintended zeros. Replacing each positive variable by n+1 gives a 15-variable equation over nonnegative integers. Replacing it by 1+u1^2+u2^2+u3^2+u4^2 gives an unrestricted-integer equation with 60 variables, using four-square representability. Those substitutions have their own arithmetic costs.

The exact factor degrees are 22,18,60,7,2,46; their sum is 155. The degree-12 final Delta cannot cancel that product's leading homogeneous part. The maximum system residual degree is 60, so its sum of squares has exact degree 120. These claims concern the fixed valid compiler slice, not arbitrary degenerate coefficients.

No received repository program was executed for this audit. Source text and JSON were read as inert data. The pinned number-theoretic proof chain and K215 logical endpoint remain imported mathematical dependencies; their complete formal build was not reproduced here.
