# Independent review: three coprime factors and one quadratic relation

Date: 24 October 2026. Reviewer: a separately tasked research agent.

## Scope and verdict

The proposed eleven-integer one-equation variant is sound and complete relative to the same retained ordinary native/compiler/refutation calibration. The proof below audits the final proposed scale **without** an extra factor2:

    A=a+2, Dm=1+Delta*c^2,
    U=r*c^2*A*Dm,
    P=Dt*(1+4D*Dt*s^2),
    Df=1+Delta*U^2*P, Q=Delta^2*U^2*P, delta=Q-1,
    V=Df*(c-R+4U*P*T)-c,
    Cy=Q*V^2-1, Da=delta*Cy,
    S=s*r*H, Z=S*n-Ac.

Here the common outer definitions, budget `D=3Budget-4`, first radicandDt, short projector `K=X(3c-2X)+2`, and `Ac=Phi_H(HT+K)` are those of the reviewed eleven-integer source. The proposed equation is

    delta*Z^2 - S^2*P*Df*Cy = 0.

The source's native index congruence or the separately reviewed short modulus `k=R+1+4h q^4` may be used. Their downstream first-index restoration is the same. Literal circuit counts and exact degrees require their separate artifact check and are not inferred from this arithmetic review.

## 1. Unconditional properties and the zero-scale case

The affine front gives evenq, evenY, `a=Y(X+1)` even, and therefore even nonzeroA. It also gives `H!=0` and `Delta=A^2-1>1`. ConsequentlyU is even even though its displayed definition contains no scalar2. `Dm=1+Delta*c^2` is always positive.

Write `ell=XY^2`. SinceX is divisible by8 andY by8, ell is divisible by4. Hence

    Dt=1+ell(ell+1)k^2=1 mod4.

The consecutive-product inequality givesDt>=1 over all integers. The guard radicand is1mod4, soP is nonzero and1mod4. BecauseU is even, Df is1mod4, Q is0mod4, delta andCy are3mod4, andDa is1mod4. AllP,Df,delta,Cy,Da are nonzero before any positivity is asserted.

IfS=0, the equation becomes `delta*Ac^2=0`. This is impossible: delta is nonzero and `Ac=H^5*pi(T+K/H)` has no rational zero. Thus `s,r!=0`. This argument remains valid atc=0 and at negativeQ.

## 2. Pairwise coprimality holds without sign assumptions

The identities

    Df=1+Delta*U^2*P,
    Q=Delta*(Df-1)

give `gcd(P,Df)=1`. ModuloP, Q=0 and thereforeDa=1, so `gcd(P,Da)=1`.

ModuloDf,

    Q=-Delta, delta=-A^2, V=-c, Cy=-Dm,
    Da=A^2*Dm.

Because `A*Dm` dividesU, Df is1 modulo each ofA andDm. Thus `gcd(Df,Da)=1` as well. These gcd statements concern absolute integers and remain correct for negativeP orDf; no Pell classification has yet been used.

At a zero, multiply the displayed equation bydelta and divide by nonzeroS squared:

    (delta*Z/S)^2 = P*Df*Da.

A rational square root of an integer is integral. Since the three nonzero factors on the right are pairwise coprime, every prime valuation of each absolute factor is even. Thus `|P|,|Df|,|Da|` are integer squares. Each factor is1mod4. A negative odd square is3mod4, so each factor must in fact be a **positive** integer square.

This establishes positivity even when the originally proposedQ was negative. It avoids applying the positive adjacent-Pell descent outside its valid domain and avoids any circular assertion thatc orU is nonzero.

## 3. Recover the guarded kernel

AsDt>0 andP>0, the guard radicand `Dg=1+4D*Dt*s^2` is positive. Since `s!=0`, `Budget<=1` would makeDg<=-3. HenceBudget>=2. Ifc=0 then `eta=-Yk` and

    Budget=k^2[q^2(1-4Y^2)-Derr]<=0,

a contradiction. Thereforec!=0, and thenU!=0. The now positiveP givesQ>1 andDf>0.

Let `p=sqrt(P)>0`, `f=sqrt(Df)>0`, and `ytilde=sqrt(Da)>0`. Since

    gcd(Dt,Dg)=1,

the product squareP also separates as `Dt=tau^2`, `Dg=g^2`, with `p=tau*g` after positive choices. Set the proof-only strong ordinate and auxiliary coordinate to

    I=U*p, T_old=p*T.

They are integers, `c^2|I`, and `|I|>=|c|`. The equations become

    f^2=1+Delta*I^2,
    Q=(Delta*I)^2,
    V=f^2(c-R+4I*T_old)-c.

Set `y=ytilde/delta`. The recovered auxiliary identity is

    QV^2-(Q-1)y^2=1.

NowQ>1, so the independently checked adjacent-coefficient descent applies and makesy integral. The displayed one-equation relation reduces to

    Z^2=S^2*p^2*f^2*y^2,

so `Z=+/-S*p*f*y`. In particular `S|Ac`, hence `H|K^5`.

The already reviewed pre-projection centered-rank argument applies with thisI andT_old. It does not require `s|I` or an odd strong multiplier. It recovers `R=2r0+1`, `r0>=24` and the strict Pell ratio. The powered-divisibility height argument then forces the same exact signed main projection, followed by orientation and old source restoration. With the short modulus, its separate proof first restores the old integralh after identifying the first index. Thus the new one-equation zero yields the same finite syntactic refutation.

## 4. Completeness with an auxiliary divisibility requirement

Take canonical outer data from a finite refutation. Choose the positive guard Pell witnesses s,g as in the selective-fusion parent. These fixDt=tau^2, Dg=g^2 and `P=p^2` with `p=tau*g>0`. At the canonical tupleA andDm are positive.

Choose one positive strong Pell pairI,f by the inherited finite-period theorem with

    4s*A*Dm*p*c^2 | I.

Define

    r=I/(A*Dm*p*c^2), U=r*c^2*A*Dm.

Thenr is a positive integer divisible by4s and `I=U*p` exactly. Fix this pair andr before choosing any residue. Every prime dividing

    M=p*s*r

dividesI. The supported-modulus interpolation theorem is therefore applicable, althoughM need not divideI.

The canonical main projection gives `H|K`; setkappa=K/H. Choose a classa modulo `s*r` for which `pi(a+kappa)=0 mod (s*r)`. Interpolate the **old** auxiliary coordinate with target

    T_old=p*a mod M.

It is divisible byp, so set `T=T_old/p`. Then `T=a mod (s*r)` and the auxiliary Pell equation holds with the required literal form `4UPT`. Furthermore

    Ac/S=H^4*pi(T+kappa)/(s*r)

is an integer. Choose `n=Ac/S+p*f*y`. It givesZ=S*p*f*y and exactly satisfies the proposed polynomial.

The fixed-witness order is canonical outer tuple; s,g,p; one strong pairI,f andr; intersective classa; interpolatedT_old,y; T=T_old/p; n. No divisibility or stronger residue theorem is silently assumed, and no strong pair varies after the residue is chosen.

## 5. Status of the final factor2 deletion

Removing the originally proposed scalar2 fromU is legitimate becauseA is already even. Every parity statement used above survives, and `|A|>=2` supplies the previous magnitude margin oncec,r are nonzero. The centered-rank source explicitly proves its strong step for arbitrary nonzero multipliers ofc squared. There is no hidden odd-multiplier requirement.

This review accepts the unbounded arithmetic equivalence. A final literal verifier should bind the actual definitions without the factor2, the exact projector sign, the original six coefficients, the selected native/short index congruence, and the complete polynomial. It should separately prove its cancellation-aware degree and arithmetic cost. This note does not claim a new proof-assistant endpoint or a global minimum.

## 6. Literal graph and leading-form cross-check

After reading the producer and the completed proof, I counted ancestors of each published output independently of the producer. The native graph has 111 live binary gates (70 multiplications, 23 additions, 18 subtractions); the short-index graph has 112 (71 multiplications, 23 additions, 18 subtractions). Both graphs contain exactly the eleven claimed live variables and no dead nodes.

I also recomputed the highest-degree form symbolically. Put q0=6 beta j, X0=12q0 w, Y0=2v q0^3, a0=X0Y0. The highest parts are

    P0=-48 q0^2 X0^4 Y0^10 k0^6 s^2,
    U0=r a0^3 c^4, S0=4sr a0, Delta0=a0^2.

The first summand has lower degree. The second summand contributes

    -16 S0^2 Delta0^5 U0^10 P0^7 T^2
    =2^36 3^7 q0^14 X0^70 Y0^112 k0^42 s^16 r^12 c^40 T^2.

For k0=h a0 this yields the nonzero coefficient 2^1002 3^707 beta^588 at exponent vector (j,w,v,h,s,r,c,T)=(588,112,154,42,16,12,40,2), whose sum is966. For k0=4h q0^4-q0^3 F0, the maximal h exponent selects coefficient 2^960 3^665 beta^588 at (588,70,112,42,16,12,40,2), whose sum is882. These are exact noncancellation arguments at the fixed nonzero beta. I therefore also accept the claimed 111/966 and112/882 arithmetic cost/degree pairs.

## 7. Final identical-polynomial register sharing

The final short-index graph computes `q2four=4*q^2` once, uses `q2four*q^2` for the index modulus `4q^4`, and reuses `q2four` in the budget. This removes one multiplication while leaving the polynomial exactly unchanged. I independently recounted the final delivered graph: 112 live binary gates (71 multiplications, 23 additions, 18 subtractions), 136 live nodes in total, and no dead nodes. The exact degree remains882. The native graph remains111/966. These final counts supersede the earlier113-gate short-index measurement.
