# A smaller weight, with no extra arithmetic operation

## Current complete coefficient instantiation

Every main JSON packet and its builder in this release selects the complete
`T4-4094-binary-copy-zero-padding-5pow11` tuple from
`../coefficients/COEFFICIENTS.json`, with tuple SHA-256
`726ac1d0ae1957f75f71966a65c8730403998a1f719e927f6894babea12cf938`.
The aliases are Bm1/beta -> beta, Kconstant/K0 -> K, MC -> MC, and
MF -> MF_source. MF_source is the shifted port MF_native + B - 1.
The whole-tuple transfer proof is `../coefficients/COEFFICIENT_PROOF.md`;
it preserves the native interface, rank congruence, parity, positive odd i,
and positive square w required by the signed and low-degree reductions.
Here B = 2^(5^11). References below to original06/blank67 and d = 5^67
describe the historical source proof, not the numerical instance selected
by this release. Its same completeness argument applies through the
proved transfer with odd d = 5^11 and odd five-power tableau area.
No individual coefficient is mixed with another compiler's tuple.
The vendored source evidence remains unchanged.

This sharpens `INTEGER27_PROOF.md`. Keep every definition and coefficient binding there, but replace its weight `M=D+v^2` by

    I=i c^2,     M=I^2+T^2.

The new thirteen-positive-variable product still has **84 operations**, but exact degree **515**, improving both the old 84-operation degree-571 product and the old 85-operation degree-515 lower-weight product. Its 27-unrestricted-integer lift has **136 operations and exact degree 1004**. The purpose is a proved arithmetic tradeoff, not a global minimum.

## 1. Main-norm bootstrap before root reconstruction

Use exactly the outer-unit, w=0 exclusion, transport, and signed-h arguments of `INTEGER27_PROOF.md`, section 2. In particular X>=q>=16, Y>=q^3>=4096, E>R+2, and Nmain=1. Write A0=a+2, so Delta=A0^2-1 and H=4A0-5.

The main norm alone has Pell classification

    c=psi_A0(p), |Dmain|=chi_A0(p), p>=1.

Because c=kY+eta>1, p is not 1. If p=2, then c=2A0 and |Dmain|=2A0^2-1. For positive Dmain,

    Dmain-a c=H+4,

so X=4 modulo H. But 16<=X<H, a contradiction. For negative Dmain, the exact identity

    4(-chi_A0(2)-a psi_A0(2))
      =-(4A0-5)(4A0+1)-1

implies 4X=-1 modulo H. Since 0<4X<H-1, this is also impossible. Thus p>=3, and

    c>=psi_A0(3)=4A0^2-1>4E^2-1.

Since c<k(Y+1) and Y>=4096,

    k > (7/2)X^2Y.

Indeed

    4E^2-1-(7/2)X^2Y(Y+1)
       =X^2Y(Y-7)/2-1>0.

Consequently, with L=Lfirst=kEY,

    L > (7/2) E^3,     A=1+L(L+k)>L^2.

This main-norm bootstrap is essential. The weaker pretyping bound k>=R-1 alone does not justify deleting k from the old smaller weight.

## 2. Exact domination for M=I^2+T^2

Let lambda=(16/15)^4=65536/50625. The basic bounds X>=16 and Y>=4096 give

    A0=E+Y+2 < (16/15)E,
    c<k(Y+1)<(16/15)kY.

Also I^2>1, so

    D=1+Delta I^2 < A0^2 I^2.

Therefore

    D c^2/I^2 < A0^2 c^2 < lambda L^2 < lambda A.      (1)

For b=c+RD, note c/I^2=1/(i^2 c^3)<1 and R+1<E. Hence

    b/I^2 < 1+R A0^2 < (R+1)A0^2 < E A0^2,
    b^2/I^4 < lambda E^6 < (4 lambda/49) A.           (2)

Put K0=Dv^2+b^2, with v=cT. Since

    M^2=(I^2+T^2)^2 >= 4I^2 T^2,
    M^2 >= I^4,

(1) and (2) imply, also at T=0,

    K0/M^2 <= D c^2/(4I^2)+b^2/I^4
             < lambda(1/4+4/49) A
             = (4259840/9922500) A
             < (9/20) A.                           (3)

The final margin is exactly 41057/1984500>0. The first inequality for the T term is immediate at T=0, rather than obtained by division by T.

Here Q=(Delta i c^2)^2>=10, so d=Q-1>=9Q/10. Equation (3) therefore yields

    d A M^2 > 2QK0.

Consequently C=d(t^2+M^2A)-e > QK0+1 > |B0|sqrt(D), exactly the strict separation needed in `INTEGER27_PROOF.md`.

## 3. Both directions and domains

All subsequent steps of `INTEGER27_PROOF.md` are unchanged:

- t=0 would give Res=(C^2-D B0^2)^2>0;
- T=0 gives the impossible integer gap equation Qb^2-(Q-1)y^2=1 with 1<b<Q;
- the nonzero-denominator formulas reconstruct integer f,tau,y;
- normalized signed-rank and native-window soundness recover a K215 blank halting run;
- canonical witnesses with odd i and square w give completeness after setting t=M tau+y;
- seven Pos substitutions give exactly 27 unrestricted integer coordinates.

For the thirteen-positive-coordinate statement, positive canonical source witnesses and t=M tau+y give completeness directly. Soundness follows from the same reconstruction, with the original 09 signed-auxiliary proof or the stronger signed theorem. Thus both the positive and integer-domain conclusions preserve the exact intended computation predicate.

## 4. Literal circuits and exact degrees

There is no additional gate. Replace the old five-gate block computing Q and D by

    I=i c^2, I2=I^2, Dminus1=Delta I2,
    D=Dminus1+1, Q=Delta Dminus1.

Replace v=cT, v2=v^2 by T2=T^2, v2=c^2 T2, using the already-computed c^2. These are again two multiplications. The new weight M=I2+T2 costs one addition, just like D+v2. All remaining arithmetic gates are unchanged.

The positive-variable degrees are:

    deg(I2)=22, deg(M)=22, deg(Q)=46, deg(D)=34,
    deg(b)=38, deg(e)=122, deg(dM^2A)=112,
    deg(C)=122, deg(U)=244, deg(Res)=488.

The unique leading term in C is now -Q b^2. The U leading term is C^2 and the resultant leading term is U^2; its subtracted term has degree 458, strictly lower than 488. Thus the product degree is 18+7+2+488=515 and the sum-of-squares degree is 976.

For the 27-integer lift, use the weights in `INTEGER27_PROOF.md`. Then deg(I2)=42, deg(M)=42, deg(dM^2A)=218, deg(e)=238, deg(C)=238, deg(U)=476, and deg(Res)=952. The other resultant term has degree 892. The exact product degree is 35+13+4+952=1004, and the exact sum-of-squares degree is 1904. The same disjoint homogeneous substitutions preserve nonzero leaders.

Final ledgers:

- 13 positive variables: product 84 gates (49M+35A), degree 515; system 78 gates (46M+32A), maximum degree 488; sum of squares 89 gates (50M+39A), degree 976.
- 27 unrestricted integers: product 136 gates (72M+64A), degree 1004; system 130 gates (69M+61A), maximum degree 952; sum of squares 141 gates (73M+68A), degree 1904.

`build_smallweight.py` emits every gate, checks independent signed/rational formulas, verifies integer substitutions, proves the rational margin computationally, and reproduces the degrees at two modular test lines. `smallweight_verification.json` records the results. Exact degree claims rely on the displayed unique-leading-term proof, not the finite tests. Neither script decides the existence of a zero or proves the inherited compiler theorem.
