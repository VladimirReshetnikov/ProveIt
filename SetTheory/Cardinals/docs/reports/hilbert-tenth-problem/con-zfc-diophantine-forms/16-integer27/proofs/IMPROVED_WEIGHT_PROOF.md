# A smaller weight at no additional circuit cost

This is a mathematical improvement to package 09's thirteen-variable resultant. All imported compiler, Pell classification, and signed auxiliary-congruence lemmas retain their original hypotheses. This note proves the new denominator argument and the resulting arithmetic sizes; it does not re-prove the native compiler.

Use the notation of `09-combined13/proofs/ROOT_AMALGAMATION_PROOF.md`. Write `A0=a+2`, `Delta=A0^2-1`, `U=XY^2`, and

    Atau=1+k^2 U(U+1), I=i c^2,
    D=1+Delta I^2, Q=Delta(D-1),
    v=cT, z0=c+RD, d=Q-1.

Replace the weight by

    M0=I^2+v^2.

For the signed-domain extension one can use the even weight `M=2M0`; all bounds below become stronger.

## 1. The retained main Pell norm supplies the missing growth

The main norm gives `c=psi_A0(p)` and `|Dmain|=chi_A0(p)`. Here `c>1`, so `p` is not zero or one. For positive gamma, `Dmain>0`; if `p=2`, then `c=2A0`, `chi_A0(2)-ac=H+4`, while `Dmain-ac=X+gamma H`. Hence `X=4 (mod H)`, impossible because `16<=X<a<H`.

For signed gamma the negative main root is also excluded at `p=2`: using `(chi-ac)(chi+ac)=1+Hc^2`, its congruence yields `4X=-1 (mod H)`, impossible because `0<4X+1<H`. Thus in either case `p>=3`, and

    c>=4A0^2-1>3A0^2.

The positive eta,zeta give `kY<c<k(Y+1)`, so `k>3A0^2/(Y+1)`.

## 2. Weight domination

The transport/mask bootstrap supplies `Y>=4`, `R>0`, and `E=XY>R+2`; it does not use the deleted first Pell root. Therefore

    Atau>k^2 X^2 Y^4
         >9 A0^4 E^2 (Y/(Y+1))^2
         >=(144/25) A0^4 E^2
         >4(R+1)^2 A0^4.

Also `I^2>1` and `c<I^2`, including when i is any nonzero integer, and

    D=1+(A0^2-1)I^2<A0^2 I^2,
    z0=c+RD<(R+1)A0^2 I^2.

Since `M0^2>=I^4`, the previous strict bound gives

    Atau M0^2>4 z0^2.

Since `M0^2>=4 I^2 v^2` and `Atau>A0^2`, it also gives

    Atau M0^2>4 Dv^2

when `v!=0`; for `v=0` the desired conclusion is immediate. Splitting the left side into halves now proves

    Atau M0^2>2(Dv^2+z0^2).

As `Q>=2`, `d>=Q/2`, so for any integer t,

    C=d(t^2+M0^2 Atau)-[Q(Dv^2+z0^2)-1]>d t^2+1>0.

Thus package 09's proof-only reconstruction denominator C is nonzero. The remaining denominator B requires `v!=0`, automatic in the positive domain and handled separately by the signed-domain extension. The root reconstruction, rational-square integrality, and signed-quotient soundness argument are then unchanged.

## 3. Circuit cost

Build the five strong registers as

    I=i c^2,
    I2=I I,
    Dminus1=Delta I2,
    D=Dminus1+1,
    Q=Delta Dminus1.

These replace package 09's five gates computing `Qr,Q,ic2,Dm1,D`. The new weight needs one addition, exactly as `D+v^2` did. The positive four-equation system therefore has 78 operations, and its single-product equation has 84, with unchanged 13 unknowns.

## 4. Exact degree

For thirteen positive coordinates of degree one,

| Register | Exact degree |
|---|---:|
| I2, M0, Atau | 22 |
| D | 34 |
| Q | 46 |
| z0 | 38 |
| P=QDv^2 | 92 |
| Z=Qz0^2 | 122 |
| L=d t^2 | 48 |
| N=d M0^2 Atau | 112 |
| C=L+N-P-Z+1 | 122 |
| PU=PZ | 214 |
| LN | 160 |
| Uroot=C^2+4(PU-LN) | 244 |
| Res=Uroot^2-16C^2 PU | 488 |

The degree-122 term of C is uniquely `-Z_top`, the degree-244 term of Uroot is uniquely `C_top^2`, and the degree-488 term of Res is uniquely `Uroot_top^2`. All are nonzero for every positive beta. The other factor degrees are 18,7,2, so the product has exact degree **515**. This improves the prior 84-operation degree-571 polynomial and matches the prior degree-515 polynomial with one fewer operation. The system degree improves from 544 to488 without adding a gate.

For the 27-integer substitution proposed by the companion signed-domain proof, seven Pos coordinates and square w have degree two; h,i,T,gamma,t have degree one. With even `M=2M0`, the exact weighted degrees are

    main=35, index=13, transport=4,
    I2=M=42, Atau=44, D=66, Q=90, z0=74,
    C=238, Uroot=476, Res=952, product=1004.

The three largest unique-term arguments remain valid, and the lower factors have nonzero leading forms (main contains gamma, index contains h, transport has the independent w term). These are uniform mathematical degree arguments, not consequences of the modular diagnostic alone.

## 5. Artifacts

`../src/build_positive.py` emits the modified positive circuit and four-equation system. Its ledger checks every gate/port is live, and an independent modular line restriction corroborates the stated degrees. `../verification/positive13.json` records the 84/78 operation counts and 515/488 degrees, together with the signed substitution's degree1004 diagnostic. The diagnostic is supplementary; the proof is above.
