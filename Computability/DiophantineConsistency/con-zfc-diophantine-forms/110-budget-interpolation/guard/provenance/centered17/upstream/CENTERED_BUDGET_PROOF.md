# Centered budget guard: three private coordinates instead of four

## Result and scope

The new centered guard combines native common-sign recovery and the Pell approximation interval using **three** private unrestricted integers. It replaces the four-coordinate joint positivity guard. On the wave-eleven projected arithmetic interface, an invertible first-root translation gives **18 unrestricted integer variables and exact degree 48**. This is not a pointwise equivalence with the old private guards: soundness uses a new centered half-binomial extraction and original-guard restoration argument, and completeness uses the authentic canonical compiler family. All compiler, Pell rank/step-down and refutation calibration dependencies remain inherited. No formal kernel certificate or global optimality claim is made.

The fixed coefficient tuple is unchanged: source34 beta,K0,MC,MF (MF already shifted), A=cone_A=2^1113 and B=cone_B=2^666104. In particular A,B>=8. The referenced predecessor proofs are wave11 guards/PROOF.md, Sections 3--5, and guards/upstream/residue/dependencies/PROOF44.md, Sections 6--8. They supply common-sign packing estimates, signed Pell rank recovery, original Q41 soundness, and canonical completeness. The new argument below states exactly where their hypotheses are weakened.

## 1. Literal arithmetic system

All unknowns are unrestricted integers:

    J3,F,alpha,z,f,h,r,v_scale,w3,tau,y,gamma,o,j,c,p1,p2,p3.

Use polynomial abbreviations

    q=beta*(3J3+1)+1, W=4*(3w3+1), X=qW,
    Y=(2v_scale+1)q^3, E=XY, a=(X+1)Y,
    C=q-F-alpha, V=fo-c, k=1-V+jc+hE,
    eta=c-Yk, I=(2r+1)c^2, Delta=a^2+4a+3,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)(3J3+1),
    L=XY^2 k,
    Derr=(AF-q)^2+(BC-q)^2,
    Hbudget=k^2(q^2-Derr)-4q^2 eta^2,
    Pos=1+p1^2+p2^2+p3(p3+1).

The seven residuals are

    tau^2+(2tau-k)L-1,
    (X+ac+gamma(4a+3))^2-Delta c^2-1,
    cj-V-R,
    (K0+W)C-F-z(q-1),
    I^2-Delta(f^2-1),
    I^2(V^2-y^2)+y^2-1,
    Hbudget-Pos.

The equation is the sum of their squares. Restoring tau_old=tau+L changes the first row into tau_old^2-XY^2(XY^2+1)k^2-1. This is an integer-polynomial coordinate bijection, with inverse tau=tau_old-L. Every displayed abbreviation is inlined in the JSON packet and is not a variable.

## 2. Universal signed budget soundness

Pos is positive for every integer triple, and represents every positive integer by the three-square theorem. Suppose Hbudget>0. If q=0, then Hbudget=-k^2 Derr<=0; if k=0, then Hbudget=-4q^2 eta^2<=0. Thus q,k are nonzero. Since Derr>=0,

    Derr<q^2,       4 eta^2<k^2.

The first inequality implies 0<AF/q<2 and 0<BC/q<2, whether q is positive or negative. Consequently F,C have q's strict sign, and

    0<F/q+C/q<2/A+2/B<=1/2<1.

Therefore alpha=q-F-C has that same strict sign. No positive input was assumed. Write Q=|q|, Z=|Y|, K=|k|. The second inequality is exactly |eta/k|<1/2. Since c=Yk+eta,

    K(Z-1/2)<|c|<K(Z+1/2),
    sign(c)=sign(Yk).

In particular all weaker estimates K(Z-1)<|c|<K(Z+1) used by the predecessor signed rank proof still hold.

## 3. Signed rank recovery with the centered interval

The common-sign packing estimates give

    Q>=16, Q(Q^2-1)<R<Q^4-2.

Put U=|X| and M=|E|. The same affine restrictions give U>=4Q, Z>=Q^3 and M>=4Q^4>3R+1. Hence k=R+1+hE is nonzero even independently of the guard. Let xi=sign(X), sigma=sign(k), B0=|a+2| and P=|2XY^2+1|. Both Pell parameters exceed one and P>B0. The first and main norms give indices n,p>=1 with

    K=2 psi_P(n), |c|=psi_B0(p).

As |c|>K and P>B0, one has p>n. The first recurrence modulo M gives

    sigma xi^(n-1) 2n = R+1 (mod M).

Exactly as in the signed predecessor proof, either n>R or n>=(R+1)/2. Therefore p is large enough for its Pell growth estimates |c|>B0(B0^2-1)^2, |c|>2p and |c|>2R. The unchanged ordinary strong equation and signed auxiliary step-down use only those bounds, I=(2r+1)c^2, V=-c mod f and V=-R mod c. They give p=R. The negative index-congruence branch is impossible, and no-wrap gives 2n=R+1.

The predecessor ratio lower bound, together with the still-valid |c|/K<Z+1, gives Z>2^R. Its signed main-root congruence then gives

    X=e 2^R, e=sign(c), R odd.

The affine restrictions give X=2 mod3. Since R is odd, e=+1 and X=2^R. In the now-positive-X case the surviving first-index congruence branch has sigma=+1, so k>0. Since c>0 and sign(c)=sign(kY), also Y>0. These signs are conclusions, not hypotheses. The only uses of the former eta*zeta>0 hypothesis in the predecessor rank/bootstrap calculation were the weaker ratio bounds and sign(c)=sign(kY), which were explicitly recovered above.

## 4. New centered half-binomial extraction and restoration

Let R=2s+1, X=2^R and Z=Y>2^R. Here s is a proof index, not the quantified coordinate r. Define

    A0=(X+1)Z,
    B0=A0+2, P=2XZ^2+1,
    L0=(X+1)^(2s)/(2X^s),
    Lratio=psi_B0(2s+1)/(2 psi_P(s+1))=c/k.

For t>=2 and m>=1, the elementary Pell recurrence bounds are

    (2t-1)^(m-1)<=psi_t(m)<=(2t)^(m-1).

The positive-Y lower ratio factor satisfies

    ((2B0-1)^2/(2P))/((X+1)^2/X)
      =(1+3/(2A0))^2/(1+1/(2XZ^2)) > 1.

The strict inequality follows from 3/A0>1/(2XZ^2), valid for X,Z>=1. The upper normalized factor is at most (1+2/A0)^2. Consequently

    L0 < Lratio <= L0(1+2/A0)^(2s)
                  <= L0(1+8s/A0).

For precision, (1+u)^m<=1/(1-mu)<=1+2mu when 0<=mu<=1/2; apply this with u=2/A0,m=2s. The needed 4s/A0<1/2 follows already from R>=49, X=2^R and Z>X.

The centered interval gives Lratio<Z+1/2, so L0<3Z/2 and

    0<Lratio-L0 < 12s/(X+1) < 1/8.

The last bound holds for every odd R>=9 by 2^R+1>96s, and therefore holds here. This argument is uniform and does not pass to a large-Y limit.

Expand

    (X+1)^(2s)/X^s = Mbin+theta,
    Mbin=binom(2s,s)+sum_{j=1}^s binom(2s,s+j)X^j,
    theta=sum_{j=1}^s binom(2s,s+j)/X^j.

Mbin is even, and

    0<theta<(sum_{j=1}^s binom(2s,s+j))/X
            <2^(2s-1)/X=1/4.

Thus L0=Mbin/2+theta/2. The preceding error gives

    Mbin/2 < Lratio < Mbin/2+1/4.

Because Z is an integer and |Lratio-Z|<1/2, necessarily

    Y=Z=Mbin/2.

Since Lratio>L0>Mbin/2,

    0<eta/k=Lratio-Y<1/4.

In particular eta>0 and zeta=k-eta>0. This recovers the original interval guard at the same arithmetic coordinates after, not before, the sign and power bootstrap.

## 5. Restoration of the original unrestricted Q41 source

The budget argument gave F alpha>0 and F C>0. Section4 now gives eta zeta>0 at zeta=k-eta. Each of these three positive integers has a Pos representation, so all original private Q41 positivity triples can be restored. Because R is odd and X=2^R, the old square coordinate u=2^((R-1)/2) is an integer and satisfies X=2u^2. Restore the monic arithmetic coordinates and tau_old as in Section1. All original Q41 rows now vanish, with the same retained arithmetic assignment. Its named inherited soundness theorem supplies a finite ZFC refutation.

This is a pointwise restoration to Q41, not to the stronger wave11 determinant-guard parent: Hbudget>0 need not imply its specific determinant d>0. It avoids any reinterpretation of the native compiler on negative Y, and invokes no unchecked rational integrality claim. We never use eta zeta>0 until after the centered-interval proof has recovered it.

## 6. Canonical completeness with a uniform margin

Start with the same authentic canonical compiler family used by wave11 guards/PROOF.md Section5. Its scale bounds are

    q/2<=AF<4q/5, q/2<=BC<3q/5,

so Derr<=q^2/2. Its canonical half-binomial choice is Y=Mbin/2, k,c>0 and eta=c-kY>0. Independently of the new guard, Mbin/2>=X^s/2>X for s>=2 (here R>=49), so every ratio estimate's Y>X hypothesis holds. For this prescribed canonical Y=Mbin/2, one has L0=Y+theta/2<3Y/2 without assuming the new guard. Thus the upper ratio bound in Section4 directly gives 0<eta/k<1/4, because 0<theta/2<1/8 and 12s/(X+1)<1/8. This use of the estimate is not circular: it uses the explicit canonical Y, not the centered interval being proved. Thus

    Hbudget > q^2 k^2 (1-1/4-1/2)=q^2 k^2/4>0.

The three-square theorem supplies p1,p2,p3 with Hbudget=Pos. All arithmetic rows are the canonical predecessor rows and the translated first root is integral. This proves completeness without demanding that every old zero lift to the new stronger budget guard.

## 7. Exact degree

Give all eighteen unknowns degree one and all fixed numerals degree zero. Then deg X=2, deg Y=4, deg E=deg a=6, deg k=7, deg eta=11, deg L=17. The seven row degrees are 24,14,4,2,14,10,24. Therefore their sum of squares has degree at most48.

Put J=J3,v=v_scale,w=w3. Leading forms are q*=3 beta J, X*=36 beta Jw, Y*=54 beta^3 J^3v, k*=hX*Y*. The first row has leading form -h^2 X*^3 Y*^4. The budget row has leading form -4h^2 q*^2 X*^2 Y*^4. Their squares are distinct monomials. In particular the coefficient at

    h^4 w^6 v^8 J^30

is (36^3 54^4)^2 beta^30 = 2^20 3^36 beta^30>0, contributed only by the first row. The equation therefore has exact degree48 on the authentic fixed coefficient slice.

## Proof boundary

The new ingredients are the joint centered budget and the centered nearest-half-binomial extraction and the late sign restoration. Pell classification, strong rank and auxiliary step-down, the exact source34 native compiler and refutation calibration are named inherited unbounded results. Finite symbolic or numerical checks validate transcription and estimates, not those unbounded semantic theorems. This is an ordinary mathematical reduction and not an encoded internal-ZFC proof.
