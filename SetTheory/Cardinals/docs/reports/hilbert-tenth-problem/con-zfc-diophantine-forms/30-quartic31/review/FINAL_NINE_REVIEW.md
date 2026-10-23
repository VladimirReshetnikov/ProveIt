# Independent review of the final nine-variable synthesis

## Audited final candidate

File: `../nine/nu31/nine_compact_magnitude_tight.json`.

- Nine nonnegative supplied unknowns.
- 1,840 live binary operations:715 additions,22 subtractions,1,103 multiplications.
- 404 fixed leaves:402 explicitly defined weighted coefficients, plus z_star and y_star.
- Exact degree:120724*5^32+366=2810824662446975708007812866.
- Uniform all-unknowns=t leading coefficient:2^274*z_star^2, nonzero because z_star is a positive power of2.
- Parent quartic:31 positive witnesses,22 quadratic residuals; after positive shifts,675 symbolic terms and402 weighted coefficient records.

Independent source-to-coefficient and degree ledger: `NU31_INDEPENDENT_AUDIT.json`.
Independent semantic check of the quartic elimination: `QUARTIC31_INDEPENDENT_REVIEW.json`.
The compact compiler tuple transfer is a separately audited prerequisite.

## 1. The reduced quartic is an exact positive zero-set equivalence

I independently matched all21 unchanged residuals against package18's pinned32-variable source after deleting its G coordinate. Only its old residuals14 and15 are affected. The replacement is justified by

L[q(q-F)-C]-[(q-F)(N-q)-CL]=(q-F)[q(L+1)-N].

On every new positive solution, unchanged transport gives

(K0+w)C=F+(z-1)(q-1)>0.

Therefore C>0 and the restored integer G=q(q-F)-C=(q-1)C+q*alpha is strictly positive. The forward and reverse coordinate maps are inverses. This is a bijection of positive zero sets, not a heuristic elimination that drops a sign constraint. The old transport coordinate z is retained unchanged.

The normalization residual remains E-X(a-E), which equals1 when all positive variables equal1. Shifting31 coordinates by+1 therefore supplies the exact Normalized hypothesis for the nine-variable compressor at nu=31. The fixed dummy input remains1. The change nu32->31 is justified by this witness reduction; it is unrelated to the backend compiler's radix exponent.

## 2. Tight unconditional majorant for the packed R

In the Jones notation, let g=g0+1, B=b^5, q=B^L, N=q^16, lambda=sum_{r<4L}B^r, and ell=sum_{j=1}^nu B^(5^j). The admissible index and natural domain imply B>2*z_star, B>=4, L>=2, e>0 and theta=B-2*z_star>0.

Set

T0=16*z_star*lambda*g^4*q^7*(N^2-N),
deltaR=2*T0,
Rbar=R+deltaR.

Then Rbar>=|R| without assuming the final equation has a solution.

For the proof, (u+g)^4<=8(u^4+g^4) for nonnegative u,g. Thus the negative piece -2*z_star*lambda*(B+1+g)^4 of R's first bracket is bounded below by -16*z_star*lambda*((B+1)^4+g^4). Adding T0 cancels the g^4 part. The positive lambda*B*q^4 term absorbs the other part because

B*q^4 >= B^9 > 128*B^5 > 16*z_star*(B+1)^4.

The middle inequality follows from B>=4; the final strict inequality follows from2*z_star<B and B+1<2B. Every remaining first-bracket term is nonnegative.

For the second bracket, ell is a subsum of1+B+...+B^(L-1), and b<=B-1. Hence b*ell<q, so q^3-b*ell>0. Its other terms are nonnegative. Thus R+T0>=0. As T0>=0, R+2*T0>=|R|.

All subsequent magnitude companions follow by triangle inequality. With bars as in the construction,

|A|<=Abar, |C|<=Cbar, |J|<=Jbar, |D|<=Dbar,
|E|<=Ebar, |F|<=Fbar, |Gp|<=Gbar, |H|<=Hbar,
|K|<=Kbar.

P is nonnegative even when R is negative, since P=2(RY)^2U and U>0. This justifies Kbar=Rbar+1+h(P+1).

For arbitrary real a,b,

sqrt(|(a^2-1)b^2+1|)<=(|a|+1)|b|+1.

Indeed, the radicand's absolute value is at most(a^2+1)b^2+1, and the proposed square exceeds this by2|a|b^2+2(|a|+1)|b|. Consequently

V0=(P+1)Kbar+2,
V1=[(Abar+1)Cbar+1][(Abar+1)Ebar+1][(Gbar+1)Hbar+1]+1

satisfy sqrt(|a0|)<=V0-1 and sqrt(|a1|)<=V1-1 before any semantic conclusion. V0,V1>=2. The same four-factor finalizer proof applies on every natural assignment. It does not need these particular bounds to hold on all unrestricted integer assignments.

## 3. Exact degree despite leading cancellation

Put L=5^32 and eta=20L+1. The base leading degrees are unchanged as functions of L. In particular degR=235L, degdeltaR=215L-1, and the diagonal leading coefficient of deltaR is32*z_star.

The important top-degree cancellation is real: V1^2 and a1 have the same leading term. Merely adding gate degrees would overestimate the final degree. The independent audit resolves it using exact telescoping identities rather than dropping a canceled term without justification.

Let deltaA=Abar-A, deltaC=Cbar-C, and similarly for J,D,E,F,Gp,H. Their polynomial identities are

- deltaA=deltaR*Y*(U+1), deltaC=2*deltaR, deltaJ=4*deltaA+10.
- deltaD=deltaA*(Abar+A)*Cbar^2+A^2*deltaC*(Cbar+C)+Cbar^2+C^2.
- deltaE=i[deltaJ*Dbar*Cbar^2+J*deltaD*Cbar^2+J*D*deltaC*(Cbar+C)].
- deltaF=deltaA*(Abar+A)*Ebar^2+A^2*deltaE*(Ebar+E)+Ebar^2+E^2.
- deltaG=deltaA+deltaF*(Cbar*Dbar+1+Abar)+F[deltaC*Dbar+C*deltaD+Abar+A].
- deltaH=2*deltaR+j*deltaC.

Define Ibar=(Gbar^2+1)Hbar^2+1 only for the audit. Then

deltaI=deltaG*(Gbar+Gp)*Hbar^2+Gp^2*deltaH*(Hbar+H)+Hbar^2+H^2.

Put M1=(Abar+1)Cbar+1, M2=(Abar+1)Ebar+1, M3=(Gbar+1)Hbar+1. The differences M1^2-D, M2^2-F, M3^2-I equal respectively

deltaD+2*Abar*Cbar^2+2*(Abar+1)*Cbar,
deltaF+2*Abar*Ebar^2+2*(Abar+1)*Ebar,
deltaI+2*Gbar*Hbar^2+2*(Gbar+1)*Hbar.

Using these expressions in

V1^2-a1=(M1^2-D)M2^2M3^2+D(M2^2-F)M3^2+DF(M3^2-I)+2M1M2M3+1

gives a cancellation-free certificate of exact degree24620L+67 and diagonal leading coefficient2^57*z_star.

Write Omega=W and E0=dn+c-Omega*c, so Theta=E0-Omega*V0*V1. The finalizer's inner bracket becomes

E0^2-2E0*Omega*V0*V1+Omega^2*V0^2*(V1^2-a1)-Omega^2*a0.

The third term is uniquely highest, of degree60362L+183 and diagonal leading coefficient2^137*z_star. Squaring dominates the final subtracted norm term (degree96124L+300), so the final polynomial has exact degree120724L+366 and leading coefficient2^274*z_star^2.

Every step of this certificate was independently checked with symbolic fixed leaves. The exact multivariate degree upper bound follows from the displayed polynomial identities; the nonzero diagonal leader gives the matching lower bound. Finite modular tests additionally checked all companion-difference and finalizer identities but are not substituted for the algebraic proof.

A draft value+334 was incorrect and was corrected before finalization: reducing degdeltaR by16 reduces the inner degree by16 and the final degree by32, changing+398 to+366, not to+334.

## 4. Circuit simplification is exact and division-free

The fresh generic circuit builder is `generic_jones_circuit.py`. It is newly authored and never imports received repository Python. It is parameterized by nu and the finite coefficient records.

It evaluates the sparse correction polynomial by sorted-exponent Horner recurrence and shared powers p_j=B^(5^j). Products for consecutive equal radix-five digit runs are cached. The complete homogeneous baseline uses suffix products B^(5^nu-5^j).

The geometric sum also factors exactly:

lambda = product_{j=0}^nu(1+p_j+p_j^2+p_j^3+p_j^4)*(1+q)*(1+q^2).

This follows by repeated geometric-series factorization for powers of5, then S_(4L)=S_L(1+q+q^2+q^3). No division, variable exponent or hidden unknown is introduced.

As a control, the nu32 baseline rebuilt from scratch has1,704 operations and exactly matches every named value of package18's20,531-operation circuit on64 random coefficient/input trials, while an independent symbolic leading audit proves its unchanged exact degree. The nu31 coefficient support is somewhat denser, so its baseline costs1,800 operations; adding the tighter magnitude companions gives the final1,840-operation circuit.

## Scope and conclusion

The algebraic simplification, index construction, quartic reduction, root majorants and exact-degree certificate have been independently audited here. The inherited K215 and native-window/Pell compiler remain ordinary mathematical dependencies; no proof-assistant endpoint was rebuilt. The result is an equivalence formalizable in ZFC, not a proof of ZFC consistency and not a global optimality theorem.
