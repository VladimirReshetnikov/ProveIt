# Independent review of the cofinal-scale repair: 42 integer variables

## Verdict

The proposed reduction is mathematically coherent under the explicitly inherited Q45 ordinary-strong Pell and compiler interfaces. The essential new ingredient is not just replacing two positivity guards by a product guard: it also changes the existing square-scale equation from w=u² to w=4u². That cofinal restriction removes the small-scale exceptional branch and closes the previously identified circular argument.

This note reviews the ordered mathematical argument. Circuit construction/counts and finite replay are to be checked separately. No new Lean/Rocq endpoint is asserted.

## Modified source

Start from the exact Q45 system and its complete original coefficient tuple. Retain the dyadic q guard, common-sign guards for F,alpha,C and all arithmetic lift equations. Replace the two equations eta=Pos(triple1), zeta=Pos(triple2) by eta*zeta=Pos(triple), saving three unrestricted variables and one quadratic residual. In the existing square-scale row replace w=u² by w=4u², introducing no new variable or degree increase.

Every zero now has eta,zeta nonzero with the same sign. Let sigma be their common sign, k=eta+zeta, k0=|k|, and e0=|eta|. Then 0<e0<k0 and eta=sigma*e0. The odd scale s remains nonzero, and Y=s q³ has |Y|>=q³.

## Ordered reverse proof

1. The retained dyadic guard implies J>0 and q>=16. The two product guards, whose three coordinates sum to positive q, imply F>0, alpha>0 and C=q−F−alpha>0. Therefore the inherited packing estimates hold independently of z: q(q²−1)<R<q⁴−2 and R−2>3q+1.

2. Initially X=wq=4u²q>=0. If X=0, then a=Y and D=ac+gamma H with H=4a+3. Reducing the main norm D²−(a²+H)c²=1 modulo H gives 0=1 modH. Because |Y|>=q³, |H|>1, impossible. Hence u is nonzero, X>=4q, and

   |E|=X|Y|>=4q⁴>3R+1.

   This strict inequality is obtained before any Pell rank or power recovery.

3. Put A0=|a+2|, where a=(X+1)Y, and c0=|c|, where c=kY+eta. For either sign of Y and either sigma,

   k0(|Y|−1)<c0<k0(|Y|+1).

   In particular c0>k0. Also A0> X|Y|=|E|>R, because |Y|>2. The first Pell parameter P0=2XY²+1 exceeds A0: it exceeds even (X+1)|Y|+2. Both parameters are positive integers at least two.

4. The retained first and main norm classifications give

   k0=2 psi_P0(n), c0=psi_A0(p), |D|=chi_A0(p), n,p>=1.

   Because P0>A0 and c0>k0, monotonicity of psi forces p>n. This step needs no sign of c or of D.

5. Since P0=1 mod|E|, psi_P0(n)=n mod|E|. Combining the exact source equation k=R+1+hE with k0=sigma*k gives

   2n = sigma(R+1) mod|E|.

   The positive least residue is R+1 if sigma=+1, and |E|−R−1 if sigma=−1. Therefore n>=(R+1)/2 in the first case, whereas n>R in the second case, by step2. In both cases n>=24 (indeed the inherited R bound is far stronger), so p>=25.

6. Pell growth now supplies the hypotheses needed by the ordinary relaxed-rank lemma, without assuming the conclusion p=R:

   c0>A0(A0²−1)², c0>2p, c0>2R.

   For example psi_A0(p)>=(2A0−1)^(p−1) with p>=25 proves the first two, and psi_A0(p)>=2A0>2R proves the third. The strong equation with odd nonzero i gives |f|=chi_A0(m), p|m, c0|m, and m>2p through that inherited lemma.

7. The auxiliary norm and exposed quotient equations give V=−c mod|f| and V=−R modc0. The first congruence is squared in the signed step-down proof, so changing c's sign has no effect. The second is likewise valid with modulus |c| for either sign of c. The inherited odd Chebyshev quotient identities and signed step-down yield R=+p or −p modc0. Since 0<R,p<c0/2, this forces p=R.

8. If sigma were negative, step5 would give n>R=p, contradicting p>n. Consequently eta and zeta are both positive. At this point the original odd-scale proof applies to exclude s<0, then the original positive-scale signed proof recovers X=2^R. It is legitimate to invoke these inherited stages only now: their eta,zeta positivity premise has been proved. Finally the Q45 transport argument restores z>0 as before. Thus a new-system zero yields an original Q45 zero, and hence a refutation under its calibration theorem.

## Forward witnesses

The original canonical Q45 witnesses have q=2^t and w=2^(R−t), with R and t odd. They also have R>3q. Thus R−t is an even integer at least two, and w/4=2^(R−t−2) is a square. Set the new scale variable u=2^((R−t−2)/2). All unchanged arithmetic coordinates remain unchanged. Since eta,zeta are positive, their product has a ternary positive representation. This provides the new product-guard triple and proves completeness.

The coefficient tuple is unchanged and never depends on whether a refutation exists. The modified system has 42 unrestricted integer variables and 27 quadratic residuals, provided the source counts Q45=45 variables/28 residuals are used. The sum of squares therefore has degree at most four; exact degree follows from retaining the isolated tau-square residual (to be confirmed in the emitted packet).

## Difference from the rejected preliminary argument

PRELIMINARY.md analyzes the unrepaired w=u² proposal and remains correct for that proposal. The current argument does not infer |E|>3R+1 from X=2^R. It obtains it immediately from w=4u², whose completeness is separately justified by the canonical witness scale. This eliminates both the exceptional X=q,Y=q³ branch and the need for a new negative-c power-recovery theorem.
