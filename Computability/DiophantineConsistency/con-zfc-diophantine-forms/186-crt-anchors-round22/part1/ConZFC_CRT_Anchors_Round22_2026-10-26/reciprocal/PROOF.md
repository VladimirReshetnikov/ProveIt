# A 212-integer reciprocal-pooling companion

The main Round22 quartics are unchanged. This separate companion trades degree
and coefficient size for three further coordinates: 212 unrestricted integers,
151 residuals, exact degree 10, 55,820 collected terms, height 31,104.
Its full literal coefficients are under `equations/`.

## 1. The exact source and the new cofinal restriction

Start with the weighted source of `../signed/PROOF.md`:

    t=32+4h^2, T=t^2, K=32T^2, F=t^K,
    H=2+4(C+A1+...+A8), q=(BH)^x,
    B=binom(F+t,t), N=B^x.

The exponentiation and binomial notation here describe arithmetic meanings of
retained polynomial certificates; no such operation is present in the final
literal polynomial. The actual stored q+1 coordinate is `pow2.output`.
Replace it everywhere by 3z+2, so actual q=3z+1, and reuse its coordinate
for z. H is NOT changed. This is a restriction to a cofinal family of complete
witnesses, not a bijection on every old zero.

For soundness, any integer tuple in this chart has q>=1 or q<=-2. Therefore
q and q+1 are nonzero and of the same sign, before any arithmetic
bootstrap or sign interpretation. The old 35-atom square frame is exactly
substituted, not weakened: it still bounds both actual bases, all requested
indices and outputs, and the actual growth index K. The signed anchor and
orientation proof therefore supplies the canonical signed Pell pairs without
assuming anything about the sign of q or C. The reciprocal theorem below
then recovers all thirteen exact signed-power requests (3 at q and 10 at q+1).
The unit cases q=1 or q+1=-1 are permitted; nonnegative indices are not
asserted for a unit base. Restoring the four old private pool witnesses
reduces soundness to the proved weighted source without circular assumptions.

For completeness, the old witness construction has the following compatible
extra choices, made in this order.

1. Choose h in the cofinal class 1 modulo 3, large enough for the finite proof.
   Then t=32+4h^2 is divisible by 3 (and remains divisible by 4). All old
   horizon, formula-label and CRT-radius estimates remain valid.
2. Put K=32t^4 and F=t^K. For every 1<=i<=t, v3(F)>v3(i). Let a=v3(t!). In
   the expansion of product(F+i)-t!, every term from a nonempty subset S
   has 3-adic valuation

       a + sum_(i in S)(v3(F)-v3(i)) >= a+1.

   Thus t!*(B-1) is divisible by 3^(a+1), and cancellation of the unit
   t!/3^a gives B=1 modulo 3. B is also odd by the unchanged 2-adic argument.
3. Construct sufficiently large beta spacing y and a beta code x as before,
   but choose x even and positive. This is possible because all beta moduli
   1+(i+1)y are odd; their CRT solution class has cofinally many even members.
   Increase x within that even class until all required lower bounds hold.
   B and the beta moduli are fixed before this choice.
4. Put N=B^x, so gcd(N^2,6)=1. Choose the eight other CRT representatives
   positive, and then choose C in its prescribed class modulo N^2, even,
   greater than all other nominal indices and representatives, and with
   3 not dividing H=2+4(C+A1+...+A8). There are two acceptable classes for C
   modulo 3, because its coefficient in H is4=1 modulo 3. CRT with modulo 6
   permits either of them, and its solutions form a cofinal progression
   of step 6N^2. This preserves every old CRT congruence and anchor bound.
5. Define H and q only now. BH is positive, even and prime to3. Even x>=2
   yields q divisible by 4 and q=1 modulo 3, hence q=4 modulo 12 and, in particular, q=1 modulo 3. Set
   z=(q-1)/3. Construct the final square frame and canonical Pell witnesses
   after these choices, exactly as before.

No earlier modulus depends on C,H orq; choosing the extra C congruence is
therefore noncircular. No extra equation h=1 modulo 3 is imposed in the source:
it is merely a permitted cofinal completeness choice.

## 2. Reciprocal pooling with the actual frame

The complete general theorem and independent review are retained in
`proofs/RECIPROCAL_POOLING.md` and its review. We use their arithmetic theorem,
not their old factorial/bootstrap application. Here the new q chart supplies
the nonzero same-sign bases before bootstrap.

For each block j=0,1, with n0=q,n1=q+1, let (Xi,Yi) be its canonical signed
Pell pairs at A, Zi=A*Yi, and define

    Tj=2*A*nj-nj^2-1,
    Hj=sum Yi*(mi-Xi),
    Sj=sum ((mi-Xi+Zi)^2-Yi^2), Ej=Sj-2*nj*Hj.

There are thirteen requests, and each actual nj,mi,ki has square less than W,
where W>=258 and |A|>W^W. The moduli Tj are nonzero, have the same sign, and
have absolute value >W^W. Replace the four rows

    Kj-2Hj-(2A-nj)Lj=0, Sj-nj*Kj+Lj=0

by the single residual

    E0*T1+E1*T0-zeta*T0*T1=0.                         (RP)

The polynomial identity sum(delta_i^2)=Ej-Tj*sum(Yi^2), where
 delta_i=mi-Xi+Zi-nj*Yi, shows that (RP) makes sum(delta_i^2/Tj) an integer.
Put b=floor(sqrt(W-1)), C0=[q(q+1)]^b, and

    di=C0*mi-(C0/nj^b)*nj^(b+ki).

All exponents are nonnegative because |ki|<=b, and C0/nj^b is integral.
Pell power congruences make sum(di^2/Tj) an integer. Furthermore
|di|<=2*b^(3b), and with r=13<=15,

    sum(di^2)<=4r*b^(6b)<W^(3b+1)<=W^W.

Consequently the integer sum has absolute value<1. All its summands have
the same sign, so all di vanish. It follows that mi=nj^ki; when a base is a nonunit its ki is nonnegative. In the unit cases the exact
signed powers still give Tj dividing every delta_i and hence Tj dividing Ej.
Restore all old pool rows before invoking the old-source sign bootstrap; no
unsupported nonnegative-index premise is needed. Conversely true powers give
Tj dividing Ej and satisfy (RP) with zeta=E0/T0+E1/T1.

## 3. Exact existential witness maps and coefficient construction

The four removed variables are private Kj,Lj coordinates, appearing only in
the four pool rows. From an old zero set zeta=L0+L1; the elimination identity
Ej-Tj*Lj=(norm row)+nj*(aggregate row) proves (RP).
From a new zero, the theorem gives integral Lj=Ej/Tj and then
Kj=2Hj+(2A-nj)*Lj. These restore all four old residuals exactly. The maps are
inverse on their zero sets, though the restored quotients are not claimed
to be globally polynomial maps on arbitrary integer tuples.

Before merging, the exact transported chart and two common-Hessian projections
reduce the restricted source from 221 to215 variables and 160 to154 rows.
Their maps are the same kinds of integral bijections proved in the inherited
signed package, independently rechecked for this changed source. The four
pool coordinates and rows remain private. Renaming their row labels is only
metadata. The final replacement deletes four variables and four rows and adds
one variable and one row, producing 212 variables and 151 rows.

Each Ej is cubic and each Tj quadratic; the replacement residual has exact
degree 5, hence the full sum of squares has exact degree 10. The complete literal
arrays, collected expansion, source substitution, projection certificates,
and pool elimination certificate are supplied. No complexity count is inferred
without collecting the actual polynomial.

## 4. Consistency calibration and scope

The cofinal construction and pool restoration prove solvability iff the
weighted source is solvable, hence iff a finite C222 refutation exists and
iff a finite ZFC refutation exists. Therefore ZFC proves

    [the 212-variable polynomial has no integer zero] <-> Con(ZFC).

This is the fixed internal effective proof presentation used in the inherited
calibration; no externally standard-code restriction is introduced. Neither
consistency nor inconsistency is concluded. The new proofs are ordinary
mathematics formalizable in ZFC; finite exact checks and arithmetic controls
are not claimed to be a new end-to-end proof-assistant verification.
