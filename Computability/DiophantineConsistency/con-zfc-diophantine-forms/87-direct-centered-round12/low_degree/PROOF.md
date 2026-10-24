# Transport pivots after auxiliary-norm centering

## Completed results

All unknowns are unrestricted integers. Each packet is the ordinary polynomial obtained by summing the squares of all its literal residuals. The five fully specified packets are:

| Packet | Unknowns | Residuals | Exact degree |
| --- | ---: | ---: | ---: |
| integer21_degree16 | 21 | 9 | 16 |
| integer20_degree20 | 20 | 8 | 20 |
| integer19_degree32 | 19 | 7 | 32 |
| integer18_degree88 | 18 | 6 | 88 |
| integer20_degree20_free_scale | 20 | 8 | 20 |

Against the initially inspected incoming 21/20, 20/32 and 19/88 family, these are smaller variable/degree points. A later Library supplement already supplies 20/20, 19/28, 18/32 and 17/88. Therefore only 21/16 is promoted as a new low-degree frontier point here; the two 20/20 packets are alternative charts, while 19/32 and 18/88 are dominated. See ../low_degree_supplement/REVIEW.md for the corrected comparison. No global minimality, historical priority, kernel formalization or operation-count optimum is asserted.

The mechanism is an exact synthesis, not a new DPRM theorem: center the auxiliary Pell root, perform a reversible strong-norm row operation, and use a monic transport pivot after selecting the remaining degree budget. Applying that pivot only to the original octic hid the savings available after other large-degree eliminations.

## Fixed coefficients and inherited theorem

The complete source34 tuple is `mixed-parity-unrounded-1064921`: beta,K0,MC,MF, with MF already shifted. The additional actual coefficients are A=2^1113 and B=2^666104. The six gzip payloads and BINDING.json give complete integers and raw SHA-256 identities. In particular beta=2^1064921-1. No coefficient is free, unspecified, or supplied by an unbounded search.

The copied `inherited/degree12_24.json` is the complete 24-integer round11 joint-positivity polynomial. Its mathematical equivalence to finite ZFC refutability is inherited from the residue-oriented native/Pell compiler chain specified in `inherited/ROUND11_PROOF.md` and its copied `round11_dependencies/`. The new transformations below are universal integer zero-set transformations of that exact parent. They introduce no new canonical compiler witness assumption. Consequently, composing both directions with the parent theorem gives, within ZFC, absence of an integer zero if and only if Con(ZFC), for the same recursive ZFC proof calculus. This is an ordinary mathematical equivalence formalizable in ZFC, not a new object-language proof file or a proof of consistency.

The centered auxiliary-root identity is also developed in the new incoming `con-zfc-centered-pell-norms` package, whose complete proof is retained as CENTERED_NORM_PROOF.md. The new incoming joint projections are retained as JOINT_PROJECTION_PROOF.md. We do not claim their ingredients are new; the endpoint compositions here are the new constructions in this iteration.

## One compact parent

The parent variables in order are

J3,F,alpha,z,f,h,r,v_scale,w3,tau,eta,y,gamma,o,j,E,c,a,V,I,t,p,qpos,rpos.

Set q=beta(3J3+1)+1, W=4(3w3+1), X=qW, Y=(2v_scale+1)q^3, H=4a+3, Delta=a^2+H, k=1-V+jc+hE, C=q-F-alpha, and

R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)(3J3+1),
T=AFBC-(q-AF-BC)^2,
Z=eta(k-eta),
Pos=1+p^2+qpos^2+rpos(rpos+1).

Make the invertible integral root shear tau_old=tau+E(c-eta). The twelve parent rows become

0. a-E-Y;
1. E-X(a-E);
2. c-eta-k(a-E);
3. tau^2+(2tau-k)E(c-eta)-1;
4. X^2+2X(ac+gamma H)+H(2ac gamma+gamma^2 H-c^2)-1;
5. cj-V-R;
6. (K0+W)C-F-z(q-1);
7. V+c-fo;
8. I-(2r+1)c^2;
9. I^2-Delta(f^2-1);
10. I^2(V^2-y^2)+y^2-1;
11. TZ-(t^2-T-Z+1)^2-Pos.

The main-norm expansion in row4 is an identity: (X+ac+gamma H)^2-Delta c^2-1 equals the displayed row. The first-root shear is invertible by subtraction, without congruence or divisibility conditions. Each packet includes fully inlined literal polynomial residuals, so the registers above are explanations, not additional unknowns.

## The exact transport pivot

Replace alpha by the complement coordinate C. This is an integral affine-polynomial coordinate change with inverse alpha=q-F-C. Row6 is then monic in F. Define

Fstar=(K0+W)C-z(q-1),   alphastar=q-Fstar-C.

Delete row6 and F, replacing every occurrence by these polynomial values. Projection and restoration are inverse on integer zeros. Fstar has degree two. T then has degree at most four, and R has degree at most five. Thus this pivot does not increase a pre-existing residual-degree budget of eight or larger, except where later substitutions already exceed that budget for other reasons.

It is important that the fixed K0 is not divided out and that q-1 is not treated as a unit. We solve for F, whose coefficient is exactly minus one. The arbitrary integer z is retained.

## Twenty-one variables at degree sixteen

In addition to the transport pivot, set V=fo-c and perform y_old=fo+y. Let S=I^2-Delta(f^2-1). Replace the old auxiliary row Aold by

Anew=(fo+y)^2-Delta(f^2-1)(c+y)(2fo+y-c)-1.

Since y_old^2-V^2=(c+y)(2fo+y-c), the exact identity is

Anew=Aold+S(y_old^2-V^2).

Keeping S=0 makes this a reversible row operation. I now occurs only in S and its monic definition. Substitute I=(2r+1)c^2 and delete row8. Also delete the V definition row7 and transport row6. All other rows are unchanged except for the displayed substitutions. The count is 24-3=21 unknowns and 12-3=9 residuals.

For any parent zero, apply the shears and project the three defined variables. Conversely, given a new zero, restore F,alpha,V,I and the old y,tau. All three deleted rows vanish identically. The retained S=0 and the identity recover the old auxiliary row. Every remaining parent row is restored exactly. This establishes both directions, including all signs and zero values allowed by the original parent.

The strong row has degree six, the reduced centered auxiliary row seven, R five, and the transformed joint guard eight. No row has degree greater than eight. The degree-four leading part of T contains -144 A^2 w3^2 C^2. Hence the guard has coefficient -12^4 A^4 at w3^4 C^4, and its square contributes

[w3^8 C^8] P21 = 12^8 A^8 = 429981696 A^8 > 0.

The guard is the only row of degree eight, and its pure (w3,C) top part is exactly minus a fourth power. Thus this is the exact degree sixteen on the actual positive fixed tuple, not a generic specialization claim.

## Twenty variables at degree twenty

Return to the centered-first-root parent but keep the ORIGINAL auxiliary row and its y coordinate. Apply V=fo-c, I=(2r+1)c^2, the transport pivot, and a=E+Y. Delete rows0,6,7,8. All are monic definitions, so the integer projection and polynomial restoration are inverse. There are 20 variables and eight residuals.

Y has degree four and top form 54 beta^3 J3^3 v_scale. Thus a has degree four. The strong norm and main norm have degree at most ten; the original auxiliary row has degree ten; the joint guard has degree at most eight. The selected coefficient of the final polynomial is

[f^4 v_scale^4 J3^12] P20 = 2^4 3^12 beta^12 = 8503056 beta^12 > 0.

It comes from the square of -a^2 f^2 in the strong norm. The main norm has no f, and the original auxiliary has no J3; no other row reaches this monomial. Exact degree is twenty.

## Nineteen and eighteen variables

Instead eliminate both E and a using

E=XY, a=(X+1)Y,

together with V,I and the transport pivot. The first two parent rows then vanish identically. Conversely they determine these E,a uniquely when the scale Y is fixed. This yields nineteen variables and seven residuals.

The degree-six top form of E is 1944 beta^4 J3^4 w3 v_scale. The degree-six T bound is actually four here, since Fstar depends only on q,W,C,z. The product Z has degree eight. The joint guard has degree sixteen; all other rows have degree at most fourteen. Its square therefore has degree32, with

[eta^4 h^4 w3^4 v_scale^4 J3^16] P19
=2^12 3^20 beta^16=14281868906496 beta^16>0.

To obtain eighteen variables, additionally use eta=c-Yk and delete row2. This is monic, not a remainder division. The top form of eta is -2^4 3^8 beta^7 h J3^7 w3 v_scale^2, of degree11. Hence Z has degree22, the joint guard degree44, and all other rows have degree at most34. The selected coefficient is

[h^8 w3^8 v_scale^16 J3^56] P18
=2^32 3^64 beta^56>0.

The final exact degree is88. The actual eighteen variables are

J3,z,f,h,r,v_scale,w3,tau,y,gamma,o,j,c,t,p,qpos,rpos,C.

The complete ordered list and polynomial restorations are also in the packet. No E,a,I,V,F,alpha,eta,Y,X,k coordinate is hidden in that list.

## A free-scale degree-twenty chart

A different twenty-variable equation replaces the pair a,E by one new integer Yfree and uses

E=X Yfree, a=(X+1)Yfree.

Keep row0, which becomes Yfree-(2v_scale+1)q^3; delete row1. Along with V,I and the transport pivot this again leaves20 variables and8 rows. Both directions follow by Yfree=a-E on old zeros and the displayed restoration on new zeros. The original auxiliary row is retained.

Now E,a have degree3, k degree4, Z degree5. The joint guard and original auxiliary have degree10; other rows have degree at most8. The selected coefficient is

[eta^4 h^4 J3^4 w3^4 Yfree^4] P20free
=36^4 beta^4=1679616 beta^4>0.

This gives exact degree20. The chart separates the cubic scale constraint from the other norms, which may be useful for future elimination searches; no operation-count superiority is claimed.

## Reproducible validation and scope

`build.py` is newly authored; it executes no downloaded repository code. It emits factored, fully inlined literal equations and restoration maps, checks all declared variables, and computes homogeneous-top coefficient certificates using symbolic fixed ports. In upper-degree propagation a canceled top form is not mistaken for proof of exactness: every endpoint has a separate nonzero coefficient at its upper bound.

`check.py` is independently written, uses only the standard library, and imports neither the builder nor SymPy. It verifies all six actual coefficient hashes, compares all restored parent rows against the new rows on750 signed modular assignments over three prime moduli, and checks the auxiliary row operation and deleted rows. It checks exact declared-variable closure. The tests pass in normal and optimized Python. These finite tests diagnose transcription and implementation errors; they do not prove the unbounded compiler/Pell theorem or replace the universal arguments above.
