# Further exact-elimination variants of POWER

4 October 2026. This appendix is a separate extension of `PROOF.md`. Its starting point is the proved 22-positive-leaf module there. It does not alter any retained source or numbered report. All counts include the output o and exclude the positive index C and any separately supplied base input. All natural aliases below have distinct positive adapters equal to the alias plus 1.

For b>=2 and C,o>0, every variant has a positive witness exactly when o=b^(C-1). The precise all-exponent theorem dependency remains the pinned `Pell.matiyasevic` and `Pell.eq_pow_of_pell` pair identified in `PROOF.md`, Section 5. The work below is exact elimination and domain recovery from that 22-leaf formula.

## 1. Sixteen positive leaves, nine residuals, degree twelve

Keep the eight directly positive leaves

    o,g,u,v,t,q_b,q_v,J,

one positive alpha_plus leaf, and seven natural aliases

    d_wb,d_wC,d_yC,q_alpha,q_sigma,q_tau,q_r.

Thus there are 8+1+7=16 positive leaves including o, or 15 auxiliary leaves beyond o. Define expressions, not new variables,

    alpha=alpha_plus+1,
    w=b+d_wb,
    y=C+d_yC,
    beta=1+4y q_b,
    M=2b alpha-b^2-1,
    x=y(alpha-b)+b o+M q_r,
    s=x+u q_sigma.                                          (1)

Retain precisely these nine residuals from the 22-leaf presentation:

    E_1=x^2-1-(alpha^2-1)y^2,
    E_2=u^2-1-(alpha^2-1)v^2,
    E_3=s^2-1-(beta^2-1)t^2,
    E_4=beta-alpha-u q_alpha,
    E_5=v-y^2 q_v,
    E_6=t-C-4y q_tau,
    E_7=w-C-d_wC,
    E_8=M-b o-J,
    E_9=alpha^2-1-((w+1)^2-1)(wg)^2.                       (2)

In the old numbering these are R_1,R_2,R_3,R_5,R_6,R_8,R_11,R_12,R_13. The other six residuals become identities after (1). Every alias in (1) is expanded before taking the sum of squares of (2).

### Positivity and exact equivalence

Projecting any 22-leaf solution to these 16 leaves gives a solution because the eliminated equations force exactly (1). Conversely, in any positive solution of (2), w=b+d_wb>=b>=2 and y=C+d_yC>=C>=1. The last residual gives alpha>w, as in the original sign proof. The eighth residual gives M=b o+J>b o>0, even though the unconstrained expression 2b alpha-b^2-1 was not assumed positive in advance.

It follows that x=y(alpha-b)+b o+M q_r>0 and s=x+u q_sigma>0. Also beta=1+4y q_b>=5, so the restored positive beta_plus leaf is beta-1>0. The restored leaves w,y,M,x,s are all positive, and alpha_plus was retained. Thus every eliminated positive-domain requirement is recovered. The definitions restore the six eliminated residuals identically and the other nine hold by assumption. These two maps are inverse: unlike the earlier 26-to-22 normalization, this elimination is a bijection of solution tuples for fixed b,C,o.

### Exact degree

For fixed b, the residual degree list in (2) is

    4,4,6,2,3,2,1,1,6.

For an independent base or b=B+1 with positive B it is

    6,4,6,2,3,2,1,2,6.

Indeed y,w have degree 1, beta degree 2, and M has degree 1 for fixed b or degree 2 for a variable base. Consequently x,s have degree at most 2 for fixed b and at most 3 for a variable base. No residual exceeds degree 6. In E_9, the leading term involving the independent g leaf is -d_wb_plus^4 g^2, whose square contributes d_wb_plus^8 g^4 with coefficient 1. No other residual uses g. Thus the sum of squares has exact degree 12 in both base conventions, including after all positive shifts. No assertion is made here for arbitrary higher-degree substitutions for the base.

## 2. Fourteen positive leaves, seven residuals, degree sixteen

From Section 1 additionally define

    v=y^2 q_v, t=C+4y q_tau.                               (3)

Remove the v,t positive leaves and the residuals E_5,E_6. The remaining direct positive leaves are

    o,g,u,q_b,q_v,J,

together with alpha_plus and the same seven natural adapters: 6+1+7=14 leaves including o, or 13 auxiliary leaves beyond o. The seven residuals are E_1,E_2,E_3,E_4,E_7,E_8,E_9 after (3).

Because y>=1, q_v>=1, C>=1 and q_tau>=0, the restored values v=y^2 q_v and t=C+4y q_tau are positive. All other positivity and equivalence arguments from Section 1 still apply. The restriction and reconstruction maps are inverse.

For fixed b the residual degrees, in the order just given, are

    4,8,8,2,1,1,6.

For a variable base they are

    6,8,8,2,1,2,6.

The squared E_2 contains alpha_plus^4 d_yC_plus^8 q_v^4 with coefficient 1. The unsquared source is -(alpha^2-1)y^4 q_v^2 of degree 8; no other residual uses q_v. Hence the sum of squares has exact degree 16 for any fixed base b>=2 and for an independent or affine base input.

## 3. Thirteen positive leaves and six residuals

One more elimination is possible by recovering the integrality of a rational Pell parameter. Keep only the six directly positive leaves

    o,g,u,q_b,q_v,J

and the seven natural aliases

    d_wb,d_wC,d_yC,q_alpha,q_sigma,q_tau,q_r.

Thus there are 13 leaves including o, or 12 auxiliary leaves beyond o. The alpha_plus leaf is absent. Define integer polynomial expressions

    w=b+d_wb, y=C+d_yC,
    beta=1+4y q_b,
    v=y^2 q_v, t=C+4y q_tau,
    M=b o+J, d=2b, A=M+b^2+1,
    X=y(A-db)+db o+dM q_r,
    S=X+du q_sigma.                                        (4)

The six polynomial residuals are

    F_1=X^2-d^2-(A^2-d^2)y^2,
    F_2=d^2u^2-d^2-(A^2-d^2)v^2,
    F_3=S^2-d^2-d^2(beta^2-1)t^2,
    F_4=d beta-A-du q_alpha,
    F_5=w-C-d_wC,
    F_6=A^2-d^2-d^2((w+1)^2-1)(wg)^2.                    (5)

There is no rational coefficient or division in (4)-(5). The final polynomial is their sum of squares with all aliases expanded.

### Integrality, positivity, and both directions

Given a 14-leaf solution, its modulus equation gives M=b o+J. Its definition M=2b alpha-b^2-1 gives A=d alpha. Hence X=dx and S=ds. The six residuals in (5) are respectively d^2E_1,d^2E_2,d^2E_3,dE_4,E_7,d^2E_9, so all vanish. Restrict to the 13 retained leaves.

Conversely, take a positive solution of (5). All of w,y,beta,v,t,M are positive by (4), and d=2b>0. For the proof only, define the positive rational number alpha=A/d. Dividing F_6=0 by d^2 gives

    alpha^2=1+((w+1)^2-1)(wg)^2,                           (6)

which is an integer. A rational number with integer square is an integer: if alpha=p/q in lowest terms with q>0, then q^2 divides p^2; coprimality of p,q forces q=1. Thus alpha is an ordinary positive integer. Moreover w>=b>=2 and g>=1 make the right side of (6) strictly larger than w^2, so alpha>w>=b and the restored alpha_plus=alpha-1 is positive.

The equation A=d alpha implies M=2b alpha-b^2-1, exactly the prior modulus expression. Define integers

    x=y(alpha-b)+b o+M q_r, s=x+u q_sigma.

Since alpha>b, M>b o>0, and all retained quotients are natural, x,s are positive. The identities X=dx and S=ds now hold over integers. Dividing the vanishing residuals by the nonzero factors d or d^2 recovers all six surviving residuals of the 14-leaf variant, and M-b o-J=0 is an identity. The remaining restored values and adapters are positive as above. Thus this is exactly a 14-leaf solution, and restriction and reconstruction are inverse. In particular no extraneous rational-alpha solutions were admitted by clearing denominators.

### The fixed base-two formula

For b=2, set

    w=2+d_wb, y=C+d_yC, beta=1+4y q_b,
    M=2o+J, A=2o+J+5,
    X=y(A-8)+8o+4M q_r,
    S=X+4u q_sigma,
    v=y^2 q_v, t=C+4y q_tau.

Then (5) is exactly

    X^2-16-(A^2-16)y^2,
    16u^2-16-(A^2-16)(y^2 q_v)^2,
    S^2-16-16(beta^2-1)(C+4y q_tau)^2,
    4beta-A-4u q_alpha,
    w-C-d_wC,
    A^2-16-16((w+1)^2-1)(wg)^2.                            (7)

The six residual degrees are 4,8,8,2,1,6. Their sum of squares has exact degree 16: the second squared residual contains J^4 d_yC_plus^8 q_v^4 with coefficient 1 and no other residual contains q_v. The same degree argument applies to every other fixed integer base b>=2, with constants d=2b.

### Variable-base degree

With a separate positive input B and b=B+1, the aliases in (4) have degrees

    deg w=deg y=deg d=1,
    deg beta=deg M=deg A=2,
    deg v=3, deg t=2,
    deg X=deg S=4.

The six residual degrees are 8,10,10,3,1,8. Their squared sum has exact degree 20. In the second square the monomial B^8 d_yC_plus^8 q_v^4 has coefficient 1, comes from the B^2 part of A, and cannot appear in any other residual square. The 13-leaf count therefore does not carry the degree-16 bound over to a variable base. A fixed base is a coefficient, whereas B is an additional external input.

## 4. Infinite fibers survive every elimination

The proof in `PROOF.md`, Section 7, fixes b,C,o and constructs a family with beta_k=beta_0+4yu k. Its directly positive q_b leaf is

    q_b,k=q_b,0+u k,

which is strictly increasing because u>0. This leaf is retained in all three variants. Projecting the full family through the bijective eliminations above therefore still gives infinitely many distinct witness tuples at every accepted (b,C,o). Removing beta_plus itself does not remove this freedom. None of the new formulas is finite-fold.

## 5. Separate composed ledgers

The new constructions may be substituted for either independent base-two module in the same native-gap formulas. The two initial shifted counters and the two gap residuals are still paid separately. Their counts are:

| Module variant | Module leaves, output included | Module residuals | Module degree, fixed base | Decoding witnesses | Decoding residuals | With compressed triple: witnesses | With six compressed residuals: total |
|---|---:|---:|---:|---:|---:|---:|---:|
| One-sided baseline | 22 | 15 | 12 | 46 | 32 | 49 | 38 |
| Exact elimination | 16 | 9 | 12 | 34 | 20 | 37 | 26 |
| Substitute v,t | 14 | 7 | 16 | 30 | 16 | 33 | 22 |
| Rational-parameter recovery | 13 | 6 | 16 | 28 | 14 | 31 | 20 |

All four native-gap compositions have three external positive inputs, excluded from the witness count. Add three to a witness count to count all polynomial variables. The compressed composition has exact degree max(D,deg P_(program,T)), where D is the corresponding module degree in the table. For T>=1, the inherited upper bound is max(D,4(T+1)^2-4); at T=0 its degree is D. The independent high-degree module monomials used above are absent from the compressed polynomial, so the degree equality is valid. These compositions have infinite complete fibers despite unique decoded powers, counters, and compressed projection.

For the trace construction, add T(E+2) positive witnesses and T(E+Z+4)+1 residual slots to the decoding columns. The first-halt-exactly-T trace version for T>=1 adds one more residual and no witness. These are new replacement constructions. No count in a frozen report is edited or retroactively reinterpreted.

## 6. Fresh finite evidence and scope

The newly authored checker expands each of the three variants with fixed base 2 and with variable base B+1. It checks every leaf count, liveness, residual degree, the full expanded sum-of-squares degree, and the exact coefficient-one monomials used above. It verifies 15 generic substitution identities for 22-to-16, 9 for 16-to-14, and 7 scaled identities for 14-to-13, including eliminated equations becoming identities. It also evaluates complete restricted Pell witnesses at exponent zero and at the nonzero exponent C-1=1, as well as finite members of the beta family for bases 2,3,4,5: 63 full variant assignments in total. The exact receipts and polynomial coefficients are in `evidence/results.json` and the six `variant_*.polynomial.json` files.

These computations support, but do not replace, the all-input reconstruction proofs above or the pinned all-exponent Pell dependency. No source-author or upstream code, counter-machine interpreter, physical simulator, saved schedule, or Lean is run. There is no claim of minimum arity, minimum degree, efficient witnesses, arithmetic-gate improvement, priority, finite-fold representation, or an unrelated universal-polynomial record.
