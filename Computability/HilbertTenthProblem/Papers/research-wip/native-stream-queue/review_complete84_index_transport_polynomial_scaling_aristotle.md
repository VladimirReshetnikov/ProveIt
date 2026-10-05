# Independent review of the index/transport polynomial-scaling bound

**PASS, with the stated local scope.** I independently read and challenged the complete frozen proof. Its multiplication lemma, exact directional-space classification, addition bound and source-independence argument are sound. No correction is requested.

The author pair is:

| File | SHA256 |
|---|---|
| `complete84_index_transport_polynomial_scaling.md` | `5616dd0f87bbd1252389287907c5f66fd6897d6fa1bea1a2ed7f03d91985f796` |
| `complete84_index_transport_polynomial_scaling.json` | `6965cfe8b619398dfef71408275552b9a8bf729984f6a99ab8113dfe05f0776b` |

## Independent proof challenge

For m nonscalar products with affine operations free, every product operand is an affine expression in the original variables and earlier product outputs. Collecting its original-variable linear part at each of the 2m operand positions makes every product a polynomial in those at most2m linear forms. The output adds at most one further affine expression. Thus their common annihilator lies in W(P)={v:D_vP is constant}, and codim W(P)<=2m. This induction does not suppose that intermediate values are homogeneous, that gates increase degree, or that coefficients cannot cancel.

For P=HNT with H nonzero and N,T nonconstant, a nonzero constant derivative along a direction would give P=c*z+d in suitable linear coordinates. This polynomial is irreducible in the full polynomial ring: a factor independent of z must divide the unit leading coefficient c. It cannot equal the product of the two nonconstant factors HN and T. A zero directional derivative instead means z-degree zero, and additivity of degree in z over an integral domain forces N and T separately independent of z. Characteristic zero is used here and in passing from a derivative to independence.

For N=k-R-hE and T=(K+w)C+U-tr, the joint derivative kernel is precisely the line e=e_k+e_R. Comparing the coefficients of E,h,C,w,r,t and the remaining constants gives the claimed seven vanishing components and v_k=v_R. Therefore W(HNT) has codimension at least8. It equals this line exactly when (partial_k+partial_R)H=0, and is zero otherwise. The resulting lower bounds are4 and5 nonscalar products respectively; the actual paid model can only cost more.

The support argument also permits reuse and cancellation. The span of *all* within-wire support differences increases by at most one at each binary addition, and multiplication introduces no direction outside the existing span. The five listed exponent differences of NT are independent by projection to R,h,w,U,t. Nonzero polynomial multiplication satisfies Newt(HNT)=Newt(H)+Newt(NT), including when coefficients elsewhere cancel; exposed vertices, equivalently nonzero initial forms, prove this. Hence every nonzero multiplier retains the five-addition lower bound.

The displayed H=1 schedule has4M+5A, and appending k times its result realizes H=k at5M+5A. These prove sharp minima *across* the two stated multiplier classes. They do not assert that every multiplier achieves the respective minimum.

## Actual-source boundary checked

I checked the paid coordinates against the inert complete84 definitions, including E=w*s*q^4, R=(qU-Z)(q^2-1)+(MC+q*MF)Jrep, and C=U-Z-alpha-ell*x. The supplied MF remains the shifted source numeral. With m=Bm1 nonzero, the displayed rational inverse independently recovers Jrep,F,Z,alpha,s,zeta on w*q*(q^2-1)!=0; h,w,t are unchanged. This proves algebraic independence of the actual nine-value cut before source-zero equations are imposed. It is not an integer or positive reconstruction, and introduces no division into the circuit model.

The literal index and transport producers cost3M+5A. Their joint product adds one multiplication. Although the original source does not materialize their product in one wire, reassociating the two existing finalizer products exposes it at unchanged cost. The theorem consequently applies to the declared nine-gate block without inventing a source register or forgetting an exterior multiplication.

I reauthenticated all four dependencies and the single hashed read span in the author receipt. In particular the source JSON is SHA256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`; its complete84 row declarations were inspected inertly. The complete84 proof was read in full, and the earlier exact-product note was read in this research sequence. The new multiplication proof is complete without importing the older quartic case analysis.

## Scope and execution limits

This is an independent written-proof review, not a proof-assistant certificate or a circuit enumeration. No supplied, archived, frozen or predecessor helper was executed or imported; no saved source array was evaluated. New inline metadata code only checked file/span hashes. No repository or Git change was made.

The result concerns nonzero polynomial multiples at the fixed independent nine-input cut over characteristic zero. Additional donors, rational or positive-coordinate changes, other whole-polynomial equations and source redesigns remain outside it. Multiplying this factor is not itself a proof of complete positive-zero equivalence. The review certifies no global84 minimum and no new universal source. Root's theorem is a strict extension of the earlier H=1 boundary, not a retraction of it.
