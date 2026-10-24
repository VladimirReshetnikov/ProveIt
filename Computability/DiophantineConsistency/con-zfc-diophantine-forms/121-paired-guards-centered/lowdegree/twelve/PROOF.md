# Compact evaluator of the twelve-integer degree-500 carrier

## Result and credit

The delivered equation has twelve unrestricted integer variables, exact total degree 500, and 139 live binary gates: 84 multiplications, 32 additions, 23 subtractions. It is pointwise identical to the retained twelve-integer degree-500/148-gate polynomial. Thus all zero sets, two-way maps, signed squareclass arguments, scale recovery, positivity recovery, and inherited compiler/refutation boundaries transfer unchanged.

This is an evaluator adaptation, not a new twelve-variable semantic reduction. The 28-gate universal four-root norm schedule is credited to the already existing repository proof at commit 84e16e43092614bae262ca59651cb9d77e31a255, `candidates/ten-positive-zero-offset/source/ORIGINAL_PROOF.md`, Git blob 88ac327ed4dde68ab30c094d531f9faca28881bc. The newly received structural-compression manuscript's `integer/COMPACT_NORM_ADDENDUM.md` explains its compact schedule. Both source texts and the upstream license are retained in `source/`.

The genuine new step here is the complete degree-500 adapter, preserving the predecessor's lower-degree centered carriers and authentic fixed constants while replacing only its norm evaluator. It improves 148 gates to 139, not the variable count or degree. The newly received packet's other twelve-variable endpoints have different degrees and are not claimed as our new results.

## 1. Full polynomial and unchanged prefix

`specification.json` gives all ordered polynomial abbreviations and every one of the twelve variables:

    j,C,z,h,r,v,w,T,c,n,p2,p3.

The shared prefix is exactly the retained degree-500 construction after the associative rebracketing L=E*(Y*k), which reuses Y*k from eta and saves one multiplication. In particular it computes integers

    z=Ztotal^2,
    a=4U^2 Dtau, b=36U^2 Df,
    c=324U^2 Da, d=729U^2 G0.

The letters z,a,b,c,d in this paragraph are temporary norm arguments, not extra unknowns and not the native variables of the same letters. In the literal DAG they are named sroot,uroot,vroot,wroot,eroot respectively.

For these five inputs define

    ab=a+b, abp=a*b,
    sigma1=ab+c, sigma2=abp+ab*c, sigma3=abp*c,
    Ucompact=z+d, Po=Ucompact-sigma1,
    Po2=Po^2, zd=z*d,
    Pe=Po2+4*(zd-sigma2),
    Ge=Pe^2+16*(zd*Po2-4*sigma3*Ucompact),
    Go=Pe*Po-16*sigma3,
    P=Ge^2-64*zd*Go^2.

This is a single division-free polynomial equation P=0 with no additional guard row or positivity witnesses. Its norm tail has exactly 28 live binary gates. The complete prefix has 111, for 139 total.

## 2. Universal identity, including singular cases

The three-root norm in the squared total coordinate w is

    N3(w)=[(w-sigma1)^2-4*sigma2]^2-64*sigma3*w.

Adjoin the fourth root and write

    w=(x +/- sqrt(d))^2=Ucompact +/- r,
    z=x^2, r^2=4zd.

Then

    (w-sigma1)^2-4*sigma2=Pe +/- 2r*Po,
    N3(Ucompact +/- r)=Ge +/- 4r*Go.

Multiplying the conjugates gives exactly

    P=Ge^2-16r^2*Go^2=Ge^2-64zd*Go^2.

It is therefore the product over all sixteen signs of

    x +/- sqrt(a) +/- sqrt(b) +/- sqrt(c) +/- sqrt(d).

These are polynomial identities over Z. No radicand nonvanishing, square-root reality, inequality, coprimality, or formal-field specialization hypothesis is needed. Thus the new tail equals the predecessor tail on every integer assignment, not merely on zeros.

## 3. Two directions and exact degree

Since the entire polynomial is pointwise identical, the identity map on all twelve coordinates gives both directions between old and new zeros. Composing it with the predecessor's explicit maps gives both directions to its fifteen-integer source, and then to the new fifteen-integer degree-48 carrier if desired. No change to the predecessor's unbounded Pell/CRT proof is asserted or required.

Exact degree 500 transfers from the same literal polynomial. In particular the retained nonzero coefficient is unchanged:

    [j^228 w^76 v^84 h^8 z^8 r^32 c^64] P
       =2^488 3^332 beta^228 > 0.

The exponents sum to 500. All six fixed numeral payloads remain identical to the predecessor. The ordinary native/compiler/refutation theorem supplies the inherited Con(ZFC) interpretation; this is not a consistency proof, global optimum, encoded internal ZFC derivation, or new end-to-end proof-assistant certificate.

## 4. Exact independent checks

`review/audit.py` imports neither builder. It checks all node types, causality, all twelve variable inputs, liveness, and the actual operation counts. It canonically fingerprints the complete five live prefix circuits, which must match the retained predecessor up to node numbering and associative/commutative addition and multiplication. It then expands both actual DAG tails over the free five-variable integer polynomial ring: all 495 monomials agree exactly. This establishes pointwise equality of the complete output polynomials.

The checker also rejects a deliberately changed opcode at every one of the 139 live arithmetic gates. Normal and optimized Python are run separately. These finite checks certify exact evaluator equality and provenance; they do not independently prove the inherited unbounded compiler theorem.
