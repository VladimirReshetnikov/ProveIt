# A fixed-arity integer certificate for finite binary sandpile stabilization

Research source, 4 October 2026. This file records the arithmetic construction; the emitted polynomial source is complete. An independent audit is in progress. Finite regressions are evidence for source correspondence, not substitutes for the all-integer proof or its stated Pell dependency.

## 1. The relation being represented

Let b=32. Inputs are positive integers p,q,r,d,e,f and natural integers T,D. T is the base-b code of a periodic tile with dimensions p,q,r, in order x+p y+p q z; D is the base-b code of finite additions in [0,d)×[0,e)×[0,f), in order x+d y+d e z. Tile digits must lie in {0,...,5} and addition digits in {0,...,15}, with no digits beyond these arrays. The configuration is the periodic tile plus this finite addition. An equivalent single-input convention uses a fixed sevenfold Cantor pairing of (p−1,q−1,r−1,T,d−1,e−1,f−1,D).

The represented predicate says that this configuration has a finite legal globally stabilizing sequence whose odometer takes only the values zero and one. It says nothing about whether a specified site fires. Malformed encodings are rejected. Larger finite addition heights cannot have binary odometer: an initial height at least 12 remains at least 6 after at most one toppling. The bound 15 is convenient for bit masks, and accepted inputs are automatically further constrained by stabilization.

No finite time bound, witness list indexed by a variable dimension, bounded universal quantifier, or arbitrary recursive decoding relation is used below.

## 2. Least-action lemma removes ranks for this predicate

For a natural configuration η on Z³, let u:Z³→{0,1} have finite support, and suppose F(v)=η(v)−6u(v)+Σ_{w∼v}u(w) is stable at every vertex. It suffices that F≤5; the construction additionally ensures F≥0. Every finite legal prefix has toppling count m≤u. Otherwise consider the first toppling that would exceed u at v. Immediately before it, m(v)=u(v), all neighbor counts are at most u(w), and hence the current height is at most F(v)≤5, a contradiction. Consequently a legal process cannot last longer than Σu. If it stopped with an unstable vertex, that vertex could legally topple, contradicting the same bound after at most finitely many further choices. Thus a finite legal global stabilization exists, and its true odometer u* satisfies u*≤u and is binary.

Conversely, its genuine binary odometer is such a supersolution. This is an equivalence of existence, not of supplied odometers or full witness fibers. For example two adjacent initially height-five sites can be included unnecessarily in a stable supersolution although the true odometer is zero. Rank/burning data are needed to rule out that overfiring when certifying the odometer itself; they are unnecessary for this existential stabilization language.

## 3. Fully algebraic bit masks

The relation Sub(M,X), on naturals, means every binary one-bit of X is a one-bit of M. Introduce positive L,Y,Z, natural q0,o,r0, and positive sc,sr, and assert

L=2^(M+1), Y=L^X, Z=(L+1)^M,
Z=(q0 L+2o+1)Y+r0,
2o+1+sc=L, r0+sr=Y.

Each displayed power is separately replaced by the fifteen-equation Pell macro in section 9. These are three power calls and three additional polynomial equations. The two positive slacks force extraction of the exact base-L digit at index X of (1+L)^M. Every binomial coefficient is at most 2^M<L, so that digit is binom(M,X), interpreted as zero when X>M. Over F₂, (1+z)^M=∏_{j:bit_j(M)=1}(1+z^(2^j)); distinct subsets have distinct exponents. Hence the extracted coefficient is odd exactly for Sub(M,X). This elementary argument covers M=0,X=0 and automatically rejects X>M.

A bitwise AND relation W=X AND Y is provided by naturals a,c with X=W+a,Y=W+c and the three predicates Sub(X,W), Sub(Y,W), Sub(a+c,a). The first two subtract bits without borrowing. The third asserts that adding a and c has no binary carries, equivalently a AND c=0. Thus every common bit is in W and no other bit is. A more economical batching variant is optional; it is not needed for fixed arity.

For t≥2,n≥0, G(t,n) is the unique natural solution of (t−1)G+1=t^n. A power call and one polynomial equation pay this geometric sum, including n=0.

## 4. Block spreading pays input reshaping

Suppose B=2^k≥2, n≥1, s≥n+1, and 0≤U<B^n. Write U=Σ_{i<n}u_i B^i with 0≤u_i<B. Define

H=U G(B^(s−1),n), M=(B−1)G(B^s,n), V=H AND M.

All powers, geometric sums and AND relations are paid macros of section 3. Then V=Σ_{i<n}u_i B^(si). Indeed, exponents i+(s−1)j for 0≤i,j<n are all distinct, since s−1≥n; hence the product has no coefficient carries. Such an exponent is divisible by s only when i=j, because |i−j|<s. The mask retains precisely these diagonal blocks and every bit of their B-ary digits. This proves the graph of the spreading function, rather than assuming a digit-array oracle.

## 5. Unknown padded prism and both decoded tensors

Choose tx,ty,tz≥2 and set

a=p d tx, c_y=q e ty, c_z=r f tz,
A=2a, B=2c_y, C=2c_z, N=ABC.

The lattice prism has lower corner (−a,−c_y,−c_z) and side lengths A,B,C. Its lower corner has zero phase for all three periods. Choose tx,ty large enough, using paid natural gaps, that

A/p≥qr+1, A/d≥ef+1, B/q≥r+1, B/e≥f+1.

All these quotients are explicit polynomial expressions (for example A/p=2d tx and A/d=2p tx). Enlarging tx,ty,tz preserves every requirement and eventually contains any fixed finite support strictly in its interior.

First certify T's digits in 0,...,5: write T=T0+2T1+4T2; for Jt=G(b,pqr), assert Sub(Jt,T0), Sub(Jt,T1), Sub(Jt,T2), Sub(Jt,T1+T2). The last excludes simultaneous 2- and 4-bits. Certify Sub(15G(b,def),D), which is exactly addition digits in 0,...,15.

To embed the tile, spread T as qr blocks of radix b^p and stride A/p, then spread the result as r blocks of radix b^(Aq) and stride B/q. The result is

T_emb=Σ h(x,y,z)b^(x+Ay+ABz), 0≤x<p,0≤y<q,0≤z<r.

The intermediate digit range required by the second spread follows because p≤A and each of the qr rows lies below its next A-position. This is proved from the first spread, so no additional arbitrary array predicate is needed. The complete background stream is

H=T_emb G(b^p,A/p)G(b^(Aq),B/q)G(b^(ABr),C/r).

Unique mixed-radix coordinates show that each product coefficient has exactly one tile contribution; it is the correct periodic height in 0,...,5.

To embed additions, spread D as ef blocks of radix b^d with stride A/d, then as f blocks of radix b^(Ae) with stride B/e. Multiply the result by b^(a+A c_y+AB c_z) to obtain Δ. This places the input patch at its unchanged physical coordinates in the centered prism. Its whole support is strictly inside because a≥2d, c_y≥2e,c_z≥2f. The stream H+Δ has digits at most 20, so there is no carry.

## 6. Binary support and exact neighbor shifts

Let X=b^A,Y=X^B=b^(AB),Z=Y^C=b^N and J=G(b,N). Define Jx,Jy,Jz by

b²((b−1)Jx+1)=X,
X²((X−1)Jy+1)=Y,
Y²((Y−1)Jz+1)=Z.

These are G(b,A−2),G(X,B−2),G(Y,C−2), without additional powers. Set I=b X Y Jx Jy Jz. Its one-bits are exactly the low bits of strict-interior base-b digits. Sub(I,U) therefore certifies a binary odometer candidate with zero on the entire boundary shell.

Introduce natural Ux,Uy,Uz and assert b Ux=U, X Uy=U, Y Uz=U. The shell makes these exact divisions possible. The six neighbor streams are bU,XU,YU,Ux,Uy,Uz. Row and plane wrap artifacts vanish because the relevant source face is zero. There is no overflow beyond the prism because the positive faces are zero. Every site outside the prism has only boundary-shell neighbors in it, all zero, so no chips leave the prism and the periodic exterior remains stable.

## 7. One conservation equation replaces all site conjunctions

Introduce Z0,Z1,Z2 and impose Sub(J,Z0), Sub(J,Z1), Sub(J,Z2), Sub(J,Z1+Z2). Set F=Z0+2Z1+4Z2. Its digits are exactly the allowed stable heights 0,...,5.

Assert the single integer equation

H+Δ+bU+XU+YU+Ux+Uy+Uz = 6U+F.

Every left digit is at most 5+15+6=26<32; every right digit is at most 6+5=11<32. Every term is supported in the N slots. Therefore this one equality holds if and only if each lattice conservation equation holds. This pays the variable conjunction by carry-free positional uniqueness, with all digit conditions themselves paid by the fixed Sub macros.

Soundness follows from the least-action lemma and the stable exterior. Conversely any finite binary stabilization supplies U; choose the three t values large enough for its support, patch, and spreading margins. Its actual endpoint supplies F and the three bitplanes. Every macro has witnesses by its proved completeness, so the system has a solution.

## 8. Meaning of fixed arity and remaining proof dependencies

Every tensor operation above uses a fixed number of scalar integer witnesses and polynomial equations. The dimensions and unknown prism enter as values, never as numbers of equations or coefficients. Expand each power by section 9; form one polynomial by squaring each residual and summing the squares. This has a fixed number of positive integer witnesses independent of the input code and any halting time. A literal source and its exact ledger are accompanying deliverables, not to be inferred from this prose alone.

The fibers are deliberately not unique or finite-fold. Arbitrarily larger successful prisms already yield infinitely many witnesses, and paired congruence quotients in the Pell macro admit simultaneous shifts. No all-real exactness is claimed. This bypasses the finite/cofinite semialgebraic obstruction by quantifying integers.

This theorem is about the encoded physical sandpile directly. To identify the particular Report 35 U15 loader, one still inherits its one-shot theorem, finite-tape compiler, geometry and universal-machine theorem. It does not become a freshly verified literal graph merely because the arithmetic certificate is explicit. The ordinary integer coding of a supplied physical periodic tile and finite patch is fully paid here. A separately efficient or literal straight-line map from raw U15 tape words to that eight-field code is not established here.

## 9. Explicit power macro dependency

For output=b0^e0, b0≥2,e0≥0,output≥1, set k=e0+1,m=b0 output. Use a,β≥2; w,T0,g,x,y,u,v,s,t,qb,qv,S>0; and δwb,δwk,δyk,α1,α2,σ1,σ2,τ1,τ2,ρ1,ρ2≥0. Assert:

x²=1+(a²−1)y²; u²=1+(a²−1)v²; s²=1+(β²−1)t²;
β=1+4y qb; β+uα1=a+uα2; v=y² qv;
s+uσ1=x+uσ2; t+4yτ1=k+4yτ2; y=k+δyk;
w=b0+δwb; w=k+δwk; T0=m+S;
a²=1+((w+1)²−1)(wg)²; 2ab0=T0+(b0²+1);
x+T0ρ1=y(a−b0)+m+T0ρ2.

This is the explicit specialization already recorded in the audited binary recoder. Its external source is mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f, Mathlib/NumberTheory/PellMatiyasevic.lean, theorems matiyasevic and eq_pow_of_pell. Source is read as inert text. The first nine equations select the exact indexed Pell pair at positive index k. The last six invoke the constructive power characterization. Equation 13 implies a>w≥b0, so the source theorem's natural subtraction a−b0 agrees with integer subtraction. Conversely its constructive choices supply all required witnesses, using differences of nonnegative quotients for the four congruences. This is a specific fifteen-equation number-theoretic theorem, not a generic invocation of MRDP.

Represent a,β as positive witnesses plus one; each zero-capable variable as a positive witness minus one. The fixed macro then has 25 positive internal witnesses and fifteen equations. The emitted implementation uses 31 multiplications, 24 additions and 15 subtractions, or 70 gates per power call. Its positive output port is quantified separately. No historical arithmetic schedule is executed.

## 10. Literal source and arithmetic ledger

`build_certificate.py` is a newly authored fixed-shape source builder. Its Python loops range only over fixed lists of macro equations, seven Cantor coordinates, and source nodes. No input dimension is a loop bound. The emitted `evidence/polynomial-dag.json` contains only positive input/witness leaves, fixed integer constants, and binary +,−,× operations. Equality assertions are converted to their residuals, squared and added to a single final output.

The complete source has 2,566 strictly positive existential variables and one strictly positive ordinary input, InputPlus. It represents the encoded natural integer InputPlus−1. The 1,491 equalities expand to one polynomial using 11,469 paid arithmetic gates:

- Before the final combiner: 3,027 multiplications, 2,443 additions, 1,527 subtractions, total 6,997
- Sum-of-squares combiner: 1,491 subtractions, 1,491 squarings, 1,490 additions, total 4,472
- Full polynomial: 4,518 multiplications, 3,933 additions, 3,018 subtractions, total 11,469

There are 92 explicit power calls, 22 Sub calls, four ordinary three-Sub AND calls, and four spreads. All powers in masks, binomial extraction, decoding and geometric repetition are included. The separate stream-products note gives a more economical AND implementation; the authoritative source deliberately uses the simpler three-Sub version and does not claim that saving. Every emitted gate and witness reaches the single polynomial output. Fixed integer literals are free under this ledger, including 31,32 and1024; no claim is made under a different literal-generation convention.

The polynomial has exact total degree18. Straight-line degree propagation supplies the upper bound. The separate checker `check_exact_degree.py` substitutes one indeterminate t for the six descriptor-dimension witnesses and the three source witnesses box.tx,box.ty,box.tz, and zero for all other witnesses and the input. It propagates exact univariate coefficient arrays through every gate and obtains leading coefficient48 at t^18. This algebraic specialization need not lie in the positive domain; its nonzero leading coefficient proves the degree lower bound. No fixed-universal-operation improvement or arithmetic optimality is claimed.

The current polynomial source SHA256 is 2e2403097ba0fb65bad349222246157bccad4ac59e99d594b48fa7a678a93723. The builder SHA256 is 6d123bbb4b20b5bff8b59915e3f7ee320207f39f036ee2143a874c9bdc28bc4a. The builder writes its count and liveness receipt; `check_source.py` independently compares 5,520 emitted POWER residual substitutions and 264 Sub residual substitutions across four modular assignments and checks the complete sum of squares. It constructs five genuine isolated POWER witness tuples, checks 64 minimal-domain geometries and 100 Cantor-code round trips. These checks do not instantiate a giant full sandpile/Pell witness, prove all-input soundness by enumeration, or run the literal universal machine.

## 11. Positive-domain audit and source provenance

All six physical dimensions are positive quantified variables. tx,ty,tz are positive variables plus one, so each is at least two. The four row/plane radices are powers of32 at positive exponents, so they are powers of two at least32. Every spread length is positive. Its separately asserted stride equation s=n+1+gap makes s−1≥1, hence the copy-base powers are at least2 and geometric denominators are nonzero. Its positive range slack imposes the strict input bound U<base^n. All other geometric lengths are positive or explicitly nonnegative, and every geometric base is at least2.

For each Sub call, the mask and value are natural expressions or separately quantified natural adapters. Its first power has base2 and exponent M+1≥1, so L≥2; the remaining bases L and L+1 meet the power theorem's domain even if X=0 or M=0. Exact quotient/remainder extraction uses positive strict-bound slacks. Every odometer-shift quotient is a separately quantified natural integer. No integer intermediate used as a nonnegative witness is silently assumed to have that sign.

The sources directory preserves byte-identical copies of the following authenticated proof sources, read as inert data:

- PellMatiyasevic.lean at mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f: SHA256 993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a
- Report35 composition proof: SHA256 6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e
- Report35 loader proof: SHA256 1791518f521a147b014ca7636910b7775df64fcfe799b6fcb5a0261de4f99d34
- Report36 real proof: SHA256 9bc26062cc0e68fc8fee18290c347b309e2f711d208644ec541b29a5492071ae

The report proofs are now placed under `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/` in VladimirReshetnikov/ProveIt, with filename prefixes22-literal-sandpiles and23-real-sandpiles. Their recorded source hashes agree with the intake review. The general physical universality reference is Hannah Cairns, arXiv:1508.00161v2. That reference and the scoped report review do not independently verify the present literal graph or this new polynomial source.
