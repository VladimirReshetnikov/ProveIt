# Independent mathematical audit of the round15 direct equations

## Conclusion and scope

The new natural arithmetic architecture and the selective-even signed compiler have an ordinary, unbounded soundness and completeness argument. The audit found no missing zero-ordinate, small-factorial, negative-output, or radix-bootstrap branch in the released constructions described below. The complete literal polynomial, not a schematic abbreviation, is the sum of the squares of every supplied quadratic residual.

The logical C222-to-ZFC refutation calibration, its fixed source syntax, and the original simultaneous Pell construction remain inherited dependencies. This audit does not claim a newly checked Lean/Rocq proof, a printed internal ZFC proof object, a proof of Con(ZFC), or a global variable minimum. Finite regressions and coefficient reconstruction are not substitutes for the following universal arguments.

The audit applies to the natural `unified_derived_cantor`, `unified_slack_shell`, both additional syntax companions, and the squared-radix companions, and to both signed sources `unified_reparam_derived_shell` and `unified_reparam_shell`. The frozen primary endpoint `integer442` has 442 integer variables, 290 quadratic rows, 4,652 collected quartic terms, and coefficient height 128,446. Its full final integral translation is independently replayed, including all 54 nonzero shifts. The derived-label source has 38 guards and the local-slack companion has 39. The equation file SHA256 is `61877e6e50550bcdf72d5cee047d184c228b5ad21947d6cb2ef827d9673715d8`.

## 1. Natural bootstrap: no binomial meaning is used prematurely

Let t>=16, rho=F^2, V=(rho+1)^t, and let B initially denote only the proposed binomial output. The natural ceiling rows are

    V+B=BF+u+1,        B=u+v+1.

The independently positive power base rho+1 and positive exponent t permit the simultaneous power theorem to recover V before interpreting B. Thus V>=1. The second raw row gives B>=1, and subtraction gives V+v=BF. Consequently F cannot be zero. Since V>F^2, division by F>0 gives B>F>=1, and then V<=BF<B^2.

This excludes both F=0 and B=1 from actual zeros, without presupposing a factorial or binomial. With K=2R, N=B^K and q=N^K, K>=2 gives q>=B^4>V. The squared-base companion has an even larger q. All these bases and exponents are now valid positive power inputs.

The inherited uniform bound binom(r+t,j)<=(r+1)^t for r>=1 and 0<=j<=t is valid without r>=t. Pascal induction handles j<t, while the product formula handles j=t. With r=F^2>=1, every low digit in the exact binomial graph is less than q. Hence the graph really returns B=binom(F^2+t,t). The distinction between a proposed B and its later exact interpretation is essential.

## 2. There is no additional factorial fixed point

Put H=t! and f=V/B. The two ceiling equations say F-1<f<=F. The exact product formula gives

    f=H product(i=1..t) (F^2+1)/(F^2+i).

Each factor is at most one, so F<=H. Since F>=1 and each factor increases with F^2, f>=2^t/(t+1)>t^2 for t>=16. The latter inequality holds at t=16 and follows inductively from 2t^2(t+1)>=(t+1)^2(t+2). Thus F>t^2.

For a_i=(i-1)/(F^2+i), one has sum a_i<t(t-1)/(2F^2)<1/(2F). Therefore

    H(1-1/(2F)) < H product(1-a_i) = f <= F.

It follows that H<F+F/(2F-1)<=F+1. Integrality and F<=H force F=H. Conversely F=H gives H-1/2<f<=H, which supplies both natural ceiling witnesses. This is a complete fixed-point proof on the padded horizon, not just numerical evidence from large candidate F.

The square-output fixed point and the uniform coefficient bound are inherited from the Synchronized Exponents / earlier Bootstrap line. The new step is identifying that exact B with the CRT modulus product and using the raw inequality V<B^2 to remove the extra radix inflation.

## 3. CRT product, carry bounds, and both directions

For i=1,...,t, d_i=1+F^2/i is integral and is congruent to one modulo F, since i divides F=t!. Every prime divisor of d_i therefore exceeds t. If a prime divided d_i and d_j, it would divide i*d_i-j*d_j=i-j, which is impossible for distinct i,j in [1,t]. Thus the moduli are pairwise coprime and their product is exactly binom(F^2+t,t)=B.

Each independent representative is at most cN^2 with c<=10. For every range lower index 1<=k<R and j<=k,

    binom(n,j)<=n^k<=10^k N^(2k)<N^(2k+2)<=N^(2R)=q.

If j>n, the coefficient is zero. The strict middle comparison follows from 10<16 and N>=2^(2R). For the derived label J, the literal majorant and F=t! give J<=N^(3ell), with 3ell(t+1)<K; hence its required coefficients are also below q. The derived label is not silently counted among the independently bounded CRT coordinates.

The standard valuation lemma used for decoding is valid: p^e dividing binom(a,k) forces a mod p^e<k. If no multiple of p^e occurred among a-k+1,...,a, every valuation summand at levels >=e would vanish and the total valuation would be at most e-1. Decode modulo p^(K v_p(d_i)), identify the index modulo p>t, and use the majorant L<2^K to turn divisibility into exact local equality.

Conversely choose CRT representatives at precision d_i^(2K) in [1,N^2]. Division by k! loses at most k-1<K powers of p, which leaves at least K v_p(d_i) powers. This proves all range divisibilities, including the derived label. The aggregate bound has a natural slack. The inherited Horn-flow argument is still required: it does not assume an acyclic supplied multiset, and it does not treat the truth label's unit weight as a distinct prime-supported label.

## 4. Signed bootstrap: establish q>=3 before using residue orientation

In the signed compiler, use Q for the digit radix q and Vc for the common auxiliary Pell ordinate, to distinguish it from the factorial numerator V.

The direct semantic nonnegative guards are reconstructed before power semantics. Seven paired guards use a weighted interval identity after remainder reparameterization:

    Q*u+s = L-2 = Q*u0+s0,
    Q>0, u0>=0, s0>=0, u*s>=0.

These imply u,s>=0. If u<0 then s>=-Q*u>0 and u*s<0; the other negative case is symmetric. The independent raw equations first give B=fact_remainder+fact_slack+1>=1 and Q=B+choose_oslack+1>=2. Neither inequality uses any weighted-pair conclusion, so there is no circularity. The anchor then gives L>=2. Every anchor pair retains its two individual guards.

Every seed exponent is already positive at this point: t>=16, K=2R>=38, t+F^2>=16, encoded representatives are positive by their +1 constructors, x+1>=1, and y+1>=2 because y=F+r0+1. In the derived-label variant, the complete monotone constructor gate ledger gives J>=64 using only these guarded leaves. The independent checker reconstructs every bound and does not presume that J is a decoded valid formula label.

The frame is exactly

    W=2(2+sum a^2),

where a runs over every distinct actual power base, exponent, and output. It bounds |a|, each positive doubled exponent 2k, and every squared output m^2. The retained A>=0 and Zminus1>=0, together with the unchanged bootstrap norm A^2=1+W^3(W+2)Z^2 and Z=Zminus1+1>=1, give A>=2. Standard Pell classification then gives A>(W^W), exactly as in the inherited construction. This bound is established before recovering any source power.

The retained common Vc>=1 and literal product Vc=product(Y_i^2)*(v+1) exclude Y_i=0 for every seed and force v+1>=1. The common norm yields |U|>=A, not U=0. The guarded comparison multiplier makes the comparison base Bc=1+4Vc(q4+1)>1 and odd. Thus no degenerate auxiliary equation with Bc=+/-1 is available.

Retain the ordinary ordinate guards at seed indices t and K. The t pair is first oriented by the call Q^t=L, whose base is already at least two and whose output is already positive by the remainder interval. The signed small-residue lemma excludes a negative abscissa and recovers the exact power. The same positively oriented t pair then recovers V=(F^2+1)^t, even if its base was only one before this step.

The ceiling rows now give F>=1, B>F and hence B>=2 and Q>=3. Only after this is the retained K seed oriented using B^K=N, permitting N to be signed beforehand. This recovers N>0 and then Q=N^K. All arguments use the square frame's absolute bounds. The derived t+1 pair is still one ordinary Pell step from the undoubled t pair and is therefore already positive. It must not receive the two-step correction required in an all-even compiler: t was intentionally not doubled here.

## 5. Even terminal indices: both the zero and unit ordinates are excluded

At each of the other thirteen seeds, the residue row now requests e=2k, but the old private Y-k slack has no nonnegative guard. Removing that one-use definition is an exact existential projection with its displayed integral restoration.

The product Vc>0 has already excluded Y=0. Suppose |Y|=1. The norm makes X=+/-A. Write |U|=chi_A(h). The comparison Pell recurrence and Bc=A modulo U imply chi_A(j)=+/-A modulo chi_A(h). The elementary abscissa-residue lemma forces j odd. Since Bc is odd, its ordinate psi_Bc(j) has parity j, whereas the modified residue R=2k modulo 4Y makes R even. This is a contradiction. Thus |Y|>=2, and Pell classification strengthens this to |Y|>=2A>e.

From Y^2 dividing Vc, the squared-divisibility lemma gives the main index i<=h and |Y| dividing h. Transfer of the comparison abscissa gives j=+/-i modulo 2h; the comparison-base-one residue gives j=+/-e modulo 4|Y|. Hence i=+/-e modulo 2|Y|. Since 1<=i<=|Y| and 1<=e<|Y|, only i=e is possible. This identifies the absolute main Pell coordinates at exactly 2k, with no assumed sign of X or Y.

For the supporting call at base n>=2, put M=m^2 and Np=n^(2k). The four sign patterns in the power congruence give, respectively, divisibility of

    M-Np,  M+Np,  M*Np-1,  M*Np+1

by the large modulus T=2An-n^2-1. The frame bounds put every nonzero candidate below T in absolute value. M+Np>0; M*Np+1>0; and M*Np-1 cannot vanish because Np>=4. Thus only the positive-coordinate branch survives, and M=Np. This works even when the unsquared m was initially negative or zero. The q-power denominator outputs are already positive from the interval bounds, so those recover m=q^k and prove the relevant denominators divisible by q.

## 6. Remainder substitution orients terminal powers without an extra unknown

For the eleven base-(q+1) terminal powers, the old remainder coordinate r is replaced everywhere by

    r=1+q*u.

This is NOT a bijection of unrestricted integer coordinate spaces, and it is not described as one. It is an existence-preserving restriction after the arithmetic power semantics. Its role is to enforce the particular residue already possessed by every true solution.

After the denominator q^k has been recovered, the division row implies m=1 modulo q. The squared-output theorem says m=+/-(q+1)^n. The positive sign has residue one. The negative sign has residue minus one and can have residue one only if q divides two. The independently established q>=3 excludes it. Thus m=(q+1)^n>0, and all terminal powers acquire their intended meaning.

Conversely start from the genuine natural arithmetic tuple. Its ordinary remainder satisfies 0<=r<q^k and r=1 modulo q. Because k>=1 and q>=3, this gives r>=1 and u=(r-1)/q>=0. Every reparameterized remainder and every weighted interval guard therefore has a witness. The endpoint and range quotient signs are recovered from positive numerators and the usual remainder inequalities, just as in the inherited signed compiler.

## 7. Completeness must rebuild the private Pell certificate

Keep the genuine arithmetic tuple, compute the enlarged exact W, and construct A=chi_(W+1)(W), Z=psi_(W+1)(W)/W. Choose ordinary positive seed pairs at t and K, doubled positive pairs at every selected seed, and the ordinary one-step derived t+1 pair. One finite-ring unit-order argument modulo four times the product of all seed ordinates squared supplies common U,Vc with Vc>0 and the required divisibilities. CRT then supplies a sufficiently large positive comparison base; fill every comparison pair and quotient from the recurrence.

All guards have witnesses from the classical representation n=a^2+b^2+c(c+1) for n>=0. The reparameterized arithmetic remainders were handled above. This gives a full signed zero whenever a natural arithmetic zero exists. In the opposite direction, the preceding recovery gives the genuine arithmetic tuple, from which a fresh natural common Pell certificate can be constructed.

This is a zero-existence equivalence, not preservation or bijection of the old and new Pell witnesses. By contrast, the subsequent monic projections and final integral translations really do have the stated exact coordinate-restoration maps, apart from explicitly unused coordinates restored to zero. The Horn factorization is also an exact existential circuit replacement, using signed affine factors only internally and restoring their squares at the external interface; private guard triples need not correspond uniquely.

## 8. Literal checker boundary

`check_direct.py` imports no generator or eliminator. It independently verifies all power-atom expansions into the actual raw retained coordinates, the full square frame, the precise thirteen doubled seeds, selected output squarings, all eleven complete remainder substitutions, weighted pair identities and guarded anchors, every sign-inference equation, every three-square guard, all private-slack deletions, the exact Horn-factorization interface and protected-variable non-escape, every monic substitution, the complete integer translation, and every collected coefficient of the final sum of squares.

It also replays the six natural projection certificates, including rational sums-of-squares nonnegativity certificates, and reconstructs their full quartics. Deliberate mutations of coefficients, seed selection, frame atoms, pair anchors, guard expressions, sign proofs, factor roots, restorations, translations, and metrics must be rejected both normally and under Python optimization. The signed semantic arguments above and the inherited logical calibration are expressly outside the claim of a finite literal checker.


## 9. Reproduction of the frozen primary audit

From the round15 root run:

    python direct_audit/check_direct.py --variant unified_reparam_derived_shell --raw unified_derived_shell --endpoint integer442 --skip-natural --output direct_audit/CHECK_INTEGER442.json
    python -O direct_audit/check_direct.py --variant unified_reparam_derived_shell --raw unified_derived_shell --endpoint integer442 --skip-natural --output direct_audit/CHECK_INTEGER442_OPT.json

The two receipts must agree byte for byte. Omit `--skip-natural` to replay all six natural projections too. The checker needs the complete certificate-bearing source directory in addition to the final five integer442 files and the raw natural source. The fourteen mutation controls include a false seed lower bound and an altered remainder residue. Neither a hash-only comparison nor successful finite arithmetic samples replace the explicit semantic proof.
