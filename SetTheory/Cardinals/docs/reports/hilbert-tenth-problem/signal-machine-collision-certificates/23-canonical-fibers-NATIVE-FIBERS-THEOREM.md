# Infinite positive native fibers at fixed ports and scale

Status: independently reviewed, PASS; see `REVIEW.md`. Date: 2026-10-03.

## Result

Fix all semantic outer history data and the prescribed dyadic native AND scale in the inherited unbounded three-mass packet. If the resulting native AND block has one positive integer witness tuple, it has infinitely many. More strongly, from any positive tuple, nineteen of its twenty-two supplied coordinates can remain unchanged: only `native__j`, `native__o`, and `native__y_aux` need vary.

For valid padded AND ports, the inherited prescribed-scale completeness theorem supplies the initial tuple. Therefore fixing the outer height, even canonically, does not make an accepted nonempty packet fiber finite. This statement concerns the particular retained native circuit. It makes no general finite-fold MRDP claim and asserts no literature-open problem.

## 1. Fixed interface and exact source

The source is pinned at ProveIt commit `ad634b2d10ad666260f9fdff04ec94b75169ee4b`:

- [Prescribed AND64, §§1–2](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_binary_masked_selection63.md)
- [Binary-selector core, §1 equations (1)–(2), §2 inequalities (3)–(5), and §5 positive converse](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/native_controller_binary_selector56.md)
- [Actual complete three-mass arithmetic receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.json), SHA-256 `fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e`
- [Residue-history packing, §2 equations (7)–(8) and §4](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.md)

Write the fixed outer joined words as H,M,Aout and fixed outer prescribed scale as Qnative. The actual native scale and three ports are

    q=16Qnative, padded_A=16H+12,
    padded_B=16M+10, F3=16Aout+8.

These do not change in the construction below. The twenty-two positive coordinates are

    F0,F1,F2,
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux,
    odd_half,bound_beta.

All names in this display acquire prefix `native__` in the full receipt. In particular native h is a Pell index quotient, not the fixed outer history height. There are sixteen native comparisons.

## 2. The only equations affected

Take any positive native witness tuple at those fixed ports. Put

    p=2r+1, R=i c², D=R²−1,
    U=j c−p=o f−c, y=y_aux.

Positivity can be read directly from the source, without the deeper Pell index classification. The fixed scale q≥16, the odd equation gives s=2*odd_half+1≥3, and E=(wq)(sq)>0. Thus k=r+1+hE>r+1 and c=(sq)k+eta>48(r+1)>p. Since j≥1, U≥c−p>0. Also R=ic²>1. Thus R is an integer at least two and D is a positive nonsquare integer. The nonsquare assertion is optional: (R−1)²<D<R²; the proof below uses only D=R²−1 and R≥2.

The two comparisons involving j,o,y are exactly

    U=j c−p=o f−c,                                   (1)
    R²(U²−y²)=1−y².                                  (2)

The second is equivalent to

    (R U)²−D y²=1.                                   (3)

The distinct unchanged auxiliary norm is

    R²=(a²+4a+3)(f²−1).                               (4)

No other native comparison uses j,o,y. Literal receipt inspection gives their only direct gate uses as `of=o*f`, `jc=j*c`, and `aux_y2=y*y`; their comparison descendants are precisely `L17=P17` and `H17=aux_u_rhs`. Thus retaining every other coordinate automatically retains all other fourteen native comparisons, including (4), the input sums, scale checksum, parity and positivity bounds.

## 3. An explicit infinite parameter family

Set N=Rcf. Consider the fixed integral matrix

             [ R   D ]
    Bmat  =  [       ].
             [ 1   R ]

Its determinant is R²−D=1. Its reduction modulo N is therefore invertible. As an element of the finite group GL₂(Z/NZ), it has a finite positive order L. For a completely specified, if very inefficient, choice one can instead take

    L=(N⁴)!.

Indeed the cyclic subgroup contains at most N⁴ matrices, so its order is an integer at most N⁴, which divides (N⁴)!. In either choice Bmat^L is the identity modulo N.

For each integer n≥0 define

    (V_n,Y_n)^T = Bmat^(nL) (R U,y)^T,
    U_n=V_n/R,
    j_n=(U_n+p)/c,
    o_n=(U_n+c)/f,
    y_aux,n=Y_n.                                     (5)

Leave the other nineteen supplied native coordinates unchanged. Matrix powers and factorials here describe witnesses mathematically; they are not new gates or uncharged predicates in the inherited circuit.

### Integrality

Since Bmat^(nL) is the identity modulo N,

    V_n≡RU (mod Rcf), Y_n≡y (mod Rcf).

Consequently V_n/R is integral and

    U_n≡U (mod cf).

The original U+p=jc and U+c=of show that the displayed j_n,o_n are integers. Nothing requires c and f to be coprime.

### Strict positivity and distinctness

The starting V_0=RU and Y_0=y are strictly positive. One multiplication by Bmat sends positive V,Y to

    V'=RV+DY>V, Y'=V+RY>Y.

Thus every V_n,Y_n is positive and the subsequences are strictly increasing because L≥1. Hence U_n,j_n,o_n,y_aux,n are positive. All fixed coordinates were positive already. Distinct n give distinct y_aux,n, so (5) defines infinitely many distinct supplied twenty-two-tuples.

### Both changed comparisons

For arbitrary V,Y,

    (RV+DY)²−D(V+RY)²
      =(R²−D)(V²−DY²)=V²−DY².

Therefore (3) implies V_n²−D Y_n²=1 for every n. Substituting V_n=R U_n and D=R²−1 gives

    R²(U_n²−Y_n²)=1−Y_n²,

which is exactly the changed norm comparison (2). By construction

    j_n c−p=U_n=o_n f−c,

so (1) holds as well. All sixteen native comparisons have now been checked, and every one of the twenty-two supplied coordinates is positive.

## 4. Consequence for fixed outer histories

The residue-history prescribed-scale completeness statement provides at least one positive native tuple whenever the fixed packed words satisfy the genuine AND and scale conditions. Applying (5) at that same scale gives infinitely many native extensions. The outer data, their height and all outer supplied coordinates remain unchanged.

The literal complete receipt has no occurrence of j,o,y in its nonnative comparisons. The existing cleanup construction adds only an affine clock comparison on outer quantities. Therefore the native family lifts to infinitely many positive zeros of the complete nonempty packet with those outer coordinates held fixed. An extra canonical-height constraint independent of these three native coordinates also leaves this family intact.

This is a seed-relative explicit parameterization, not a numerical materialization of the astronomical canonical native tuple. Existence of the seed is the inherited completeness theorem; infinitude thereafter is the elementary matrix construction proved above. No claim is made that (5) enumerates the entire native fiber, and no claim of witness uniqueness or finite-foldness is drawn from deterministic computation. The separate zero-step no-witness circuits are outside this conclusion.

## 5. Relation to the pinned auxiliary-index construction

The pinned [fixed-minus parity proof, §§3–5](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md) already retains noncanonical auxiliary indices. It writes a normalized Pell index as s=epsilon*p+2mt and establishes that the retained minus congruences force t even. It explicitly materializes examples at s=4m−p and s=4m+p. Those statements suggest the family s=p+4mn while holding m fixed.

The proof above deliberately avoids a new index-classification or divisibility lemma: it obtains a simultaneous congruence period by finite matrix arithmetic. This is sufficient for the exact question about fixed ports and fixed native scale and does not require following the broader universal-computation references.

## Evidence boundary

The new local checker reads the pinned JSON only as data, independently traces occurrences of the three changed coordinates, and checks the small auxiliary recurrence examples described in its receipt. It does not import or execute third-party Python and does not numerically realize a complete packed native zero. The unbounded conclusion is the proof in §§2–4, conditional only on the inherited positive seed and its stated positivity bound.
