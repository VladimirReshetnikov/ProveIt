# A single factorial separates proof labels and carries the CRT certificate

## Completed change and precise scope

The generated equations in factorial_carrier_cantor/natural and
factorial_carrier_shell/natural have natural zeros exactly when the direct
C222 calculus has a finite refutation. With the inherited C222/ZFC
calibration, their absence of natural zeros is therefore Con(ZFC) in the
same ordinary external sense as the prior direct releases. This is not a
formal Lean endpoint and does not establish either consistency or
inconsistency. The elementary replacement proofs below are complete in
both directions; inherited syntax/calculus and Pell theorems are identified
in HYBRID_PROOF.md.

The structural change is to use the SAME F=t! twice:

1. As the separator for formula-label weights W_j=1+jF.
2. As the separator for reciprocal CRT moduli d_i=1+F^2/i.

A single new local bounded coordinate ensures that all possible labels in
a row are <=t. Consequently the former carrier power ((t+1)^t)^(2^22),
its 22 squarings, and the M0 parameter disappear. A new range column costs
one power request, so the total power count stays 19 after the carrier
power is deleted. This is a different certificate architecture, not an
algebraic rewrite of the old polynomial.

## 1. One global label bound per local row

Retain the inherited nine axiom/schema constructor codes c_1,...,c_9,
implication constructor I, and universal constructor A. A local row has
natural parameters a,b,c,d and arithmetic coordinates S,Sp,u,vq,w.
The bound imposed by one extra squared residual is

    t = w + c_1+...+c_9 + a+b+I(a,b)+A(a,b)+1.             (1)

All summands are natural. Therefore every axiom conclusion, each modus
ponens premise/conclusion a,I(a,b),b, and each generalization
premise/conclusion b,A(a,b), is at most t. Truth has label 0. The original
branch product remains unchanged, except that every occurrence of its
carrier M0+1 is replaced by F. In particular (1) is not inserted into
each branch separately, and the original signed-factor compression remains
applicable to the first seventeen difference-square gates.

The nine local column bounds are

    a,b,c,d,w <= t;       S,Sp <= y;       u,vq <= x.

The code in build_factorial_carrier.py prints the full finite definition.
Its local majorant is produced from the full modified expression, including
(1), not inherited unchanged: the emitted exponent remains E=8388608
for each syntax variant. The majorant certificate is part of every raw
endpoint and says 0<=L(i,local)<R^E, with R=2+t+x+y+F.

## 2. Exact multiplicity separation by one small factorial

For 1<=j<=t, W_j=1+jF is greater than one. For distinct j,k, a common
prime divisor p of W_j,W_k divides (j-k)F but does not divide F. Hence
p divides j-k and p<=t. But then p divides t!=F, contradiction. Thus
W_1,...,W_t are pairwise coprime. W_0=1 deliberately carries no prime.

For each j>0 choose a prime p_j dividing W_j. Its valuation isolates
label j: v_(p_j)(W_k)=0 for every other positive k<=t, and also for k=0.
This does not require the weights themselves to be prime or square-free.

## 3. Soundness of the unordered Horn-flow certificate

For a horizon t, let a zero of every bounded local polynomial be given.
The overlapping beta equalities are

    x = S_i  + [1+(i+1)y]u_i,
    x = Sp_i + [1+(i+2)y]vq_i             (0<=i<t),

with S_i,Sp_i<=y. Because each remainder modulus is greater than y,
uniqueness of nonnegative remainders yields Sp_i=S_(i+1) for i<t-1.
The outer endpoint rows are

    x=F+1+(y+1)u0,     y=F+1+r0,
    x=1+[1+(t+1)y]ut,

so S_0=F+1=W_1 and Sp_(t-1)=1.

The nonnegative Horn branch product is zero, so at least one actual
calibrated rule branch vanishes. Write its premise labels p_i,q_i and
conclusion label v_i, using label 0 for unused premises. Its equality is

    Sp_i W_(v_i) = S_i W_(p_i) W_(q_i).                    (2)

For an axiom this includes p_i=q_i=0. For generalization one premise is
0. For truth all three are 0. A zero of the bundled schema factor also
sets its nonnegative side-condition square to zero, so it is an actual
source rule, not just its numerical weight equality. Equation (1) bounds
all these labels by t.

Every weight is positive. Since S_0=W_1>0, (2) inductively proves every
S_i and Sp_i positive. Multiplying (2) and cancelling the overlapping
positive accumulators is therefore legitimate. The endpoints give

    product_i W_(v_i) = W_1 product_i W_(p_i)W_(q_i).       (3)

Take v_(p_j) for a positive label j. Pairwise coprimality reduces (3) to

    #conclusions(j) - #premises(j) = 1 if j=1, else 0.       (4)

The nonzero multiplicity v_(p_j)(W_j) cancels. No balance assertion for
label 0 is made or needed.

For completeness of the logical extraction, let D be the closure of
truth 0 under the finitely many valid source rules chosen above. Suppose
1 is not in D. For each rule whose conclusion is outside D, at least one
premise is outside D. Therefore

    total conclusions outside D <= total premises outside D.

But summing (4) over the positive labels outside D gives left minus right
equal to 1. This is a contradiction. Hence 1 belongs to D and has a
finite derivation by the actual source rules. This proves soundness even
when the supplied rule multiset has cycles or repeated rules. Truth's
unit weight cannot create a false refutation because 0 already belongs
to D.

## 4. Constructive completeness without a circular horizon

Start from a finite C222 derivation of falsity. Expand its finite proof
DAG to a finite proof tree and collect the finitely many rule parameter
tuples. For each tuple compute the entire label sum in (1), including
codes of the branches not used by that tuple. Also include the fixed
truth-padding tuple with a=b=c=d=0.

FIRST choose a horizon t at least 32, at least the expanded proof-tree
step count, at least every parameter a,b,c,d, and at least every one of
these finitely many label sums. This choice does not depend on F or on
any arithmetic accumulator. Set the new slack w in each row to t minus
its label sum; it lies in [0,t]. THEN define F=t! and the weights.

Starting with the one-element pending multiset containing falsity, expand
the root of the proof tree backwards. At each step replace a conclusion
v by its premises p,q. Let S be the product of weights of the pending
multiset before the step and Sp that product after it. Both are positive
integers and (2) holds. Truth leaves have weight 1. After the proof tree
is exhausted the product is 1. Insert enough truth steps p=q=v=0 to
reach exactly t rows; these leave the current accumulator unchanged.
Their fixed label sums were included before choosing t.

Now, after the horizon and factorial are fixed, choose a positive y
large enough for every S,Sp and for F+1, and divisible by t!. The beta
moduli 1+(i+1)y, for 0<=i<=t, are pairwise coprime by the same elementary
argument as above. CRT gives a common natural x with the required
accumulator residues. Its Euclidean quotients are natural and at most x,
because every residue is between 0 and y. The two endpoint quotients and
r0=y-F-1 are natural. This supplies exactly the bounded local source
certificate. There is no dependence of t on the accumulator sizes or on
their beta encoding.

The Horn proof uses existing source-rule calibration; it does not require
any numerical encoding of a universal Turing machine.

## 5. Combining the shared factorial with reciprocal prime-power CRT

Use t=t0+32, F=t!, T=F^2, B=binom(T+t,t), N=B^K, and

    R=2+t+x+y+F,                   K=2R.

All arguments in HYBRID_PROOF.md Sections 1-3 apply without change to
the now-nine local columns. There are ten total range requests after
including the index range. In particular the strengthened precision-2K
CRT completeness construction is retained; the invalid fixed canonical
index is not used.

The old large-carrier growth proof is replaced by a smaller fixed floor:

    F >= 32! >= product_(j=17)^32 j > 16^16 = 2^64.

Thus R>2^64. For E=8388608, 64E<2^64 and 2E<=2^64. At r0=2^64,
r0^E=2^(64E)<2^r0. For all r>=r0,

    (1+1/r)^E <= sum_(j=0)^E (E/r)^j < 2,

so integer induction yields R^E<2^R<2^K. This establishes the amplified
CRT evaluation bound. It is used only AFTER recovering F=t! by the
self-bounding factorial/digit proof, not as a prerequisite for that
recovery.

Use the same self-bounding radius rho=Ft^2, V=(rho+1)^t and radix
q=N(N+V+1)^K. The exact order from HYBRID_PROOF.md remains valid: raw
index congruence gives B>0; positive V and the ceiling rows give F>0;
q>V^2 allows the first exact factorial digit and then the reciprocal
product digit to be interpreted; only then use B>=2 and N>=2^K.
No assumption about the new label carrier is required in this bootstrap.

For the ten positive CRT representatives the aggregate inequality is now

    sum(all ten representatives) + g = 10N^2.

For every range lower index 1<=k<=R-1 and every digit j<=k,

    binom(n,j) <= n^k <= 10^k N^(2k)
                        < 16^R N^(2k)
                        <= N^(2k+2) <= N^(2R) < q.

This proves carry-freeness and correctness of all ten fused divisibility
graphs. The raw generated value remains a nonnegative source polynomial,
so its quotient by N is natural. The simultaneous positive-power theorem
supplies witnesses for the finite power family in the reverse direction.
Every other forward/reverse step is as in the complete hybrid theorem.

## 6. Literal endpoints and reproducibility

Each polynomial is the sum of squares of the entire residual list in its
natural/equation.json, equivalently the full coefficient list in its
natural/expanded_polynomial.json. Every unknown is a nonnegative integer.

| Variant | Unknowns | Rows | Degree | Monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Factorial carrier, Cantor | 350 | 268 | 4 | 11472 | 116081874 |
| Factorial carrier, square shell | 351 | 269 | 4 | 14871 | 39191215 |

The raw natural systems have 537/552 unknowns respectively; the independent
contraction replay certifies all 187/201 eliminations and expands every
quartic coefficient. Both variants use one factorial, two exact binomials,
ten range graphs, nineteen positive powers, sixteen seed indices and one
derived index. These are variable/support/height tradeoffs. In particular
the earlier 363-natural equation has fewer monomials; no global optimum is
claimed.

Commands (run from the round14 directory's parent):

    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round14/architecture/build_factorial_carrier.py --horizon-minimum 32 --output NEW_DIRECTORY
    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round14/architecture/build_factorial_carrier.py --syntax xx0 --horizon-minimum 32 --output ANOTHER_NEW_DIRECTORY
    PYTHONDONTWRITEBYTECODE=1 python diophantine_zfc_round14/architecture/check_semantics.py --output SEMANTIC_CHECKS.json

The semantic regression suite checks 361200 prime-power range cases, 32
constructive CRT fixtures, 600 proposed factorial values, 47904 small
Horn-rule multisets, and explicit negative controls. These finite checks
do not prove an unbounded theorem, decide consistency, or replace the
ordinary proofs above.

The later factorial16_cantor and factorial16_shell snapshots retain the
same variable counts but use t=t0+16. Their coefficient heights improve
to 86523090 and 10855087 respectively. The horizon-16 growth proof is
given in DERIVED_LABEL_RANGE_PROOF.md Section 3 and applies to these
slack variants as well. The builder's current default is explicitly 16;
the commands above preserve the original horizon-32 snapshots.
