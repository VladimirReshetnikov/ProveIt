# Independent mathematical audit: one Pell cap and a common ordinate budget

Status: the cap reduction, the aggregate bound, and the pooled residue-square
replacement are mathematically sound over the nonnegative integers under
the inherited positive-power interface. This note separates
the new argument from the unchanged indexed-Pell theorem and source
calibration. It does not assert an object-ZFC or Lean proof certificate.

## 1. Exact lemma

For an integer A >= 2, define X_j(A), Y_j(A) by

    X_0=1, Y_0=0,
    X_(j+1)=A X_j+(A^2-1)Y_j,
    Y_(j+1)=X_j+A Y_j.

Let W, A, k be integers with 1 <= k < W < A-1. Suppose the full inherited
index certificate has established V=Y_W(A). Then the following system in
nonnegative integers X,Y,q,s is equivalent to (X,Y)=(X_k(A),Y_k(A)):

    X^2-(A^2-1)Y^2=1,
    Y=k+(A-1)q,
    V=Y+s+1.

Proof. The second row gives Y>=k>=1. The principal Pell classification
therefore gives a unique j>=1 with (X,Y)=(X_j,Y_j). The last row and strict
monotonicity of Y_j give j<W. The recurrence gives Y_j(A)=j modulo A-1,
so j=k modulo A-1. Both j and k belong to [0,W), an interval shorter than
A-1, hence j=k. Conversely, Y_k>=k and the same congruence give the
nonnegative quotient q=(Y_k-k)/(A-1). Strict monotonicity gives
s=Y_W-Y_k-1>=0.

No intended value of a power output is used in this proof. In particular,
one must not infer j=k from the congruence without the cap.

## 2. One aggregate cap replaces all individual cap slacks

Let k_1,...,k_m be the distinct seed exponent *atoms* (syntactic identities
are what the frame deduplicates). Replace all individual final rows by

    V=1+Y_1+...+Y_m+s,   s>=0.

Soundness is immediate: each Y_i is nonnegative, so each Y_i<V. The proof
in Section 1 applies separately.

For completeness, the raw common frame is

    W=2+sum(a : a is a distinct semantic base, exponent, or power output).

Every seed exponent atom occurs in that set, and each prescribed exponent
is positive. Consequently m<=sum_i k_i<=W-2. Since k_i<W,

    sum_i Y_(k_i)(A) <= m Y_(W-1)(A)
                        < (2A-1)Y_(W-1)(A)
                        < Y_W(A).

The last inequality follows from

    Y_W=2A Y_(W-1)-Y_(W-2),

and Y_(W-2)<Y_(W-1). Here m<=W-2<A-1<2A-1. Thus the aggregate slack
V-1-sum_i Y_(k_i) is a nonnegative integer.

This argument remains valid if distinct syntactic exponent atoms have the
same numerical value. It would require a fresh count argument if zero
exponents were added to the supported interface. No such extension is
needed for the current positive-power source.

The implemented fused variant uses

    V=W+1+Y_1+...+Y_m+s

and deletes the old private cap margin Y_cap-W. This also supplies the
inequality V>=W needed by the full cap certificate. Completeness needs the
slightly stronger estimate

    V-sum_i Y_(k_i) > (2A-1-m)Y_(W-1)
                      >= 2A-W+1 > W.

Thus its slack V-W-1-sum_i Y_(k_i) is nonnegative as well.

Only seed ordinates belong in either sum; the cap ordinate itself must not
be included. The exact addition identities then certify the remaining
derived Pell indices from certified seed pairs.

## 3. The large base is proved before any power semantics

The retained global scale rows have W=2+sum(atoms), Z>=1 and

    A^2-((W+1)^2-1)(WZ)^2=1.

They imply W>=2 and A>=2 without interpreting any power output. Classify
this Pell solution at parameter W+1: A=X_h(W+1), WZ=Y_h(W+1), h>=1.
Since Y_h(W+1)=h modulo W, h is a positive multiple of W, hence h>=W.
For a>=2, X_h(a)>=a^h; for instance this follows inductively from the
addition recurrence and nonnegativity. Therefore

    A >= (W+1)^W > W+1,

which gives the required strict W<A-1. Every actual requested exponent
atom k occurs in the raw sum defining W, so k<W independently of the
equation's intended arithmetic interpretation.

The order is therefore:

1. Read W as the sum of the proposed semantic arguments and outputs.
2. Recover the large common A from the last norm, without knowing whether
   the proposed power outputs are correct.
3. Interpret the one full cap certificate to obtain V=Y_W(A).
4. Recover every seed index using its principal norm, residue, and cap.
5. Recover derived indices by the exact Pell addition identities.
6. Apply the unchanged positive-power residue theorem.

There is no need to put the new cap pair in the semantic power list. Doing
so would change the frame and could introduce a circular completeness
specification. The examined construction creates the cap as an index
certificate, not as a new exponentiation request.

For constructive completeness, first evaluate the finite semantic power
DAG with its genuine integer outputs. This fixes W. Choose a solution of
the last norm whose index is a positive multiple of W, giving A. Next
construct the old full indexed-Pell certificate at the numerical index W.
Then use its V to bound the already determined principal pairs. The old
certificate's auxiliary witnesses do not enter the definition of W.

## 4. Interface and literal obligations

The full cap certificate must retain all its old conditions: the three
Pell norms, cap ordinate at least W (which may be supplied by the fused
aggregate row), positive auxiliary multiple of its
square, the comparison-base congruence, and the two index congruences.
The new argument does not replace that one certificate.

The graph must retain natural domains for X,Y,q,s and all aggregate
ordinates. An unrestricted-integer equation cannot inherit this proof by
simply dropping these sign restrictions.

The seed exponent atoms must be a subset of the exponent atoms of actual
semantic power requests. Addition-derived indices must be topologically
grounded in seeds or the fixed index pairs. The cap pair must be excluded
from the aggregate sum and from the semantic frame atoms.

The contraction checker remains responsible for equivalence between the
raw quadratic system and the exported quartic. A successful contraction
check proves that finite algebraic equivalence, not the unbounded source
calibration to C222/ZFC.

## 5. Adversarial controls

The strict cap is essential. At A=4, k=2 and j=5 one has
Y_j=3905 and Y_j=k+(A-1)*1301. Thus principal norm and residue alone
accept the wrong index.

The large-base hypothesis is also essential. At A=3, W=5, k=1, j=3,
Y_j=35, and Y_j=k+(A-1)*17; nevertheless j<W and Y_j<Y_W. The cap and
congruence do not determine the index if W exceeds the residue modulus.
The retained last norm rules out this regime.

These examples are tests of omitted hypotheses, not counterexamples to
the stated construction.

## 6. Audit conclusion

The cap and aggregate-budget replacement has a complete elementary
soundness and completeness argument once the one inherited cap certificate
is interpreted. The further replacement in Section 7 is also sound. The
source refutation equivalence, the universal indexed-Pell certificate,
positive-power graph correctness, and the final quadratic-to-quartic
contraction remain the declared dependencies.

## 7. Preferred refinement: one pooled residue-square congruence

Once the fused global cap is present, remove the m individual congruence
rows and their m quotient variables. Introduce one natural Q and the
single quadratic residual

    sum_i (Y_i-k_i)^2 - A Q + Q = 0.

The principal norms and natural domains give pairs
(X_i,Y_i)=(X_(j_i)(A),Y_(j_i)(A)) with j_i>=0. The index may now be zero:
no individual row Y_i>=k_i has been assumed. The global cap still gives
j_i<W. Reducing the pooled row modulo A-1 and using Y_j(A)=j modulo A-1
gives

    A-1 divides sum_i (j_i-k_i)^2.

Every semantic exponent is positive before interpreting any power, so its
atom contributes at least one to the raw frame. Thus m<=W-2. Since both
j_i and k_i lie in [0,W),

    0 <= sum_i (j_i-k_i)^2 <= m(W-1)^2 < W^3.

The scale bound proves W^3<A-1 for W>=3. Indeed for W=3,
(W+1)^W-1=63>27; for W>=4, (W+1)^W>(W+1)^3>W^3+1.
The selected horizon-12 source has t>=12 and a power with exponent t,
hence W>=14. The earlier horizon-16 checkpoint gives W>=18. Both exceed
the required threshold three.
The only multiple of A-1 in the displayed range is zero. Therefore each
j_i=k_i, simultaneously.

For completeness, choose the genuine principal pairs. Each Y_(k_i)-k_i
is divisible by A-1, so the integer

    Q = sum_i (Y_(k_i)-k_i)^2/(A-1)

is nonnegative. No individual quotient must remain in the equation.

This refinement uses a sum of squares only to collect bounded *index
errors after reduction modulo A-1*. It does not require the enormous
ordinates Y_i themselves to be bounded by A-1. The separate cap supplies
the correct smaller index interval. Without that cap the pooled row can
still admit wrong indices separated by multiples of A-1.

The new raw residual has degree at most two in the graph variables,
including the variables that already store the k_i. Squaring it in the
final sum of residual squares therefore preserves total degree four.
