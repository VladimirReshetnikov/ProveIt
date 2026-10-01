# Absorbing the strong Pell comparison lowers degree at the same cost

The shifted-X variant of the
[shared-history compiler](group_projective_shared_history_rhs.md) has
an equivalent polynomial with smaller degree and the same literal
operation count. Turn its retained strong comparison into one more
unit factor. A modulo-four exclusion makes this an exact transformation
over all supplied integer assignments, including signed assignments.
All positive witnesses, ordinary inputs and fixed compiler constants
remain unchanged.

Write the parent's strong residual as

    delta=T^2-Delta(f^2-1),
    T=ic^2, Delta=(a+2)^2-1,

and its existing five-unit product as W. Add

    N4=1+delta,        U=W*N4.                          (1)

Delete the strong comparison, and replace W=1 by U=1. The final
polynomial is

    F=U*(1+sum_remaining_outer R_i^2)-1.                (2)

The default illustrative ten-letter result remains **279 operations
and 42 positive witnesses**, while its degree falls from 4298 to
**3502**. The certificate has 259 operations and seven comparisons.
This is a complete fixed-table theorem. The universal numerical matrix
alphabet is still uninstantiated, and the separate numerical 75/88
frontiers are unchanged.

## 1. Unconditional integer zero-set equivalence

For arbitrary integers A,T,f, let

    N=1+T^2-(A^2-1)(f^2-1).

Modulo four, squares are zero or one. If A is odd, N is congruent
to 1+T^2, whose possible residues are one or two. If A is even, A^2-1 is three modulo four. For f odd,
N is again congruent to 1+T^2; for f even, N is congruent to T^2.
Thus N has residue zero, one or two, and never three. In particular,

    N != -1.                                           (3)

Apply this with A=a+2. No positivity, dyadic scale, recovered native
unit or strong equation is assumed. In the actual source T is itself
an integer polynomial, so the exclusion applies on every supplied
integer assignment.

Now W*N4=1 forces both integer factors to be units. By (3), N4 must
be +1, and then W=1. Therefore

    W*N4=1  iff  W=1 and delta=0.                       (4)

This proves equality of the two certificate zero sets on exactly the
same supplied coordinate vectors. All unchanged outer comparisons
remain explicit. It also restores the original strong comparison
before invoking any positive native-selector proof. No native sign
lemma has been reordered or weakened.

For the final output (2), the second factor is a positive integer
at least one. Hence F=0 iff U=1 and every remaining R_i=0. Combining
this with (4) gives exactly the parent's integer zero set, and therefore
exactly its strictly positive zero set. Unlike a sum of squares, the
output need not be nonnegative away from its zeros; no off-zero sign
claim is used.

## 2. Literal schedule and full compiler costs

The parent already computes T^2 and K=Delta(f^2-1). The
[source](group_projective_strong_unit_product.py) appends exactly

    strong_unit_difference=T^2-K,       one subtraction,
    strong_unit=strong_unit_difference+1, one addition,
    seven_units=six_units*strong_unit,  one multiplication.

Names `six_units` and `seven_units` are historical source names; their
values are the five-factor W and six-factor U, respectively. The
existing certificate prefix is unchanged instruction for instruction.
The comparison U=1 replaces W=1, and T^2=K is removed. No witness,
input, parameter or other comparison changes.

If the parent has n certificate gates and e comparisons, the new
certificate has n+3 gates and e-1 comparisons. Both outer-product
finalizers use one multiplication per comparison and two additions
minus one per comparison count. Thus

    new polynomial cost=(n+3)+3(e-1)-1=n+3e-1.

The M/A split is also unchanged: the certificate adds 1M+2A, and its
finalizer removes exactly 1M+2A. Every fixed-numeral multiplication
and each of the new three gates is charged.

Use the preceding fixed-table notation:

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

The complete certificate costs C+1 and has `8-chi` comparisons and
`m+27-chi` positive witnesses. Its final polynomial costs
`C+24-3chi`. For the illustrative ten-letter table:

| Mask reuse | Computed P | Certificate | Polynomial | M | A | Equations | Positive witnesses | Degree |
|---|---|---:|---:|---:|---:|---:|---:|---:|
|No|No|260|283|119|164|8|43|1485|
|No|Yes|260|280|118|162|7|42|2926|
|Yes|No|259|282|118|164|8|43|1773|
|Yes|Yes|259|279|117|162|7|42|3502|

The source exposes the actual complete certificate and final output
DAG for every option. It does not merely count a formal product or
assume the old strong residual was paid inside the certificate.

## 3. The remaining outer degree, including an idle-only table

All degrees below are measured in actual supplied coordinates before
any equation is imposed. Set

    Q=nu L,          A0=nu(4L+m+15).

The shifted-X parent proves the exact degrees and nonzero highest forms

    deg W=5A0+8Q+32,       W* as in the parent,
    deg delta=2A0+6,       delta*=-(a*)^2*f^2.

Adding one does not alter delta's highest form. Therefore

    deg U=7A0+8Q+38,       U*=W* delta*.                (5)

The only remaining outer residuals are four histories, the joint
scalar bound, sparse flow, and the repunit comparison when P is
supplied. They all have degree at most three. We next identify their
exact maximum, rather than assuming it for an empty macro list.

Let D*=alpha*x+height_slack, B*=16D*, and

    J*=sum_e Ehat_e,
    ell_i=sum_{label(e)=2i+1} Ehat_e
          -sum_{label(e)=2i+2} Ehat_e,  i=0,1,2,3.

The physical selector differences are affine with highest parts ell_i.
The common coordinate shift is D-1. Each history residual is literally

    B*(H_i+Zhat_(2i)-Zhat_(2i+1)-(D-1)(S_(2i)-S_(2i+1)))
      -H_i-end_i*P+initial_i,

where both possible end coordinates have highest form D*. Sharing
the history right-hand sides changes none of these residuals.

If P is computed, P*=B*J*. The degree-three history parts are

    -B*D*(J*+ell_i).                                    (6)

Each J*+ell_i is nonzero: the required hub idle edge has coefficient
one, and all other coefficients are zero, one or two. Thus at least
one degree-three history is nonzero, uniformly in the fixed table.

If P is supplied and the macro list is nonempty, its instructions have
labels one through eight. Some ell_i is then a nonzero linear form
in the independent edge hats. The degree-three parts are

    -B*D*ell_i,                                         (7)

so the maximum outer residual degree is again three.

Finally, for the empty macro list with supplied P, all ell_i vanish.
The four degree-two history parts are

    B*(H_i+Zhat_(2i)-Zhat_(2i+1))-D*P.                   (8)

The retained repunit comparison has highest form B*J*, also of degree
two and nonzero. Flow is identically zero in this case and the joint
bound has degree one. Thus the exact maximum is two.

In every case the highest part of the positive outer factor is the
sum of squares of the residuals of maximal degree. Denote it by
Omega. Equations (6)-(8), and additionally (B*J*)^2 in the last case,
give Omega explicitly. It is a nonzero polynomial. The other residual
bounds are uniform: joint degree is at most nu<=2, and sparse flow
and repunit degree are at most two because their state coefficients
are fixed integers, not variable radix powers.

## 4. Exact final degree and the scope of the rewrite

Put d=3 if P is computed or the macro list is nonempty; otherwise d=2.
By (2), (5) and the nonzero outer highest form,

    F*=W* delta* Omega,
    deg F=7A0+8Q+38+2d
         =nu(36L+7m+105)+38+2d.                       (9)

In the usual case d=3 this is `nu(36L+7m+105)+44`. The idle-only,
supplied-P exception is two degrees lower. The product of the three
nonzero highest forms cannot cancel. This argument uses literal
source polynomials; no equality or power relation is substituted to
artificially lower their degrees.

This same unit absorption is valid for the unshifted six-field parent,
but it would increase its degree. There, the surviving native-bound
residual has degree nu(3L+m+15)+1, and the new final degree would be
`nu(29L+3m+45)+38`, greater than its present degree by
`nu(2L+2m+30)-8>0`. Only the improving shifted-X variant is implemented.
This is a comparison of this specific local rewrite, not an optimality
claim for either compiler.

## 5. Reproducible evidence

The [receipt](group_projective_strong_unit_product.json) stores ten
compact ledgers and one complete certificate with its finalizer.
Across 640 complete-source assignments, including 160 signed cases,
the checker independently evaluates N4 from A,T,f, verifies the exact
new residual `(old_W_residual+1)*(old_strong_residual+1)-1`, and checks
every other residual and retained register. It compares the actual
final output with a separately assembled unit product times positive
outer factor, and verifies identical final M/A counts.

Ten exact weighted-offset evaluations check all five inherited native
factor polynomials and N4, including their degrees and leading
coefficients. The literal product chain is checked separately, and
the much smaller remaining outer factor is expanded exactly. The
source verifies (6)-(9), including both idle-only cases, without
expanding an unnecessarily large final product. Distinct powers of
two for edge weights avoid accidental cancellation in a nonzero
selector difference during these specializations.

Another 64 modulo-four cases and 15,435 integer unit/outer-residual
fixtures supplement the unconditional proof in Section 1. They are
not presented as full positive Pell witnesses or as a substitute for
the parametric equivalence. Run normally to compare the deterministic
receipt, or with `--write` to regenerate it.

Independent proof/source review and a fresh default replay passed without
findings. The review checked the unconditional modular exclusion, exact
integer zero-set equivalence, literal finalizer count and the exceptional
idle-only supplied-P degree.
