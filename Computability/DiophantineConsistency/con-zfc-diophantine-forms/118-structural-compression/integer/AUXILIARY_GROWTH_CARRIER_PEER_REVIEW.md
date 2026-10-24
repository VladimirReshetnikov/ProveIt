# Independent review of the auxiliary-growth carrier L=b

Review date: 24 October 2026.
Scope: the root's new replacement of L=HI+b by L=b in the ten-positive
unweighted zero-offset and direct-zero-offset equations.

## Conclusion

The new transport argument is valid. In particular, its large-b estimate
can be established before the transport-sign conclusion, before p=R,
before q parity, and before any denominator cancellation. The auxiliary
Pell growth is available at that stage and is sufficient to replace the
old strong-ordinate summand in L. Completeness remains valid with fresh
canonical n. No new hypothesis on the fixed coefficient tuple is required.

This review uses the complete parent proofs and the already reviewed
unweighted radical extraction. The degree/count results 96 operations at
degree360 and102 at degree332 are the author's separately checked literal
metrics; this note reviews their new unbounded mathematical reduction. It
does not reprove the transitive native/refutation calibration or claim a
new Lean/internal-ZFC certificate.

## 1. Exact stage at which the argument starts

The input domain is the same ten strictly positive integers as before.
At this point the new unweighted norm has already supplied integral
positive roots tau,f,y and the unchanged individual Pell equations.
The unconditional positive-input bounds include

    q>=32, mu=q^2+1, X>=q, Y>=1,
    A=mu*Y*(X+1)+1, Delta=A^2-1, H=4A-5,
    k=eta+zeta>=2, c=kY+eta>=3, I=i*c^2>=c^2,
    Df=Delta I^2+1, Q=Delta^2 I^2, delta=Q-1,
    b=c(T+alpha)-R, V=Df*b-c,
    QV^2-(Q-1)y^2=1.

The existing all-index folding recovers c=psi_A(p), p>=1, without
requiring V positive. In its auxiliary classification one first uses
(S|V|,y), with S=Delta I. The auxiliary index nu is odd: an even-index
chi_S is plus or minus1 modulo S, whereas S divides its first coordinate.

**The folded p is already odd.** The folding reduces nu modulo2m and
possibly replaces the remainder by2m minus that remainder. Both operations
preserve its parity. Therefore p is odd before transport or the equality
p=R is used. Since c>=3 and psi_A(1)=1, p cannot equal1. Monotonicity
therefore gives

    p>=3, c>=psi_A(3)=4A^2-1=4Delta+3.                 (1)

This supplies the critical lower bound independently of the later native
rank determination. In particular the argument does not infer p odd from
an as-yet-unproved parity statement about R.

## 2. Pretransport positivity of b

The first-norm classification and the existing n0=1 exclusion still give

    n0>=2, c>8Xmu^2Y^2>8q^5.

Neither fact involves W or L. The coherent port box gives the unconditional
mask estimate

    R<q^4+(alpha+2)q^2<c*alpha/4.

The second inequality is explicitly established in the retained
SHIFTED_PROOF.md, Section3, using only c>8q^5, q>=32 and alpha>=1.
It is valid even if R is negative and does not require C=q-F-alpha>0.
Consequently

    b=c(T+alpha)-R
       >cT+3c*alpha/4>c.                              (2)

We may now use V>0; it was not assumed in the preceding folding step.
Combining(1) and(2),

    V=(Delta I^2+1)b-c
      >Delta I^2 c
      >4Delta^2 I^2=4Q.                               (3)

Every strict inequality is justified: b-c>0 and c>4Delta.

## 3. The auxiliary index must be at least five

Classify the positive Pell solution (SV,y), where S=Delta I and Q=S^2.
As above, its index nu is positive and odd. The first two odd indices give

    chi_S(1)/S=1,
    chi_S(3)/S=4Q-3.

Both contradict(3). Hence nu>=5 and monotonicity gives

    V>=chi_S(5)/S=16Q^2-20Q+5>8Q^2.                   (4)

The final inequality is uniform for Q>=4, because
8Q^2-20Q+5 is positive there and increasing. Here S>=2, so Q>=4
is already available; in the actual source the bounds are much larger.

Also Df<Q. Indeed Q-Df=Delta(Delta-1)I^2-1>0 for the actual
Delta>=8 and I>=1. Equation(4) therefore yields

    b=(V+c)/Df>8Q^2/Df>8Q.                            (5)

Since

    Delta-H=A^2-1-(4A-5)=(A-2)^2>0,

and I>=1, it follows in particular that 8Q>2HI. Thus

    b>2HI.                                           (6)

This is the new useful domination. It comes from the auxiliary index,
not from the later source interpretation or an assumption that R is large.

## 4. The two remaining errors are each less than b/4

By(3), V>1. The auxiliary norm gives

    y^2-V^2=(V^2-1)/(Q-1)>0.

Using y>V and V<Df*b,

    0<y-V=(V^2-1)/[(Q-1)(y+V)]
          <V/[2(Q-1)]
          <Df*b/[2(Q-1)]<b/4.                        (7)

For the last step,

    Q-1-2Df=Delta(Delta-2)I^2-3>0,

which follows already from Delta>=8,I>=1.

Put e=k-R-1. No absolute-value estimate or positivity of e is needed:

    b-e=c(T+alpha)-k+1>0,

because c>k and T+alpha>=2. Therefore e<b, and mu^2>4 implies

    e/mu^2<b/4.                                      (8)

This is a signed upper bound. It remains valid when e<0, as required
before any divisibility or positive-rho conclusion.

## 5. Transport contradiction with the smaller W

All retained estimates preceding the old transport contradiction remain
available; in particular Kpos/H>0 and

    tau+f<HI                                         (ordinary source),
    tau+f+X/q^4<HI                                   (direct source).

In fact the parent proved the stronger corresponding inequalities with
3tau. Combine them with(6): the applicable positive-root sum is <b/2.

For the ordinary source set W=1+(q-1)b. If Bt<=-1 then

    W*Bt/(q-1)<=-W/(q-1)<-b.

The exact signed-center equation consequently gives

    n < (tau+f)+(y-V)+e/mu^2-b
       < b/2+b/4+b/4-b=0,

after dropping the two strictly negative projection/scale terms. This
contradicts the strictly positive input n. Thus Bt>=0.

For the direct source set W=1+q(q-1)b. If B<=-1 then
WB/[q(q-1)]<-b. The same argument groups the extra positive X/q^4
with tau+f and uses its retained bound above. It again gives n<0.
Thus B>=0 in that source.

The remaining chronology is unchanged: positive transport gives C>0 and
the outer R bounds; rank recovery gives p=R; q parity follows; only then
are denominator coprimality, the first-index identity, whole-product
projection, late q divisibility and source reconstruction applied.
The new W preserves all required congruences W=1 modulo q-1 (or modulo
q(q-1) for the direct carrier). None of the subsequent parent steps uses
the old HI term except through the already replaced transport estimate.

## 6. Completeness does not depend on the old size of W

Take the fresh canonical witnesses from the accepted zero-offset
completeness construction. They have b>0 and the same integral

    t_transport>=0, rho>=1, u=y-V>0, s=Y/q^3>=1,
    kappa=Kpos/H>0, tau>s, f>kappa.

With the new positive W=1+(q-1)b, define

    n=W*t_transport+rho+tau+f+u-s-kappa.

It is an integer and strictly positive, since tau-s and f-kappa are
positive and every remaining summand is nonnegative. Its normalized
center equals tau+f+y. No lower bound involving HI is needed for W
in this construction, including when t_transport=0.

For the direct companion, keep the same kernel and put

    n_direct=n+(q-1)^2*b*t_transport+X/q^4.

The recovered canonical source facts make X/q^4 a positive integer.
The direct center identity and norm homogeneity are the parent's exact
ones with L replaced everywhere by b. Thus the direct companion also
has a positive zero for each finite source refutation.

This completes the two existence directions for the new carrier. The
result is an ordinary mathematical reduction, retaining the same precise
native/refutation calibration boundary as the earlier endpoint.
