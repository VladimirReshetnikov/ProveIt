# One natural selector in place of three Boolean selectors

## Scope

This note proves an ordinary degree-14 **local** polynomial with 21 natural
witnesses for the height-controlled commutative-certificate architecture.
The incoming Round11 alternative has degree 14 and 23 local witnesses.
It also proves a degree-12 alternative with 22 local witnesses. The number
of exposed local coordinates remains five. A fixed-dimensional
global consistency polynomial is not compiled here; no final 21-variable
Con(ZFC) equation is claimed.

The construction combines two exact changes: natural-domain interpolation
weights, and deletion of a stuttering truth rule. Neither changes the
logical calculus or the inherited calibration. No claim of first discovery
in the mathematical literature is made.

## 1. Nonnegative interpolation on the natural numbers

Let k>=1 and let G_0,...,G_(k-1) be integer polynomials that are nonnegative
on all their natural inputs. Define

    g_k(r) = product_(0<=j<k) (r-j),
    L_i(r) = product_(0<=j<k, j!=i) (r-j),
    W_i(r) = L_i(r)                  if k-1-i is even,
             (r-k)L_i(r)            if k-1-i is odd.

These are ordinary integer-coefficient polynomials. For every natural r,
g_k(r)>=0, with equality exactly when 0<=r<k. Every W_i(r) is nonnegative.
On the allowed selector set, W_i(r)=0 for r!=i and W_i(i)>0.

Proof: for r<k, all statements except the value at i follow from an explicit
zero factor. At i the sign of L_i(i) is (-1)^(k-1-i); in the odd case the
additional factor i-k is negative. For r>=k, all factors of g_k are
nonnegative; all factors of L_i are positive, and the optional r-k is
nonnegative. This proves every assertion for every natural r.

It follows that

    exists r in N: g_k(r)+sum_i W_i(r)G_i=0
      iff at least one G_i=0.

Indeed, all summands are nonnegative, so a zero first forces r<k and then
forces the selected G_r to vanish. Conversely, select the index of any
vanishing G_i. This argument is pointwise and uniform in all other inputs.

The weight degrees are k-1 or k. Squared Lagrange weights have degree
2(k-1). Natural-domain nonnegativity therefore produces a useful reduction
without adding Boolean coordinates. The restriction r in N is essential.
For k=6, W_1(-1) is negative, so the displayed construction must not be
silently treated as nonnegative on all integers.

These degrees are optimal for each individual interpolation weight, even
among real-coefficient polynomials. Any polynomial V nonnegative on N,
zero at every j<k except i, and positive at i, has degree at least k-1.
If equality holds, its k-1 distinct roots force V=c L_i. Nonnegativity at
large naturals forces c>0. Consequently V(i)>0 is possible exactly when
k-1-i is even. In the odd case degree at least k is necessary, attained by
our W_i. Likewise the k-root penalty g_k has the least possible degree k.
This is an optimality statement for this precisely stated local
interpolation task, not a lower bound for consistency equations in general.

## 2. The source rows and a removable identity transition

The included source file is an exact copy of Round11's
`commutative/horn_shared_source.json`, SHA-256

    bef85fcf1fbd70fc109162b5b518fe7c4803a54864c867c64f3e6ea7e3be71cf.

It in turn inherits source68's branch-shared C222 Horn relation. Write its
twelve nonnegative branch sums of squares as h_0,...,h_11. Their degrees
are 2 for h_0 (truth), 8 for h_9 (bundle), and 4 for every other branch.
The local coordinates p,q,v are the two padded premises and conclusion.
There are 17 shared branch witnesses a,b,c,d,q0,...,q12.

The truth branch is exactly

    h_0 = p^2+q^2+v^2.

Over naturals its vanishing says p=q=v=0. Put M=M0+1 and retain the two
accumulator residuals

    E = S'(1+vM)-S(1+pM)(1+qM),
    F = R'-R((1+p)(1+q)+v).

At the truth triple these are E=S'-S and F=R'-R. Thus a truth step is an
identity transition for both accumulators.

### Stutter-deletion theorem

Any finite accepted source trace may have all steps assigned to the truth
branch deleted, preserving the endpoints and every remaining step. At a
deleted step the values of both state registers are identical before and
after it. If multiple branches vanish, choose truth only when the step is
actually being deleted; otherwise retain any nontruth branch. The updated
length is another admissible natural existential parameter. Both final
height R_N and M=R_N+1 remain unchanged. A new finite beta encoding exists
for the shortened sequences by the same finite CRT argument as before.

Conversely, any trace using only the eleven remaining branches is already
an old trace. Consequently the existential global source predicate is
unchanged when h_0 is omitted. This is a theorem about existence of finite
traces, not equality of the two local zero sets for a fixed step.

The distinguished endpoints cannot be joined by a trace consisting only
of truth steps: S_0=M+1 and S_N=1 differ because M>0. Hence deletion cannot
create an inadmissible empty successful trace.

## 3. The literal degree-14 polynomial

Group the eleven remaining branch factors as

    G_0=h_9,        G_1=h_1 h_2,   G_2=h_3 h_4,
    G_3=h_5 h_6,    G_4=h_7 h_8,   G_5=h_10 h_11.

Each G_i is nonnegative and has degree exactly 8. For k=6, the weights are

    W_0=(r-1)(r-2)(r-3)(r-4)(r-5)(r-6),
    W_1=r(r-2)(r-3)(r-4)(r-5),
    W_2=r(r-1)(r-3)(r-4)(r-5)(r-6),
    W_3=r(r-1)(r-2)(r-4)(r-5),
    W_4=r(r-1)(r-2)(r-3)(r-5)(r-6),
    W_5=r(r-1)(r-2)(r-3)(r-4).

Define

    L = r(r-1)(r-2)(r-3)(r-4)(r-5)
        + sum_(i=0)^5 W_i G_i + E^2 + F^2.

All displayed terms are nonnegative on natural inputs. Thus L=0 is exactly
the conjunction E=F=0 with selection of one nontruth Horn branch. All
ordinary coefficients, branch residuals and weights are supplied in the
JSON files; the large expression is not being denoted by an unspecified
universal polynomial.

There are 21 local witnesses: p,q,v; the 17 inherited witnesses; and r.
The exposed state/parameter coordinates are S,S',R,R',M0. The upper degree
bound is 14: the degree-8 groups are multiplied by weights of degree at
most 6, while E^2 has degree 10 and F^2 degree 6. Exactness is proved by
the supplied sparse coefficient calculation: the degree-14 homogeneous
part evaluated at all coordinates equal to one is 723072, which is nonzero.
Equivalently the polynomial L(t,...,t) has leading coefficient 723072 at
degree 14. The full sparse expansion has 50,461 monomials.

### Two ternary selectors: degree twelve

The same theorem for k=3 has penalty g_3(u)=u(u-1)(u-2) and weights

    U_0(u)=(u-1)(u-2),
    U_1(u)=u(u-2)(u-3),
    U_2(u)=u(u-1),

of respective degrees 2,3,2. Use independent natural selectors u,w and
the following 3-by-3 array of nonnegative groups:

    [ h9,     h5,   h1*h2 ]
    [ h6,     h7,   h8    ]
    [ h3*h4,  h10,  h11   ].

All eleven nontruth factors occur exactly once. The three degree-eight
groups occupy corners; every other group has degree four. Define

    L12=g_3(u)+g_3(w)+sum_(i,j) U_i(u)U_j(w)G_ij+E^2+F^2.

Every summand is nonnegative. A zero forces u,w in {0,1,2}; precisely one
group has a positive weight, so the same branch/exact-update equivalence
holds. Conversely select the cell of a vanishing branch. The corner
weights have degree four, so their degree-eight groups contribute at
degree twelve. Other groups have degree at most 4+6=10. E^2 is degree ten
and F^2 is degree six. Thus the bound is twelve, and the full expansion
certifies exactness: its top homogeneous part at all variables one is
627840. There are 40,990 monomials and 22 local witnesses. Both new variants
strictly improve the old 23-witness degree-14 source in their respective
dimension/degree comparison.

## 4. Relation to the global source and closure interface

Use precisely the previous endpoints and beta-coded two-register source,
replacing its local relation by L. The stutter-deletion theorem and selector
theorem prove equivalence of its existential finite-trace predicate to the
earlier one, and hence to the same C222 refutability predicate under the
inherited logical calibration. All new reasoning is finitary and uses
integer polynomial identities and elementary natural order. It is therefore
formalizable in ZFC; no kernel certificate is claimed here.

The incoming index-free inert-prime closure has conditional coordinate count

    2m+9+2f+p+(m+1)b,

where m is the local witness dimension, and f,p,b are the internal witness
counts of chosen exact factorial, power and binomial graph polynomials.
Holding the other exposed graph conventions fixed, changing m=23 to m=21
reduces this interface count by exactly 4+2b. This is a conditional interface
calculation, not a materialized whole-checker variable count: different
polynomial expression costs and subsequent quartic flattening still need
to be charged. Applying the closure to a beta-decoded local step may add
further local witnesses common to both alternatives; the same difference
holds if those additions are identical.
For the degree-twelve variant, changing m=23 to m=22 saves 2+b coordinates
under the same stated convention.

## 5. Verification

Run `python3 build_and_verify.py` (also works with `python3 -O`). It checks
all twelve inherited SOS expansions exactly against their residual rows,
rebuilds every polynomial and its full sparse expansion, checks exact degree
and variable support, and exercises 14,471 finite selector/stuttering
controls. Explicit exceptions are used instead of removable assertions.
The finite controls supplement the universal proofs above. The script has
no third-party dependencies and imports no executable upstream code.

The source data are attributed to ProveIt source68 and the incoming
Round11 structural-reductions package. Reproducing their entire logical
calibration is outside this local artifact; the source and parent reports
must remain cited when this component is integrated.
