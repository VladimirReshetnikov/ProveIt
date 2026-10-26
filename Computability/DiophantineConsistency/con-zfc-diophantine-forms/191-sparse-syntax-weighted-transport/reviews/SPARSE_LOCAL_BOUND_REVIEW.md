# Independent local bound and source-graft review

## Scope

Reviewed the local block in `sparse_work/prototype.py`, the emitted
`sparse_work/sparse/source_graft.json`, and the parent source216 equation.
This is an ordinary mathematical review of the new sparse source and its
interfaces. Finite coefficient checks must accompany it; no end-to-end
formalization or global optimum is claimed.

## 1. Local equation and the two retained interfaces

Write the nine source axiom labels as h_1,...,h_9, with h_9 the guarded
bundle. Put r=S-Sp and w(j)=1+Fj. The source polynomial is

    axis = r * product_(j=1..8)(S-Sp*w(h_j))
             * [Sp*w(b)-S*w(a)*w(I(a,b))]
             * [S*w(b)-Sp*w(A(a,b))],
    guard = ((c-a)*(c-b))^2-(d+1)^2,
    bundle_factor = S-Sp*w(h_9),
    joint = guard^2+bundle_factor^2,
    Local = axis^2*joint
            +[x-S-(1+(i+1)y)u]^2
            +[x-Sp-(1+(i+2)y)vq]^2.

These agree with the generated formulas, including the guard's fourth
degree before its final square. For nonnegative local integers, Local=0
means a genuine source inference, its correct weighted Horn update, and
both beta transitions. Truth, the eight ordinary axioms, modus ponens and
generalization are the eleven zero factors of axis. The remaining joint
factor authenticates the guarded bundle. The guards exclude c=a and c=b
because d+1 is strictly positive, and conversely every nonzero product of
differences has the witness d=abs((c-a)*(c-b))-1.

The parent source216 rows4 through80 define the old local block. Outside
that interval the only old syntax coordinates still used are79, the
joint sum of squares, and95, the squared axis product. Both occur in row83,
where their product is combined with the two squared beta residuals.
The old FS coordinate207 occurs only inside the old local block and in
its own defining row. Its row is labeled `shared F times S`, so the
prototype's conditional deletion for label `multiplication` does not
remove it. It remains a harmless definitional extension until a later
certified projection. The new local block supplies fresh FS and FSp
values. The a-coordinate is restored as old coordinate8
minus1; it is not silently interpreted as coordinate8 itself.

The homogeneous-quadratic sharing is exact over unrestricted integers.
If an existing definition is z=g0*q+l0, and a newly requested quadratic
is g*q+l with g/g0 an integer, the replacement

    l+(g/g0)*(z-l0)

is polynomial and equals the request on the defining row. A new wire is
introduced whenever the ratio is not integral. No divisibility is assumed,
no denominator is introduced, and target79/95 definitions remain explicit.
This is the appropriate proof rule for the compiler's sharing step.

## 2. A fresh unbounded local-value estimate

After the retained range and sign bootstrap, let

    R=2+t+x+y+F.

Here t>=2; the growth argument below gives F>2^32 and thus R>=16.
All local a,b,c,d are in [0,t-1], the local index i lies in
[0,t-1], the states S,Sp lie in [0,y], and the beta quotients u,vq lie in
[0,x-1]. Thus every local atom is nonnegative and strictly below R. The
global positive numbers F,x,y,t are also strictly below R.

For any integer e>=1, sparse constructor inputs below R^e give an output
at most

    16(R^e-1)^2+4(R^e-1)+3
       =16R^(2e)-28R^e+15 <16R^(2e)<=R^(2e+1).

Hence a constructor tree of depth r has value below
R^(2^(r+1)-1). The actual axiom-depth vector is

    (4,3,3,3,3,5,4,3,19).

In particular each of h_1,...,h_8 is below R^63, and h_9 is below
R^(2^20-1)=R^1048575. The inference labels I(a,b),A(a,b) are below R^3.
This bound is newly proved for the sparse constructors: it does not reuse
the old shell coefficient-eight inequality.

The following estimates concern absolute values of unsquared factors.
Because S,Sp are both nonnegative and below R, abs(S-Sp)<R. Also FSp<R^2.
Each of the eight ordinary axiom factors is therefore below R^66.
For modus ponens,

    1+F I(a,b)<R^5,
    S+aFS<R^4,
    Sp+bFSp<R^4,

so its difference has absolute value below R^10. For generalization the
two sides are below R^4 and R^6, so its factor is below R^7. Consequently

    axis^2 < R^[2(1+8*66+10+7)]=R^1092.

For the bundle, abs(bundle_factor)<R^1048578, so its square is below
R^2097156. Each difference c-a,c-b has absolute value below R. Hence
abs(guard)<R^5 and guard^2<R^10. It follows that

    joint < R^2097157,
    axis^2*joint < R^2098249.

Both beta denominators are below R^3. This also applies to the second:
i+2<=t+1<R. Each beta residual is in absolute value below R^6, so each
square is below R^12. Therefore

    0<=Local<R^2098250<R^(2^23).

All inequalities are uniform for the allowed integer local data. They do
not rely on numerical testing, an exact exponential value of F, or the
relative sizes of any unbounded global CRT representatives.

## 3. Conversion to the CRT uniqueness budget

The retained bootstrap gives y>=F>=t^t and x>=2+(t+1)y. The standalone
growth estimate gives F>2^32 already for t=2. These facts imply

    R=2+t+x+y+F<2x,  x>2^32.

For the first inequality, it suffices to observe
(t-1)y>t, since y>=t^t and t>=2. For the second, the sparse growth bound
has L>=2^(5d-4), d=2^19, and hence F>=L^t>=2^(10d-8)>2^32.
Let 2^k<=x<2^(k+1), k>=32. Then

    2^23*log_2(2x)<2^23*(k+2)<2^k<=x.

The middle inequality holds at k=32 and persists because the right side
doubles when k is incremented. Thus

    Local<R^(2^23)<(2x)^(2^23)<2^x.

The unchanged CRT selector modulus is at least2^x. Hence a local value
congruent to0 modulo that modulus is exactly0. This is the precise
unbounded budget needed by the new source graft.

## 4. Global growth must use the new label coefficient

The local bound above does not justify retaining the old factor-eight
global label bound. For factor separation, the sparse code has

    label+1<=16^(2^19-1)*t^(2^19).

The new final equation must therefore use the center8t+1 standalone
growth certificate specified in `SPARSE_RECODING_PROOF.md`, or another
proved certificate with the required strength. Its norm is

    X^2-64Z^2-16ZF=1,  Z=tF.

The source216 prototype initially retains the old center4t+1 block.
The subsequent `direct_work/sparse_final/source214` stage makes the
required growth edit; its affine213 stage also changes the horizon to
t=2+4z. Exact projection after these edits remains allowed.

The signed affine horizon is safe at this smaller threshold. Before any
Pell classification, it forces t nonzero and even with abs(t)>=2; the
divisibility row forces F nonzero even and abs(F)>=2^19*abs(t). The
retained square frame includes F^2, so it activates the signed anchor
and every power interface without a prior sign assumption on t. Because
C+F+1 is odd, abs(D)>=2. The D^x request gives x>=0. At x=0 the final beta
equation would make 1+(t+1)y a divisor of -1, yet its absolute value is
at least abs(y)-1>1. Thus x>=1, abs(q)>=2, and the retained q^t request
forces t>=0. The affine horizon then gives t>=2. Only now is the standalone
Pell center8t+1 classified and the growth estimate used.

For cofinal completeness choose positive t=2 modulo2^23, so t=2+4z,
v2(t)=1, and bit20 of t is zero. With n0=2^19*t,
y0=Y_n0(8t+1) and a0=X_n0(8t+1), the quotient b0=y0/(2^19*t) is odd,
v2(y0)=20 and a0=1 modulo4. For any N>23 with 2^N>t, choose a positive
odd s using the parent's residue permutation so that
(t/2)b0*Y_s(a0)=1 modulo2^(N-20). Then
F=y0*Y_s(a0)=2^20 modulo2^N. Its binary support is disjoint from that of
t, and therefore binomial(F+t,t) is odd. All later beta/CRT data can be
chosen in the original noncircular order. The available horizons and F
values are cofinal. The smaller t threshold creates no exception in the
selector-radius estimate F>=L^t>=t^(2t)>=(t!)^2, including t=2.

## 5. Finite-marker self-review

The recoding proof must be a finite-proof embedding, not a purported
global constructor bijection. For each finite derivation include all
numerals occurring as parameters, subterms, intermediate constructor
expressions, premises and conclusions. Distinct unused sparse numerals
are distinct atom leaves. The equal-height Cantor markers have height
strictly above every constant-only term in that finite set. A constructor
term containing an atom has image height strictly above the marker height.
This separates an atom from every composite term; constructor disjointness
and injectivity then prove the finite substitution injective.

Both codings identify I(0,0) with the normalized leaf0, and the proof
explicitly respects this only exceptional constructor cycle. Markers are
nonzero, so no extra occurrence can collapse to0. The map fixes
1=M(0,0). It preserves every finite equality and every bundle freshness
disequality used in the derivation. The converse global map from original
Cantor trees to sparse trees is injective because those trees have no
extra atoms. These statements suffice for the two finite-refutation
transformations. No semantic soundness assumption, outside model, or
truth of Con(ZFC) is used.
