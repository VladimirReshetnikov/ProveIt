# Independent algebraic audit, completed before numerical testing

Baseline: frozen Report47; candidate: ant-fusion-next-20261004/fusion_source.py.
This audit concerns ordinary integer-polynomial equality, not ant dynamics.
The inherited coefficient theorem and its conditional assumptions are unchanged.

## Index conventions

Let S=576000=600*960, c=288650=600*481+50, L=240619037200,
u=2L, R=601547591, and Z=3^400. The old arithmetic initializer's V is S,
whereas the profile-construction V is L. They are different dimensions.
The initializer runs tile and first Horner for exactly S coefficients.
For an S-array A define E_p(A)=sum_(j=0)^(S-1) A[(c-j-p) mod S]W^j.
Equivalently, E_p(A)=sum_(x=0)^(S-1) A[x]W^((c-p-x) mod S).
This equivalence is a permutation of fixed indices, not reduction of W powers.

## Correction identity over a universal polynomial ring

Work first over Z[Q_(a,d),T_(a,s)][W], treating every coefficient as an
independent symbol. Let I_0=[0,50], I_1=[51,650], I_2=[651,1199].
For d in I_b put ell=50+600b-d. Then 0<=ell<=599, including d=50,51,650,651.
For p in {0,288000} and 0<=s<=956 put k=(480-b-s-p/600) mod960.
The integer 600k+ell belongs to [0,S-1] and is congruent to
c-p-600(s+1)-d modulo S. Uniqueness of the least nonnegative remainder proves

(c-p-600(s+1)-d) mod S = 600k+ell.

Thus, by finite distributivity,
E_p(C)=sum_(a,b) Q_ab(W) L_abp(W^600), where
Q_ab(W)=sum_(d in I_b) Q_(a,d)W^(50+600b-d),
L_abp(Y)=sum_(s=0)^956 T_(a,s)Y^((480-b-s-p/600) mod960),
and C[x]=sum_(a,s,d: x=600(s+1)+d modS)Q_(a,d)T_(a,s).
The map s -> k is injective on 0..956, leaving exactly three zero positions.
The exponent sum never leaves the ordinary range 0..575999. No product is
formed and then reduced modulo W^S-1. The identity remains valid after any
substitution of integer coefficients, in particular the frozen signed ternary
profiles and Report47 occurrence constants. Overlap of different terms is
handled by addition, exactly as in C, rather than a uniqueness assumption.

## Grouping fixed profiles

For each p and each fixed profile, let a_(k,r)=A[(c-600k-r-p) modS].
Partition k=0..959 into classes J_g with identical full 600-tuples a_(k,*).
Let b_g be that tuple. Finite distributivity gives
E_p(A)=sum_g (sum_(r=0)^599 b_(g,r)W^r)(sum_(k in J_g)(W^600)^k).
An exhaustive equality of all tuples and a disjoint-cover check suffice to
prove equality of all S coefficients, independent of numerical evaluation.
The second phase rotates k by480 and leaves the tuple contents unchanged.
Hlow and Hhigh are independent digit masks with H=Hlow+3^25 Hhigh;
first is exactly bit25 of H. Both phases must be checked for H,B,F,Hlow,
Hhigh,first even though the candidate uses only eight specific combinations.

A run of block positions [k,k+n-1] has weight Y^k G_n(Y).
P_1=Y,G_1=1; P_(2n)=P_n^2,G_(2n)=G_n+P_n G_n;
P_(2n+1)=P_(2n)Y,G_(2n+1)=G_(2n)+P_(2n).
Induction proves P_n=Y^n and G_n=sum_(i=0)^(n-1)Y^i in Z[Y].
The supplied source pays each multiplication/addition used by this grammar,
including the otherwise-unused P output, and pays each uncached power chain.
The special aliases at n=1 or exponent0 follow polynomial identities.
No division is used, so W=0,1,-1 are included without any special assumption.

## Tile and initializer identity

The frozen theorem gives U=B*G+C, Full=H+Z*U+3^(L-400)*F,
Cut=Hhigh+3^375*U+3^(L-425)*F, and
Tile[x]=Cut[x]+3^(L-25)*Full[x-S/2]+3^(u-25)*Hlow[x].
Applying E_0 and linearity gives exactly candidate Fusion.build:
U_p=G*E_p(B)+E_p(C);
TilePolynomial=E_0(Hhigh)+3^375 U_0+3^(L-425)E_0(F)
 +3^(L-25)*(E_half(H)+Z*U_half+3^(L-400)E_half(F))
 +3^(u-25)E_0(Hlow).
Here E_0(A shifted by -S/2)=E_half(A) by the definition of the fixed indices.
FirstPolynomial=E_0(first). Report47's labels use x=(c-j) modS, so these
are exactly sum_j tile:j W^j and sum_j first:j W^j.

Replacing only these two Horner outputs leaves the old expression
hy*(hx*TilePolynomial+Wp*FirstPolynomial) identical for every assignment.
For each remaining gate, unchanged opcode/operands under the checked mapping
preserve its polynomial by induction. The same argument covers residual
operands and every sum-of-squares finalizer gate, hence the entire final
polynomial, not merely its zero set. Declared coordinates and domains need
no change. Exact degree is inherited by equality, not inferred from new
syntactic intermediate degree bounds. Source/count/splice verdicts require
separate emitted-source validation and are not claimed by this proof alone.
