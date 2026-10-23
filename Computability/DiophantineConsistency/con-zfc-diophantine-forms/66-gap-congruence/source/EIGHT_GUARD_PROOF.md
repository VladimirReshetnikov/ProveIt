# Eight positivity guards suffice (an optional source lemma)

This lemma improves the previous twelve-guard argument, but is not by itself
an operation-count improvement for the degree-separated finalizer. That
finalizer already shares the full positive offset with its low digit mask.
Using a smaller separate offset may add gates. No gate saving is asserted.

## Domain and hypotheses

Use either the round-8 original 31-positive quadratic parent or the incoming
original parent in parent_source.json. Assume beta,K0>0 and MC,MF>=0, with
the same complete fixed tuple as its inherited semantics. Allow all31
coordinates to be nonnegative, requiring only these eight to be positive:

F, alpha, z, h, s, w, eta, zeta.

Then every simultaneous zero has all31 coordinates strictly positive.
Consequently shifting precisely these eight by one gives a bijection of the
old positive zero set with the new natural zero set. This statement concerns
the original coordinates, before optional P/N/L gap substitutions.

## Proof

Set q=1+beta J, C=q-F-alpha, k=eta+zeta, Y=a-E.
Transport is (K0+w)C=F+z beta J for the round-8 convention and
(K0+w)C=F+(z-1)beta J for the incoming parent convention. Both right sides
are strictly positive: z>=1 and J>=0. Therefore C>0, q>=3 and J>0.
The defining equations give L=q^2-1>0, N=q^3>0, X=wq>0,
Y=sN>0, E=XY>0, a=E+Y>0. Also c=kY+eta>k>0,
T=P-k=E(c-eta)>0, P>0, and tau^2=PT+1>0.
Thus tau>0. Delta=a^2+4a+3>0, C2=c^2>0 and
D=X+ac+gamma(4a+3)>0 even with gamma=0.

Define R=jc-V using row14. On the already established equations,

R=(q^2-1)[(q-1)C+q alpha]+(MC+q MF)J>0.

Since c>0 and V>=0, j>=1. Row13 is exactly

k=jc-V+1+hE.

If i=0, then I=i C2=0, Baux=I^2=0. Row22 gives y^2=1,
so y=1. Row18 gives V^2+g=1; hence V<=1. Thus the preceding
identity gives k>=jc+hE>=c, contradicting c>k. Therefore i>0.
It follows that I>0 and Baux>0. From Baux=Delta(F2-1) and
F2=f^2 we obtain f>=2. If g=0, then row22 and row18 give
y=V=1, and the same contradiction k>=c follows. Hence g>0.
Now y^2=Baux*g+1>1 and
V^2=(Baux-1)g+1>=1, so y,V>0; of=V+c>0 forces o>0.

Finally suppose gamma=0. Since R>0 and h>=1,
k=R+1+hE>E. Since Y>=1,
c=kY+eta>k>E=XY>=X. Therefore
D=X+ac<(a+1)c. But Delta=(a+2)^2-1>(a+1)^2, contradicting
D^2=Delta*c^2+1. Thus gamma>0.

Every coordinate has now been proved positive. The inverse map subtracts
one exactly from the eight guarded coordinates, so the claimed zero-set
bijection follows. The native nonnegativity of MC,MF is an explicit new
hypothesis compared with the earlier twelve-guard lemma.
