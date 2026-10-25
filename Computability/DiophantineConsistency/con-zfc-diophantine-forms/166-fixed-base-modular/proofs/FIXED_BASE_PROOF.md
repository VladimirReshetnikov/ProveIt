# Fixed-base radius and binomial proof weights

Research note for ProveIt, 25 October 2026, prepared with AI assistance.

## 1. Scope and exact source

The selected source is `stages/fixed_base/raw_source.json`, built by
`code/build_fixed_base.py` (selected linear beta is the default). It changes the arithmetic front of
the incoming Factorial-Free Binomial CRT package. The source retains its
C222 rule polynomial, generalized binomial CRT theorem, large-evaluation
Horn-flow theorem, signed Pell certificates, and common remainder norm.
The logical calibration remains the inherited pair
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

The variable-base growth request F=[2(t+1)]^t, radius F^2, and Horn
weights 1+jF are replaced by

    R = 16^t,       B = binom(R+t,t),       W_j = 1+jB.

The binomial already needed for selecting proof rows now also provides
the large evaluation point for recovering label multiplicities. The
remaining independent growth request has fixed base 16. There are still
eighteen power requests in this source. Any later modular-numerator
successor is a separate source change with its own proof obligations.

Exponentiation and binomial notation in this note describe values of
certified registers. Every residual in the literal source is an integer
polynomial of degree at most two. The final single polynomial is the
sum of their squares, after the supplied exact transformations.

## 2. The changed arithmetic front

Let t=16+h^2. Let C,A_1,...,A_8 be the nine actual CRT representatives;
some stored source coordinates are these values minus one. Put

    H = 2 + 2(R+t) + C + sum(A_j),
    N = B^x,
    q = (BH)^x = 6z+3,
    y = R B (2v+1)^2.

The beta identity uses three quadratic rows:

    beta.RB = R B,
    beta.odd_square_multiplier = (2v+1)^2,
    y = beta.RB * beta.odd_square_multiplier.

The first of these also supplies the term 2RB in the quadratic graph
for BH. The retained endpoints and raw index congruence become

    x = B+1+(y+1)u_0,
    x = 1+[1+(t+1)y]u_t,
    B h_B = C+R+1.

All old Horn weight occurrences of F become B. The old radius definition
R=F^2 is removed. The first power output is R. The complete list of
eighteen requests is in `mutation.json`; the square frame is recomputed
from all their base, exponent and output atoms, deduplicating equal atoms.

Multiplication by R in the beta formula is essential for completeness.
The canonical binomial B is odd, so B(2v+1)^2 alone is odd. R supplies
the necessary power of two to make y divisible by t!.

## 3. An elementary lcm bound

Write L_n=lcm(1,...,n). For every n>=1,

    L_n <= 4^n.

For n=2m the ratio L_(2m)/L_m divides binom(2m,m). Indeed, every
new prime power between m+1 and 2m contributes its prime to this
ratio; the corresponding term in the binomial's valuation is one,
and all other valuation terms are nonnegative. There is at most one
new power per prime. Inductively,

    L_(2m) <= L_m binom(2m,m) <= 4^m 4^m.

For n=2m+1, similarly L_(2m+1)/L_(m+1) divides binom(2m+1,m).
The two equal central binomial coefficients together do not exceed
the row sum, so binom(2m+1,m)<=2^(2m)=4^m. Hence

    L_(2m+1) <= L_(m+1) 4^m <= 4^(2m+1).

The cases n=1,2 start the induction. Consequently R=16^t>=L_t^2,
which is the radius hypothesis in the inherited generalized binomial
CRT theorem.

Also 16^t>t(t+1) for t>=1: the initial inequality is 16>2, and
(t+2)/t<=3<16 is the ratio of consecutive polynomial factors. Every
factor (R+i)/i, 1<=i<=t, is therefore greater than t+1. Thus

    B = product((R+i)/i, i=1,...,t) > (t+1)^t.

This is exactly the inherited Horn label-separation bound with B in
place of F. It uses no authenticated factorial.

## 4. Sign bootstrap before authenticating B

The unchanged square frame and semantic anchor first recover the
signed principal Pell coordinates. Its signed-power interface is
valid for bases n with |n|>=2: the certificate forces k>=0 and
m=n^k. A negative exponent would instead give the impossible integer
identity m n^(-k)=1. Bases +1 and -1 have separate exact treatment;
none is used in the following bootstrap.

The fixed-base request gives R=16^t>0. Since q=6z+3, we have
|q|>=3 and |q+1|>=2. The nine numerator requests at base q+1 force
their actual exponents C,A_j to be nonnegative even if q+1 is
initially negative. Hence H>=2+2(R+t)>2. The raw index congruence
excludes B=0 because C+R+1>0.

The exact request at base q and exponent y+1 forces y+1>=0. But
y=RB(2v+1)^2 is a nonzero multiple of R. Since R>1, a nonpositive
y would satisfy y<=-R<-1, impossible. Therefore y>0 and B>0.
This recovers the binomial output's sign before using a binomial digit.

Now BH>=2. Its exact request gives x>=0 and q=(BH)^x>0. The
progression q=6z+3 excludes x=0, which would give q=1. In fact the
retained denominator ratio q^(t+1)d=q^x gives x>=t+1, since |q|>1
and d is an integer. Thus x>1. The final endpoint forces u_t>=1,
and consequently

    x >= 2+(t+1)y >= t+3.

Because y>=RB>B, a negative u_0 would give x<=B-y<=0. Thus
u_0>=0 as well. No digit interpretation, factoriality, or assumption
about the size of a hypothetical proof has entered these deductions.

## 5. Recovering the binomial output

Put n=R+t. For 0<=j<=t,

    binom(n,j) <= n^t < (H/2)^t,
    binom(n,j)/q < 2^(-t) H^(-3) < 1/64,

using q=(BH)^x>=H^x and x>=t+3. The actual low binomial remainder
of (q+1)^n modulo q^t is therefore less than q^t/32. Indeed the
geometric sum contributes at most the factor q/(q-1)<=3/2.

The unchanged normalized remainder construction has common denominator
M=q^x. Its norm gives absolute value less than M/2 for every normalized
remainder. For D=q^t and d=M/D, the actual normalized remainder has
absolute value less than M/32. The retained numerator identity makes
the supplied remainder congruent to it modulo M. Their difference
has absolute value less than M, so the two values agree.

Dividing the exact numerator identity by its nonzero ratio d and
then extracting the q^t digit gives

    B = binom(R+t,t) modulo q.

Moreover B<=BH<q/2 because x>=3 and BH>=2; the binomial coefficient
is below q/64. Thus the congruent integers differ in absolute value
by less than q. They are equal:

    B = binom(R+t,t).

The precise scaled numerator and ratio identities are unchanged from
the inherited common-remainder construction; this proof changes only
their upper index and the bounds that justify canonical decoding.

## 6. All remaining range and local-rule bounds

After authentication, B>R>=2^64 and y>=RB>B. The endpoints have
their intended canonical remainders B+1 and 1. The old exceptional
y=F branch has disappeared because y>B holds automatically.

The bounds needed by the inherited decoder follow:

    t,t+1,y+1 <= x,
    x >= 2+(t+1)y,
    x>2^32,
    2+t+x+y+B < 2x.

For the last inequality, use y>=RB, R>=2^64, and
x>=2+(t+1)y; then t+y+B+2<x. The same estimates imply
ell(t+1)<x for ell=2^22.

The original derived-label bound h_*<=H^ell remains valid since H
exceeds the old 2+sum(actual representatives). Every ordinary or
derived low binomial coefficient is at most H^x. Its ratio to q is
at most B^(-x), and H^x/(q-1)<1/32. Thus all remaining common-norm
remainder arguments are unchanged.

The local rule polynomial has the retained majorant
L<(2+t+x+y+B)^E, E=2^23. The displayed estimates and the elementary
bound E log_2(2x)<x for x>2^32 give L<2^x. Together with
R>=L_t^2, this verifies all hypotheses of the inherited generalized
binomial CRT theorem. Every local C222 row is recovered.

Every decoded update uses W_j=1+jB. Multiplying the updates and
cancelling positive intermediate accumulators gives the inherited
label-product identity, with initial accumulator B+1 and final
accumulator 1. Because B>(t+1)^t, that identity recovers the exact
label multiplicity balance. The inherited single-conclusion flow
lemma yields a finite C222 refutation and therefore a finite ZFC
refutation.

## 7. Constructive completeness

Start with a finite C222 proof tree. Choose t=16+h^2 large enough
for its rows and bounded labels, set R=16^t and B=binom(R+t,t),
and construct the pending accumulators with weights 1+jB.

B is odd. For 1<=i<=t, the inequality
v_2(R)=4t>floor(log_2 t) gives v_2(R+i)=v_2(i), so the numerator
and denominator valuations of the binomial cancel.

Let O be the odd part of t!. Choose an arbitrarily large positive
odd multiple w of O and put y=RBw^2. Since v_2(R)=4t>v_2(t!),
y is an even multiple of t!, and can be made larger than every
accumulator. The beta moduli 1+(i+1)y are pairwise coprime and
odd. CRT supplies a common beta code x; adding their odd product
lets us choose x positive, sufficiently large, and even. Set
v=(w-1)/2 to complete the beta graph.

Use the inherited generalized binomial CRT construction to obtain
the actual representatives modulo N^2, where N=B^x is odd. Choose
a odd and the other eight actual representatives even. This makes
the inherited semantic anchor h_* even and H odd. If 3 divides B,
BH is already an odd multiple of 3. If 3 does not divide B, the
modulus N^2 is coprime to 6: a lift of a can satisfy both its odd
parity and H=0 modulo 3.

Concretely take the other eight representatives positive and at
most 2N^2. Choose a among a0+kN^2, 2<=k<=7, to satisfy the two
residue conditions. It is above 2N^2 and below 8N^2. The inherited
bound h_*>=2a^2 then dominates all other indices exactly as needed.
The front indices satisfy R+t<B<N^2 and x,y+1,t<N^2. The larger
allowed upper bound on a causes no problem: the radix uses its
actual value through H, and increasing a strengthens dominance.

Now q=(BH)^x is a positive odd multiple of 3, hence q=6z+3 for
an integer z. All modified front rows hold. The unchanged Pell,
range, common-norm and semantic-anchor completions are available
from the parent proof, with the changed request list and larger H.
This constructs a source zero from every finite refutation.

## 8. Finite algebra and proof boundary

The builder records every changed row, reconstructs the full frame,
and invokes the inherited exact Horn factorization, integral monic
projection and coordinate translation. Their certificates give exact
integer transformations, and the complete expanded polynomial is
emitted. Separate verification must check that literal interface and
the transformations. Finite checking does not prove the unbounded
arithmetic claims or recompile the full logical formalization.

The new theorem composes this ordinary proof with the explicitly
identified inherited arithmetic and C222/ZFC interfaces. It is
formalizable in ZFC, but no new end-to-end Lean/Rocq proof object is
claimed here. No assertion of Con(ZFC), global simplicity minimum,
or literature-wide priority is made.
