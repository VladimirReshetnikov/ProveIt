# A positive three-kernel source of height 1954

## Claim and exact scope

This is a new composition of inherited ideas, not a new Diophantine universality
or consistency theorem. It combines the 108-position weights from the incoming
Separated Degrees packet, the two row shears from our previous degree-separated
packet, a new target placement, and a global sign reversal. The resulting source
has 89 kernel records, maximum variable position 108, maximum target 1939, and
convolution height 1954. In particular all three kernel leaders are positive,
so positivity follows separately for each kernel. The finite checker verifies
22 exact formal identities through 22,544 isolation interactions. It does not
verify the inherited unbounded compiler theorem or any numerical finalizer.

The original31 positive source is `parent_source.json`, SHA-256
1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.
Its four ports beta,K0,MC,MF must be bound together to the original31 native
Wang943121x8801 tuple, not mixed with other coefficient releases. Their bit
lengths are 1064921,1070004,1064921,1064922; beta=2^1064921-1 and MF is already
shifted. The inherited adapter identifies a positive source zero with a finite
syntactic ZFC refutation. All new arguments below are elementary integer
arithmetic and hence formalizable in ZFC. Combining them with a correctly
proved finalizer and that adapter gives the claimed consistency equivalence.

## 1. Exact source extraction

Let r_1,...,r_22 be the parent residuals. Set rho_14=r_14+r_2,
rho_15=r_15+r_3, rho_j=r_j otherwise, and sigma_j=-rho_j for every j.
The two shears are invertible, and global negation changes no common zero.
The ordered coordinate weights, in the parent variable order, are

    104,76,79,60,108,8,99,55,36,54,98,11,7,10,44,32,
    106,22,17,1,3,4,37,89,97,107,39,40,86,45,92.

The row order and corresponding targets are

    rows:    8,15,20,9,4,19,7,12,13,17,16,10,5,21,1,3,11,6,14,18,22,2
    targets: 34,229,274,319,524,533,573,767,820,1007,1053,1064,
             1089,1291,1320,1366,1381,1410,1617,1707,1798,1939.

For a degree-d source monomial a p^alpha in sigma_j, place
2a alpha!/d! at exponent q_j-sum alpha_i w_i in D_d(T), for d=0,1,2.
Here the multiplier is 2 for constants, linear terms and quadratic squares,
and 1 for quadratic mixed products. `split_kernels.json` is the complete
literal list of these 89 records. Negative exponents do not occur.
For U_p(T)=sum p_i T^w_i the checker proves, over the formal coefficient ports,

    [T^q_j](D_2(T)U_p(T)^2+D_1(T)U_p(T)+D_0(T)) = 2 sigma_j(p).

The degrees of D_0,D_1,D_2 are 1939,1842,1738; their leading coefficients are
2,2,beta respectively. Thus W=108 and H=max(deg D_d+dW)=1954.
The checker does not assume global uniqueness of all pair sums: it proves
precisely the supported-monomial and target-isolation identities needed here.

## 2. Positivity and uniform bounds

Every coefficient of every D_d has magnitude strictly below C=2^2134927.
The checker obtains this bound from the exact formal coefficients and the four
port bit lengths. Fix kappa=2134940 and, for integer b>=1, set

    B=2^kappa b^2 =8192 C b^2, ell=sum B^w_i, U=ell+g,
    G=D_2(B)U^2+D_1(B)U+D_0(B), Targets=sum B^q_j,
    N0=B^109, Z=B^1955,
    Mask=N0-1-(b-1)ell,
    Jcode=2G+Targets,
    S=g+N0 Jcode, T=Mask+N0(B-2)Targets,
    Gcap=32bB^108.

For a polynomial of degree h with leading coefficient a>=1, the absolute
lower-tail contribution is <C B^h/(B-1). Since B>2C, each D_d(B)>0.
Consequently G>0 for every U>=0, and in particular S>0 for every b,g>=1,
without assuming a final zero or that b is a power of two. Also 0<=Mask<N0
because 0<=b-1<B and the weights are distinct positions below 109. Hence T>=0.

On the branch g<4bB^108, ell<2B^108 and U<6bB^108. Geometric estimates give

    G < C/(B-1) (36b^2 B^1955+6b B^1951+B^1940)
      < 43Cb^2 B^1955/(B-1),
    2G/Z <86Cb^2/(B-1)<1/64.

The last inequality follows from B=8192Cb^2 and B>=4.
Since the targets are distinct and at most1939,

    Targets<Z/64, (B-2)Targets<Z/64.

Also g<N0. It follows that S+T<N0 Z=B^2064. These are uniform bounds on the
full ratio-derived range g<4bB^108, not just the smaller witness range.

## 3. Exact binary-disjointness decoder

Suppose b=2^k, B=2^v, where v=kappa+2k. The base-B mask has digit B-b at
active positions w_i and digit B-1 at all other positions below109. Thus,
for 0<=g<N0,

    g & Mask=0 iff g=sum z_i B^w_i with integers 0<=z_i<b.

On that branch U encodes the strictly positive coordinates p_i=z_i+1<=b.
If h_t is any coefficient of D_2(T)U_p(T)^2+D_1(T)U_p(T)+D_0(T), then

    |h_t| < C((sum p_i)^2+sum p_i+1) <=993Cb^2 < B/8.

The formal coefficients of Jcode are a_t=2h_t+delta_target(t).
Normalizing these signed coefficients in base B has only incoming borrows
0 or -1: indeed -B/4<a_t<B/4+1, and this interval remains strictly between
-B and B after adding either possible incoming borrow. At a target position,
if h_t=0 the normalized digit is either1 or0. If h_t>0 the digit is at least2
and less than B/2. If h_t<0 it is between B/2 and B-1. In both nonzero cases
it has a bit in common with B-2. Thus the target digit is disjoint from B-2
exactly when h_t=0, independently of the incoming borrow. No condition is
imposed at non-target positions. The positivity and Z bound above guarantee
a finite nonnegative high word, so no unsigned extension is being assumed.
The low and high blocks are separate, and therefore

    S & T=0 iff g encodes a positive common zero of the parent source.

Conversely, given any positive parent zero p, choose a sufficiently large
power of two b>max p_i, put z_i=p_i-1 and g=sum z_iB^w_i. Then
0<g<bB^108. Strict positivity uses the fact that the all-one tuple is not a
source zero (parent r_5 evaluates to1). Hence 32g<Gcap. All weights are
positive, so canonical g is divisible by B and therefore by b^2.

## 4. Population calibration for the free-coordinate route

The low mask has 109v-31k one bits. Each of the22 distinct high target digits
B-2 has v-1 one bits, so

    pop(T)=131v-31k-22.

Let L=bB^2064 and R=(S+T)L+L-1-S. Unconditionally for positive b,g,
R=(L-1)S+LT+L-1>=8. On the bounded branch S+T<B^2064<=L.
For binary b, put u=log_2 L=k+2064v. The two blocks in R give

    pop(R)=u+pop(T)-tau,
    tau=pop(S)+pop(T)-pop(S+T)>=0,

and tau=0 exactly when S&T=0. Set

    c=2^(15kappa/2-11)=2^16012039, N=c B^1090.

The even choice of kappa makes c an integer, and

    u+pop(T)=2195v-30k-22=2log_2 N.

Legendre's identity v_2(binomial(2R,R))=pop(R) now proves
N^2 divides binomial(2R,R) exactly when S&T=0. This source contract plugs
into the inherited free-coordinate numerical finalizer; that finalizer's
remaining hypotheses and its two directions must still be checked separately.
R has total degree8255 in b,g, and N degree2180 in b.

## 5. Calibration for the integer two-root route

For the alternative outer word use n=B^2064 and

    X=n^2+(S+T)n+n-1-S,
    Y=2^(2195kappa-21) b^4359.

On the bounded binary branch the top leading bit adds1, giving
pop(X)=1+2064v+pop(T)-tau=log_2 Y-tau. Thus Y divides
binomial(2X,X) exactly when S&T=0. If b=1 modulo3, then B=1 modulo3
because kappa is even, ell=31 modulo3, Targets=22 modulo3, Mask=0 modulo3,
and T=22(1-2)=2 modulo3. Consequently X=2+T=0 modulo3.
Also X+1=-g modulo b since n and N0 are divisible by b. These are exact
source contracts, not a replacement for the separate two-root theorem.

## Validation and limitations

`verify_split.py` uses standard-library arbitrary-precision integer arithmetic
and explicit `require` calls, not Python assert. It independently parses all
22 parent polynomial expressions, verifies their sparse expansions and inverse
shears, proves all22 extraction identities, derives all89 kernels, and checks
leading coefficients, degrees and conservative coefficient bounds.
`test_split.py` repeats the checks in an isolated directory with and without
Python -O and rejects11 intentional corruptions, including omitted sign reversal.
Neither test is evidence for the inherited compiler semantics beyond its
explicit algebraic interface. No global minimum or new kernel certificate is
claimed.
