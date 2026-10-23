# Independent review: split source, reduced rank, and circuit certificate

## Disposition and scope

PASS for the positive nine-variable adjunct in this directory: exact degree
1,910,404 and 473 live binary operations (289 multiplications, 162 additions,
22 subtractions). This is an independent AI-assisted mathematical and
implementation review within the project, not external human peer review or
an end-to-end proof-assistant certificate. The free-coordinate numerical
adapter is reviewed separately; the inherited source compiler and Jones
ratio interface remain explicit dependencies.

No frozen baseline files were changed. The source is the coherent old31
tuple, not a mixture with the alternate packet52 tuple. The split layout and
kernel hashes are unchanged from the separately verified degree-separated
source certificate.

## 1. The source hypotheses hold before the equation vanishes

Write M=2^2134927, a=4096M=2^2134939, B=ab^2, with b,g>=1.
Use the original split116 definitions of ell, targets A_q, N0=B^117,
G_s=D2(B)(ell+g)^2+D1(B)(ell+g)+D0(B),
J_c=2G_s+A_q, S_c=g+N0 J_c, and
T_c=N0-1-(b-1)ell+N0(B-2)A_q.

The quadratic kernel has leading coefficient +1 at exponent 1929.
The other kernel degrees are 2027 and 1719. Geometric bounds give

    D2(B)>B^1929/2,
    |D1(B)|<2M B^2027,  |D0(B)|<2M B^1719.

For U_s=ell+g>=B^116, their negative contributions relative to
B^1929 U_s^2 are below 2M/B^18 and 2M/B^442. Each is below 1/8.
Therefore G_s>B^1929 U_s^2/4>0 for every g>=1, not just bounded g.
The mask N0-1-(b-1)ell has digits B-b at selected positions and B-1
elsewhere, so it lies in [0,N0). Thus S_c,T_c are positive.

The changed source registers are

    L=b B^2279,
    R=(S_c+T_c)L+L-1-S_c=(L-1)S_c+L(T_c+1)-1,
    N=c b B^1201,  c=2^17079501.

Consequently R>=L-1>=8, b<=R, and N>=max(8,b) without any equation,
digit, or square assumption. No assertion R>=N or R>=N^2 is needed by
the numerical interface used here.

## 2. The soundness range is four base words, not two

The normalized margin retains the original Gcap=32b B^116. Ratio
soundness therefore gives 0<g<4b B^116. This review does not reuse a
bound valid only for g<2b B^116.

Since ell<2B^116 and b>=1, one has U_s<6b B^116. Summing the three
kernel bounds gives

    |G_s|<43 M b^2 B^2162/(B-1).

Set Z=B^2162. Because B>=4096M b^2 and B>=4096,

    2|G_s|/Z < 86 M b^2/(B-1) <= 86/4095 < 1/32.

Also A_q<Z/64 and (B-2)A_q<Z/64, since the largest target is 2129
and the gap to Z is 33. Thus g<N0, J_c<3Z/64,

    S_c<N0+3N0 Z/64,
    T_c<N0+N0 Z/64,
    S_c+T_c<2N0+N0 Z/16<N0 Z=B^2279<=L.

All inequalities are strict where block separation requires them. They
hold even at b=1. The halved block therefore needs no stronger margin or
completeness restriction.

After low-mask recovery, y_i=z_i+1<=b and every convolution coefficient
has absolute value below 993M b^2<B/4. The existing sparse +1 borrow
argument is unchanged, as are all 22 residual identities. It proves
S_c & T_c=0 exactly when the packed positive source coordinates are a
common zero.

## 3. Removing the leading bit changes the threshold by exactly two

For L=2^u and S,T>=0 with S+T<L, the new rank has two disjoint blocks:

    R=(S+T)L+(L-1-S).

The lower block is the u-bit complement of S, hence

    pop(R)=u+pop(T)-[pop(S)+pop(T)-pop(S+T)].

The bracket is nonnegative and is zero exactly when S&T=0. This is the
ordinary binary carry identity, not a finite-search assumption.

If b=2^k and B=2^nu, then nu=2134939+2k, including k=0. The low mask
population is 117nu-31k, and the 22 high target cells contribute
22(nu-1), so pop(T_c)=139nu-31k-22. With u=k+2279nu,

    u+pop(T_c)=2418nu-30k-22
              =2(17079501+k+1201nu)=2 log2(N).

The old leading L^2 bit contributed one set bit, and halving L lowers
u by one more. Hence the squared threshold falls by two powers of two,
implemented by halving its square root c. Legendre's valuation formula
then gives precisely the original no-carry test.

At b=1 the low mask is N0-1, while soundness gives 0<g<4B^116<N0;
therefore g & (N0-1)=g!=0. That extra boundary introduces no zero.
Completeness continues to choose arbitrarily large powers of two; the
all-one source tuple is not a zero, so the required packed g is positive.

## 4. Literal circuit and exact-degree checks

`check_source_independent.py` imports no builder, evaluator, or author
checker. It independently authenticates the four original coefficient
payloads, parses the emitted arithmetic DAGs, and proves 97 exact local
register polynomial identities. These include all three source kernels,
the changed R,L,N, free positive C, the sole j-minus-one domain shift, and
E0=J(n+(bw)^2)+Q. Five universal polynomial identities prove equivalence
of the direct norm and its cancellation-resolved certificate form.

The source diagonal degrees and heads are

    deg S_c=4556, head(S_c)=2a^2278;
    deg T_c=4494;
    deg R=9115, head(R)=2a^4557;
    deg N=2403, head(N)=c a^1201.

In the certificate circuit, deg Omega=93880 and deg Delta1=767442.
The unique dominant inner term is Omega^2 Delta1, of degree 955202.
Its square gives degree 1910404; the subtracted final term has degree
4*93880+130606+879822=1385948 and cannot cancel it.

Independent multivariate upper-bound propagation and nonzero diagonal
coefficients modulo the primes 101, 1009, and 1000003 establish the exact
degree using the actual fixed tuple. Their residues are 96, 469, and
114598. They also agree with the author's explicit head
2^186 a^954792 c^400. The gate audit checks every node is live and
topologically ordered, and counts 473 binary operations.

## 5. What the finite receipt does and does not establish

Normal and optimized Python runs agree byte for byte. In addition to the
universal polynomial identities and exact-degree witnesses, the receipt
checks 43,945 reduced-rank block examples, six mask-population cases
including b=1, and 50 source-bound stresses including the cap boundary and
inputs far above it. These diagnostics support the implementation; the
universal inequalities and equivalences are the arguments above. This
review neither decides consistency nor replaces any imported compiler
theorem by numerical testing.
