# Sparse target extraction with positivity translated in the packed word

This note supplies the new source theorem. The ten-integer
construction uses the source-interface finalizer of package40 at
ProveIt commit124c07c0b77a9e20e84676514d8b1ff78536ea3f. Its dependencies are
copied into upstream/. Its square-root separator is strengthened by the
separate finalizer proof supplied with this package. The complete circuit
in data/polynomial.json uses ten unrestricted integer variables and has
709 live binary operations and exact total degree 54,768,104. This note makes no global optimality claim.

## 1. A general support-sensitive extraction lemma

Let r_1,...,r_m be integer polynomials in n variables of degree at most2.
Their coefficients may be polynomials in fixed integer ports. Choose
w_0=0,w_1,...,w_n>0 such that all unordered pair sums w_i+w_j, including
repetitions, are distinct. Write

    S = {w_i+w_j : 0<=i<=j<=n},
    S_j = {alpha.w : coefficient of p^alpha in r_j is nonzero}.

For each row choose a target E_j. The sufficient and directly checkable
conditions are:

1. E_j>=max S_j;
2. E_j are distinct;
3. for j!=k, (E_k-E_j+S_j) is disjoint from S.

Condition3 is the essential improvement: it uses the actual source support
S_j. The previous construction used uniform spacing greater than2max w_i,
which is sufficient but not necessary. Crucially, S is still the full set
of quadratic pair sums, including monomials absent from every source row.

If r_j(p)=sum_alpha a_(j,alpha) p^alpha, put

    c_(j,alpha) = (2-|alpha|)! product_i alpha_i! a_(j,alpha),
    D(Z) = sum_j sum_alpha c_(j,alpha) Z^(E_j-alpha.w).

Then for every p,

    [Z^E_j] (1+sum_i p_i Z^w_i)^2 D(Z) = 2r_j(p).

Proof. The coefficient at alpha.w in the square is exactly
2!/((2-|alpha|)! product alpha_i!) times p^alpha. Pair-sum uniqueness
ensures there are no other monomials there. A contribution from row j to
another target E_k would require alpha.w+E_k-E_j in S, excluded by3.
The factorials cancel at the correct target. This is a polynomial identity,
not a statement checked only at bounded assignments.

No two nonzero terms of D from different rows have the same exponent:
if E_j-s=E_k-s', then E_k-E_j+s=s' in S for s in S_j,
contradicting3. Thus, if every ordinary coefficient of every r_j has
absolute value at most H, every coefficient of D has magnitude at most2H.
For nonnegative p the coefficients of the square are nonnegative and sum
to(1+sum p_i)^2. Consequently every coefficient of its product with D has
absolute value at most2H(1+sum p_i)^2. The full product has degree at most
M=max E_j+2max w_i.

## 2. Concrete parent, positions, and exact certificate

The parent consists of the31 positive variables and22 quadratic equations
of package40, retained exactly in upstream/parent_system.json and independently
in sparse coefficient form in upstream/parent_sparse.json. The31 names,
in their order, are:

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
    N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta.

The raw equations are retained, without replacing p_i by n_i+1 in their
coefficient expansions. Negate row8 and place it last in the coefficient
record ordering. Negation preserves its zero set. Its constant term is+1.
All other rows have their original signs. The support-sensitive targets,
listed in original row order, are:

| Original row | Sign | Target |
|---:|---:|---:|
| 1 | +1 | 714 |
| 2 | +1 | 6707 |
| 3 | +1 | 6262 |
| 4 | +1 | 634 |
| 5 | +1 | 6148 |
| 6 | +1 | 5133 |
| 7 | +1 | 4099 |
| 8 | -1 | 7243 |
| 9 | +1 | 1024 |
| 10 | +1 | 2665 |
| 11 | +1 | 4617 |
| 12 | +1 | 5288 |
| 13 | +1 | 2271 |
| 14 | +1 | 3114 |
| 15 | +1 | 1023 |
| 16 | +1 | 5402 |
| 17 | +1 | 5193 |
| 18 | +1 | 2781 |
| 19 | +1 | 1906 |
| 20 | +1 | 6470 |
| 21 | +1 | 6168 |
| 22 | +1 | 4539 |

The32 weights, including padding0, are unchanged from package40:

    0,10,35,55,62,105,144,145,159,168,232,245,306,323,325,
    353,371,374,382,494,499,525,566,578,610,647,681,685,741,
    777,783,799.

Hence t=799, max E_j=7243, M=8841. The target positions are literal fixed
integers. Their discovery procedure is irrelevant to their correctness.
code/verify_source.py verifies528 pair positions,1974 cross-row support
conditions, and49,632 dense convolution pairs; it recovers each of the22
quadratic rows as an exact polynomial in the31 parent variables and the
four symbolic coefficient ports. It also verifies that D has94 weighted
records and leading coefficient2 at degree7243. No unproved combinatorial
search assertion remains in the equation.

## 3. Moving positivity into the packed variable

The source digits should be nonnegative, while the parent variables are
strictly positive. The old construction expanded every substitution
p_i=n_i+1 inside every r_j. That creates136 weighted records and161
expanded coefficient terms.

Instead put ell(Z)=sum_i Z^w_i and encode g(Z)=sum_i n_i Z^w_i.
Then

    1+g(Z)+ell(Z)=1+sum_i(n_i+1)Z^w_i.

The extraction lemma applies directly to the original r_j:

    [Z^E_j] (1+g(Z)+ell(Z))^2 D(Z) = 2r_j(n+1).

This identity reduces the weighted records to94 and the expanded
coefficient terms to99. In the final circuit ell is already required for
the low digit mask; inserting it in the square costs only one extra
addition. This is an exact translation of all positive parent witnesses.
It does not restrict the original variables to a sparse subset.

## 4. Fixed coefficients

Use the whole unchanged native tuple from package31:

    (beta,K0,MC,MF),

with MF already shifted. The binary payloads are supplied. Their respective
bit lengths are1064921,1070004,1064921,1064922. Set

    H=8(1+beta+K0+MC+MF)^2,
    beta_S=2^2140030.

Every raw ordinary coefficient has port degree at most2 and coefficient
L1 norm at most4, so H is a conservative bound. The exact integer audit
checks beta_S>4*33^2*H and beta_S>36H+2. Both follow also from the
package40 bit bounds. The exponent2140030 is even, so beta_S is a square
and beta_S=1 modulo3. Nine derived nonliteral coefficient leaves plus
beta_S occur in the exported circuit. All ten actual values are supplied
as signed-magnitude payloads with finite recipes and hashes.

## 5. New two-variable source

For final variables f,g define

    b=1+3f, B=beta_S b^2, ell=sum_i B^w_i,
    N0=B^(t+1), N1=4B^(M+1), N=N0N1,
    Mc=N0-1-(b-1)ell,
    Qc=(B-2)sum_j B^E_j,
    Tc=Mc+Qc N0,
    Jc=2(1+g+ell)^2 D(B)+sum_(i=0)^M B^(i+1),
    Sc=g+Jc N0,
    Rc=(Sc+Tc+1)N+Tc+1,
    X=(N-1)Rc, Y=N^2, Ccap=bB^t.

All exponents are fixed nonnegative integers, so these expressions are
ordinary integer polynomials in f,g. The sum expressions are evaluated by
finite arithmetic circuits, not by variable-length operations.

### Broad ranges before binary decoding

Assume f!=0, b is a square, and0<=g<2Ccap. Since b=1+3f is a square,
b>=4 and f>0. B>2b. The leading term of D is2B^7243; every other coefficient
has magnitude at most2H. Since B>2H+1, D(B)>0.

The low mask has digits B-b at selected positions and B-1 elsewhere, so
0<=Mc<N0. Also0<=Qc<B^(7244)<N1, giving0<=Tc<N.

From g<2bB^t and integrality,1+g<=2bB^t. Since
ell<B^(t+1)/(B-1)<2B^t and b>=4,

    1+g+ell<3bB^t.

Thus, using M=7243+2t,

    0<Jc<[(36Hb^2+B)/(B-1)] B^(M+1)<2B^(M+1)<N1.

The penultimate inequality follows from36Hb^2<B-2. Also g<N0;
therefore0<=Sc<N. This is a genuine bound for every integer in the broad
range; it does not presuppose a valid digit encoding.

Since b=beta_S=B=1 modulo3 and N=4B^(M+t+2), N=1 modulo3,
so3 divides X. Moreover Rc>=N+1>B>b and N>=4, hence X>3b.
The fixed base gives Y>max(b,256). These are the inherited finalizer's
pre-decoding source bounds.

### Binary mask equivalence

Assume further that b is a power of two. Then B,N0,N are powers of two.
For g<N0 the condition of no binary carries between g and Mc is equivalent
to

    g=sum_i n_i B^w_i, 0<=n_i<b.

At selected cells Mc leaves exactly the low log2(b) bits available; it masks
all bits at every other cell. Set p_i=n_i+1, so1<=p_i<=b.
The coefficient bound from section1 now gives

    2H(1+sum p_i)^2 < 2H(33b)^2 < B/2.

Consequently the base-B digits of

    Kc=(1+g+ell)^2D(B)+(B/2)sum_(i=0)^M B^i

are precisely B/2 plus the corresponding product coefficients, all strictly
between0 and B. Its digit at E_j is B/2+2r_j(p). For any digit0<e<B,
no binary carries between e and B/2-1 holds exactly when e=B/2.
Applying this at all target positions and doubling both words gives

    no carries(Jc,Qc) iff every r_j(p)=0.

The low and high words occupy disjoint blocks, so

    no carries(Sc,Tc)
      iff g encodes valid digits and every r_j(n+1)=0.

Package40's elementary central-binomial lemma applies without alteration:
for the displayed Sc,Tc,N,X,Y,

    no carries(Sc,Tc) iff Y divides binomial(2X,X).

### Completeness and the positive lower bound on g

Given any positive parent solution p, choose a sufficiently large
b=4^a with b>max p_i; then f=(b-1)/3 is a positive integer. Set n_i=p_i-1
and g=sum n_i B^w_i. The preceding identities imply the required central
binomial divisibility. The all-ones positive tuple is not a parent solution:
row5 is E-X(a-E)=1 there. Hence some n_i>0. Since every w_i>=1 and B>b,
g>=B>b. Also g< bB^t=Ccap, by n_i<=b-1 and the geometric-series bound.

Conversely, f!=0, b a square and power of two,0<=g<2Ccap, and the central
binomial divisibility force valid digits and all parent equations.
This establishes exactly the forward and reverse source interface used by
the inherited ten-integer finalizer, including its cofinal-square-base
completeness requirement.

## 6. Composition, result, and proof status

Substitute this source into package40's ten-integer finalizer with the
proved new separator weights (1,b,bK), retaining the quintic divisibility
merger and three-square norm. The separate finalizer proof supplies the
new separation theorem. The source interface just proved is the only
contract needed from the quadratic encoder. Therefore the new fixed
polynomial has an integer zero iff the positive quadratic parent has a
solution. By the inherited native-window/Pell compiler and K215 calibration,
its absence of integer zeros is ZFC-provably equivalent to Con(ZFC).

This is an ordinary mathematical argument formalizable in ZFC. The finite
scripts certify the new explicit arithmetic, coefficient binding, and
support conditions. They do not constitute a new end-to-end Lean, Rocq,
or object-language ZFC derivation of the compiler or of Sun's theorems.
Neither consistency nor inconsistency is assumed or decided.

The literal evaluator has189 additions, 25 subtractions, 495 multiplications.
Its exact total degree is 54,768,104. The upper bound is propagated through
the DAG. Substituting all ten variables by one indeterminate gives a
nonzero coefficient at that degree:323596601 modulo 1000000007. This proves
that the upper bound is attained. The independent JSON audit reproduces
the nonzero leading coefficient modulo three primes and compares all 54
named nodes against literal source and finalizer formulas in120 deterministic
control assignments. The finite evaluations are diagnostics; the nonzero
leading coefficient is an exact degree certificate.

## 7. Further opportunities

1. Optimize the target positions jointly with arithmetic evaluation cost;
   minimum span need not minimize operation count.
2. Replace the full B2 condition by protection only for supported monomials,
   while retaining all dense-square pollution checks.
3. Further simplify the nine-positive-variable Jones finalizer; the current
   package already applies the new source to that interface.
4. Formalize the support-sensitive extraction lemma and coefficient compiler.
5. Improve the finalizer's square-root separation using relations among its
   actual radicands. This is independent of the present source proof.
