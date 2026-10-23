# Independent audit of the B2 multi-target source reduction

Prepared for the parent research task, 2026-10-23. This note audits the new
source construction, not the inherited K215/native compiler or Sun's 2026
Lucas bridge. The direct reference checked was Sun, *Further results on
Hilbert's Tenth Problem* (2021), arXiv:1704.03504v7, Lemmas 2.2, 2.4, 2.6
and the proof of Theorem 3.1. The proof below is an adaptation for a system
with multiple test digits; it is not a restatement of Sun's theorem.

## 1. Finite data independently checked

The parent supplied `research_root/weights_b2.json`. The 32 integers are

```
0,10,35,55,62,105,144,145,159,168,232,245,306,323,325,353,
371,374,382,494,499,525,566,578,610,647,681,685,741,777,783,799.
```

Independent enumeration of all 528 unordered pairs with repetition verified
that their sums are distinct modulo 1023. Hence their integer sums are
distinct. Padding a monomial of degree at most two by zero-weight letters
to length two proves injectivity of its weighted exponent. The finite check
does not need the finite-field derivation of the table as an assumption.

Write the positive weights as w_1,...,w_31 and t=799. For 22 rows choose

    E_j = 2t + (j-1)(2t+1),       1 <= j <= 22,
    E_max = 44t+21 = 35177,
    M = E_max+2t = 46t+21 = 36775.

The spacing 2t+1, rather than 4t+1, is sufficient. Product supports may
overlap away from targets; no target lies in another row's product support.

## 2. Abstract quadratic-system statement

Let r_1,...,r_m be integer polynomials of degree at most two in n variables,
with no common zero at the all-zero tuple. Assume r_m(0)>0; reordering and
sign reversal of a row are allowed. The actual parent has r_5(0)=1, so move
that row to the last position without changing its sign. Let H>=1 bound
the absolute values of every ordinary coefficient of every row. Choose

    beta = 2^(2a) > 4(n+2)^2 H,       a >= 1.

For the fixed n=31,m=22 instance this is a fully effective coefficient
bound, not an additional witness. Define b=1+3f and B=beta*b^2. For a
multi-index alpha of weight at most two put

    e(alpha) = sum_i alpha_i*w_i,
    c_(j,alpha) = (2-|alpha|)! * product_i(alpha_i!) * [x^alpha]r_j.

Thus |c_(j,alpha)|<=2H. Define

    D(B) = sum_(j,alpha) c_(j,alpha) * B^(E_j-e(alpha)),
    ell(B) = sum_i B^w_i,
    N0 = B^(t+1),       N1 = 4 B^(M+1),       N=N0*N1,
    mask = N0-1-(b-1)*ell(B),
    target = (B-2)*sum_j B^E_j,
    T = mask + target*N0,
    J = 2(1+g)^2 D(B) + sum_(k=0)^M B^(k+1),
    S = g + J*N0,
    R = (S+T+1)N + T+1,
    X = (N-1)R,       Y=N^2,       cap=b B^t.

Every exponent is a fixed nonnegative integer. The notation D(B) introduces
no polynomial evaluation at an existentially encoded coefficient: its
displayed coefficients are the fixed source coefficients.

## 3. Sparse coefficient extraction

For z_i>=0 put C_z(Z)=(1+sum_i z_i Z^w_i)^2. Its degree is at most 2t,
and all its coefficients are nonnegative. The coefficient at exponent
e(alpha) is

    2! / [(2-|alpha|)! product_i(alpha_i!)] * z^alpha.

Each row contribution D_j has support inside [E_j-2t,E_j]. These intervals
are disjoint because E_(j+1)-E_j=2t+1. Consequently every coefficient of
D has absolute value at most 2H. Further, C_z D_j has support inside
[E_j-2t,E_j+2t]. For k!=j, the target E_k lies outside this interval.
It follows exactly that

    [Z^E_j] C_z(Z)D(Z) = 2 r_j(z).

This is the essential system improvement: one square of the packed digit
word tests every quadratic row. It never forms the sum of squared rows.

## 4. Positivity and uniform ranges before digit recovery

Suppose f!=0 and b is an integer square. Since b=1+3f, b is nonzero;
f<0 would make b<0, and f=0 is excluded. Thus f>0 and b>=4. In particular
B>=beta*b^2>2b and B>=4.

The leading coefficient of D at E_max is 2r_m(0)>=2. Every other exponent
is strictly smaller, because all variable weights are positive and the
last row has strictly larger target than the earlier rows. The coefficient
bound and 2H<=B-1 give

    D(B) >= 2 B^E_max - 2H * (B^E_max-1)/(B-1) > 0.

The weaker bound with leading coefficient one would also suffice. Moreover

    |D(B)| <= 2H sum_(k=0)^E_max B^k.

The mask has digits B-b at the selected positions and B-1 elsewhere, so
0<=mask<N0. The target has digit B-2 at the distinct E_j and zero elsewhere,
so 0<=target<B^(E_max+1)<=B^(M+1)<N1. Therefore 0<=T<N.

Now suppose 0<=g<2 cap and g is an integer. Then

    1+g <= 2b B^t,       0<=g<N0.

The coefficient condition implies B-2>=16H b^2. Hence

    0<J
      <=16H b^2 B^(2t) sum_(k=0)^E_max B^k
            +sum_(k=0)^M B^(k+1)
      < [(16H b^2+B)/(B-1)] B^(M+1)
      <=2 B^(M+1)<N1.

Since g and J are integers, 0<=S<N. No assumption that b is a power of two
has been used in these range inequalities.

Also beta and b satisfy beta=1 mod 3 and b=1 mod 3, so B=1 mod 3 and
N=4 B^(M+t+2)=1 mod 3. Consequently 3 divides X. Since R>=N+1>B>=b and
N>=4, X>3b. The large fixed beta also gives Y=N^2>max(b,256).
Finally cap=2^(2at) b^(2t+1), exactly the coefficient-and-power form used
by the later Lucas bridge.

## 5. No-carry equivalence when b is a power of two

Assume in addition b is a power of two. Then B,N0,N are powers of two.
For g in [0,2cap), the mask test has the exact equivalence

    tau_2(g,mask)=0
      iff g=sum_i z_i B^w_i for some integers 0<=z_i<b.

This follows digit by digit: adding B-1 forces an unselected digit to
zero, and adding B-b permits exactly the digits below b because b divides
B and both are powers of two. The cap bound ensures g<N0.

For such a packed g define

    K = (1+g)^2 D(B) + (B/2)sum_(k=0)^M B^k,       J=2K.

By the coefficient condition,

    2H(1+sum_i z_i)^2
      <=2H(1+n(b-1))^2 < B/2.

All coefficients e_k in the base-B expression for K therefore satisfy
0<e_k<B. Its digit at E_j is B/2+2r_j(z). There is no carry between these
digits because they already lie in the valid digit interval. Since B/2
is a power of two, for any integer e in [1,B),

    tau_2(e,B/2-1)=0 iff e=B/2.

Applying this to every distinct target digit proves

    tau_2(K,(B/2-1)sum_j B^E_j)=0
      iff r_1(z)=...=r_m(z)=0.

Multiplying both summands by two preserves the number of binary carries,
so the left side is equivalent to tau_2(J,target)=0.

Because g,mask are below N0, concatenation gives

    tau_2(S,T)=0
      iff tau_2(g,mask)=0 and tau_2(J,target)=0.

This remains true when the blocks in C_z D overlap: overlaps only affect
ordinary non-target coefficients, and the uniform coefficient bound above
already covers them.

## 6. Central binomial bridge and both existence directions

For N a power of two and S,T in [0,N), the binary carry identity is

    tau_2(S,T)=0 iff N^2 divides binomial(2X,X),
    X=(N-1)((S+T+1)N+T+1).

This is the p=P=2 case of Sun's Lemma 2.2. Combining it with Section 5 gives
the exact reverse implication required by the later bridge: f!=0,
b square and a power of two, 0<=g<2cap, and Y|binomial(2X,X) imply a
nonnegative common zero of the rows.

Conversely, given a nonnegative common zero z, choose b=2^(2q) larger
than every z_i and as large as desired. It is 1 mod 3, so f=(b-1)/3 is a
positive integer and can exceed any prescribed bound. Let

    g=sum_i z_i B^w_i.

The tuple z is nonzero because the rows have no common zero at zero.
Thus g>=B>=b. The digit packing inequality gives g<bB^t=cap. Every
target test vanishes, so the central binomial divisibility holds. This
proves the required cofinal positive source direction, as well as ordinary
existential completeness.

## Audit conclusion

The multi-target quadratic source satisfies the same explicitly stated
input/output interface as the source polynomials consumed by the existing
Sun-2026 ten-integer finalizer. Its proof requires only the checked B2
table, elementary coefficient arithmetic and the inherited binary carry
identity. It yields a valid source replacement while preserving the
number of final unrestricted variables.

The following remain separate obligations of the final release: derive
the actual row coefficients from the literal parent, certify their bound,
choose and bind one complete native coefficient tuple, verify the final
straight-line circuit, and retain the existing mathematical proof of the
Sun-2026 finalizer. No formal-kernel verification of those inherited
theorems is asserted here.
