# Shortening the first packed block: a decoding lemma and an obstruction

This note investigates the product-bound 91-operation construction. It
does not modify its source system or establish a smaller operation count.
The new facts `sigma=(e-ell)C^2`, `ell+sigma<q`, and `e>ell` make a
width-q first block more plausible, but reducing the packing parameter
requires a separate argument. The two issues must not be conflated.

## 1. Conditional decoding despite a first-block borrow

Retain the base-four alphabet and write

    B=H0+1+b, theta=B-4, q=B^L,
    lambda=(q^2-1)/(B-1),
    0<ell<e<q, 0<sigma<q, 0<g<q.

Consider the shortened arrangement

    S=g+q*(ell+e*q+q^2*sigma),
    Tplus=q*(1+theta*lambda)+ell*(theta*q^3-b),
    T=Tplus-1.                                      (1)

Suppose the binary nonoverlap condition `S & T = 0` has already been
established. This is an explicit hypothesis of this section, not a
consequence proved below for a smaller packing parameter.

Let k=floor(b*ell/q), and let r_b=b*ell-k*q. Then

    T=(q-1-r_b)+q*(theta*lambda-k)+q^3*theta*ell.

Here 0<=k<=b-1<theta. Subtraction of k changes only the first
base-B digit of theta*lambda: that digit becomes B-4-k, and all
remaining 2L-1 digits remain B-4. Thus the middle mask permits
all base-B digits of ell+e*q to be at most three except its unit
digit d0, for which bitwise complementation gives

    d0<=k+3<=b+2=B-H0+1.                          (2)

Let F(T) be the actual base-B digit polynomial of ell+e*q. Assume
the usual fixed-index congruence and bound

    ell+e*q=V modulo (B-4),
    V=ell0(4)+4^L*e0(4),
    deg ell0,deg e0<K, K+1<L,
    H0>2*4^(2L+1).

The canonical combined polynomial has digits at most three, so
0<=V<4^(L+K)<4^(2L). Equation (2) gives

    0<=F(4)<=B-H0+1+3*sum_(j=1)^(2L-1)4^j
             =B-H0+4^(2L)-3<B-4.

Also V<B-4. The congruence therefore implies F(4)=V as integers.
This alone does not give uniqueness of the digit polynomial, because
d0 has not yet been bounded by three.

However, nonnegativity now excludes any e digit in degree K or above:
such a digit contributes at least 4^(L+K)>V. Hence e<B^K, and the
strict product-bound inequality ell<e gives ell<B^K too. Consequently

    b*ell<B^(K+1)<q,

so k=0. Now d0<=3 and ordinary uniqueness of base-four digits recovers
ell=ell0(B), e=e0(B). The recovered short code also gives theta*ell<q,
and therefore S,T<q^4 for this arrangement.

This is a valid way to remove a first-block borrow *after* obtaining
binary nonoverlap. It does not supply the packing-range hypothesis
needed to infer nonoverlap from central-binomial divisibility.

## 2. Why n=q^4 does not follow by the old packing lemma

The usual identity is

    r=S*(n^2-n)+(T+1)*(n^2-1).

For 0<=S,T<n and n a power of two, the binary digit-sum formula
relates `n^2 | binomial(2r,r)` to `S & T = 0`. Its range hypothesis
is essential. Even the abstract example S=3,T=n+1, for any power
of two n>=8, satisfies the binomial divisibility although S&T=1.

There is also an exact infinite family respecting the stronger
product bound, the geometry, and the form (1). Let

    H0=2^h, h>=2,
    s=2^k, k>h, B=s^2, L>=3, q=B^L, n=q^4,
    b=B-H0-1, theta=B-4, lambda=(q^2-1)/(B-1),
    ell=1+2B^(L-1), e=ell+1,
    x=1, g=s-1, C=s, sigma=B.

Then beta=b-x and alpha=q-ell-sigma are positive, and

    sigma=(e-ell)*C^2,
    ell+sigma+alpha=q,
    0<S<n, T=n+T0 with 0<T0<n,
    floor(b*ell/q)=1.

The only overlapping bits of S and T are the H0 bit in their unit
digits and the unit bit in their base-B digits at position L. Thus
S&T is nonzero. Nevertheless

    popcount(r)=2*log2(n)+h-2,                     (3)

so n^2 divides binomial(2r,r).

Here is a direct derivation of (3). The low q-block of T has digits
H0 at zero, B-1 at positions 1 through L-2, and 2H0+1 at L-1.
The middle mask has B-5 at position L and B-4 at all its remaining
positions. Its high q-block has B-4 at its first position and B-8
at its last, followed by the single overflow bit at position 4L.
Adding S and T causes a digit-sum loss k-h at their unit digit and
a loss two at position L; all other displayed additions are
carry-free. Hence

    popcount(S+T)=popcount(S)+popcount(T)-(k-h+2).

On the other hand, S+1 replaces its unit digit s-1 by s, so
popcount(S+1)=popcount(S)-k+1. Since T=n+T0 and S+1<n, the
three base-n blocks of r give

    popcount(r)=2*log2(n)+popcount(S+T)
                  -popcount(S+1)-popcount(T0).

Substitution proves (3).

The parameters h and k may be made arbitrarily large; in particular
H0 can exceed the fixed interpolation and coefficient bounds for any
chosen L. This family deliberately does not impose the admissible
fixed-index congruence. Its r is odd, so it also does not establish
compatibility with the canonical necessity construction of the
half-parameter Pell block. It is an obstruction to directly reusing
the packing lemma under the displayed product/range hypotheses, not
a spurious solution of the complete universal system. A further
argument using the retained equations might still exclude it.

The finite checker `../../tmp/check_short_first_block.py` verifies
these exact identities without constructing factorials or printing
large decimal integers. The displayed formulas prove the family.

## 3. Operation accounting remains a separate obstacle

Even if the mathematical range problem for (1) were solved, the
direct schedule would only tie the current count. The old powers
q^2,q^4,q^8 cost three multiplications. Arrangement (1), with
n=q^4, needs q^2,q^3,q^4, again three multiplications. Replacing
the outer q^2 scaling by q and the high-mask q^4 by q^3 otherwise
preserves the counts.

Another order is

    S=g+q*sigma+q^2*(ell+e*q),
    Tplus=q+q^2*theta*lambda+ell*(theta*q-b).

This uses only q^2,q^4 for its powers, saving one multiplication,
but loses the shared constant in Tcoef=1+theta*lambda and requires
one extra addition for the displayed q. The total again ties.

Thus neither reblocking currently establishes a count below 91.
The narrow-borrow lemma is potentially reusable, while the range
obstruction and operation accounting remain explicit boundaries.
