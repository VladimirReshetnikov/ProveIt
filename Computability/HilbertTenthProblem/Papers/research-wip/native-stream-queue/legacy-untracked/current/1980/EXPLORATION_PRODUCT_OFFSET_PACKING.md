# Product offset with explicit canonical-code bounds

The support and unit-normalization barriers identified in this exploration
were subsequently resolved by the reset padding and two square tests in
`LINEAR_RADIX_96_PROOF.md`. The present note preserves the earlier
conditional arithmetic audit; that separate note contains the completed
96-operation universality argument.

This is an independent arithmetic and packing audit of the proposed
replacement of the 97-operation unit-centered offset. It is not a
proof of a 96-operation universal system: the linear-radix coefficient
tests still need a complete support and unit-normalization construction.
Fixed numerals and equality tests are free.

## Exact arithmetic comparison

Keep the supplied positive quantity `Omega=lambda-e`. Replace

    P2=(theta*lambda)*q,
    P1=Omega*C2,
    sigma=P2-P1

by

    gap=q-C2,
    sigma=Omega*gap.

The shared register `theta*lambda` is retained because the packed
mask needs it. This replacement deletes one multiplication and
does not change the addition count. Add the positive bound

    ell+alpha2=q.

It costs one addition. Thus the new offset and explicit bound
together still cost 97 operations, now 53 multiplications and
44 additions. If a new coefficient test justifies `B=H*b` in place
of `B=H*b*b`, deleting `b2=b*b` gives 96 operations, specifically
52 multiplications and 44 additions.

The new variable `alpha2` is positive. Every retained positive
quantity has the same role, and the altered positive `sigma` is
defined by the new product. This is a count of this explicit
proposed schedule, not a correctness claim about the missing code.

## Preliminary ranges do not require decoded exponents

Assume the retained equations and positive unknowns give

    B=H*b, H>16, b=x+beta>=2,
    theta=B-4,
    q^2=1+(B-1)*lambda,
    C=x+g,
    Omega=lambda-e>0,
    sigma=Omega*(q-C^2)>0,
    S2=ell+e*q,
    S2+alpha=q^2,
    ell+alpha2=q,
    n=q^8.

These are statements before using either Pell exponent identity.
The geometry gives `B<=q^2`, `q>=6`, and
`lambda<q^2/(B-1)`. Positivity of both factors in the sigma equation
gives

    C^2<q,
    0<g<C<q,
    0<sigma<lambda*q<q^3.

Also `0<S2<q^2` and `0<ell<q`. Therefore

    S=g+q^2*S2+q^4*sigma

satisfies `0<S<q^7<n`. One can check the strict bound using
integer maxima: the three summands are at most `q-1`,
`q^2*(q^2-1)`, and `q^4*(q^3-1)`.

Put

    Tcoef=1+theta*lambda=q^2-3*lambda,
    Tplus=q^2*Tcoef-(b-1)*ell+theta*ell*q^4.

Because `theta*lambda>=B-4>b`, the positive first summand is
greater than `b*q^2`, while `(b-1)*ell<b*q`. Thus `Tplus>0`
without assuming that its unnormalized first block is nonnegative.
For the upper bound, `Tcoef<q^2`, and

    1+theta*ell <= 1+(B-4)*(q-1) < B*q.

Consequently

    Tplus < q^4*(1+theta*ell) < B*q^5 <= q^7 < n.

The existing packed index

    r=S*(n^2-n)+Tplus*(n^2-1)

therefore still satisfies `n^2-1<=r<2*n^3`. In particular, all
retained preliminary Pell estimates that use `B<=n`, `n>=64`,
`r<2*n^3`, and `U*Y>=n^4>r+1` remain available. There is no
packing-range obstruction to this product offset.

## Canonical splitting after the Pell step

Once the unchanged Pell proof yields `q=B^L` with `L>=2`, one has
`b<B<q`. The first unnormalized mask block is then nonnegative:

    q^2-1-(b-1)*ell
      >= (q-1)*(q-b+2) > 0.

The explicit bound makes both supplied coefficient-code quantities
smaller than q: `ell<q` directly, and `e<q` follows from
`ell+e*q<q^2`. The second no-carry test and the fixed congruence can
therefore recover the two codes separately, without using a high
third-mask argument to eliminate a quotient alias.

The retained third mask is still needed to establish the encoded
equations. Freeing its high digits from their former alias-removal
role does not, by itself, prove any new low-digit test.

## A tied alternative bound

One may replace the two positive bounds by

    ell+e+alpha=q.

This costs two additions, exactly as the two former bounds did.
It implies `ell<q`, `e<q`, and

    ell+e*q <= (q-e-1)+e*q < q^2.

For the intended short coefficient and indicator codes, necessity
can choose q sufficiently larger than their sum. This formulation
uses one fewer unknown/equality but saves no arithmetic operation.
The already needed `S2=ell+e*q` still has to be computed.

## Remaining code barrier

For `B=H*b`, a bounded number of quadratic products of digits below
b can have size comparable with `B^2`, rather than B. Testing two
adjacent digits at each row can reject a negative residual, and
paired residuals F and -F can then force zero. A zero-coefficient
position immediately preceding each row reduces a wider incoming
carry to -1 or 0.

This does not automatically preserve the unit test. The old special
row accepts a delta-square digit only in 0 through 3, which forces
delta in {0,1}; two separately allowed digits can instead admit a
large square. For example, with B=256, delta=16 has square B and
both its low digits are allowed. A stronger range or a separate
unit-normalization argument is needed.

Likewise, introducing a constant term 1 in the complementary
coefficient polynomial makes `C^2` contribute `2*x*X_i` at a
variable position. Because the shared indicator also tests those
positions, the previous necessity proof no longer applies. Moving
the input from weight zero to a positive position by `C=x*B+g`
costs one extra multiplication and returns the conditional count
to 97. No absorption of this extra product into the current Pell
or packing registers has been established.
