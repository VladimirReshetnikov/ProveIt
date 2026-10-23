# Independent review of the fused nine-variable positive-source change

Reviewed: `nine_fast/build_nine.py`, function `positive_source` and
its use in `build`; the pinned positive quadratic source and the selective
code in `nine_fast/upstream/code_positive.json`. This review concerns the changed source
layer and the parity of its packed variable. It does not independently
certify the downstream ratio theorem or fused finalizer.

**Conclusion:** the change is sound with the corrected selective targets
and quantitative bounds below. Reusing the old shifted-source code without
recertification would have been incorrect: shifting the source variables
canceled two source monomials, so its support certificate did not imply a
certificate for the original unshifted support. Independent direct checks
detected five unwanted target interactions. The corrected code changes
row 13's target from 2212 to 2124 and row 21's from 1050 to 1059; it keeps
the coordinate weights, all other targets, and maximum target unchanged.
The decoder still stores nonnegative offsets. The evaluated word is
`1+g+ell`, so the unshifted positive residuals are evaluated at those
offsets plus one. The new reversed polynomial has 94 distinct exponents,
degree 5102, and leading coefficient 1. Its degree must not be described
as the maximum marked target 5190.

## 1. Exact change of coordinates and extraction

Let the original positive source have residuals r_j(z_1,...,z_31).
For a monomial z^alpha of degree at most two, pad its index multiset with
zeros to a pair and multiply its coefficient by

    (2-|alpha|)! product_i alpha_i!.

The new `positive_source` implements precisely this operation on the
unshifted source. The old implementation instead expanded each source
coordinate as x_i+1 before forming the reversed polynomial.

For decoded offsets x_i>=0 put g=sum_i x_i B^w_i and
ell=sum_i B^w_i. Then

    1+g+ell = 1+sum_i (x_i+1) B^w_i.

The retargeted selective certificate has been checked directly on the
unshifted support, independently of the builder's implementation.
There are 94 used reversed terms. Every one of their 94*528=49,632
interactions with a padded input pair was enumerated. Exactly 94 land at
marked positions, all on the correct row and the same monomial. Thus,
as a polynomial identity in the positive source variables,

    [t^target_j](1+sum_i z_i t^w_i)^2 D(t)=2r_j(z).

This also proves injectivity of the reversed exponents: if two reversed
terms shared an exponent, multiplying by either used source monomial
would violate the just-checked selective isolation.

## 2. The new leading term and unconditional positivity

The largest reversed exponent is 5190-88=5102. It comes from the linear
E term of residual 5, `E*X+E-a*X`, and has weighted coefficient 1.
The two other terms of that row have smaller reversed exponents; all
other rows lie below them. Hence D has degree 5102 and positive leading
coefficient 1, despite having no constant term at the marked target 5190.

The coefficient magnitude bound remains |D_k|<M, with
M=2^2134927. The coefficient recipes were bounded using all four fixed
port bit lengths and the triangle inequality, without evaluating an
astronomically long decimal integer. For B=a b^2, a=8192M and b>=2,
B-1>M. Therefore

    D(B) > B^5102 - M*(B^5102-1)/(B-1) > 0.

This is unconditional in the nine supplied coordinates. In particular,
Jcode=2(1+g+ell)^2 D(B)+sum_j B^target_j is positive before any ratio,
radix, mask, or zero-set conclusion is used.

## 3. The larger word still satisfies the source size bounds

Write W=183, Q=5190, K=Q+2W=5556, and Z=B^(K+1).
Assume the ratio margin has supplied 0<g<4bB^W. Since the 31 distinct
positive input weights are at most W,

    1+ell <= (B^(W+1)-1)/(B-1) < bB^W,
    1+g+ell < 5bB^W.

The coefficient and degree bounds give

    0<Jcode/Z < (50 M b^2+1)/(B-1) < 1/128.

For the final strict inequality put x=M b^2 and B=8192x: it reduces to
128(50x+1)<8192x-1, equivalently 129<1792x, which holds already for x>=1.
The estimate uses the harmless upper bound deg D<=Q; its actual lower
degree 5102 only strengthens the inequality. Thus the shifted positive
word does not invalidate the fused construction's claimed Jcode bound.

## 4. Decoded coefficients and sparse target carries

After low-mask decoding, 0<=x_i<b and z_i=x_i+1 satisfy 1<=z_i<=b.
The convolution coefficients of C_z(t)D(t), where
C_z=(1+sum z_i t^w_i)^2, satisfy

    |[t^k] C_z D| < M*(1+31b)^2 < 1024 M b^2 = B/8.

The raw coefficients of Jcode=2 C_z(B)D(B)+Targets are consequently
strictly between -B/2 and B/2. At a marked cell they are exactly
4r_j(z)+1. In base-B normalization every incoming carry is -1 or 0:
this follows by induction from carry_0=0 and the coefficient bound.

When B is a power of two, the high mask B-2 permits exactly the base-B
digits 0 or 1 at each marked cell. An allowed target digit cannot have
outgoing carry -1, because that would require a raw coefficient plus
incoming carry at most 1-B, outside the stated bound. Therefore it is
4r_j(z)+1+c with c in {-1,0}, and its being 0 or 1 forces r_j(z)=0.
Conversely r_j(z)=0 gives 1+c in {0,1}, so the mask passes. This proves
that the sparse target mask continues to enforce precisely the original
positive source residuals after the global word shift.

The terminal carry eventually vanishes because Jcode>0; no negative
infinite base expansion is being treated as an ordinary integer word.

## 5. Completeness, nonzero encoding, and the even parameter

Given a positive source zero z, set x=z-1. The all-one vector is not a
source zero: residual 5 is identically 1 there, independent of the four
coefficient ports. Thus x is not identically zero and g>0.
Choose an arbitrarily large power of two b with b>max x_i. Then

    g <= (b-1)ell < bB^W,

which gives the strong completeness margin 32g<32bB^W. All input
weights are positive and B is even, so this genuine encoded g is even.
It is therefore represented by the builder's substitution g=2g' with
g'>=1, or by g=2(g0+1) with g0>=0. The substitution does not lose a
canonical source zero.

On arbitrary outer assignments, the builder enforces g even. Also N0
and L are even, so Scode=g+Jcode*N0 is even and

    R=L^2+(Scode+Tcode)L+L-1-Scode

is odd. Doubling the ratio h then makes K=R+1+h(P-1) even, independently
of any decoded mask. Those parity assertions are valid at the point in
the proof where the fused finalizer uses them.

## 6. Limits of this review

The source pin is the original positive package-31 quadratic system,
including its original transport coordinate. The review does not mix
package45's additional transport shift into these coefficient recipes.
The four-port native tuple remains unchanged as a whole. The selective
code changes exactly the two targets identified in Section 1 and has
been recertified from its source expressions.
This is a same-session independent mathematical and computational review,
not an end-to-end Lean or Rocq certificate. The exact checks and source
hashes are recorded in `fused_positive_source_audit.json`.
