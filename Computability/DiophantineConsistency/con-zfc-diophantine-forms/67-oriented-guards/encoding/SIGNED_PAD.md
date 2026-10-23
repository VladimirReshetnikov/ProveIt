# An off-target pad for arbitrary signed packed coordinates

This is an optional variant of PROOF.md, needed only when the outer equation
allows arbitrary signed g before its final-zero conditions are known.
Keep b>=1, B=8192Cb^2, U=ell+g and all other source definitions, but replace
G by Gplus=G+B^1946. This adds one literal constant record to D0; it does
not change the 89-record extraction core. The polynomial degree of D0 becomes
1946, but H=max(1946,1842+108,1738+216)=1954 remains unchanged. The added
exponent is strictly above every target (Q=1939), so no extracted residual
changes. It is also strictly below the existing top degree1954.

## Unconditional positivity for every integer g

The geometric lower-tail estimate used in PROOF.md gives

    0<D1(B)<3B^1842,     D2(B)>(beta-1)B^1738.

Since beta=2^1064921-1>10,

    D1(B)^2/(2D2(B))
      < 9 B^1946/[2(beta-1)] < B^1946/2.

For every real U, completing the square yields

    D2 U^2+D1 U >= (D2/2)U^2-D1^2/(2D2).

Using D0>0, it follows strictly that

    Gplus > (D2/2)U^2+B^1946/2.

For every integer U, and consequently every integer g=U-ell,

    Splus = g+N0(2Gplus+Targets)
          > N0 D2 U^2+U+N0 B^1946-ell > 0.

For the last inequality, N0D2 is a positive integer, so
N0D2 U^2+U>=0 for every integer U (including U=-1). Moreover,
ell<2B^108<N0B^1946. This does not assume the ratio-derived range or g>=0.
The mask T remains nonnegative for b>=1.

## Bounds and decoder after the finalizer establishes its range

On the branch 0<=g<4bB^108, the previous bound sharpens to

    2Gplus/Z < 86Cb^2/(B-1)+2/B^9
             < 87Cb^2/(B-1) < 1/64.

Here 2(B-1)<Cb^2B^9 and B=8192Cb^2 prove the last two inequalities.
Thus Splus+T<B^2064 as before.
The new D0 coefficient is1 and its exponent did not occur in D0, so every
kernel coefficient still has absolute value<C. The convolution bound
|h_t|<993Cb^2<B/8 therefore remains valid, as does the entire borrow decoder.
The added coefficient is off-target and cannot create or remove an extracted
source zero. All population thresholds depend only on T and block lengths,
so the calibrations in PROOF.md remain unchanged.

## Threshold caution

For the leading-bit word X in PROOF.md, the exact population threshold is
2195v-31k-21. For the top-bit-free word R in PROOF.md it is
2195v-30k-22. A signed wrapper must substitute its own b-versus-epsilon
relation into the threshold it actually uses. No signed square-root threshold
is asserted by this source-only addendum.

For the specific odd-exponent parametrization b=2 epsilon^2, the corrected
polynomial square threshold is

    Nhat=eta epsilon^3 B^1089,
    eta=2^(17kappa/2-9)=2^18146981.

Indeed Nhat^2=2^(17kappa-18)epsilon^6 B^2178,
while epsilon^6=b^3/8 and B=2^kappa b^2; hence exactly

    Nhat^2=2^(2195kappa-21)b^4359=Y.

The cubic, rather than linear, epsilon factor is necessary. This identity
holds for all nonzero integer epsilon, not only when b is binary; using
Nhat itself as a positive numerical parameter requires epsilon>0 or an
explicit sign normalization in the consuming theorem.
