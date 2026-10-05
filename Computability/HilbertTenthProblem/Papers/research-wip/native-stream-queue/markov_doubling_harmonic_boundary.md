# Doubling cannot carry two nonzero sine-coordinate eigenmodes

A normalized doubling Markov mask cannot act as a nonzero scalar identity
on the span of two distinct sine harmonics, even when the frequencies are
chosen sparsely. The mask need not be even or a trigonometric polynomial.
This closes a frequency-selection escape from the earlier consecutive-basis
argument for the two-dimensional identity/decrement lift. It is a restriction
on that representation, not a lower bound on universal Diophantine arithmetic.

## Exact one-harmonic classification

Let a be a continuous real function of period one and define

    (T_a f)(y) = [a(y/2) f(y/2)
                    + a((y+1)/2) f((y+1)/2)] / 2.

Assume normalization T_a 1=1. Equivalently,

    a(x)+a(x+1/2)=2                                      (1)

for every real x. For a positive integer m, put s_m(x)=sin(2πmx).
Then, for any real λ,

    T_a s_m = λ s_m

holds if and only if m is odd and

    a(x)=1+2λ cos(2πmx).                                (2)

For even m=2n, normalization gives T_a s_m=s_n, which cannot equal
λs_m, including at λ=0. For odd m, the half-period shift changes the
sign of s_m. Substituting y=2x and using (1) gives the exact functional
identity

    (T_a s_m)(2x)=(a(x)−1) sin(2πmx).                   (3)

The claimed eigenvalue equation and the double-angle identity imply

    [a(x)−1−2λ cos(2πmx)] sin(2πmx)=0.

Away from the discrete zeros of the sine, the bracket is zero. Continuity
extends the conclusion across those zeros, proving (2). Conversely, (2)
with odd m satisfies normalization and makes (3) equal λs_m(2x).
No division at a sine zero, Fourier truncation, spectral theorem or
unverified computational claim is used.

The classified mask is strictly positive exactly when |λ|<1/2. It is
nonnegative exactly when |λ|≤1/2; at equality it has zeros. At λ=0 it
is the constant mask one, which annihilates every odd sine harmonic.
This zero-eigenvalue exception matters in the following corollary.

## Consequence for arbitrary sparse sine-coordinate blocks

Suppose S is a finite set of at least two distinct positive frequencies
and V=span{s_m:m∈S}. If T_a restricted to V were λI with λ≠0, each
s_m would be an eigenfunction. The theorem excludes even frequencies.
For two distinct odd m,n, it would require simultaneously

    a(x)=1+2λ cos(2πmx)=1+2λ cos(2πnx).

Distinct cosine harmonics are distinct functions, giving a contradiction.
The same reasoning excludes two individual sine harmonics with any
nonzero real eigenvalues, even if those eigenvalues differ: equality of
their nonzero cosine multiples fails, for example by Fourier orthogonality.

Consequently dilation two cannot encode a family containing I/q on any
such sine-coordinate space, for any finite nonzero q. Reordering, rescaling
or changing basis within that same span does not help, since a scalar
identity is independent of the chosen basis of V.

For the two-action identity/decrement matrices, the existing strictly
positive **dilation-three, q=5** sine lift therefore has minimum integer
dilation among all encodings using the span of two distinct individual
sine harmonics. The earlier proof required the standard frequencies 1,2;
this one allows arbitrary frequency selection and arbitrary continuous
normalized masks. The established q=5 minimum itself still has its earlier,
narrower finite-even standard-basis scope; this corollary does not extend
that denominator optimality statement.

## What this leaves open

An arbitrary two-dimensional subspace whose basis vectors mix more than
two Fourier frequencies need not be the span of two individual harmonics.
The theorem does not exclude that encoding, arbitrary nonsinusoidal
functions, state-dependent coordinate changes, different matrix families,
or unnormalized operators. It does not assert a general eigenspace
multiplicity bound. Nor does it prove b≥r+1 for arbitrary sparse r-frequency
sets when r>2; only the exclusion of b=2 follows here.

The older consecutive-frequency theorem and the complete positive counter
certificates remain unchanged. In particular the local 8/22 operation
counts, the fixed-duration 9T+1/15T+2 counts, and the best fully accounted
84-operation universal construction receive no new saving from this
negative representation result.

## Fresh evidence

The companion newly authored standard-library check uses exact rational
Fourier arithmetic for explicitly constructed masks, and solves the finite
linear eigenfunction constraints for degrees D=0,…,9 and frequencies
m=1,…,11. These 110 finite systems corroborate the classification; the
functional argument above proves the unrestricted continuous statement.
The finite systems allow all normalized odd cosine coefficients, including
negative ones, rather than assuming the conclusion in their unknowns.

The earlier lift and counter notes are read and hashed as inert evidence.
No archived, supplied, predecessor or frozen helper/source array is
executed, imported or replayed. Only this new checker runs before freeze.
Its metadata and finite tests are separate from a universality theorem or
arithmetic lower bound.
