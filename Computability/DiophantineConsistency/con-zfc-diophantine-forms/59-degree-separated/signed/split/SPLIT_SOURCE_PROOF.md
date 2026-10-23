# Degree-separated extraction with a certified positive leading layer

## Scope

This is a new local source-encoding theorem for the coherent original package-31
positive quadratic system. It establishes universal polynomial identities,
positive-word bounds, the precise coefficient bound needed by carry-free
extraction, and a one-position all-real positivity repair. It does not establish
the inherited compiler-to-refutation or Jones/Sun finalizer theorems. Those
semantic dependencies remain explicit in the enclosing construction.

The source file `parent_source.json` has SHA-256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
The 31 variables and four fixed ports are in its original order. Its port
convention is the complete original tuple, including the already-shifted MF.
No port from another tuple is substituted.

## 1. Two elementary row operations

Let r_1,...,r_22 be the original residuals. Replace only

    rho_14 = r_14 + r_2,
    rho_15 = r_15 + r_3,

and put rho_j=r_j otherwise. These are elementary integer row operations with
inverse r_14=rho_14-rho_2 and r_15=rho_15-rho_3. Consequently the common zero
set, including its strictly positive witness domain, is unchanged for every
value of the four ports. The unshifted source then has 89 coefficient records:
7 constants, 39 linear records, and 43 quadratic records. The support union
still has 1 constant, 22 linear monomials, and 39 quadratic monomials.

## 2. Do not homogenize with a dummy coordinate

For independent p_1,...,p_31 define

    U(Z) = sum_i p_i Z^(w_i).

Decompose each rho_j into its homogeneous degrees 0,1,2. If a monomial p^alpha
has degree d, let e(alpha)=sum alpha_i w_i and put

    c_(j,alpha) = 2 a_(j,alpha),                     d=0 or d=1,
    c_(j,alpha) = a_(j,alpha) product_i alpha_i!,   d=2.

Thus diagonal quadratic coefficients are doubled, and cross coefficients are
not. Define three reversed kernels

    D_d(Z) = sum_(j, |alpha|=d) c_(j,alpha) Z^(q_j-e(alpha)),
    G(Z,p) = D_2(Z) U(Z)^2 + D_1(Z) U(Z) + D_0(Z).

The finite conditions are degree-specific:

1. Every supported degree-d monomial has a unique label against ALL monomials
   of that SAME degree. There are 1, 31, and 496 candidate monomials.
2. A term of D_d from row j, multiplied by any degree-d monomial from U^d,
   can land at a target q_k only when k=j and the monomials agree.

No separation is required between labels of different degrees. Their kernels
are separate summands, not parts of a common convolution. This is the new
structural relaxation: a linear label may coincide with a quadratic label
without introducing a cross-degree product or contaminating an output.

The multinomial coefficient in U^2 is 1 on squares and 2 on cross products.
It cancels the above factorial weighting in both cases. For d=0 or1 the
multiplicity is 1 and the coefficient was explicitly doubled. Hence

    [Z^(q_j)] G(Z,p) = 2 rho_j(p)

as an identity in all 31 witnesses and all four ports. The supplied checker
parses the original residuals independently, verifies both inverse row
operations, and checks every one of the 22,544 source/expansion interactions.
It then compares all 22 extracted formal polynomials, not merely their
numerical values at samples. There are exactly 89 intended contributions.

`split_code.json` is the canonical finite certificate and `split_kernels.json`
is its exact derived sparse kernel data. The code has

    M=max w_i=116,  Q=max q_j=2129,
    deg D_0=1719, deg D_1=2027, deg D_2=1929,
    H=max_d(deg D_d+dM)=2161.

The largest term of D_2 is exactly +Z^1929, from the E*X monomial of row5.
Every kernel has distinct exponents internally. Coefficients from different
kernels may occupy the same exponent; that is harmless.

## 3. Fixed coefficient majorant

The inherited native ports obey the strict bit bounds

    beta < 2^1064921, K0 < 2^1070004,
    MC < 2^1064921, MF < 2^1064922.

For each weighted coefficient, replace every port power by the corresponding
power of two and every signed integer multiplier by its absolute value.
The maximum resulting integer has bit length 2134927. Thus every weighted
kernel coefficient has absolute value strictly less than

    C = 2^2134927.

This finite inequality is recomputed from every supplied coefficient, not
copied as an unchecked metadata field. The common selected source constant
beta_S=2^2134940 therefore satisfies beta_S>4096 C. For B=beta_S b^2 and b>=1,

    B > 4096 C b^2.

This conservative shared floor needs no change to the native coefficient binding.

## 4. Positivity before digit recovery

Let B be an integer with B>=4096C, put ell=sum_i B^(w_i), and let g>=0 be an
integer. Write U=ell+g. Because one weight is 116, U>=B^116.

For a polynomial with coefficients of absolute value below C and degree A,
its value at B has absolute value below 2C B^A. The leading coefficient +1
of D_2 gives the stronger bound

    D_2(B) > B^1929 (1-C/(B-1)) > (1/2) B^1929.

Moreover |D_1(B)|<2C B^2027 and |D_0(B)|<2C B^1719. Normalize by
B^1929 U^2. The two possibly negative contributions are bounded by

    |D_1 U|/(B^1929 U^2) < 2C/B^18 < 1/8,
    |D_0|/(B^1929 U^2)   < 2C/B^442 < 1/8.

Consequently

    G(B,U) > (1/4) B^1929 U^2 > 0.

This is an unconditional numerical statement for every g>=0, before the
source has recovered any binary or base-B digits. It uses the actual signed
leading coefficient and strict degree gaps, not a mistaken assumption that
all kernel coefficients are positive.

## 5. Sparse padding and the arbitrary-g range

Assume b>=4 and 0<=g<2bB^116. Distinct positive weights give ell<2B^116, and
therefore U<3bB^116. With H=2161, the degree bounds give

    |G(B,U)| < 2C(1+3b+9b^2) B^H <= 26C b^2 B^H,
    2G(B,U) < B^(H+1)/64.

Put Targ=sum_j B^(q_j), N0=B^117, and N1=B^2162. Since Q=2129 and B>=4,

    Targ < 2B^2129 < N1/64,
    (B-2)Targ < 2B^2130 < N1/64.

The sparse high word Jcode=2G(B,U)+Targ is strictly positive and less than
N1/32. In particular

    Jcode+(B-2)Targ+2 < N1.

Thus the usual disjoint low/high blocks obey S+T<N=N0*N1: the low parts of
S and T are each below N0, and the displayed strict high-word inequality
absorbs their possible carry. This argument does not require B to have
already been proved a power of two.

A dense comparison word 2G+B sum_(h=0)^H B^h also lies strictly between zero
and 2B^(H+1), so the older N1=4B^(H+1) interface remains valid if desired.
The sparse choice is strictly preferable for the calibrated finalizers.

## 6. Coefficients after digit recovery

If g=sum n_i B^(w_i), with 0<=n_i<b, set p_i=n_i+1. Then U=ell+g is exactly
the positive-coordinate word. Since sum p_i<=31b, every coefficient of G
has absolute value bounded by

    C[(sum p_i)^2+sum p_i+1] <= 993 C b^2 < B/4.

This bound controls all coefficients, including unsupported collisions. It
sums the three homogeneous layers separately and does not assume unsupported
pair labels are isolated. Every marked coefficient is exactly 2rho_j(p).
Thus the established sparse-borrow padding lemma applies with padding bit1
at each q_j; it forces the marked residuals to vanish exactly as in the
previous source interface. The elementary row inverse then recovers r_j=0.

Conversely, every positive source solution gives digits n_i=p_i-1 for all
sufficiently large b. The all-one tuple is not a common zero, because original
row5 is 1 there. Since row5 is unchanged, at least one n_i is positive and
all weights are positive; hence g>=B>b. The source's required lower witness
bound is therefore preserved. The finite width and coefficient bounds hold
for every sufficiently large admissible base exactly as in the old source.

## 7. Optional positivity for every real packed input

Some signed adapters need positivity for ALL integer g, before proving g>=0.
For that interface use just one extra off-target monomial:

    G_plus(B,U) = G(B,U) + B^2162.

This does not change any target coefficient because 2162>Q. It has exact
height2162. Complete the square in U, using D_2>(1/2)B^1929:

    G_plus >= B^2162 - |D_0| - D_1^2/(4D_2)
            > B^2162 - 2C B^1719 - 2C^2 B^2125 > 0.

For the last inequality divide by B^2162. Both 2C/B^443 and 2C^2/B^37 are
less than 1/4 under B>=4096C. This proves positivity for every real U,
therefore for every integer g, without a sign assumption. Digit extraction
and row identities are unchanged, and the added off-target coefficient1
satisfies the same coefficient majorant. A sparse adapter may take N1=B^2163;
all arbitrary-g upper bounds hold on the required bounded interval.

## Interpretation

This construction does not eliminate quantified variables from the source.
Its gain is a different multiplication architecture: only same-degree
monomials can interfere. Against the frozen wave7 code, the convolution
height falls from5556 to2161 (61.10% smaller), and the combined source
exponent H+M+2 falls from5741 to2279 (60.30% smaller). These are source-coding
metrics, not final equation degrees. The final degree and operation count
must be audited from each composed arithmetic DAG. No global optimality is
claimed, and the search program is not a proof dependency.
