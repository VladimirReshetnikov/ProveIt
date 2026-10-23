# Support-aware quadratic extraction and overlapping target bands

## What is new, and the exact baseline

The reviewed repository is ProveIt at commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
Wave-6 packages 40 and 45 encode the same 22 quadratic equations in 31
positive variables with a full 32-element Sidon set of maximum 799.
Their reported points are 10 integer variables / degree 237,520,456 /
782 operations (package 40), and 9 positive variables / degree 129,875,980 /
788 operations (package 45). Their final arithmetic theorems and native
compiler calibration remain inherited dependencies.

This package uses three changes confined to the source adapter:

1. Isolate only monomials that actually occur in a source residual.
2. Allow source row bands to overlap, and certify that no overlap touches
   any selected output coefficient.
3. Share fixed powers through an explicit binary multiplication schedule.

The first two changes reduce the degree. The last reduces the cost of
evaluating the resulting fixed polynomial. No lower bound or globally
optimal layout is claimed.

## The finite parent and support certificate

Let r_0,...,r_21 be the integer quadratic residuals obtained from the
literal `data/parent_system.json` by replacing each original positive
variable X_i by x_i+1. The original coordinate order is preserved:

J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta.

Adjoin x_0=1. Homogenize each degree-at-most-two monomial to degree two by
powers of x_0. Among the 528 unordered pairs from 32 positions, exactly 71
occur in at least one homogenized source monomial. The following 32 weights
are indexed by (0,J,F,...,Delta), not by increasing numerical order:

```
0,174,166,110,137,115,65,168,126,105,49,155,54,60,15,4,
118,146,26,44,7,17,57,38,158,177,179,116,46,94,35,96
```

For each of the 71 supported pairs (a,b), its sum w_a+w_b differs from
the sum for every other one of the 528 pairs. Unsupported pairs may have
the same sum. In fact the 528 pairs occupy only 266 distinct sums. All 31
nonpadding weights are positive and distinct; W=max w_i=179.

This is a finite, exact certificate. The heuristic used to discover the
weights plays no role in the proof.

## General extraction theorem

Write x^alpha for a degree-at-most-two monomial in the 31 variable
coordinates and s(alpha)=sum alpha_i w_i. For row j put

    q_(j,alpha) = (2-|alpha|)! (product alpha_i!) p_(j,alpha),

where p_(j,alpha) is its coefficient in r_j. Choose row signs sigma_j in
{+1,-1}, row offsets H_j >= 2W, and define the ordinary polynomials

    C(t) = (1+sum x_i t^w_i)^2,
    D(t) = sum_j sum_alpha sigma_j q_(j,alpha) t^(H_j-s(alpha)).

Assume the following *output isolation* certificate:

    H_i-H_j = s(beta)-s(alpha), alpha in supp(r_j), |beta|<=2

holds only when i=j and beta=alpha. Then

    coefficient of t^H_j in C(t)D(t) = 2 sigma_j r_j(x).

Proof: expand the product. A term can reach H_i only under the displayed
equality. Output isolation removes all other rows and monomials. The
multinomial coefficient of x^alpha in C is
2!/((2-|alpha|)! product alpha_i!), which cancels the factor in q.

Output isolation also implies distinct exponents for all terms of D with
different (row,monomial) indices: an exponent collision would be detected
at either row's output by its own monomial from C. Therefore every D
coefficient is one signed q coefficient, with no extra factor of 22.

Notice the exact weakening relative to a full Sidon hypothesis: only a
supported alpha must be distinguished from arbitrary beta. No separation
between two unsupported monomials is ever used.

## Two certified layouts

The uniform layout uses the package-40 row order
(original rows 1,2,3,4,6,...,22,5), signs +1, and

    H_j = 358+359j, 0<=j<22.

Every nonzero row difference exceeds 2W, and within-row isolation is the
71-pair certificate. Here H_max=7897.

The overlap layout uses the exact row ordering and signs recorded in
`data/overlap_layout.json`, with offsets

```
358,608,939,1147,1432,1739,1989,2170,2512,2699,2972,
3305,3492,3683,3914,4108,4399,4697,4926,5224,5469,5775.
```

All successive gaps exceed W, so differences between nonadjacent offsets
exceed 2W automatically. Adjacent differences are checked against every
supported monomial and all 528 input pairs. The final row is the negative
of original residual 9, whose constant becomes +8. Thus the highest
coefficient of D is the positive constant 16. In the uniform layout the
last row is original row 5, with constant +1 and highest coefficient 2.

## Digit bounds survive nonsupported collisions

Fix the four complete native coefficient ports as in data/ports. Let
M bound the absolute values of every q coefficient. Their exact integer
values and the explicit power-of-two bound are checked independently.
If 0<=x_i<b then all coefficients of C are nonnegative and their sum is

    (1+sum x_i)^2 <= (32b)^2.

Even when unsupported pair sums collide, this identity for the sum of
coefficients is unchanged. Since every D coefficient has magnitude <=M,
each coefficient of C D has magnitude <=M(32b)^2.

Both source adapters choose B large enough that

    B > 4 M (33b)^2.

Put K=H_max+2W and

    A(t)=C(t)D(t)+(B/2) sum_(v=0)^K t^v.

Every coefficient of A is strictly between 0 and B, and each selected
coefficient lies strictly between B/4 and 3B/4. If B is a power of two,
binary carry-freeness with mask

    (B/2-1) sum_j B^H_j

forces each selected digit of A(B) to be a multiple of B/2. The strict
interval leaves only B/2, so the carry test is equivalent to simultaneous
vanishing of all signed residuals, and hence of all original residuals.
Off-target coefficients are not constrained beyond their digit bounds.

The witness encoding g=sum x_i B^w_i still recovers all 31 coordinates,
because individual weights remain distinct. The maximum W still supplies
the same witness-size bound. Positivity of D(B) follows from its positive
highest coefficient and B>M+1: the total magnitude of all lower terms is
strictly smaller than one unit in the leading place.

## The unchanged source interface

Let ell=sum_i B^w_i, N0=B^(W+1), N1=4B^(K+1), N=N0*N1. Then define

    mask=N0-1-(b-1)ell,
    target=(B-2)sum_j B^H_j,
    T=mask+target*N0,
    J=2(1+g)^2 D(B)+B sum_(v=0)^K B^v,
    S=g+J*N0,
    R=(S+T+1)N+T+1,
    X=(N-1)R, Y=N^2.

These are exactly the package-40/45 source formulas with the certified
weights, offsets, and D substituted. Their size arguments use K and W,
not the full Sidon property or equal offset spacing. The nine-variable
adapter uses b=2^2140030+epsilon and B=b^3; the ten-integer adapter uses
b=1+3f and B=2^2140030 b^2. The latter's finalizer supplies the required
domain conditions before the binary source argument is used. The source
cap is 32bB^W in the nine-variable finalizer and bB^W in the ten-integer one.

Hence every proven endpoint equivalence of the imported finalizers is
preserved. Together with the inherited native compiler and literal K215
calibration, existence of a solution remains equivalent to a syntactic
ZFC refutation. Negating this equivalence yields the requested consistency
equivalence. No coefficient is selected according to the truth of Con(ZFC).

## Evidence and proof boundary

The code checks exact finite source identities, all coefficient bytes,
all live arithmetic gates, and exact degrees using a nonzero leading
coefficient after diagonal specialization modulo a stated prime.
The nine-variable evaluator has a known leading cancellation; the shipped
equal-polynomial certificate circuit exposes it through a telescoping
identity. This is an exact algebraic certificate, not a random degree guess.

The complete native/Pell/compiler correctness and the number-theoretic
finalizer theorems are mathematical dependencies of this construction.
This package does not contain a new end-to-end proof-assistant certificate
or an exported object-language ZFC proof, and does not prove Con(ZFC).

## Reproducible endpoint metrics before further finalizer improvements

With W=179 and H=H_max, the imported nine-variable finalizer has exact
degree 3456H+10380W+7192. The imported ten-integer finalizer has exact
degree 6320H+19016W+12992. These formulae are supported by the literal
certificate circuits and nonzero diagonal leading coefficients.

| Layout | Domain | Exact degree | Binary arithmetic gates |
| --- | --- | ---: | ---: |
| Uniform | 9 positive | 29,157,244 | 562 |
| Uniform | 9 nonnegative | 29,157,244 | 565 |
| Uniform | 10 integers | 53,325,896 | 595 |
| Overlap | 9 positive | 21,823,612 | 618 |
| Overlap | 9 nonnegative | 21,823,612 | 621 |
| Overlap | 10 integers | 39,914,856 | 651 |

The source changes are independent of any later improvement to the final
radical-separation arithmetic. Such refinements should have their own proof
and degree certificate, and can share this source unchanged.
