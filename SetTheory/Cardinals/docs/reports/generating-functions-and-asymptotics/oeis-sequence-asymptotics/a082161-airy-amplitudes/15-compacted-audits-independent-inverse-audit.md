# Independent audit of the compacted inverse supplement

Audited: `inverse-supplement.md`, 2 October 2026.

**Verdict: approved as an asymptotic inversion and discrete-threshold consequence of the forward expansion.** No new spectral assumption or differentiated unknown sequence remainder is used. The numerical amplitude and all model tests are appropriately described as uncertified.

## Forward logarithm

Stirling contributes `+(1/2)log n +(1/2)log(2pi)+1/(12n)` to the factorial. Combining this with the compacted prefactor gives exactly `p=5/4`, `C=log(gamma_c*sqrt(2pi))`, and

    E = 393/1120 + 1/12 - 1304 z^3/42525
      = 1459/3360 - 1304 z^3/42525.

The smooth model has the stated derivative and curvature estimates on a large positive interval.

## Explicit expansion

The Lambert anchor solves `x log(4x/e)=T` on the principal real branch for sufficiently large T. Writing `s=log(4x)` and `q=p log x+C`, I independently substituted the proposed u,v,w,r,k into all five successive residual coefficients. Each simplified exactly to zero. In particular the terms involving AB, q^2, and A^3 in k have the displayed signs and denominators.

The undisplayed residual is O(x^(-4/3)). Indeed q=O(s), u=O(1/s), v=O(1), and w,r,k=O(1/s), and the Taylor series are uniform because the displacement divided by x is O(x^(-2/3)/s). Division by h'~s gives the model inverse error O(x^(-4/3)/s).

The coarser expression follows from

    -q/s = -p +(p log4-C)/s.

Its Airy displacement is positive, since z<0. It correctly locates the first amplitude dependence at order 1/log x.

## Newton iteration

On the relevant interval, a Newton step multiplies the squared error by O(1/(x s)). Starting with error O(x^(1/3)/s), the first and second errors are respectively

    O(x^(-1/3)s^-3),
    O(x^(-5/3)s^-7).

Inductively the j-th error is `O(x^(1-2^(j+1)/3)s^(1-2^(j+1)))`, as stated. The initial displacement is o(x), so all fixed finitely many steps remain in the interval where these derivative bounds apply. Two steps are already smaller than the displayed forward/model uncertainty.

## Discrete threshold

The all-orders forward expansion gives eventual strict monotonicity with the stated leading log ratio. Finite earlier values cause no obstruction for sufficiently large Y.

Assume the explicit log-error bound K. At the integer immediately below `ceil(r_*-eta)`, the smooth model lies below T by at least `(1/2)log(4r_*)*eta`; at `ceil(r_*+eta)` it lies above T by at least the same amount. With

    eta=8 max(K,1) r_*^(-4/3)/log(4r_*),

this margin is at least `4 max(K,1) r_*^(-4/3)`, larger than the local sequence-error bound `2K r_*^(-4/3)`. Thus both bracket directions are correct, including strict lower-side exclusion. When 2eta<1 the two ceilings differ by at most one. Away from integer boundaries they coincide. A model-inversion error must indeed be added to eta if r_* is replaced by a finite formula or numerical Newton iterate.

The supplement correctly distinguishes an eventual bound with unspecified constants from a certified finite-Y algorithm. Its final observation about a fixed amplitude error is also correct: it gives an inverse shift of order 1/log n, which tends to zero but is much larger than the claimed algebraic inverse remainder.

## Coarse prior-theorem consequence

The published Theta estimate already supplies an O(1) error in the logarithm after the leading factorial, Airy, and power terms. Dividing by the leading derivative gives an O(1/log x) inverse localization around the displayed Airy and -5/4 terms. Consequently the coarse two-ceiling localization can validly be attributed to that existing theorem; identifying the constant amplitude and algebraically refined radii requires the new forward result.
