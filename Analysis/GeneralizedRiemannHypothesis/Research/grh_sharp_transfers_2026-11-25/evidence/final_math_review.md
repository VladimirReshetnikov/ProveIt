# Final mathematical review of the manuscript fragments

Reviewed `sections/torsion.tex`, `sections/applications.tex`, and
`sections/targets.tex` in `output/grh_sharp_transfers_2026-11-25`, consulting
the Mellin calculation in `sections/artin.tex` where needed.

## Concrete issue

In `applications.tex`, after

    g_N(T)=((1+T)^(p^N)-1)/T,

the prose says that this polynomial vanishes on every nontrivial p-power
root of the indicated order. Its zeros are the **shifted** points zeta-1,
not zeta. Replace that wording with:

> vanishes at every zeta-1 with zeta a nontrivial p-power root of unity
> of order at most p^N.

This is a variable-description correction, not a defect in the displayed
formula, the budget, or the sharpness argument.

## Mathematical conclusions

No substantive proof flaw was found in the requested sections.

- The bounded-series Delta argument correctly retains the possibly
  nonattained coefficient infimum as a real lower bound. Truncation keeps
  the Gauss value and makes the tail strictly larger at the whole grid.
- The Lubin--Tate radius induction is correct for general integral
  defining series. The formal difference unit factor supplies exactly the
  ordinary metric needed by the root proof. The w(pi)=1 normalization is
  consistent with the q-based endpoint.
- The several-powers witness exists: the monic polynomial
  (1+Y)^j-(1+x) has integral roots, whose valuations sum to v(x) when
  x!=0. Hence one root has valuation at least v(x)/j; x=0 is handled
  separately. Coordinatewise choices give the asserted rho/m witness.
  Composition preserves integrality and boundedness. The mB packet
  budget therefore follows.
- The Mellin pole cancellation at 1 is exact. At a zero alpha the residue
  is +ord_alpha(L)/(alpha(1-alpha)), with the required sign on (0,1).
  Subtracting T from the upper majorant changes this residue to a negative
  one for the nonnegative Mellin integral, giving the stated contradiction
  at its real abscissa. The finite-integral correction is entire, and the
  case of abscissa minus infinity causes no exception.
- The A5 implication uses the already established meromorphic-product
  identity and positive multiplicity comparison correctly. Its conclusion
  remains conditional on the explicitly unproved arithmetic estimate.

This review is mathematical and source-based; it is not Lean compilation
or kernel verification.

## Resolution in the delivered manuscript

The shifted-root wording was corrected before final compilation. The final PDF was also visually checked; no material clipping or overflow was found.
