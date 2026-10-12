# Source-question updates and safeguards

## Directly answered here

**Repeated rational poles / rank-one harmonic data.** Theorem 6.3 gives a complete
finite residue criterion in the rational-weight model with poles on finitely many
translated integer lattices. The only nonzero possibilities are a common geometric
Hankel direction or the final-coordinate corner direction. Theorem 6.5 proves that
at nonzero critical decay x^(-(2r-1)), rank one is equivalent to a normalized
(2r-2)nd finite difference of a proper rational seed. This includes repeated poles
and multiple residue classes.

**Harmonic rank and cutoff depth.** Proposition 7.1 bounds harmonic determinant
degree by generic pencil rank rho. Theorem 7.2 gives a constructive cyclotomic
generator-depth bound rho+1, including normalized Euler primitives. It does not
prove equality or minimal arithmetic depth.

## Keep prior incoming results separate

The incoming `ProveIt_Polygamma_Reconstruction_and_Resonance_2026-10-11.zip`
records a next-two-particle-resonance result and all higher spatial Mellin
coefficients. These were not re-proved or claimed as new here. The older question
list should be cross-linked to that package after its own integration review.
The incoming `ProveIt_Harmonic_Tails_Shifts_and_Twists_2026-10-11.zip` records the
gap-four rank family; this delivery does not claim that family as its contribution.

## Corrections versus safeguards

No newly false theorem was found in the targeted source material inspected here.
The following prevent false extrapolations of the present results, rather than
alleging errors in unread source files.

1. Exact critical decay needs a nonzero leading coefficient. The weight
   2/((x+1)^2(x+2)(x+3)) has a rank-one geometric pencil, but is not a second
   difference of a proper rational seed.
2. The new spectral escape amplitude is A_r(s,a)=(s)_(2r-2)V_r(s,a)/(2r-2)!,
   not V_r(s,a) away from s=1.
3. The all-jet coefficient formula includes b_(k+1)/(k+1), from multiplication
   by the Hurwitz pole. Omitting it corrupts every row.
4. Spectral finite part minus hard-cutoff constant is partial_s A_r(1,a).
   At r=2,a=1 the difference is 3/8+log(2)/4, not zero.
5. At s=0 all pointwise weights vanish, but the continued two-particle value
   is -1/4. Isolated pointwise specialization is not normal continuation.
6. Neither formal rank nor an explicit Li(2,2) term proves minimal arithmetic
   depth. Rational-weight polylog closure is not asserted for arbitrary
   noninteger spectral orders.

The Gaussian S6 and revised S8 statuses remain unchanged. General higher Gauss
resonances and the listed arithmetic-depth questions remain open in this report.
