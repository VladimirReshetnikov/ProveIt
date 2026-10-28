# Closing audit: newly placed matching-refinement packet

Reviewed at ProveIt commit
`474ddba696a5d385c091c23fb2995f69edd13e00`.

The new packet was added by `d098ba43` and placed under
`Computability/SubexponentialSAT/Research/eth_matching_refinement`
by `6d3adc45`, according to the parent's closing repository inspection.
This audit directly reads the placed `README.txt`, `report.tex`, and
`code/refinement.py`.

## Conclusion

**The new packet does not change the strongest combined theoretical or
implemented baseline used for this delivery.** Its generic normalized
polynomial-space coefficient is

    94.74820225953415...

on the scale `s/sqrt(log2 s)`, the same as the previously reviewed
balanced-packing and high-moment packets. It gives a distinct exact matching
potential construction with an adaptive integer schedule; it supplies none
of the stronger local-mode or asymmetric scheduling ingredients that control
our final comparison.

The corpus count should increase from fourteen to fifteen research packets.
The seven earlier incoming archives plus this eighth arrival have been placed
under Research; `docs/incoming` now has no unplaced SAT packet at this pin.

## Inspected result and parameters

The main theorem uses the original arbitrary bipartite multigraph interface:
root `M<=Cs`, maximum degree `ceil(s^.9)`, original tensor-entry allowance,
and fixed source algebraic dependencies. For the displayed numerical
coefficient it normalizes `C=1`.

The packing lemma is at `report.tex` lines147-224. It partitions edges into
matchings, permitting parallel edges, and minimizes an exact rational sum of
conditional expectations. With `N=r^a`, `D=N²`, `L=2^a`, `c=2 Delta`, and
`tau=ceil(log2(8cD))`, it proves

    max X_gamma < (1+1/lambda) M/D + 2c lambda tau,
    padded_mass/M < 1+1/lambda + D(2c lambda tau+L)/M.

The exact guard `M>=lambda D(2c lambda tau+L)` yields padded mass less
than `(1+2/lambda)M`. The potential proof and common-denominator bit bound
are coherent at the inspected level. The shared side-degree bound remains
Delta on both sides; this does not provide the stronger descendant
asymmetry exploited in the current delivery.

The schedule, at lines235-307, fixes `r=54` at every depth. Define

    k=ceil(log2 lambda), g=6k,
    dmax=min{d:18^d>=C0 lambda},
    A=max{a:54^(20a)<=2^lambda},
    U=A-(dmax+1)g-k²,
    u_d=floor(8U/9^(d+1)),
    a_d=sum_(j<=d)u_j+(d+1)g.

This safely approaches the symmetric total capacity
`lambda/(20 log2 54)` and gives the same asymptotic retained ranges as the
balanced/high-moment reports. Its thin logarithmic guard and adaptive slack
are valid existing ingredients already included in our prior baseline.

At lines379-410 the report uses factorial modes
`w_b=1+3b-2 popcount(b)`, of uniform slope3, and charges all families
`2 eta M/D_i`. It does not exploit the exact unequal-symbol fraction
`1-1/r`. Lines412-449 give the same optimized symmetric coefficient

    C54=(9 pi/(4 ln2))*sqrt(15 log2 54)
       =94.74820225953415... .

No smaller unrestricted SAT logarithmic order is asserted. The separate
Claude manuscript's unspecified constants are correctly excluded from
numerical dominance claims. The packet's published comparison snapshot
predates the other newly placed research packets, which explains why its
own comparison does not include their improvements.

## Compositions with stronger prior ingredients

Applying the same full-Cauchy slope4 lemma gives

    94.74820225953415*sqrt(3/4)=82.0543501196627... .

Also retaining exact unequal-symbol counting gives

    94.74820225953415*sqrt(3/4)*sqrt(53/54)
      =81.29103724896603... .

Both are weaker than the prior asymmetric schedule compositions and the new
63.8522033905 polynomial-space result. Applying the existing group-cache and
three-block Strassen construction gives the same r54 cached comparison as
balanced/high-moment scheduling:

    time55.99058602076087..., space48.62480007091123... .

These do not affect the conservative fixed-r8 comparison38.1677456970 or
the new7/9 cached result37.9301090829 time /33.6230409217 space.

## Code and novelty overlap

`code/refinement.py` contains small exact component routines only:

* `color_matchings` greedily partitions the graph's edges into matchings.
* `potential` recomputes a complete product over matching edges for every
  ordered label pair and matching.
* `label_graph` calls that complete potential separately for every candidate
  label, checks the averaging identity, and uses deterministic index ties.
* `exact_budget` uses exact rational logarithm intervals to compute the
  integer capacity, and `schedule` has a partial `basic_guard` explicitly
  distinguished from complete finite contraction guards.
* `precision` implements the inherited exact Hermite loss.
* `weighted_count` counts an abstract unbounded slope3 mode inventory.

There is no asymmetric side-degree schedule, heterogeneous alphabet,
full-Cauchy4 basis, group cache/Strassen contraction, multilinear peeling,
or cached row-sum potential update. In particular it does not duplicate the
new `O(NQ²)` candidate-score update or supply a faster reference than the
already benchmarked asymmetric packing implementation. Different matching
and two-stage potentials need not choose the same labels, so the practical
identity benchmark should remain against the actual asymmetric reference
algorithm it optimizes, rather than assert equality across constructions.

The packet's claims remain mathematical component results with finite exact
checks, not SAT runtime measurements or a new Lean certificate. I did not
execute its full archived suite, since the closing question was whether it
changes the frontier or novelty scope. No counterexample to its inspected
local proof was found. No modification to the new theoretical certificates
or practical code is required; only corpus inventory, source pins, and
comparison references need updating.
