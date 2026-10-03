# Independent audit of the binary mass-four expanding shuttle

3 October 2026. This audits `BINARY-EXPANDING-SHUTTLE.md`, `test_binary_expanding_shuttle.py`, and the emitted radius-six conservation certificate. The verdict is **pass** for conservation, locality, the complete orbit formula, exact anchored-pattern hit times, and the stated natural/rational witness conclusions. The rule is not reversible.

## 1. Global conservation and locality

Components join consecutive occupied sites at distance at most two. Exact recognition of one of the four rewritten finite components requires its specified occupancy together with two vacant sites beyond each endpoint. This excludes both a nearby extra particle and an extension of the component through a chain.

Each rewrite preserves component cardinality. Its output hull is within the input hull enlarged by one at each end. If neighboring input components have right and left endpoints r and l, then l−r≥3. Their possible output hulls therefore end at r+1 and begin at l−1≥r+2, respectively. They remain disjoint even in the densest allowed inter-component arrangement. Arbitrarily large unrecognized components are fixed, and the same separation argument applies to them. This proves conservation for every finite input.

For the four rule shapes, inspect every site whose output is changed and its exact-recognition window:

- {0,1}→{1,2}: recognition window [−2,3]
- {0,2}→{−1,1}: recognition window [−2,4]
- {0,1,3}→{−1,1,4}: recognition window [−2,5]
- {0,2,4}→{0,3,4}: recognition window [−2,6]

In each case every necessary input coordinate lies within six of any changed output site. Every other output site retains its old bit. Therefore the component description gives a genuine translation-equivariant binary radius-at-most-six CA, with quiescent vacuum and stationary isolated units.

I independently reconstructed the output bit at the origin by testing the four guarded finite patterns directly, without using the producer's component-splitting function. All 8,192 reconstructed bits match the exported local table. I also independently rechecked every conservation identity

f(w)−w_6=P(w>>1)−P(w & 4095)

against the 4,096 exported potentials. This exact finite certificate telescopes for every finite-support input. Its SHA-256 is

6c99365818697ddd83bdbf529e17756fffaf2eacd55763b235919523b0041699.

## 2. Complete cycle and hit exclusivity

Start a cycle at C_D={0,3,4,D}, D≥7. Its length is ell_D=2D−10. For 0≤s<ell_D the entire configuration is exactly

- {0,3+s,4+s,D}, when 0≤s≤D−6
- {0,2D−9−s,2D−7−s,D+1}, when D−5≤s≤2D−11

The right endpoint case s=D−6 is the connected right-contact component {D−3,D−2,D}. Its next step produces {D−4,D−2,D+1}. At s=2D−11, the left-contact configuration is {0,2,4,D+1}; the next step is C_(D+1). These formulas include both collision boundaries and cover every time of the cycle without gaps or overlap.

In the right-flight interval, the adjacent pair occupies sites 3 and 4 only at s=0. In the left-flight interval, its two occupied sites differ by two, while the other occupied sites are 0 and D+1≥8. It therefore cannot occupy both 3 and 4. The pattern 10011 at sites 0 through 4 occurs exactly at s=0, including its required zeros at sites 1 and 2.

Consequently, from C_d with d≥7, the complete configuration at the k-th occurrence is C_(d+k), and its exact time is

t_k=sum_(i=0)^(k−1)(2(d+i)−10)=k²+(2d−11)k.

There are no additional occurrences between these times. The successive gaps 2k+2d−10 tend to infinity, so this infinite occurrence-time set is not ultimately periodic and hence not Presburger-definable.

## 3. Quartic witness and its limits

With d=7+x and x,t natural, the polynomial

Q(x,t;k)=[k²+(2x+3)k−t]²

has total degree four, one squared quadratic residual, and exactly one natural witness variable. Since

(k+1)²+(2x+3)(k+1)−[k²+(2x+3)k]=2k+2x+4>0,

the natural witness fiber is a singleton at a pattern-hit time and empty otherwise. There is no omitted phase witness or extra collision case: hit exclusivity was proved above.

A rational k satisfying the residual is a rational root of a monic integer polynomial, so it is an integer. Thus the same empty-or-singleton conclusion holds for nonnegative rational witnesses. For nonnegative real k, the residual's quadratic part is strictly increasing from zero to infinity, so every natural t has a real root. This is why the nonnegative-real witness claim fails.

The stated arithmetic evaluator counts are correct under their explicit straight-line arithmetic convention: four additions/subtractions and two multiplications with x,t,k as inputs, or two additions/subtractions and two multiplications once the gap coefficient is fixed. They are not bit-complexity or CA-input-construction bounds.

## 4. Reversibility must remain unclaimed

The rule is not injective. The distinct configurations

A={0,1,4,6}, B={1,2,3,5}

both map to B. A consists of a right-moving pair and a left-moving pair. Their outputs merge into the connected four-site component B, which is an unrecognized shape and therefore fixed. Hence the example cannot be described as reversible.

## 5. Independent executable receipt

`audit_binary_shuttle.py` passed:

- 8,192 independently reconstructed guarded local-rule entries
- 8,192 independently checked potential identities
- 1,396 complete-state, one-step checks of the closed orbit formula, including all phases for small gaps and boundary phases at section indices through 10^80
- 1,396 anchored-pattern exclusivity checks
- 25 large-integer quartic/discriminant checks, including x=10^70 and k=10^80
- The explicit noninjective pair above

The machine-readable receipt is `binary-independent-audit-results.json`. The finite formula checks supplement the exact cycle proof; the potential identity itself is an exact conservation certificate.

This ordinary binary example strengthens the earlier weighted R/L shuttle: failure of fixed-input timed semilinearity already occurs in the standard numerical-state subclass. It remains compatible with the separately audited mass-four untimed decidability theorem and establishes no literature-priority or universal-computation claim.
