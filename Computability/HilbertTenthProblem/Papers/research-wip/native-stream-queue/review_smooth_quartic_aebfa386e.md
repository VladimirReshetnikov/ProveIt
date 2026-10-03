# Review: Smooth Quartic Diophantine Certificates

**PASS within the stated mathematical and implementation scope.** I read all of `article.tex` (1,733 lines), the README, research-status and source-audit documents, all three Python modules, and the emitted example schemas. The original 21,128-assertion verifier passes. Both expanded example exports reproduce byte for byte. Independent symbolic identities, integer/natural fibre fixtures, local-point checks and counter-machine runs also pass. I found no theorem defect or required implementation repair in this package.

The archive `Smooth_Quartic_Diophantine_Certificates.zip` has SHA-256 `52cea74ad86e678a10963c2d8db4cb5874fc8aece9691c2dcfea45bfb00f9551`. The [portable review helper](review_smooth_quartic_aebfa386e.py) pins the entire archive and every one of its 16 members, safely extracts a private temporary copy, runs the original verifier there, and performs the independent checks. Its [receipt](review_smooth_quartic_aebfa386e.json) contains the complete hash inventory and exact counts. Original repository archives are unchanged.

## Mathematical result and domain audit

For homogeneous quadratic lifts `q_i(x,t)` of the source equations, the delivered formula is

```
F = Σ q_i² + (tu−1)² + g(z1)+g(z2)+2g(z3),  g(z)=2z²−z.
```

The source-to-target natural-zero map is exactly `(x,1,1,0,0,0)`. Over integers, the target has two sign-related copies `(εx,ε,ε,0,0,0)`, with `ε=±1`. This follows because every summand is nonnegative on the integer lattice, each guard vanishes only at zero, and `tu=1`. It does not assert equivalence over rationals or reals. The `t²u²` monomial proves exact degree four even for an empty source system. The monomial-count and coefficient-height estimates in the article count expanded polynomials; they are not straight-line arithmetic-operation bounds.

I checked the full integral Jacobian identity, including the expanded coefficients of the equation and every derivative. Its intermediate relations are `E=4H`, `J=8(tu−1)²−4`, and `4u(2R−1)F_u−(2R+1)J=4`. Combining the last with `F_z1=4z1−1` gives the unit ideal over the integers, so the proof applies in every characteristic and after coefficient base change. This is stronger than smoothness of only the real locus. In odd characteristic, rank three of the quadratic guard part forbids an affine-linear factorization; primitivity then gives geometric integrality. In characteristic two the equation solves uniquely for `z1`, giving the stated affine-space fibre.

The explicit dyadic construction is correct. The parity-pair conversion from four squares gives weights `(1,1,2,2)`, and its substitution cancels the completed guard squares exactly. The coordinate-height estimate is distinct from the complexity of finding a four-square decomposition. The implementation's one-million search cap is documented and a supplied decomposition can be verified. Odd-prime integral points come from dyadic denominators; the derivative of `c+2z²−z` is odd, giving compatible roots at two. This establishes every integral local test, without implying a global integer point.

The rational-density proof correctly uses rational points on nonsingular quadric fibres and a boundary approximation argument. It does not silently promote dyadic existence to dyadic density. The two-component real-locus proof uses `tu>0` and explicitly connects the positive-`t` part after rescaling `x/t`; the negative part follows by sign symmetry. Geometric integrality ensures that easy rational points and hard integer points inhabit the same component algebraically. No smooth proper or projective model is asserted.

The total-weight classification is also correct under its hypothesis that the first guard weight is one: universal smoothness occurs precisely for totals 4 and 16. The necessity proof supplies actual bad-prime singularities; the sufficiency uses the integral elimination identity after two becomes invertible in the Jacobian quotient. The `(1,3)` obstruction correctly excludes all dyadic points for the three-constant-residual example by a primitive modulo-eight descent and a modulo-sixteen obstruction. The five-auxiliary minimum is limited to positive guards of total weight four; it is not a global lower bound on Diophantine representations. The higher-degree power-of-two extension has the same domain and unit-ideal reasoning and is explicitly not implemented.

## Computational scope and paid input

The counter frontend is a bounded natural-number compiler. Natural selectors summing to one are one-hot. A selected positive guard forces a positive counter and determines its slack; an inactive guard forces its slack to zero. Initial states/counters, every transition, and the final halt state are all paid in the source equations. Absorbing padding means acceptance is halting **by** the external horizon, not first halting at that horizon. The counts

```
n_T=(states+counters)(T+1)+(edges+positive_edges)T,
m_T=(states+counters)+T(1+2states+counters+guarded_edges)+1
```

are correct, and the finalizer adds exactly five variables. These counts grow with `T`; this is not a fixed-arity unbounded-history compiler. Nor do natural selectors automatically describe legal executions over unrestricted integers.

The report obtains fixed-arity unbounded universality only by starting from an established fixed-arity universal Diophantine relation, uniquely lifting its arithmetic circuit to quadratic equations, and applying this finalizer. That transfer preserves existing witness multiplicities; it proves no single-fold MRDP theorem. Its input-degree distinction is accurate: treating an ordinary loader parameter `a` as a coefficient turns `v−a` into `tv−at²`, whose square has total degree six when `a` is subsequently counted as a coordinate. Homogenizing `a` instead keeps the total polynomial quartic but does not prove relative smoothness of each fixed-input fibre. The article explicitly keeps these contracts separate.

This provides a useful source-independent smoothing layer with explicit algebraic certificates. It supplies no smaller fully paid operation schedule for the maintained 87-operation universal polynomial. Adding geometric regularity does not remove the source compiler, homogenization or variable costs.

## Executable review

Before running code, I read `smooth_compiler.py`, `counter_frontend.py`, and `verify.py`. The sole substantive executable verification entry point is `python code/verify.py`; it also regenerates both example exports. The helper runs this in a fresh isolated extraction with a 300-second timeout and checks the saved result after normalizing only the explicitly reported Python and SymPy versions. The two example files must remain byte-identical. PDF compilation and document-layout tooling are outside this executable scope.

The independent checks use two new two-variable source systems and the zero-variable inconsistent/empty cases. They evaluate the exported sparse polynomial independently over exact integers or rational fractions, verify the actual expanded Bézout identity, confirm the characteristic-two unit derivative, and replay the dyadic and compatible two-adic points. They compare six one-counter program tables against a separate instruction interpreter across 120 input/horizon cases, including zero horizons. Malformed polynomial domains and natural frontend inputs are rejected. Finite obstruction replays supplement, rather than replace, the unbounded divisibility argument.

The source system snapshots its declared symbols and residuals into immutable tuples. The public finalizer checks degree, integer coefficients, undeclared symbols and auxiliary collisions. `SmoothCertificate` is a plain certificate carrier; this package is not an authenticated checker for arbitrary caller-constructed or edited certificate objects or hostile sparse JSON. The article's export appendix explicitly places such a future checker outside the delivered proof boundary. No defect is inferred merely from that omitted feature.

The independent helper's receipt reports the exact census and fixture details. No universality claim rests on those finite checks, and no full universal Pell witness or small fixed universal counter table is materialized.

## Primary references checked

I opened Poonen's [author manuscript, Lemma 4.1 and Corollary 4.3](https://math.mit.edu/~poonen/papers/automorphism.pdf). It supports the report's attribution of earlier smooth-variety undecidability and does not supply this exact five-variable weighted formula. I also checked the primary [mechanized MRDP record](https://arxiv.org/abs/2003.04604) and the [Stacks Project smoothness section](https://stacks.math.columbia.edu/tag/01V4). These support the background interfaces; the package's new integral identity, arithmetic constructions and scope claims were audited directly. This was not a complete historical priority search.

## Reproduction

```
python review_smooth_quartic_aebfa386e.py \
  --archive /path/to/Smooth_Quartic_Diophantine_Certificates.zip \
  --expect review_smooth_quartic_aebfa386e.json
```

Use `--output PATH` to create a new deterministic receipt. Expected receipts use recursive exact-type comparison. The helper has no fixed `/tmp` dependency and restores the caller's imported package modules after its independent checks.
