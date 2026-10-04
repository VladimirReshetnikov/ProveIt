# Independent adversarial audit: rational-rotation family 59

Date: 4 October 2026

## Verdict

**PASS within the stated conventional-proof and inert-source scope.** I found no mathematical or implementation defect requiring a correction to the frozen packet. The proof supports the full rational infinite-order rotation family, arbitrary positive rational scaling, exact complete-word domains, the strict-boundary orbit characterization, both finite-sign obstructions, fixed-machine polynomial-time rational membership, and the literal degree-12 Diophantine template.

The static physical constructor is supported by an arbitrary-parameter source invariant argument below, not just its fixtures. Every field in all 45 supplied JSON fixtures was independently reconstructed and matched. The arithmetic statement is a displayed polynomial template; it is **not** a claim that a general arithmetic DAG/compiler was emitted. No Lean proof checking, physical simulation, author/upstream executable, or saved collision schedule was run.

### Final binding

- `PROOF.md`: `14c3d694d9e0c21f3ad3b125c0d1f2bbf47793e1283c9314aa3855ef60c89fc5`
- `static_family.py`: `c6ce6ae3873da154c4b7f200f762408f36583d20e424ac6fca4661bd0bd9ce41`
- `PACKET_MANIFEST.json`: `646de47472089e9909fafbf0ed1e1a7851a114d862e4df9b31d0802815772044`
- Pell source: `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`

The final proof binding includes the newly added Section 7.1 fixed-machine polynomial-time corollary. The preliminary `4406ad…6adb` proof is not the version to which this verdict is bound.

## 1. Method and independence

The full proof and complete 158-line physical constructor were read as inert text. The constructor was also parsed as Python syntax, not imported or run. The packaged arithmetic review was not substituted for the fresh arithmetic review in `ARITHMETIC_AUDIT.md`.

The newly written and inspected `audit_static.py` uses closed block endpoint formulas and closed arithmetic-series duration sums. These differ from the author's incremental endpoint loop. Its static phase grammar is specified independently from the primitive geometry. It compares all fields, including every guard name/coefficient, phase range, temporary speed, messenger label, rule, return row, duration row, nearest-row record, contact, count, and default declaration. It then checks abstract label occupancy. This last check updates sets of labels only: it computes no physical position or time and chooses no next collision.

The newly written and inspected `audit_geometry.py` checks 13 exact symbolic identities, a deliberately degenerate multi-contact rational polygon, and 672 signed/composite-denominator power cases. Its synthetic polygon is an algebraic test of the general chamber lemma; it is not presented as a polygon emitted by this physical family.

All 59 manifest entries and the exact 60-file packet inventory were verified. All seven external source pins in `SOURCE_PINS.json` match their referenced inert files. The Report 57/58 dependencies were consulted only for the identified earlier example and Pell/certificate provenance. The prior 138-event machine was not substituted for the present 174-event machine. Snapshot hashes establish unchanged author-packet bytes throughout this audit.

## 2. Parameter coverage and shear synthesis

For primitive integer `a²+b²=c²`, `c>1`, both legs are nonzero, `c` is odd, and both `gcd(a,c)` and `gcd(b,c)` are one. The trace argument is sufficient: a finite-order `(a+ib)/c` would make `2a/c` a rational algebraic integer, hence an integer, forcing `c|2`. Conversely the rational finite-order exceptions have denominator one. Thus the quantifier really covers every rational infinite-order planar rotation, including all signs and coordinate orders.

Since `|a|<c`, the denominator `c+a` is strictly positive even when `a<0`. The step choice is finite, nonzero, and satisfies `|delta_x|,|delta_y|<=1/4`. Near translations therefore have `e<1`; far translations have `|e|<=1/6`. The source never relies on a small total x-shear: `Nx` can grow, while each individual pair returns the center to the center.

Multiplying the three shear matrices gives diagonal entries `1+tx*ty=a/c`, lower-left entry `ty=b/c`, and upper-right entry `2tx+tx²*ty=-b/c`. The two x factors coincide, so the chronological x/y/x order does not reverse the desired rotation. The independent symbolic check reduces all four residual numerators modulo `a²+b²-c²` to zero.

For the reflected y block, `r=D-y`, `s=D-x`. The update `r'=r+ty(s-2D/3)` gives `y'=y+ty(x-D/3)`. Both the sign of the physical velocity and the sign of the y shear have been checked; reflecting coordinates requires negating every physical velocity, which the source's `eps=-1` does.

## 3. Complete primitive chronology and exact guards

### 3.1 Single-marker scaling

Take anchor coordinate zero, target initially at `z>0`, final target coordinate `z'=uz>0`, and stationary inner markers `0<s1<...<sk<min(z,z')`. The four principal events have times

`z, 2z, 2z+z', 2z+2z'`.

On the four messenger legs, each inner marker `s` is encountered at

`s, 2z-s, 2z+s, 2z+2z'-s`.

Within each leg these are strictly ordered by the spatial order or its reverse. The gaps at the target ends are `z-sk` and `z'-sk`; the gaps at the anchor ends are positive inner coordinates. This accounts for every spectator event and every principal event. An outer stationary marker is never reached by the messenger and remains separated from the target if both target endpoints lie below it.

The target's world line with slope `(u-1)/(u+1)` passes through the asserted restoration point. Its speed has magnitude less than one. Between launch and restoration the target remains in the open interval between its checked stationary neighbors, so it cannot create a remote collision. On each messenger leg, the relative speed has a fixed strict sign; there is no additional target/messenger contact. All other marker pairs are stationary and distinct. These facts exclude both an omitted competitor and an independent simultaneous collision elsewhere.

For necessity, if a target endpoint reaches a neighbor, the target has an extra or coincident contact by that checkpoint; if it passes the neighbor, continuity forces an extra contact earlier. Equality with the anchor also collapses required timing. Such contacts count even if the machine's default identity rule would leave velocities unchanged: the specified word is complete, not merely a selected subsequence.

### 3.2 Reflector homothety

The target is the nearest marker to its anchor. Let its starting and final distances be `t,t'`, let reflector distance be `z`, and let any intervening spectator have coordinate `q`. Directly solving the world lines with speed `(1-v)/(1+v)` gives

`t'=vt+(1-v)z`, restoration time `2z-t'`, final anchor time `2z`.

The target launch is at time `t`; outward spectators are at times `q`; the reflector bounce is at `z`; return spectators are at times `2z-q`. The required strict gaps follow from `0<t,t'<q1` and `qk<z`. In the empty-spectator case they follow from `0<t,t'<z`. The target moves monotonically between its checked endpoints. Again these inequalities exclude target/spectator and remote collisions, and failure forces an extra/tied contact or collapsed chronology.

This argument would be invalid if an unlisted stationary marker lay between the anchor and target. The actual x phases target X from L; the reflected y phases target Y from D. Both are nearest-marker arrangements. The source never calls H for a non-nearest target.

### 3.3 Translation

For `e<1`, composing `L(1/(1-e))` with `H(1-e)` gives intermediate coordinate `m=t/(1-e)` and final coordinate `f=t+ez`. Both moving phases have slope `e/(2-e)` in anchor coordinates.

The claim that no intermediate guard is needed is correct. If `e>0`, then `f<z` implies `t<(1-e)z`, and

`m-t=e*t/(1-e)>0`, `f-m=e*((1-e)z-t)/(1-e)>0`.

If `e<0`, `t<z` makes both those differences negative. For `e=0`, all three coordinates agree. Thus the intermediate point is between the checked endpoints and the target is monotone across the complete two-primitive gadget, including its stationary pauses. Start/end order is necessary as well as sufficient.

### 3.4 Macro guards

After k completed pairs in an anchor-based shear block, the target is

`t_k=t_0+k*delta*(z-2D/3)`.

Its next near endpoint is `t_k+delta*z`; its far endpoint is `t_(k+1)`. Therefore the supplied `2n+1` endpoint pairs together with `0<z<D` give exactly `4n+4` rows. Their pullbacks are necessary and sufficient for the complete composed word by the first-failed-checkpoint argument above. They are not merely a conservative safe polygon.

At the centered input, each pair starts and ends at anchor-distance `D/3`; its odd endpoint is `D/3+2delta*D/3`, lying in `[D/6,D/2]`. This closed interval is strictly inside `(0,2D/3)`. Every row has strictly positive center coefficient for every finite number of steps. Initial-order rows bound the normalized chamber inside `0<x<y<1`, so the chamber is a bounded open rational polygon with a genuine interior neighborhood of zero.

## 4. Arbitrary-parameter source invariants

This section supplies the all-input justification separately from the 45-fixture check. Line numbers refer to the pinned `static_family.py`.

1. **Validation and representation (22–36).** Positive rational lambda and primitive integer rotation parameters imply finite positive loop counts and the bounds on both step sizes. `Fraction` arithmetic preserves exact rational rows. A row's first coefficient is its value at the center; the mathematical centered-pair argument proves each `guard` assertion, rather than using that assertion as evidence by itself.
2. **L expansion (42–55).** Before the phase, the messenger points toward the target and all markers are stationary. The loop visits inner markers in increasing anchor distance, launches the target, reverses the inner order, bounces at the anchor, revisits the increasing order, restores, visits the reverse order, and bounces again. This is exactly the four-leg chronology above. It adds `4+4k` events and one temporary label, and restores its entry direction.
3. **H expansion (56–67).** Launch preserves direction, spectators are visited forward and backward around the reflector bounce, restoration preserves the inward direction, and the anchor bounce restores entry direction. It adds `4+2k` events and one temporary label. Reflected phases simply negate `eps`.
4. **Translation (68–75).** Its target update is `t+delta*z`; its duration addition is `2(1+1/(1-delta))*t+2z`. The empty L-inner list is justified because every translation target is anchor-nearest. Near H has no spectator; far H has exactly the near reflector as one spectator.
5. **Shear loop (76–90).** At loop entry j the target row is `t0+j*delta*(z-2D/3)`, the fixed row z and D are unchanged, all markers are stationary, and Q is at the same anchor with the same entry direction. A near translation appends the odd checkpoint; a far translation appends the next even checkpoint and reestablishes the invariant. This proves all endpoint rows, counts, and maps for arbitrary n, without extrapolating from sampled n.
6. **Transfers and composition (91–102).** The terminal strict ordering of the preceding block gives all three transfer events. Each transfer takes duration D and reverses entry direction at the opposite anchor. The A1/B/A2 composition gives the independently derived rotation. In particular the source's reflected y branch implements `D-y`, not `y-D`.
7. **Scaling branch (103–108).** When lambda<1 the source scales X,Y,D; when lambda>1 it reverses the same list to D,Y,X. All previously scaled markers are stationary. The inner lists X none, Y [X], D [X,Y] are valid under either order. No extrapolated endpoint is used to choose an event. The duration contribution uses each target's pre-scaling coordinate once.
8. **Rule and label loop (109–125).** Each indexed event receives exactly its own pre-event messenger label and advances to the next, with the last advancing to Q0. A launch changes a stationary target label to its unique temporary label; its restoration changes that temporary label back; crossings and bounces preserve the stationary identity. Direction continuity follows from the phase invariants and transfers. No two prescribed input sets conflict because their messenger labels differ. There are exactly four stationary labels, `4K0+3*[lambda!=1]` temporary labels, and `18K0+6+24*[lambda!=1]` messenger labels. This yields `22K0+10` or `22K0+37` meta-signals while preserving exactly five live identities.
9. **Contact scan (126–135).** All constants are positive and at least one row is nonconstant because the chamber is bounded. The scan computes rational squared distances and rational perpendicular contacts, uses exact equality for nearest lines, and deduplicates exactly. No rounding, heuristic irredundancy test, or uniqueness assumption is present.
10. **Return/serialization (136–158).** The advertised gap matrix equals the centered-coordinate conjugate, independently checked by expressing final x,y,D back in initial gap rows. Serialization converts exact fractions to strings, not floats. The runner only calls the finite constructor and writes JSON. The full source contains no physical event-selector, trajectory solver, imported old program, or arithmetic frontend.

The source's assertions are ordinary development checks, not a security-hardened input validator under Python optimization. No such hardened-execution claim is part of the theorem. The all-parameter claim is restricted to its stated integer/rational mathematical inputs.

## 5. Scaling, counts, and time

Under contraction, when the current target z is scaled, each inner marker has already moved from s to lambda*s. Since s<z, `lambda*s<lambda*z`, so the target stays above every scaled inner marker. Every outer marker is still unscaled and above z. Under expansion the outer markers are already scaled, so the target ends below `lambda*s` for every original outer s; all inner markers remain below z. This proves the whole homothety valid on every ordered section, including lambda arbitrarily close to zero or arbitrarily large.

Each micro-shear has 8 near-translation events and 10 far-translation events. The two transfers add six events. Scaling X,Y,D has event counts 4,8,12 regardless of order. Thus the claimed `18(2Nx+Ny)+6` and optional `+24` counts are exact.

Duration is a rational linear row. Independently, summing block start coordinates gives

`sum t_k = n*t0 + delta*n(n-1)/2*(z-2D/3)`.

Using this closed sum for both translations reproduced every emitted duration row. Each translation takes less than `6D`, and the transfers take exactly `2D` in total. With homothety, the additional time is `2(1+lambda)(x_rot+y_rot+D)<6(1+lambda)D`, yielding the stated upper bound.

For lambda<1, each complete macro stays in `[0,D_n]` and `D_n=lambda^n D0`; hence all strands tend to the fixed left anchor and the time series converges. The rational resolvent formula `ell(I-N)^(-1)` is valid because every eigenvalue of N has modulus less than one. For lambda>=1, the transfer-time sum alone diverges. This proves the iff without making any continuation claim at the accumulation.

## 6. Boundary geometry and both finite-sign obstructions

Write each row as `alpha+v.w>0`, with alpha positive. On a circle of radius rho equal to the least line distance, Cauchy–Schwarz shows that a row can vanish only at its perpendicular nearest contact. A nonnearest row is strictly positive at every point on that circle. A nearest row is also positive there away from its contact. Thus the circle complement of P is exactly the finite deduplicated E, even when rows are redundant, repeated, or proportional.

At smaller radius every row is strictly positive. At larger radius any nearest half-plane cuts out a nonempty open arc, and every irrational rotational orbit meets it. Because normalization removes lambda, the exact infinite-validity formula is the open disk plus the critical circle with the finite union of oriented inverse orbits removed.

No assumption that different contacts have disjoint orbits is needed. Choose p in E. On its full orbit, E occurs at finitely many unique integer indices I, and the union of their backward tails is exactly `k<=max(I)`. Therefore both the accepted forward tail and rejected backward tail are dense and rational.

The positive-gap qualification is handled correctly. The closed disk lies inside the closed initial-order triangle. A strict initial-order line can vanish on its circle only at its perpendicular contact, so there are only finitely many zero-gap circle points. Removing them from a rejected dense tail keeps it dense. The accepted tail is already in P and therefore has positive gaps. The proof never needs all critical-circle points to be admissible initial sections.

The critical excluded set is countably infinite and the retained set is uncountable; moreover both are dense. A semialgebraic subset of a circle is a finite union of arcs and points, so the exact real validity set is not semialgebraic. The same finite-arc argument contradicts any finite real-coefficient polynomial-sign formula agreeing on all positive rational inputs.

For integer inputs, homogenizing each polynomial by its eventual leading nonzero homogeneous component is the necessary bridge. The eventual-sign formula is a finite semialgebraic, positive-scale-invariant case distinction. Correctness on every positive integer multiple of an integer vector forces correctness of the eventual formula on that ray. Clearing denominators then covers every positive rational ray, contradicting the rational obstruction. No homogeneity assumption on the original formula is smuggled in. This claim is about finite polynomial-sign formulas, not formulas with quantified integer witnesses.

### Deliberate degeneracy test

All 45 physical fixtures have J=1. To avoid suggesting otherwise, the extra geometry check uses a separate rational polygon with radius squared `1/18`, contact `p=(1/6,-1/6)` on the initial face `y=x`, contacts `R^-3 p`, `R^2 p`, and `-p`, plus proportional duplicate rows. It has eight supplied rows, six nearest rows, and four distinct contacts. Three nearest rows represent p; the first three distinct contacts share one rotation orbit.

The exact denominator-based membership test agrees with `R^k p` being accepted exactly for `k>2` in 101 checked indices. The only zero-gap point in that checked tail is k=0. This tests the difficult cases together, while the general argument above supplies their proof beyond any finite range. It does not assert that this synthetic polygon occurs among the compiled family machines.

## 7. Arithmetic certificate and complexity

The separate fresh `ARITHMETIC_AUDIT.md` gives a detailed positive-domain mapping to the pinned `Pell.matiyasevic` and `Pell.eq_pow_of_pell` source statements, including ordinary versus natural subtraction and both completeness directions. Its conclusions are incorporated here after checking the report and dependency pin.

Key audit points:

- Modulo each prime p dividing c, `(a-ib)^n=(2a)^(n-1)(a-ib)` for n>=1. Both coordinates remain nonzero modulo p. No field property of `(Z/pZ)[i]` is assumed. The denominator is exactly `c^n` even for composite c
- The quotient numerator is `t(rA+sB)+i*t(rB-sA)` over `3(r²+s²)D`, so the final mismatch square has sign `v+sign(b)*S`
- The decomposition `q=c^n*r` with `c` not dividing r is repeated whole-integer division, not an additive prime-adic valuation. It does not incorrectly require `gcd(r,c)=1`
- The enlarged radix `4P+2c+1` both uniquely decodes bounded signed Gaussian coefficients and guarantees a positive ordinary POWER base for negative a
- Exponent zero, zero numerator coordinates, the center, natural zero slacks, strict positive acceptance, and strict Pell modulus slack all survive the positive-leaf adapters
- The native ledger is one shared radius leaf plus `6+6+16+26+26=80` per contact, and one radius residual plus `13+15+15=43` per contact. Outputs P,T are counted only in their POWER modules
- After affine adapters, every POWER residual has degree at most six, and residual 13 has leading term `-w^4*g²`. Its square yields nonzero total degree twelve. Sum-of-squares leading terms cannot cancel identically
- The optional Cantor encoding adds four witnesses and two quadratic equations, preserving degree twelve

The fixed-machine O(L³) bound is justified. Fixed-size rational arithmetic and gcd reduction keep all fractions at O(L) bits. Repeated division by fixed c uses O(L) steps. If q is a power of c, its forced exponent n is O(L); every intermediate Gaussian numerator has magnitude at most q, and multiplication by fixed a-ib has polynomial cost. No factorization or unbounded orbit search is needed. J and all contact constants are fixed. This is not a bound on compiling a machine or finding the potentially enormous Pell witnesses.

The additional exact arithmetic checks cover 32 signed/coordinate-ordered triples over c=5,13,65,169 and exponents 0 through 20, giving 672 denominator and 672 bounded-radix checks. In particular c=65 tests distinct-prime composite behavior in addition to the prime-square c=169 in the physical fixtures. These checks are supporting examples, not a replacement for the prime-divisor proof.

## 8. Fresh primary-literature check

The strongest overlap warnings in the packet are warranted. Fijalkow–Ohlmann–Ouaknine–Pouly–Worrell, [STACS 2017, Example 1](https://people.mpi-sws.org/~joel/publications/semialgebraic-invariants17.pdf), explicitly use `(1/5)[[4,-3],[3,4]]` and show that an unreachable target on the orbit-closure circle may lack a semialgebraic separating invariant. Its opening also recalls the polynomial-time Kannan–Lipton orbit decision result. The present strict-boundary classifier and physical realization are different objects, but dense-circle semialgebraic obstruction and polynomial-time point-orbit membership cannot be presented as new general phenomena. The source's angle text has an arctan typo; its displayed matrix fixes the intended rotation.

Durand-Lose's [AGC6 author manuscript](https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/Publications/2012_IJUC_UC_HC.pdf), especially the introductory conservation requirement and Section 3, explicitly describes equal incoming/outgoing counts, rational stack encoding, translation/scaling, and conservative shrinking. Thus rational conservative arithmetic and shrinking are prior art. This does not by itself supply the present exact five-total-live-signal rotation realization or exact strict chamber. The packet's lowercase `/membres/` PDF route failed one fresh fetch; the indexed `/Members/` route above succeeded. This is a nonblocking access note, not a mathematical correction.

This fresh check is deliberately bounded. It certifies neither novelty nor priority, and does not independently replicate every repository search recorded in `PRIOR_WORK.md`. The proof's cautious claim boundary is appropriate.

## 9. Receipts, negative controls, and remaining boundaries

`STATIC_INDEPENDENT_RECEIPT.json` records:

- 45 fixtures, 13,572 indexed binary rules, 3,336 guard rows, and 2,976 phases independently matched
- Complete field equality and receipt hashes, 59 manifest entries, exact 60-file packet inventory
- Five-label occupancy and stationary phase restoration, distinct collision speeds, unique prescribed input sets, cyclic Q0 closure
- Twelve rejected deliberate mutations: spectator deletion, contraction-order reversal, reflected-speed sign, guard coefficient, initial row deletion, tangent sign, duration, return orientation, missing default, stale messenger label, collapsed temporary label, phase endpoint
- Preserved author packet bytes

`GEOMETRY_INDEPENDENT_RECEIPT.json` records the exact identity, degeneracy, denominator, and radix tests. `AUTHOR_PACKET_SNAPSHOT.json` pins every author-packet file. `ARITHMETIC_AUDIT.md` provides the separate Pell and ledger analysis. `AUDIT_RECEIPT.json` binds the final audit outputs and source state.

No blocking defect remains. The explicit limitations are important: conventional proof, not formal verification; finite fixtures supplement rather than establish arbitrary-parameter correctness; all physical fixtures have one contact; no emitted general arithmetic DAG; no general arithmetic gate ledger; no finite-fold witnesses; no arbitrary-matrix, unchanged-universal-machine, lower-bound, or novelty claim; and no post-accumulation semantics.
