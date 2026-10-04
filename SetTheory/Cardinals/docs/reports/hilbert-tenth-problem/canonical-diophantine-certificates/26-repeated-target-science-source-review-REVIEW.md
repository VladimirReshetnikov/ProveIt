# Independent exact-source review: repeated target firing

Date: 4 October 2026. **Verdict: PASS for exact source realization and degree. No source defect was found.** The submitted JSON implements the specified variable-radix repeated-firing certificate with all arithmetic macros expanded. This report does not independently reprove the entire physical/sandpile theorem or discharge the inherited constructive Pell dependency.

The source and submitted builder were read-only throughout. Neither the submitted builder, any upstream checker or script, nor Lean was executed or imported. The independently authored `check_source.py` uses only Python's standard library and treats the two polynomial DAGs as inert formal syntax over Z. It does not evaluate the submitted arithmetic schedule at numerical witness assignments.

## 1. Frozen inputs and exact coverage

Submitted DAG: `../evidence/polynomial-dag.json`

SHA256: `7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6`

Submitted builder, inspected only: `../build_repeated_certificate.py`

SHA256: `c37f455dc5a9a673fb2b980fb5dc41103f9a85e82a97c24cae296ed580fe9928`

The checker constructs an independent contract-level specification using sparse formal integer polynomials. This specification has no DAG construction API and does not obtain its intended parameters from the new submitted macro metadata. Its equations use algebraically rearranged forms. It separately normalizes all 10,523 body gates from the submitted DAG and compares exact coefficients and monomials.

Checks passed:

- Exactly 2,251 distinct named residuals agree with the independent specification, without missing or extra equations
- All 186 macro interfaces agree, including the fully expanded internal equations of all calls
- All 44 exposed ports agree as exact polynomials
- The exact set of 3,865 distinct positive witness names agrees with the independent adapters and macro witnesses
- Every body/reference contract is well formed: only integer literals, the single `InputPlus` input, declared witnesses, and earlier `+`, `-`, or `*` gates occur
- The schema, declared domain, single input, fixed-literal gate convention, and exact metadata key set agree
- Every witness, every gate, and the free input is reachable from the final output
- Every one of the 6,752 post-body gates is checked directly as the complete ordered sum of the squares of the listed residuals, with the declared output being precisely its final gate
- The frozen source hash agrees both before and after checking

Thus the output is exactly

`P(InputPlus,w) = sum_{j=1}^{2251} residual_j(InputPlus,w)^2`.

There are no primitive powers, exponentiation gates, comparisons, bit operations, array operations, unexpanded macros, or implicit integer variables in the submitted DAG. POWER/Sub/AND/SPREAD names are metadata describing already expanded polynomial constraints.

The domain is the supplied positive integer `InputPlus` and 3,865 strictly positive integer witnesses. Each natural is an explicit positive leaf minus one. Pell's `a,beta>=2` and the three box padding multipliers are explicit positive leaves plus one. Positivity is part of the theorem's quantified domain, not a claim that the polynomial alone enforces that domain over all real inputs. On the positive-integer domain, the sum of squares vanishes exactly when every reconstructed residual vanishes.

## 2. Exact ledger

| Part | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|
| Body | 4,537 | 3,681 | 2,305 | 10,523 |
| Sum of squares | 2,251 | 2,250 | 2,251 | 6,752 |
| Entire polynomial | 6,788 | 5,931 | 4,556 | 17,275 |

Macro calls: **138 POWER, 34 Sub, eight AND, six SPREAD**.

The witness decomposition is

`138*26 + 34*5 + 8*3 + 6*4 + 5 + 11 + 9 + 3 + 3 + 3 + 3 + 8 + 1 + 13 = 3865`.

In order, the terms are POWER outputs/internals; Sub outer witnesses; AND partition values; SPREAD outer witnesses; five geometric-series values; eleven input descriptors/signed coordinate codes; nine internal Cantor codes; three tile bitplanes; three extra radix witnesses (`width,half,growth_gap`); three box padding leaves; three spatial-mask geometric factors; eight time quantities (`K,R,pre,event,final,nx,ny,nz`); legality slack; and twelve local signed-target witnesses plus one event-time witness.

The equation decomposition is

`138*15 + 34*3 + 8*2 + 6*4 + 10 + 1 + 5 + 2 + 3 + 1 + 1 + 3 + 1 + 12 = 2251`.

After the four macro terms come the ten Cantor equations; tile reconstruction; five geometric equations; two radix equations; three spatial-mask equations; temporal repetition; recurrence; three exact negative-shift divisions; selected legality; and twelve signed-coordinate clauses.

POWER count by role: 102 inside the 34 Sub calls, 18 direct powers inside six SPREAD calls, five geometric-series powers, one variable-radix power, five physical row/plane/z radices, one patch shift, three box radices, one time-end shift, and two target powers, totaling 138.

All source loops have fixed lengths or iterate over these fixed emitted lists. The polynomial's arity, clause count, and arithmetic gate count are independent of the decoded dimensions, eventual box size, time horizon, target coordinates, and witness values. These are literal-source counts, not optimality/minimality claims.

## 3. Exact total degree

Sparse normalization gives the following residual degree histogram:

| Degree | Residuals |
|---:|---:|
| 1 | 462 |
| 2 | 983 |
| 3 | 211 |
| 4 | 423 |
| 5 | 7 |
| 6 | 138 |
| 7 | 18 |
| 8 | 6 |
| 9 | 3 |

Only `patch.shift.eq8`, `patch.shift.eq9`, and `patch.shift.eq11` reach degree nine. Each has highest homogeneous part

`-4 p q r d e f tx0 ty0 tz0`,

where `tx0,ty0,tz0` mean the raw positive witness leaves `box.tx,box.ty,box.tz`; the actual padding multipliers are those leaves plus one.

The checker exactly normalizes the sum of their highest homogeneous squares. The output's highest homogeneous part is

`48 (p q r d e f tx0 ty0 tz0)^2`.

It is nonzero. Together with the exact residual degree upper bound, this proves that the literal output has **exact total degree 18**. An independent syntactic all-gate degree calculation also gives upper bound 18. This proof does not substitute the semantic identity `b=32^width` into the polynomial: the radix output is, correctly, one of the independent witness leaves constrained by POWER.

## 4. Compatibility with the approved arithmetic macros

The accepted audit was read at `/workspace/shared/sandpile-target-independent-audit-20261004/AUDIT.md`. Its approved DAG was independently read as inert JSON and pinned to

`352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504`.

The fresh checker verifies the old DAG's 157 macro interfaces and all 1,886 macro-internal residuals against the **same independent macro templates** used for the new source. This is an exact formal comparison, not an inference from function names or a textual copy test. In that compatibility check alone, the old audited interfaces supply instantiation parameters; every equation and nested interface is then independently regenerated and compared. No old program is executed or imported.

For POWER, with `k=exponent+1`, `m=base*out`, the template contains the three Pell equations; beta congruence modulo `4y`; beta congruence modulo `u`; `v=y^2*qv`; the two `s,t` congruences; `y>=k`, `w>=base`, `w>=k`; strict `M>m`; the auxiliary Pell equation; `2a*base=M+base^2+1`; and the final modular power relation. All paired congruence quotients are independently represented by natural adapters. Each POWER has exactly 26 positive leaves and fifteen equations.

Sub uses its three powers, odd binomial digit, positive digit gap, and positive remainder gap. AND uses both partitions and all three Sub calls, including disjointness of the residual supports. SPREAD retains its strict input bound, explicit stride gap, geometric copy equation, full-digit mask equation, and expanded AND selection. The new source therefore inherits precisely the approved macro obligations and semantics, rather than a weakened variant.

The inherited constructive Pell dependency remains the one recorded by the accepted audit: mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorems `matiyasevic` and `eq_pow_of_pell`, accepted source SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. This review does not rerun Lean or independently certify that external formalization.

## 5. New source clauses and their contracts

### Input and radix conversion

The input remains exactly the eleven natural fields

`(p-1,q-1,r-1,T,d-1,e-1,f-1,D,zeta_x,zeta_y,zeta_z)`

under ten right-associated Cantor pairings of `InputPlus-1`. All six dimensions are positive. The source reconstructs and validates the original base-32 tile digits 0 through 5 using three bitplanes and the excluded 6/7 pattern, and patch digits 0 through 15 using the full four-bit mask. The declared array sizes are enforced by the finite masks, including any leading zero slots.

Only after these ordinary input contracts does the source introduce

- `K>=1` and `width>=1`
- POWER enforcing `b=32^width`
- Positive `half` with `2half=b`
- Natural `growth_gap` with `b=64(K+1)+growth_gap`
- `SPREAD(T,32,pqr,width)` and `SPREAD(D,32,def,width)`

The two conversion stride bounds additionally require `width>=pqr+1` and `width>=def+1`. This is an existential witness restriction, not a bound on admissible physical instances: sufficiently large widths satisfy both volume requirements and the time growth bound. The converted integers are exactly the same finite digit sequences in radix b. In particular `b=2^(5width)` is a power of two, `b>=64(K+1)`, and the lower-half mask is well defined.

### Variable-radix geometry

Every subsequent physical radix is built from this same b. The independently reconstructed geometry is

`hx=p*d*tx`, `hy=q*e*ty`, `hz=r*f*tz`,

`A=2hx`, `B=2hy`, `C=2hz`, with `tx,ty,tz>=2`.

The two tile and two patch reshapes, three tile repetition factors, and patch shift all match the approved original geometry with base 32 replaced by b **after** the two explicit input conversions. The patch shift exponent is `hx+A*hy+AB*hz`. The box powers are `X=b^A`, `Y=X^B`, `Q=Y^C`. The source does not accidentally mix an old fixed spatial radix with a new variable one.

The three interior-mask equations are precisely

`b^2((b-1)jx+1)=X`,

`X^2((X-1)jy+1)=Y`,

`Y^2((Y-1)jz+1)=Q`,

with `I=b X Y jx jy jz`. The lower corner remains period-aligned; the source includes all six zero faces through this strict-interior mask. The initial coefficient bound remains five plus fifteen, hence twenty, after conversion.

### Temporal counts and legal repeated firing

The exact reconstructed new clauses are

`W=Q^K`, `(Q-1)R+1=W`,

`Sub((b-1)IR,Apre)`, `Sub(IR,E)`, `Sub((b-1)I,V)`,

`Q(Apre+E)=Apre+WV`,

`b nx=Apre`, `X ny=Apre`, `Y nz=Apre`.

Thus the pre-count and final-count masks admit full radix-b digits; only the event stream is a one-bit-per-slot stream. The source does not inadvertently retain the old binary history restriction. The available-height expression exactly matches initial height repeated through time plus the six shifted cumulative neighbor counts.

Both selections use the same complete event-slot mask `(b-1)E`:

`Csel=AND(Cval,(b-1)E)`,

`Asel=AND(Apre,(b-1)E)`.

The slack and threshold are exactly

`Sub((half-1)E,L)`,

`Csel=6Asel+6E+L`.

The previous own firings are explicitly charged by `6Asel`. No old five-plane, binary-prefix slack construction remains. The emitted source has exactly these masks, two selections, and threshold; every nested Sub and POWER parameter was compared symbolically.

The arithmetic proof of recurrence uniqueness and carry control is treated separately in `../recurrence-review/REVIEW.md`. In particular one must first establish the canonical-count uniqueness using `gcd(Q-1,Q^K)=1` and the bounded pre-stream, and only then conclude that `Apre+E` is carry-free. This exact-source review does not use a candidate count bound that the masks alone do not prove.

### Supplied signed target at an existential event time

For each axis, the source includes all four equations: unique zigzag parity/half decoding, binary sign, translation into the box, and strict local upper bound. Thus the point exponent is the correctly bounded index

`local_x + A*local_y + AB*local_z`.

The source has separate POWER calls for `point=b^index` and `timepoint=Q^tau`, with tau a natural adapter, followed by the full expanded `Sub(E,point*timepoint)` call. It tests an actual event at the supplied location; it does not test a fabricated count or omit the temporal factor. No explicit `tau<K` clause is needed once the proved event support and bounded spatial index hold.

## 6. POWER and macro domain review

The source's domains can be established in a well-founded order; no POWER theorem needs a negative exponent or a base whose lower bound depends circularly on that very theorem.

1. Original base-32 masks have positive volume lengths. Their Sub calls receive natural mask/value expressions
2. `width>=1` gives `b=32^width>=32` by a valid POWER call. The growth equation strengthens this to `b>=64(K+1)` and `2half=b` supplies the exact half radix
3. Every SPREAD length is positive. Its stride-bound equation independently establishes `stride>=length+1`, making the copy-base exponent `stride-1` nonnegative. Its positive range gap supplies the strict input bound
4. All physical row, plane, z, patch-shift, and box exponents are nonnegative products or sums of positive dimensions, positive padding multipliers, and positive extents. Every such base is b or a previously established power with base at least two
5. Every geometric-series base is at least two, and its length is positive. Every AND operand is natural once these prior contracts hold. Partition outputs and differences are independently natural adapters
6. Sub's first POWER has constant base two and exponent `mask+1>=1`; its next bases are that positive power and that power plus one, hence at least two, and their exponents are natural values/masks
7. `pre`, `event`, `final`, the negative-shift quotients, repetition, and slack are natural adapters. The full-digit factors `b-1` and lower-half factor `half-1` are nonnegative before these masks are used
8. The target local coordinates and tau are natural adapters; the target point/time exponents therefore meet POWER's natural-exponent contract even before their geometric/time bounds are deduced

The six SPREAD margins are compatible with completeness: choose width large for the two conversion bounds and the growth requirement, then enlarge each independent box padding multiplier for the four physical reshape margins and the finite support. Those choices do not invalidate the width constraints.

## 7. Reproduction, omissions, and limits

Run only the fresh audit program, with assertions enabled:

`python -I /workspace/shared/sandpile-repeated-target-20261004/source-review/check_source.py`

The outputs are `receipt.json` and the saved `run.log`. An isolated replay reproduced the receipt byte for byte. `manifest.json` records hashes of the audit deliverables and submitted files. The source was not changed.

Source coverage is exhaustive: every residual, declared witness, macro interface, exposed port, arithmetic gate, and final sum-of-squares gate is checked. The checker did not completely expand all 2,251 sequential partial sums; instead it checks the exact literal SOS topology and exactly normalizes all residuals and their highest homogeneous squares. This proves the claimed polynomial identity and degree without unnecessary quadratic memory growth.

The report does not claim a new all-integer proof of the accepted Pell, Sub, AND, or SPREAD lemmas. It establishes exact compatibility with their approved expanded equations and reviews the new call domains. It does not materialize the enormous constructive Pell witnesses for a complete physical instance, rerun Lean, repeat every finite physical-loader or sandpile test, or independently certify the entire unrestricted target-firing theorem. Those semantic and theorem obligations remain with the accompanying reviews and the explicitly inherited arithmetic dependency. The gate count and degree are implementation measurements, not lower bounds on all possible representations. No real-witness equivalence, witness uniqueness, finite witness fibers, universal loader, or raw-program compiler claim follows from this source audit.
