# Independent adversarial audit of ordinary repeated target firing

Date: 4 October 2026. **Verdict: PASS for the exact stated ordinary finite target-firing relation, conditional on the explicitly pinned constructive Pell theorems used by POWER.** No mathematical, domain, physical-input, emitted-source, carry, boundary, or target-parity defect was identified. This verdict is not a claim of a newly formalized Lean theorem, an executed universal loader, an input compiler, finite-foldness, real-domain exactness, or minimal resource counts.

The packet `/workspace/shared/sandpile-repeated-target-20261004` was read as data and kept unchanged. No submitted builder or checker, upstream program, saved schedule, or Lean program was imported or executed. Prior PASS reports were not substituted for the checks here. The fresh source auditor reconstructs the entire mathematical specification in a separate sparse-polynomial implementation. A separate fresh arithmetic checker constructs actual small POWER witnesses and tests arithmetic interfaces. An independently delegated semantic challenge supplies additional mathematical reasoning and finite probes; see `semantic-challenge/`. Its enlarged-radix two-site tests cover the complete dynamical tableau at macro level, not a materialized full raw-interface/Pell witness; the physical conversion is proved and checked separately.

## 1. Exact accepted statement

For a positive `InputPlus`, decode `InputPlus−1` through ten right-associated Cantor pairs into

`(p−1,q−1,r−1,T,d−1,e−1,f−1,D,ζx,ζy,ζz)`.

The six dimensions are positive. The tile stream has exactly the declared `pqr` radix-32 slots, each digit in 0–5, and the patch has the declared `def` slots, each digit in 0–15. Leading zero slots are allowed; nonzero higher slots are forbidden. The background is periodic on Z³ with those tile dimensions. The patch is added at `[0,d)×[0,e)×[0,f)`. The signed coordinate code is `ζ=2h+s`, with `s∈{0,1}`, for physical coordinate `h−2sh−s`.

The frozen polynomial has a zero at strictly positive integer witnesses if and only if the physical input is valid and **some finite ordinary legal toppling sequence fires the exactly supplied target**. A site may occur repeatedly. Neither a one-shot prefix nor global stabilization is required. The only free input is `InputPlus`; all box dimensions, duration, radix width, intermediate arithmetic values, and target event time are among the fixed witnesses.

The fixed implementation has 3,865 positive witnesses, 2,251 residual equations, 17,275 binary arithmetic gates, and exact degree 18. These are literal-source counts with fixed integer constants free, not minimality claims.

## 2. Independent exact source reconstruction

`audit_source.py` treats the submitted JSON as inert arithmetic syntax. It independently reconstructs the intended clause polynomials using sparse integer coefficient dictionaries. The reconstruction expands products and normalizes natural adapters; it does not invoke the author's Python expression machinery or rely on numerical polynomial fingerprints.

The following passed exactly:

- Every one of the 2,251 named residual polynomials
- All 186 macro interfaces: 138 POWER, 34 Sub, eight AND, six SPREAD
- All 44 exposed ports
- The complete set of 3,865 declared positive witnesses, with no duplicates or hidden extras
- Gate operations, reference legality and topological order
- Every residual square and the complete ordered sum-of-squares output
- Reachability of all gates, all witnesses, and the input from the output

The independently recounted gate ledger is:

| Part | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|
| Body | 4,537 | 3,681 | 2,305 | 10,523 |
| Sum of squares | 2,251 | 2,250 | 2,251 | 6,752 |
| Whole source | 6,788 | 5,931 | 4,556 | 17,275 |

The separate witness and clause decompositions also reconcile:

`138·26 + 34·5 + 8·3 + 6·4 + 59 = 3865`,

`138·15 + 34·3 + 8·2 + 6·4 + 39 = 2251`.

Thus the two physical radix conversions and the event-time target test are genuinely paid, including their nested arithmetic macros. Source inspection found only fixed-length construction loops; no input value, physical volume, witness duration, or coordinate controls source arity.

### Exact degree

The maximum normalized residual degree is nine. Exactly `patch.shift.eq8`, `patch.shift.eq9`, and `patch.shift.eq11` attain it. In each, the top homogeneous term is

`−4 p q r d e f tx0 ty0 tz0`,

where `tx0,ty0,tz0` are the positive source padding leaves before adding one. All other residuals have degree at most eight. Since the actual output is the checked SOS, its degree-eighteen homogeneous part is

`48(p q r d e f tx0 ty0 tz0)²`.

The coefficient is nonzero, proving exact degree 18 rather than merely a propagated upper bound. The degree histogram and all exact source matches are recorded in `source-audit-receipt.json`.

## 3. Arithmetic theorem and macro audit

### POWER

The inherited source is mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorems `matiyasevic` and `eq_pow_of_pell`. Its inert local source text was inspected and its SHA256 independently recalculated as `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`.

For each intended POWER domain `b≥2,e≥0`, the source uses `k=e+1≥1` and `m=b·out`. The first nine clauses put the three Pell equations, congruences, divisibility, and `k≤y` into the positive-index branch of `matiyasevic`. The exact integer Pell equalities imply the theorem's natural-subtraction versions. Four paired natural quotient variables represent arbitrary signed congruence quotients without excluding a sign.

The last six clauses give the auxiliary Pell equation, `w≥b,k`, strict `m<M`, modulus identity, and final congruence required by `eq_pow_of_pell`. The auxiliary Pell equality, `w≥b≥2`, and positive `g` force `a>w≥b`: indeed `a²=1+(w²+2w)w²g²>w²`. Consequently the polynomial `a−b` equals the theorem's natural subtraction. The theorem gives `b^k=m=b·out`, hence `out=b^e`.

For completeness, the constructive choice `w=max(b,k)`, `(a,wg)=Pell(w+1,w)` has `g>0`. The second Pell characterization uses positive index `k`, then index `2ky`, so all `x,y,u,v,s,t` are positive. The CRT parameter β is greater than one and congruent to one modulo `4y`; therefore `qb=(β−1)/(4y)>0`. Similarly `qv=v/y²>0`. The modulus slack is strict by the power theorem. All natural quantities are positive-leaf-minus-one adapters. Thus no positivity restriction in the emitted specialization discards valid powers, including exponent zero.

The fresh arithmetic checker constructs nine actual positive tuples: exponent zero at bases 2 through 8 and exponent one at bases 2 and 3. All 135 equations and 234 positive leaves pass exactly. The largest witness has 34,887 bits. These are tests of the specialization, not a replacement for the pinned all-integer theorem. Lean was not run.

### Sub and AND

For natural `M,V`, the source computes `R=2^(M+1)`, `Y=R^V`, `Z=(R+1)^M`. All binomial coefficients are strictly smaller than `R`. The two strict extraction bounds force the genuine radix-R digit at index V, and requiring this digit odd is equivalent to bit containment. This remains correct when `M=0`, `V=0`, or `V>M`; no quotient or remainder can manufacture a nonzero digit outside the expansion. The parity equivalence follows by factoring `(1+z)^M` over F₂.

For AND, Sub(X,Z) makes subtraction `X−Z` borrow-free. The two partitions leave only non-common residual bits. Sub(a+c,a) is equivalent to disjoint supports of a and c: subtracting contained a from a+c is borrow-free, so c has no bit in common with a. Thus the output is exactly `X AND Y`.

The fresh tests cover 17,920 exact binomial extractions, 2,187 actual positive Sub outer-witness constructions, and 64,000 candidate AND triples, including false proposed outputs.

### SPREAD and its substantive bounds

For power-of-two base B, `0≤U<B^n`, and `s≥n+1`, copy multiplication places digit `u_i` at exponents `i+(s−1)j`, for `0≤i,j<n`. These exponents are pairwise distinct because `s−1≥n`. The full-digit mask selects positions sℓ. The equality `i+(s−1)j=sℓ` gives `i−j=s(ℓ−j)`, and `|i−j|<s` forces `i=j=ℓ`. Therefore the output is exactly `Σu_i B^(si)`.

Both geometric values are uniquely enforced because their denominators exceed zero; the mask value is `Σ_(ℓ<n)B^(sℓ)`. This proof applies to full radix digits and therefore to composite row and plane blocks. It is not restricted to binary input digits.

Fresh checks cover 18,354 SPREAD instances at bases 2,4,8,32, with zero inputs, maximal digits, n=1, and minimum allowed stride. Another 238 cases explicitly compare fixed-base-32 input conversion to the corresponding enlarged-radix digit stream.

## 4. Exact raw physical input and domain order

The ten Cantor equations have all-natural coordinates and tails. Cantor pairing is a bijection on N², so the decoded fields are unique. The source does not silently receive a different recoded input. The six dimension leaves are positive, while T,D and target codes are natural adapters. The tile's bitplanes permit exactly digits 0–5: overlapping upper planes would place a forbidden second bit in the relevant radix-32 block. The patch full-low-four-bit mask permits exactly digits 0–15. Both masks disallow higher nonzero slots. Fresh finite checks include all two-slot tile plane choices, all 32³ candidate patch codes against a two-slot mask, and 300 eleven-field Cantor round trips.

The new radix is really `b=32^L`, with L positive. Two distinct SPREAD calls convert the original T and D with length pqr and def, respectively, and stride L. Their constraints give `L≥pqr+1,def+1` and strict original-code ranges. Thus they produce exactly the same physical digits at the powers of b. There is no free replacement tile or patch.

The exact half equation gives `h_b=b/2`; the growth equation gives `b≥64(K+1)`. Hence b is a power of two and `b>K`. In completeness, the dimensions and K are already fixed; choose L sufficiently large for both volume bounds and the radix lower bound. Increasing L changes only witnesses.

All arithmetic interfaces have a well-founded domain proof:

1. Positive dimensions give natural positive volumes and validate the radix-32 inputs
2. Positive L gives `b≥32`; the half and growth clauses strengthen this
3. The conversion SPREADs have positive lengths and their paid gaps make copy exponents nonnegative
4. Positive padding leaves plus one give `tx,ty,tz≥2`; every box side is at least four
5. Row/plane/copy radices are powers of two at positive exponents; the four spatial SPREAD gaps make every copy base at least two
6. Geometric values, interior masks, event/count streams, quotients, and slacks are natural; every use of `b−1` or `h_b−1` is nonnegative before applying Sub
7. The time end power uses `Q≥2,K≥1`; target local coordinates and event time are natural, so neither target power uses a signed exponent
8. Every Sub's own radix is at least two even at a zero mask/value, and every nested exponent is natural

The proof does not apply POWER outside its domain to rule out invalid assignments, and it does not assume small candidate counts to justify recurrence masks.

## 5. Physical geometry and finite-box boundaries

The extents are `hx=p d tx`, `hy=q e ty`, `hz=r f tz`, with sides `A=2hx,B=2hy,C=2hz`. The lower corner is period-aligned in each axis. The tile row spread changes row stride from p to A; the plane spread changes plane stride from Aq to AB. The patch uses the corresponding d,e,f strides. The second spread input range is justified explicitly: after row spreading the tile's greatest possible exponent is at most `A(qr−1)+p−1<Aqr`; the patch bound is `A(ef−1)+d−1<Aef`.

The three tile repetition factors have unique mixed-radix decomposition for all x,y,z positions in the box. They cover each position once, without coefficient collisions. Patch shifting moves physical origin to exactly `(hx,hy,hz)` and keeps the whole patch strictly inside: for example `hx+d−1≤A−2` since `hx≥2d`. Consequently every initial digit is precisely its physical height and lies in 0–20.

The three J equations uniquely give the interior geometric factors of lengths `A−2,B−2,C−2`; their product after multiplication by bXY has one bit exactly at strict interior indices. Thus every source count and event is zero on all six faces.

For any supported source index, subtracting 1,A,AB remains a nonnegative index in its frame; adding them remains below N=ABC. The x faces prevent row wrap, y faces prevent plane wrap, and z faces prevent time-frame wrap. Exact negative-shift quotients exist, and all six shifted streams put each count at its actual physical neighbors. Destinations may be on the shell, which is intended. Neither the first nor last time frame borrows or emits counts across a temporal boundary.

In a finite legal prefix there are no unrecorded outside topplings to include. Outside and shell vertices may be unstable after the prefix; that does not invalidate a legal prefix or require any final stability condition.

## 6. Arbitrary-count recurrence and malicious carries

Write `Q=b^N`, `W=Q^K`, `R=Σ_(t<K)Q^t`. The event mask fixes binary event digits, supported on the interior. Independently, the count mask puts the proposed Apre in `[0,W)` with arbitrary allowed digits up to b−1; it does not initially give small counts.

Construct canonical cumulative counts solely from E:

`a*_(t,j)=Σ_(s<t)e_(s,j)`,

`A*=Σ_(t<K,j)a*_(t,j)b^jQ^t`,

`V*=Σ_j(Σ_(s<K)e_(s,j))b^j`.

Because `a*_(t,j)≤t≤K<b`, all these are genuine digits and `0≤A*<W`. Telescoping gives `Q(A*+E)=A*+WV*`. Subtracting from the submitted recurrence gives

`(Q−1)(Apre−A*)=W(V−V*)`.

Since `gcd(Q−1,W)=1`, W divides `Apre−A*`. Both Apre and A* lie in `[0,W)`, so they are equal; then V=V*. This excludes every competing large-digit tableau, not only candidates that are already carry-free. It is independent of legality.

This also validates the frame-induction proof: the zero frame is forced modulo Q, after which each next count is at most t+1≤K<b and cannot carry. Empty layers, K=1, the last frame, and any proposed above-last carry are covered. No self-starting or cyclic history remains.

## 7. Repeated-own-firing legality and slack-carry attack

The exact available stream before own depletion has coefficients

`c_(t,v)=η(v)+Σ_(w~v)a_(t,w)`.

The proved prior counts give `c_(t,v)≤20+6t≤6K+14<b`. Its sum is therefore genuinely carry-free, including the initial stream repeated in disjoint frames. AND with `(b−1)E` selects precisely c and a at event slots.

The half-radix slack mask permits exactly `0≤s_(t,v)≤b/2−1` at event slots and zero elsewhere. Before any potential carry, the right-side coefficient in the threshold equation is at most

`6(K−1)+6+(b/2−1)=6K+b/2−1<b`.

Thus equality is coordinatewise and gives exactly

`η(v)+Σ_(w~v)a_(t,w)−6a_(t,v)=6+s_(t,v)≥6`.

Prior own firings are charged, while same-layer and future support are excluded. Conversely a legal event has slack at most `6K+8≤b/2−1`, so the restricted slack never rejects a legal prefix.

The restriction is substantive. If one instead used the full-digit slack mask, take two adjacent slots with zero background, patch heights `[0,7]`, K=1, E=1+b, Apre=0, and slack=b−6. Then `6E+slack=7b=Csel`: a carry fabricates the event at the height-zero target, which can never legally fire in this configuration. The actual lower-half mask rejects this slack. This is a sensitivity test of the safeguard, not a flaw in the frozen source.

## 8. Exact signed target, serialization, and completeness

The signed decode equations force `ell=half_extent+h−2sh−s`, with `0≤ell<full_extent`. Thus `j=ell_x+A ell_y+AB ell_z` is the unique target index in `[0,N)`. Separate powers give point=b^j and timepoint=Q^τ. Sub(E,point·timepoint) selects a genuine event bit at j+Nτ. Since E<Q^K, containment of that positive bit forces j+Nτ<NK, hence τ<K. The interior event mask also excludes shell aliases.

This test is independent of the parity of the final count. Retaining Sub(V,point) would incorrectly reject even positive target counts; the checked source does not do so.

Every member of a layer is unstable at the start of that layer. Serialize its finitely many distinct sites in any order. Before a site fires, earlier members only add chips to it, so it stays unstable. Repeating this through K layers gives an ordinary legal sequence, with exactly the certified cumulative counts and the marked target event.

Conversely, given any finite ordinary legal prefix containing the target, choose one event per layer, take K to be its length (or stop after the first target event), and choose a sufficiently large L. Choose independent tx,ty,tz sufficiently large that its finite support is strictly inside and all four spatial spread inequalities hold. These requirements are compatible and each extent is unbounded. The exact converted input, physical initial tensor, cumulative counts, neighbor shifts, legal slacks, and target time satisfy all outer clauses. Macro completeness supplies the remaining positive witnesses. No global termination, maximality, or terminal stability condition is introduced.

The `[12,4]` separator is accepted with sequence origin, origin, neighbor and counts `[2,1]`. Selecting the origin as target explicitly tests even final count. Two adjacent height-five sites cannot bootstrap a first event because the forced initial count frame is zero. A height-five periodic background with one added chip has a valid one-step target certificate although no finite global stabilization: any nonempty finite toppling support has an extreme vertex sending a chip to an untopped height-five outside neighbor. These examples distinguish the exact theorem from binary-prefix and stabilization relations.

## 9. Evidence, pins, and limitations

Fresh reproducible commands:

`python -I audit_source.py`

`python -I audit_arithmetic.py`

The separate semantic-challenge report and checker describe their own finite coverage and pins. All finite probes corroborate the mathematical proofs; none establishes the all-integer theorem by enumeration. A gigantic combined complete Pell witness for a full physical instance was not materialized.

Authoritative pins:

- DAG: `7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6`
- Builder, inspected only: `c37f455dc5a9a673fb2b980fb5dc41103f9a85e82a97c24cae296ed580fe9928`
- Architecture proof: `ccb59eac23edab6db8500814123c0e0e9486253d577f52be1e177c959efe5e9f`
- Source notes: `d71d365bea90b6be44b2d03f81849aa51dbff5b3f0840a862bdd8b38cfe80038`
- Inherited Pell source: `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`

The audit manifest records final hashes of the submitted packet and this independent audit. The claimed universal-loader identification and raw machine-program-to-physical-code compiler remain separate tasks; this audit concerns the raw physical input itself. All accepted facts are conditional only on the identified constructive Pell theorem, not a hidden arbitrary MRDP representation. No article has been produced by this audit.

## 10. Separate conditional computability corollary

The core verdict above does not depend on a universal sandpile simulation. I also read the separately prepared interface review at `/workspace/shared/sandpile-universality-interface-20261004/REVIEW.md` and its primary-source anchors. The following composition step is mathematically valid, with an additional explicitly stated dependency:

Assume the published vertex/alarm simulation, with the initializer endpoint corrections disclosed in that review, supplies a total computable reduction from machine halting to an exact target's first firing on a stable periodic tile with a finitely supported nonnegative bounded seed. Then its interface normalization is compatible with the audited theorem: translate seed positions by whole periods to make the finite patch nonnegative, translate the target by the same vector, retain the periodic tile, encode the bounded heights in base 32, and use the specified signed target and Cantor pairing. The normalization is finite and computable and preserves legal sequences by translation.

Under that published-simulation dependency, the set of positive inputs having positive-integer zeros of this **same frozen polynomial** is r.e.-complete. Membership is r.e. either by enumerating positive witness tuples or by enumerating finite legal sequences. Hardness follows by composing the computable physical reduction with the exact semantic equivalence established here. If the physical reduction fixes a universal-machine tile and varies only the finite seed and supplied target, the corresponding fixed-tile slice is likewise r.e.-complete.

This corollary does not identify that tile with another frozen loader, re-audit the published routing geometry, or include a raw program-to-physical-code compiler in the 17,275-gate count. It is a computable many-one composition statement, not an arithmetic parameter-substitution claim. The separate review discloses its two initializer endpoint corrections; neither those corrections nor an author-issued erratum is silently assumed to have been published. No fresh full-physical-graph audit is claimed here.
