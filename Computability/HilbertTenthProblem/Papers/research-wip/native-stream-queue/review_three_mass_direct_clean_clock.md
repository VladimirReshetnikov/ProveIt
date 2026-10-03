# Independent review of the four direct clean-clock sources

**PASS.** The complete source rewrite, paid ledgers, exact degrees and scoped first-clean-target theorem in [the author note](three_mass_direct_clean_clock.md) agree with the authenticated parent and clean-wrapper evidence. No author change is requested. This review independently reads saved source arrays as data; it imports or executes no author or predecessor Python.

The frozen author pins are:

- Python: `9627ffd85f79e5ed2c0174f716e95afcf1f92c0f3035e65c76aaa15f98af34b6`
- Receipt: `a360d1573dfb12b2e5fb3188bdce3a36e7029c4fc13b86b61969f34d2644b7d1`
- Note: `59efd3d56b794f8632c1da48c080083a750895e9897bf213662195e45861167c`

The [independent helper](review_three_mass_direct_clean_clock.py) authenticates all three author files and all 20 declared dependency files, including the actual parent trio, its twelve ancestor pins, the previous parent review and the placed clean-wrapper and clock proofs. The [receipt](review_three_mass_direct_clean_clock.json) binds this helper's own source hash. Older receipt fields that hash an instruction list are not mistaken for hashes of their Python files.

## Full source and interface checks

The independent reconstruction starts at the four actual `three_mass_target_free_height.json` packets. It checks both original time-port consumers (height and the final clock right-hand side), the unique old payload-port consumer (`5*y`), the sole radix literal and the complete old SOS. It then constructs the declared renaming `T→U,y→clean_final_payload`, replaces only the radix 131072 by 262144, appends the five bridge instructions, replaces only the last comparison's left operand and independently emits the full new SOS.

Every instruction, operand, comparison pair, interface, coordinate order and mapping table agrees with the saved author packet. Every gate and supplied coordinate is output-live. The new free coordinates are the two natural parameters x,U; moving the old y coordinate into positive existential F accounts for the witness increase. There is no supplied forward time hidden in the interface.

| Variant | M | A | Complete gates | Positive witnesses | Comparisons | Exact degree |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| inc2;dec2 |237|360|597|59|19|2344|
| zero3 |182|290|472|57|19|1192|
| nop |180|290|470|57|19|1192|
| positive3 |187|286|473|57|19|1192|

All 2,012 complete gates are independently recounted. Each full finalizer has 19 subtractions, 19 multiplications and18 accumulator additions. The sole source-cost delta is the five paid bridge gates, 2M+3A; none of the arithmetic used to extract the endpoint or packed clock is omitted.

The declared radix recipe gives max(131072,4768*30+2310)=145350, whose next power of two is262144. The source retains all old paid height/radix computations with that new fixed literal. These circuits are not asserted identical to the old fixed-radix polynomials.

## Complete algebra and actual clock extraction

All 72 retained comparison instances agree literally under the explicit coordinate/constant adjustment. Independent expansion of the actual five bridge gates gives

    D=2*Ctau+192*x+192*F+208.

The two complete SOS finalizers prove the all-value identity

    Q=P_adjusted−(Ctau−rhs)²+(D−rhs)².

The helper expands the full local correction in independent indeterminates Ctau,x,F,rhs; its coefficients are saved. This is an identity over every commutative ring, including signed or rational assignments. The adjusted parent has the new coordinate names and radix constant. It is neither the original parent polynomial nor an asserted positive parent zero. The correction is not dropped by appealing only to a shared zero set.

The 120 literal residue-map and physical-clock coefficient rows are separately derived from the four instruction tables, using N=6q+offset, state modulus5 and the actual guards. Their guard values are constant on each residue modulo 30. For every map-slope class the physical clock slope is fixed. A separate recursive affine expansion of each entire paid Ctau cone then verifies

    Ctau=c_base*W+sum_a(c_a−c_base)*Z_a+sum_s b_s*E_s,

in the supplied hats with every subtraction of1 included. Thus the clock arithmetic is checked against the actual physical tick coefficients, not merely the saved `mapping` metadata. No native constraint is used in this all-value affine equality.

Supplemental evaluations check 32 complete signed corrections, including 12 rational assignments, 576 retained residual values and the independently summed complete SOS in every case. These checks supplement the exact source and coefficient proofs.

## Exact degree certificates

The independent checker recursively computes the formal degree bound at every source node. It separately computes the coefficient at that bound after mapping supplied coordinate i to (i+2)z modulo1,000,003. A vanishing intermediate coefficient never lowers its formal bound. The output coefficients are

    667404,476833,476833,476833.

All are nonzero, establishing integer-polynomial lower bounds equal to the propagated 2344/1192/1192/1192 upper bounds. The full per-node trace digests agree with the author receipt. This is an exact total-degree certificate in all supplied coordinates, not merely a numerical degree bound or a calculation restricted to a zero set.

## Mathematical scope and ordering

I read the complete author helper/note, the current target-free-height proof, the placed clean-wrapper theorem and folded-clock addendum. The proof keeps the necessary dependency order:

1. Natural x,U and positive height slack give h=n0+U+eta≥2 and 0≤U<h before typing. The global equation excludes J=0. The old native pretyping bounds use only this height margin, the enlarged valid fixed radix and unchanged positive padded ports.
2. Typed current/next digits and chronological transport recover the final encoded payload by successive radix cancellation. No assumed target upper bound or supplied forward-time equality enters this step. Totalization makes an accepting chronology a first halt; deterministic current states cannot repeat, so its length is at most 30h.
3. The semantic forward time theta and clean-wrapper formula yield L=2theta+192(F+x)+208. The physical bounds imply L≤4768*30*h²+4608h+16. The exact identity 2308h²−4608h−16=(h−2)(2308h+8), valid already at h=2, gives L<B−1 with the enlarged radix. Since the new clock row yields U=L modulo B−1 and 0≤U<h, it forces U=L. No positive parent zero is assumed.
4. Completeness chooses an arbitrarily large new dyadic height, packs the genuine forward history, sets eta=h−n0−U and takes the positive clock quotient hat1+2(Ctau−theta)/(B−1). The prescribed native-AND theorem then supplies fresh positive native witnesses. This is an existential equivalence, not a bijection of positive witness fibers to the immediate parent.

The original clean-wrapper theorem supplies exact whole-configuration restoration, the two NOP bridges, no premature reverse exit and first-target semantics. It concerns the input-dependent target at the original absolute positions. The current four literal sources satisfy its fresh-entry and terminal-halt hypotheses. I do not reprove the underlying CA local-rule compiler or claim a compiled universal source table.

Thirty-six independently constructed genuine outer histories, at two chosen dyadic heights and several raw inputs, satisfy all three actual outer equations and the whole prescribed AND. The source path and physical ticks are derived directly from the instruction semantics, independently of the author's fixture constructor. Native Pell coordinates are placeholders; no enormous full polynomial zero is claimed numerically. These examples supplement, rather than replace, the general existence proof.

The author correctly limits the result to four fixed nonuniversal raw-input sources, the first exact clean target and integer witness domains. The report 21 comparison saves six operations and one witness from its historical folded sources; it does not revise those older counts. It gives no universal arithmetic bound, paid ordinary-input loader, rational-zero theorem, stationary target, later-return theorem or finite-fiber claim.

## Reproduction

From any directory, against the installed author files:

    python3 /absolute/path/review_three_mass_direct_clean_clock.py \
      --repo-root /absolute/path/Proofs \
      --expect /absolute/path/review_three_mass_direct_clean_clock.json

For a separately frozen author directory, add `--author-root DIRECTORY`. The author source remains a bounded CLI, with no maintained public API or hostile-call promise; its explicit rejection of optimized Python is accurately documented. The independent review uses explicit checks and passes both normal and optimized Python.

Writer and fresh normal and `-O` saved-receipt replays from `/` passed. No repository or frozen author files were modified. No archived code, ancestor builder or historical suite was executed.
