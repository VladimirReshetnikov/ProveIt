# Comparison of the eight packets and the combined construction

Pinned source: [ProveIt at 3b201cde](https://github.com/VladimirReshetnikov/ProveIt/tree/3b201cdea32d2c816f5f3d20734051f25fd3ef14/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms).

## Main conclusion

There is a concrete improvement beyond choosing the smallest existing packet.
Combine the **blank/Start-only removal of the input interface** in 06/08 with
the **ordinary-strong Pell equation** in 02. The result has fifteen positive
unknowns, six equations of maximum degree 28, and a 61-operation shared
evaluator. Its single-polynomial forms have either 69 operations and exact
degree 99, or 78 operations and exact degree 56. The full circuits and proof
are provided next to this comparison.

The 67-operation, degree-155 existing polynomial remains preferable if
operation count alone is the objective. There is no single winner across
variables, equations, degree, operation count, coefficient height, and proof
complexity, and no global minimality theorem is claimed.

## 1. Comparison convention and what was independently checked

All compact main forms in the next table quantify **strictly positive
integers**. A source's intermediate registers are polynomial abbreviations,
not additional unknowns or positivity requirements. Each binary +,-,* is
charged, including squares and multiplication by numerals. Fixed coefficients
and shared reuse are free; equality comparisons are free for systems.

We fetched the actual JSON circuits at the pin and independently parsed and
recounted 24 representatives. `audit_packet_circuits.py` treats downloaded
JSON as data, never imports repository programs, and checks dependency order
and exact gate counts. A separately implemented finite-field line substitution
attains all listed representative degrees. This corroborates, but does not
replace, the packets' symbolic uniform degree arguments. The receipt is
`PACKET_CIRCUIT_AUDIT.json`. Statements about ancillary domain conversions and
quadratic lifts below are identified as delivered results, not newly rerun.

## 2. All eight packets

Here a row `v/e/d/o` means positive variables/equations/degree/operations;
for a system, d is the maximum residual degree.

| Packet | Representative forms (v/e/d/o) | Main contribution | Limitation relative to the combined result |
|---|---|---|---|
| 01 explicit82 | 18/1/187/82; 20/9/42/72 | Direct authenticated specialization of the universal84 source; detailed original definition and a separate tag-system route | Keeps the input bridge and extra slack/root coordinates. It is a conservative baseline, not the smallest fixed-instance form. |
| 02 system63 | 16/7/28/63; 16/1/101/74; normalized product16/1/157/72; SOS16/1/56/83 | Fixed marker, merged gamma slack, absorbed2d, and particularly the ordinary-strong rank argument that lowers degree without raising system cost | Still carries the marker witness Z and budget equation. Squared-budget product variants preserve existence, not identical zero tuples. |
| 03 system64 | 16/7/28/64; SOS16/1/56/84; 15/1/295/82; 15/6/244/71 | Independently recovers ordinary strong rank and eliminates f by a norm/resultant construction | Its2d shift costs one more gate than02. Root elimination raises degree dramatically and does not beat inputless15-variable forms. |
| 04 poly73 | 16/1/156/73; 16/7/60/65; SOS16/1/120/85 | Linear affine marker guard, and a smaller direct two-sided normalized machine | Linear marker optimization is unnecessary once the input marker is removed. Its two-sided coefficient simplification is superseded by06's raw machine approach. |
| 05 fixed15-16 | 16/7/34/66; 15/1/295/82; 15/1/346/80; SOS16/1/68/86 | Constructive fixed-input inverse and signed-root/norm elimination; explicitly emitted integer-domain variants | Its15-variable forms save f but retain the input architecture;06/08 remove a different coordinate and attain lower degree/operations. |
| 06 blank67 | 15/6/60/61; 15/1/155/67; reduced15/6/46/62; 15/1/123/68; SOS15/1/120/78 or15/1/92/79 | Raw K215 blank tableau; no input normalizer; impossible End selector; fully numerical layout; cancellation of correction bit by band spacing | Strong normalization inflates auxiliary degree. Importing02's ordinary-strong proof fixes this without enlarging the six-equation evaluator. |
| 07 fixed70 | 16/1/169/70; 16/1/156/71; 17/8/28/61; SOS17/1/56/84 | Delayed repunit-sign recovery and the X=wq² scale; transparent low-degree system | Signed repunit machinery is not needed for the already-fixed q=beta J+1 inputless core. Its transparent system costs61 but uses two more variables and equations than the hybrid. |
| 08 start-only67 | 15/6/60/61; 15/1/155/67; SOS15/1/120/78; delivered34-positive-variable/25-quadratic lift | Independently discovers the same arithmetic as06; gives the best delivered positive-domain quadratic lift; proves Start uniqueness is unnecessary | Uses a larger normalized-machine coefficient backend. Its retained-index fallback and Start-only coefficient bindings must not be interchanged. |

Every packet's headline gate count in this table agrees with the independent
recount where the literal circuit was sampled. The two67-operation sources
are the same arithmetic after renaming, but **not the same numerical
polynomial**, because their fixed coefficients differ.

The03 and05 degree295,82-operation forms are likewise the same root-elimination
idea, up to their slack shift and different coefficients. The root elimination
is real, but not advantageous once the simpler inputless architecture exists.

## 3. Fixed coefficient algorithms and coefficient height

The coefficients are defined by finite enumerations and fixed integer
arithmetic, with no oracle, unspecified program index, or reference to whether
ZFC is consistent. Thus these are fixed individual polynomial definitions,
not existential choices of coefficients. However none of the packets
materializes the full K215 coefficient tuple; the algorithms terminate in
principle but are astronomically impractical to run literally.

| Packet | Compiled machine/cell alphabet | Cells | b,d with B=2^d |
|---|---|---:|---|
| 01 | Folded437-state,8-symbol machine | 3510 | Given by finite formula |
| 02 | Folded436-state,8-symbol machine | 3502 | 5^43,5^87 |
| 03 | Folded436-state,6-symbol machine | 2628 | 5^42,5^85 |
| 04 | Direct two-sided220-state,3-symbol machine | 669 | 5^35,5^71 |
| 05 | Folded436-state,10-symbol machine | 4376 | 5^45,5^90 |
| 06 | Raw K215,216 states including padded halt,2 tape symbols | 439 | 5^33,5^67 |
| 07 | Folded435-state,10-symbol machine | 4366 | 5^44,5^89 |
| 08 | Same-size normalizer,Start-only window language | 4366 | Given by finite formula |

Packet06 is the strongest existing coefficient backend. It does not need
input erasure or a one-sided fold. The fixed first K215 transition supplies
the Start window directly, and a center-valid but globally impossible window
fills the forbidden selector1 position. Its count is exactly
1,420,903,358,357,108,792,377 allowed windows. The changed clause-band gap makes
2D_C-D_R=3 modulo5 identically, removing the older conditional correction bit.

This coefficient-height gain is independent of the arithmetic improvement.
The hybrid circuit can use any fully proved compatible blank-input compiler
contract, but all four ports must be rebound together and the required
Start, carry, mask, transport and completeness interfaces proved. Arbitrary
positive constants satisfying the low congruences do not suffice.

All packets use the **shifted** high-mask source port
M_F^src=M_F^nat+B-1. Confusing those two masks changes the polynomial and
invalidates its coding interpretation. The ordinary-input marker constant
W0=2^(2d+b) disappears entirely in the inputless forms.

## 4. Verification and logical assumptions

There are four different levels of evidence, and they must not be conflated:

1. **Literal arithmetic:** finite circuits, exact gate counts, uniform leading
   forms, polynomial identities, and algebraic positive projection/lifting
   proofs. These are the part most amenable to small reproducible checks.
2. **Pell and finite-window mathematics:** soundness and completeness of the
   native compiler. These are mathematical proofs in research notes, not
   newly kernel-checked Lean/Rocq theorems in any of the eight packets.
3. **Machine endpoint:** the repository's K215 blank-halting iff finite ZFC
   refutation endpoint, mirrored by Lean/Rocq developments. The eight packets
   do not rebuild those developments or formalize the new complete reduction.
4. **Internal statement:** the ordinary coding arguments are formalizable in
   ZFC, establishing ZFC proves unsolvability iff Con(ZFC). One must not replace
   this argument by an unsupported assumption that ZFC proves Lean's soundness.

No consistency assumption is needed to prove the equivalence. If ZFC is
consistent, the resulting positive equation has no standard solutions, and
ZFC cannot prove that unsolvability by its second incompleteness theorem.
The further claim that ZFC cannot prove the existence of a solution requires
an appropriate stronger soundness hypothesis; it does not follow from bare
consistency alone.

Finite toy checks are not a demonstration of an accepting K215 computation.
Neither integer polynomial evaluation at arbitrary inputs nor small tableau
fixtures prove or disprove consistency. No packet has an end-to-end proof
assistant certificate of its new Diophantine equivalence.

## 5. Why the combination works rather than merely renaming counts

Packet06's source uses normalized strong

    f²-Delta i_n²c⁴=1,

and auxiliary coefficient (Delta i_n c²)², of degree46 before its interaction
with the auxiliary square. Packet02 instead uses ordinary strong

    (i_o c²)²=Delta(f²-1).

The isolated two equations are not equivalent: the latter can have rational
Pell coefficients before the main-index hypotheses are used. The hybrid proof
first derives c=psi_A(p)>A Delta² from the first/main norms and the index range.
The relaxed-rank lemma then supplies f=chi_A(m),p|m,c|m and
i_o c²=Delta psi_A(m), which restores the required auxiliary congruences.

Completeness has the direct positive map i_o=Delta i_n. Soundness decodes
the ordinary system independently; no reverse quotient i_o/Delta is assumed.
The inputless boundary C=0 is retained until index/transport sign recovery,
and only the valid weaker bound R<q⁴-q³+q²-1<E-2 is used beforehand.
These are the two delicate interfaces that make the combination substantive.

## 6. Pareto recommendations, not an absolute optimum

Among the reviewed compact positive-variable arithmetic forms, the following
are the useful choices after combination:

| Priority | Recommended presentation | Variables/equations/degree/operations |
|---|---|---|
| Small transparent system | New ordinary-strong inputless system | 15/6/28/61 |
| Fewest displayed arithmetic operations for one equation | Existing06/08 P67 | 15/1/155/67 |
| Intermediate degree/operation tradeoff | Existing06 P68 | 15/1/123/68 |
| Much smaller degree for only two extra operations | New ordinary-strong product | 15/1/99/69 |
| Lower-degree single polynomial with no new unknowns | New ordinary-strong SOS | 15/1/56/78 |
| Quadratic equations/quartic single equation | Delivered08 lift (further improvement under separate review) | 34/25/2; SOS degree4 |

The new system dominates the delivered small low-degree systems on the tuple
(unknowns,equations,degree,operations). The69-operation product does not
dominate P67 because it uses two more operations; rather it adds a new point
to the degree-operation frontier. Quadratic lifting trades additional
unknowns and equations for degree and is not directly comparable under a
single scalar score.

Compared with the previous01 attempt, the new recommended system drops
20→15 unknowns,9→6 equations,maximum degree42→28, and72→61 operations.
The new69-operation single polynomial drops18→15 unknowns,82→69 operations,
and187→99 degree. The already-delivered67-operation polynomial has an even
shorter evaluator but a higher degree155 than the new product.

These comparisons exclude coefficient bit length. With that charged, improving
the finite local-language encoding may matter far more than saving one gate.
They also do not contradict classical nine-variable universal-existence
results: those optimize another coordinate and do not supply the same compact
fixed coefficient circuit/low-degree tradeoff.

## 7. Domains and low-degree alternatives

Positive, nonnegative, mixed-sign, and unrestricted-integer counts should not
be compared without recording the conversion. Shifting each positive variable
by1 preserves variable count and degree but adds an evaluation gate per
coordinate. Replacing a positive variable by
1+u²+v²+w(w+1) costs three unrestricted integer variables and doubles its
degree contribution; one plus four squares costs four variables instead.

The delivered packets use these different choices. For example06's41-integer
forms retain tau,y as signed because they occur only squared and cannot vanish
at zeros;04 reports44 integers,05 reports45/48,07 reports64, and08's naive
four-square P67 conversion reports60. Those are different encodings, not
contradictory counts for one object. Further justified signed-coordinate
relaxations can improve these counts without changing the positive core.

Delivered quadratic lifts also use different domains:01 has180 naturals,
02 has79 naturals,03 has128 integers,04 has83 integers,08 has34 positives.
None should be described as uniformly better than all the others without
stating the domain and resulting single-polynomial degree.

## Reproducibility and source limits

Source READMEs, relevant proof notes and representative JSONs are retained
under `sources/`. `tree_manifest.json` records the pinned packet trees.
`overview_README.md` is the repository intake overview, not a substitute for
the independent recount or proofs. No downloaded repository Python was
executed. No huge coefficient expansion or full proof-assistant rebuild was
attempted. Repository placement omitted some byte-identical vendored files;
a fresh full reproduction needs the recovery mapping in its `PLACEMENT.md`.
