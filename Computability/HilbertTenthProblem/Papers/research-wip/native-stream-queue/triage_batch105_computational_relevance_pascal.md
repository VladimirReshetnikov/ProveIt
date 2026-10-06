# Bounded relevance triage of four incoming report topics

**Frozen bounded triage.** No new Turing-completeness theorem, machine-simulation interface or Diophantine representation was found in the inspected guides and theorem statements. All four reports concern finite combinatorial enumeration or asymptotic analysis. A398540 does contain a computability theorem for one real growth constant; that is the only concrete computational result needing a terminology distinction. No further computational-substrate review is recommended from this batch on the evidence inspected.

This is a relevance triage, not a proof review. Only immutable commit summaries, README passages and selected primary TeX statements were read. No report program, saved fixture, scientific array or PDF build was executed, imported or evaluated; no repository file was changed. The receipt records the exact bytes, immutable Git blobs, limited read spans and search scope. External papers mentioned by the reports were not newly reviewed.

## Immutable reports and scope

Every path below is relative to `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/`; the receipt expands the exact README and article paths.

| Report directory | Immutable commit inspected | Relevant content |
|---|---|---|
| `a398540-proportional-placement-game` | `0480c618447a71ecd508a23cf96ac44251adaabe` | Fixed proportional placement policy, exact rational probability recurrence, asymptotic rate/amplitude, logarithmic corrections and computable rate enclosures |
| `a224182-unique-1432-order` | Write `bb5ca9433d452980a7983d17a573e8d60300a1c9`; corrected text `c437f27be5f35ef2f983c2cf82f97969a26849b5` | Permutations with exactly one 1432, growth order, explicit injections and a finite exact-image certificate; later wording corrections |
| `a279551-inversion-log-deficit` | `b54142448cb6157ba0d37a1fa76da1ab739de6f5` | Pattern-avoiding inversion sequences, stretched-exponential logarithmic deficits, non-D-finiteness and correction of numerical/proof-scope wording |
| `a005163-diagonally-symmetric-asms` | `77cec68db89773d7a2672644c1c9a4e1839a209d` | Symmetric alternating-sign matrix counts, fugacity polynomials, amplitude/pressure limits and weak-interlacing corrections |

## Relevance findings

**A398540.** The game receives n independent uniform numbers and makes n placements into ordered slots under one fixed proportional policy. Its first-step decomposition uses smaller subgames and yields positive rational winning probabilities W_n. The report studies their exponential rate and fixed-order logarithmic corrections. Theorem 35.1 states a terminating finite-coefficient algorithm that encloses the fixed rate R to any positive rational tolerance; it explicitly supplies no bit-complexity bound and reports no new numerical run. This is an approximation algorithm for a specified real constant, with no program/input-to-game simulation or acceptance encoding supplied in the inspected text. The heading “Other policies and universality” asks which positive size-dependent convolution kernels share the same asymptotic mechanisms. It is not a computational universality assertion.

**A224182.** The main theorem claims b_n=Theta(9^n/n^3), with explicit injection bounds and inverse-threshold width. The separate exact-image theorem concerns a bijection onto eligible marked pattern avoiders; its stated finite obstruction reduction is to at most eight points followed by a 2,074-core certificate. The phrase “universal obstruction reduction” in its trust-boundary paragraph means this bounded combinatorial reduction. It is not an unbounded interpreter or universal-machine simulation. The report explicitly leaves the proposed ratio 3/80 and D-finiteness open. Non-algebraicity of a generating function does not itself supply a computational-universality or Diophantine interface.

**A279551/A279556.** The objects are finite inversion sequences avoiding listed patterns. The main statements bound and refine n log(mu)-log(a_n), with growth constants 8 and 9, inverse thresholds and analytic boundary behavior. Commitment trees provide a counting construction; the inspected text does not turn them into a programmable computational substrate. The later commit corrects rounding and qualifies which deficit bound is used, without introducing a new operational representation.

**A005163.** The matrix terminology concerns enumeration of diagonally symmetric alternating-sign matrices and a fugacity polynomial for diagonal statistics. The primary leading-equivalent theorem and guide discuss amplitude, pressure and interlacing. They do not give matrix-semigroup mortality, word acceptance, or a Diophantine compiler. The later source corrections remain within analytic/combinatorial and numerical-evidence scope.

A full-text keyword scan of these eight immutable README/TeX files found no occurrence of Turing, Diophantine, undecidability, halting, register machine, counter machine, automaton or simulation under the exact case-insensitive patterns recorded in the receipt. The broader universality/complexity matches were read in context where relevant. This scan supplements the explicit statement reads; it is not a proof that no future encoding could use these objects.

## Retained source corrections and questions

**Remark 1 (A398540 source-recorded refutations).** The guide records corrections to Serra's prefactor sqrt(2pi), approach from below, profile interpretation of an integral equation, pure inverse-power expansion at higher orders, and a log-convexity/log-concavity reading. It also leaves optimality, other kernels, effective constants and the proposed S_A=1/12 open. These are attributed report statements, not newly certified results of this triage. No claim that every possible placement policy lacks computational universality is made here.

**Remark 2 (A224182 source-recorded boundaries).** The guide says the cited deletion argument only justifies an n^2 fibre factor, and records nine preimages of a size-seven avoider; it does not thereby refute the separate unproved factor-n inequality. The later correction preserves three earlier wordings: the split proof belongs to the manuscript itself; the staircase range is x>=b_4=1; and numerical extrapolants straddle the cited interval rather than lie within it. The limit ratio 3/80 remains open. None of these finite or asymptotic claims was rechecked numerically here.

**Remark 3 (A279551 source-recorded corrections).** The guide retains the first rounded values 1.083 and -3.05 and corrects them to 1.082 and -3.04. It restricts the “upper half suffices” statement to b>0 and identifies the comparison root in its proper exponent normalization. The finite numerical evidence and analytic proof are not recertified by this triage.

**Remark 4 (A005163 source-recorded corrections).** The guide replaces unqualified interlacing by weak interlacing; strict interlacing and root simplicity remain open beyond the reported finite tests. It retains the amplitude-estimate rounding correction, the distinction between individual boundary errors and their four-term maxima, and the distinction between a half-mass finite root measure and its normalized version. These corrections do not concern computational completeness.

The next computational research target should remain the existing group/word-to-arithmetic bridge rather than these reports. That is a relevance recommendation based only on the bounded scope above, not a certification of the reports' mathematics, archive placement, numerical evidence or citations. Root read all 40 lines of this note and passed its bounded scope, and directly checked game article lines 3063–3075 and 3150–3153 plus unique-1432 article lines 967–983. Root also reviewed the metadata structure and bindings; separate byte/Git/span authentication does not widen this scientific scope. Only status/provenance changed afterward, and this pair is now frozen.
