# Report 51 independent manuscript audit

Date: 4 October 2026 UTC

## Verdict

Mathematical PASS, conditional on the explicitly imported source-17 finite scattering mechanism and source-18 complete fixed-input chart theorem. The final 19-page PDF passes all-page visual review, and exact reviewed bytes are pinned in FINAL-VERIFICATION.json. This is a manuscript and algebra audit, not formal verification, a general cellular-automaton implementation, or an independent proof of the imported classification.

The manuscript preserves the approved theorem and does not strengthen it to two or five total polynomial witnesses. Its newly explicit copied-input sum-of-squares construction, integer-domain preparation, canonical external encoding, full witness ledger, and empty-or-singleton natural-fiber proof are correct.

## Scope and sources

Read the complete Report 51 TeX, the frozen uniform proof note and prior adversarial audit, and the relevant inert pinned article sections. Compared the new exposition against the actual source-17 large-gap proof (especially lines 6083–6223) and source-18 interface and compiler (lines 6660–6910). No inherited or upstream program was run; no saved schedule was run; no frozen input was changed.

Verified frozen evidence hashes:

- Inherited article: 17d3c0d9b449c689f88c1dc082ffee9b116993e4f5585b65d52c4fe591b2d962
- Uniform proof note: 2e6484f4a2dbc0419e9662bf1ca02d4154469a1f4dcf93f4320f9951c9124962
- Science manifest: 0fb634cca9f665b44c3601509a6cef49391599064a9715164227fc475260be4c
- Prior independent-audit manifest: 7719ee3d73a9811975218309d61db5ec6e622977f3cc6197c76771f7c7edb085

## 1. Conditional boundary and uniformity

The title is supported by the abstract and theorem's explicit conditional assumptions. The report imports source 17's actual section mechanism, rather than inferring uniformity from a fixed-input normal form. The original connected mass-three seed library has span at most 4S. Its fixed B, N=4B+12S, and W=N+2B are independent of arbitrary initial gaps and are not defined circularly from all span-W seeds.

The current-gap condition D>N is sufficient at every live edge: at target contact the seed anchor lies within 4S of the target; the old marker is therefore farther than B+2S from the seed's entire fixed prefix. The residual-marker displacement is bounded and does not reverse marker order. For a periodic packet flight, D>N makes each candidate lower numerator positive. On a fixed gap residue, candidate times have the same leading coefficient, so eligibility and earliest phase do not require a hidden gap-dependent cutoff. The manuscript retains outward escape, inward small-gap reset, and compact-outcome long-flight branches.

Source 18 is used only for finitely many normalized bounded ordinary reset shapes. The fixed template may have a very large materialized history, but it is independent of arbitrary original coordinates. The report explicitly disclaims deriving uniformity from source 18 alone.

## 2. First contact and exhaustive initial dispatch

The signed/zero-drift first-contact interval is handled correctly. A nonzero drift is divided only by a fixed integer, its earliest count is clamped at zero, and the opposite bound tests candidate eligibility. Congruence refinement and affine comparison select one earliest arithmetic description. Fixed transients are included. Ties preserve all simultaneous physical contacts. For compact shapes with holes, the report uses occupied-site pairs rather than a false hull test.

The component mass partitions 4, 3+1, 2+2, 2+1+1, and 1+1+1+1 are exhaustive at mass four. The three-component case includes both simultaneous and single contacts. A safe seed's compact outcome is accelerated through an arbitrarily long flight rather than treated as a fixed-duration reaction. The uniformly bounded number of initial symbolic stages is justified.

Terminal independent profiles use one common phase period and one shared clock. Precontact half-open ownership, disjoint support at the actual contact time, and affine input-dependent entry times and anchors are used consistently.

## 3. Complete guards, contraction, and joint degree

The cycle minimum includes c_0 through c_p, retaining both all interior endpoints and the final endpoint. Counting natural n with a*n < d+b-N gives exactly K=max(0,ceil((d+b-N)/a)). Equality and K=0 are handled correctly. The previous complete cycle's final endpoint proves that the failed cycle still starts live. The arriving edge is included strictly before its first failed endpoint, which belongs to the reset.

The final gap is bounded by the last fixed decrement and N, while the imported mechanism preserves positive marker order. The normalized reset shape is therefore in a fixed finite family. Refining a residue and sign makes K affine in the external input; it is not retained as an extra free witness.

The clock

S_s(n)=T_*+n(Ad+C)+A*Delta*n(n-1)/2+A_s(d+n*Delta)+C_s

has joint total degree at most two. In particular the zero-net case retains n*d. No input-dependent coefficient multiplies n squared. Contracting-cycle bounds n<K(x) and within-phase bounds are affine. The manuscript correctly refuses to use t<Q(x) as a nonlinear chart-domain guard. Affine substitution n=K(x) preserves the degree bound.

## 4. Reset composition and uniqueness

The reset suffix is an additive composition Q(x)+t_o(z), a(x)+v_o(z), not substitution of a quadratic arrival time into another quadratic clock. The normalized shape removes unbounded relative geometry. Only the affine anchor and quadratic elapsed time remain external-input dependent. At most two template evolution parameters are needed.

The explicit half-open boundaries, first-contact tie rule, first failed endpoint, common phase clock, and Euclidean quotient provide exactly one chart point per physical time for each fixed input. Sorting by strict affine stationary-coordinate differences selects exactly one order even with repeated labels. The report expressly limits injectivity to fibers over the input; it does not claim that different initial configurations cannot merge.

## 5. Small masses, no unit, and empty input

The no-unit argument correctly distinguishes weight-two and weight-three singletons, which cannot split, from weight-four singletons, which can. All singletons and all complete states of diameter at most 2S belong to the finite normalized core. Outside it, exactly two independent weight-two walkers remain. Core-return repetition repeats the complete intermediate orbit up to translation. No fictitious stationary unit is introduced.

The report pads S to at least one and covers radius zero. Empty input has a one-clock vacuum chart t=z. That chart is compatible with the algebraic claim: for empty output the simple polynomial (t-z)^2 has exactly one natural zero witness z=t; incompatible nonempty output is the empty relation. The nonempty-input count is explicitly not applied at m=0.

## 6. Residues and the parameter ledger

All input residue tests are translation invariant and therefore depend on initial gaps. Pulling the residue of an integer-valued rational affine form (a*g+c)/d modulo M back to the numerator requires modulus d*M. The report states and uses this product, not an insufficient least common multiple of d and M.

A finite common H resolves all such finitely many pulled-back congruences. Each ordered input has one residue vector and one natural quotient vector in g_i=H*u_i+r_i, with u_i>=1 when r_i=0. These at most m-1 quotients do not cause multiplicity. Thus the report correctly distinguishes at most two free evolution parameters from at most m+1<=5 total natural affine-chart parameters. It does not claim two total raw-coordinate affine auxiliaries.

Dropping time from stationary-frame charts leaves affine-domain affine-output relations, whose existential projection is Presburger. This establishes only untimed stationary-frame uniform reachability. The original-frame addition delta*T is degree-safe for the timed compiler but does not imply untimed original-frame Presburger reachability. The report makes these limitations explicit.

## 7. Copied-input quartic and all-natural proof

Every signed external coordinate uses a canonical natural pair. These are fixed external inputs or outputs, not nonunique private difference-pair witnesses. For each chart, X^+-e*x^+ and X^--e*x^- have total degree two. Replacing external input coordinates everywhere in that chart by the copied difference makes every domain or output form a polynomial in private variables with numerical coefficients.

The constant lift f(v)-f(0)+e*f(0) multiplies only a numerical constant by the selector. Output forms retain degree at most two even when time contains a genuinely quadratic external-input term. The inactive gate contains every natural private coordinate: both signed-input copies, all initial-gap quotients, evolution coordinates, and inequality slacks.

At a natural zero, the selector sum is one, so exactly one selector is one without extra Boolean equations. Every inactive gate is a sum of natural quantities equal to zero and forces all its private quantities to zero. Its lifted forms vanish. On the active chart, copying fixes the inputs; the lifted domain equations recover exactly the intended constraints; and the pooled output equations recover its outputs. Canonical quotients and cleared-integer inequality slacks are individually unique. The chart theorem gives empty or singleton fibers. Conversely a chart point uniquely reconstructs all witnesses. This proves the unrestricted natural-fiber assertion; bounded fixture searches are only additional checks.

The order of operations is important and correct: positive domain denominators are cleared before a natural slack is introduced, and one common denominator clears the complete pooled expression for each output coordinate. Each residual has integer coefficients and degree at most two; its square therefore has degree at most four. Optional external canonical-pair product squares add no witnesses and preserve degree four. The literal SOS is globally nonnegative over the reals, but the exactness proof is only over natural witnesses. The report does not confuse these two statements.

When no chart survives output-label filtering, C=1 with no witnesses represents the empty relation. Invalid ordering is rejected by retained chart guards. The optional tagged/padded label packaging makes no optimized arity claim.

## 8. Exact polynomial ledgers

For J>=1 and m>=1, with k_h<=2, total inequalities I and total equalities H_0 including quotient equations, the exact natural-witness count is

W=J+sum_h(2m+(m-1)+k_h)+I=3mJ+sum_h k_h+I <= (3m+2)J+I.

The private per-chart count before selector and slacks is at most 3m+1<=13. The exact displayed residual-slot count is

1+2mJ+I+H_0+(ell+1)+J.

Optional canonical-input/output conditions add m+ell residual slots and no witnesses. Zero or redundant slots can be removed, so these are unoptimized construction counts. The manuscript's statement that the full polynomial witness count is neither two nor five is correct.

## 9. Fresh independent algebra fixtures

The new checker in this audit directory imports no upstream checker or article code. It passes:

- 531,441 witness tuples in [0,2]^10 for a signed-input two-chart fixture, across five canonical and four noncanonical input pairs
- 15 singleton output fibers and 865 sampled empty fibers in the bounded canonical cases; all noncanonical input pairs rejected by the optional canonical residual
- 13 canonical signed-output representation checks
- 2,904 constructive two-input chart points with canonical signed copies, parity gap quotients, two evolution parameters, integer inequality slacks, pooled rational output coefficients, and two ordered output coordinates
- 14,644 rational-affine congruence pullback comparisons
- Symbolic quartic degree and both witness/residual counts, including an actual degree-six naive lift and the retained zero-net n*d cross term

The complete receipt and checker hash are in CHECK-RESULTS.json. These are finite arithmetic fixtures, not realizable-CA examples, a rule-to-chart generator, or a proof by finite search. The manuscript accurately preserves equivalent limitations for the two frozen checkers and accurately transcribes their recorded counts.

## 10. Manuscript corrections and final verification

Three presentation issues were sent to the writer: a missing backslash before qquad in the packet profile, an overfull inline eight-witness tuple (not the ledger equation), and an enumitem negative-labelwidth warning. The writer confirmed corrections. Final text/PDF pins, rendered-page checks, and unresolved issues are recorded in FINAL-VERIFICATION.json. No mathematical correction or stronger theorem hypothesis was required.
