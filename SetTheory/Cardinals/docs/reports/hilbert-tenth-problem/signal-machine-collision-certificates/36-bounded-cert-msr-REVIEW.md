# Independent manuscript and visual review of Report 66

Date: 4 October 2026

## Disposition

The combined article faithfully preserves the two accepted arithmetic continuations. No substantive mathematical defect, lost proof obligation, changed constant, or inflated scope claim was found. All 21 pages of the candidate PDF were inspected individually at 120 dpi and are legible, with no overlapping or clipped content. Both diagrams accurately illustrate the displayed formulas.

**Final disposition: ACCEPT.** The sole requested domain clarification has been applied: the definition of `F_b` and Proposition 8.2 now explicitly require integer base `b` and integer `n`. This was a manuscript wording correction, not a correction to either frozen source packet. The final-binding addendum below authenticates the corrected source and render.

## 1. Exact review boundary and method

Release reviewed: `/workspace/shared/report66-bounded-certificates-counting-release-20261004`.

Initial candidate bindings:

- Flattened `Report66.tex`, 58,976 bytes: SHA-256 `b06448940b4d106115dfb760dd1d3b32a7c00a66fdcb371a733b5a14b3b780a7`
- `manuscript/MANUSCRIPT_PINS.json`, 425 bytes: SHA-256 `579e372099ca2431392113f0a9c2a435ee76cc41c1f289e111eca349cf2b83f2`
- `/workspace/shared/report66-work-20261004/build3/Report66.pdf`, 420,299 bytes, 21 pages: SHA-256 `343202bffd9e0a41802e6b271897329d39711d2fbfd6232fc31fa66e79248a97`

All five manuscript modules were read in full. The complete bounded-certificate `AUDIT.md` and counting `REVIEW.md` were read, their relevant recorded evidence was inspected as JSON data, and the actual pinned Pell theorem statements at lines 760–766 and 860–864 were inspected as inert text. This review reconstructs the mathematical implications from the article and checks transcription against the accepted dossiers; it is not a new computational audit or a formal proof.

No science/audit checker, author/upstream mathematical program, native counter interpreter, physical simulator, collision schedule, or Lean was executed or imported. The only newly executed verification was ordinary file/hash/JSON/metadata comparison. The existing candidate page rasters and typesetting log were inspected. No release file was edited by this review.

`STATIC_SOURCE_CHECK.json` records a fresh comparison of all 40 frozen files and six frozen directories against `INPUT_PINS.json`: bytes, SHA-256, permissions and modification times all match. Read-access times are neither asserted nor used as preservation evidence.

The candidate build receipt is still labelled `BOOTSTRAP`; its dependency-lock and packaged-PDF-match fields are false. This review certifies the identified manuscript/render, not a subsequently completed archive, release-tool audit, or locked rebuild. Those release checks remain separate.

## 2. Bounded certificate and resource claims

Sections 2–5 correctly use `Q=(T+1)^2`, distinct from the counting height `X`. The clipping induction compares instruction-entry times `t<T`, where the representative is at least `T-t>0`. It makes no false assertion about equal final counters, final zero status, or transition `T+1`. The decrement/zero-test example proves sharpness of this clipping threshold, and the shifted threshold is correctly `T+1`. Horizon zero and initially halted programs are handled explicitly.

The factorial-cleared Lagrange basis has the correct sign and binomial coefficient. At each node its value is `(Q-1)!`, producing exactly the selected coordinates without an input-dependent denominator. The range and acceptance products include the empty acceptance set correctly.

There are exactly three declared positive witnesses and six residual slots. Soundness forces `(A-u)(u-K)=0` and `A-u=r-1>=0`, and therefore `u=min(A,K)`; the analogous statement fixes `v`. The class code and both slacks are then unique. Completeness supplies precisely those values. No hidden trace, selector, or denominator witness is introduced. The two horizon-zero polynomials have degree two and nine nonzero monomials.

The degree statement is an upper bound `4Q-4` for `T>=1`, not an asserted equality. The coefficient norm estimate `66 Lambda^4`, unsigned magnitude-bit bound `7+4 ceil(log_2 Lambda)`, and sparse-support ceiling `16Q-5` are preserved. The five disjoint support classes sum to `16m+11` with `m=Q-1`; slack terms are not double-counted. Expanded storage is bounded by `O(Q^2 log(Q+1))` bits.

The article explicitly pays for the `Q` Boolean table and at most `QT` native transitions in principle, with representative counters at most `2T`. Its direct `O(Q^3)` integer-arithmetic construction is described as an arithmetic-operation bound, not a unit-cost bit bound. It distinguishes a uniform effective generator from the separately compiled horizon-indexed polynomial family. It does not infer one fixed unbounded-halting polynomial, finite-fold MRDP, optimality, or a faster single-instance decision method.

## 3. Paid native-gap composition

All 26 positive leaves and 15 residuals of each POWER module are displayed. The count `13+2+11` is correct; natural aliases are explicit positive-leaf-minus-one substitutions, and the two copies are disjoint. The Pell index is the positive shifted counter `C`, while the output exponent is `C-1`.

The text-level specialization agrees with the pinned `Pell.matiyasevic` and `Pell.eq_pow_of_pell` statements. The nonzero-index branch, positive divisibility quotients, positive `t_p`, strict modulus slack, signed quotient adapters, and natural-subtraction issue are covered in both directions. The exponent-zero fixture is consistent. The all-exponent conclusion remains dependent on the imported theorem pair, with no new Lean claim.

The two gap residuals, two POWER copies and native polynomial give `2+52+3=57` positive witnesses, 60 total variables and `2+30+6=38` residual slots. The independent `w^8 g^4` monomials establish the exact degree identity `deg F=max(12,deg P)` without turning the separate upper bound on `deg P` into equality.

The decoded counters and compressed witnesses are unique, while a common shift of one paired congruence quotient supplies infinitely many complete witnesses. The article states this distinction correctly and does not claim finite full fibers. Physical instruction-section transport and its inherited timing/contact bounds remain explicitly conditional; arbitrary unencoded executions and collision horizons are not promoted into the arithmetic theorem.

## 4. Counting, endpoints and exact constants

Sections 7–12 count all encoded positive integer triples once each, independently of any program or halting predicate. They do not count witness tuples, primitive pairs, or distinct totals under the same symbol.

The primitive classification includes every exceptional low pair and the case in which both counters are `3 mod 4`. The gcd argument supplies the lower bound `d(a,b)>=2^(max(a,b)+1)`, positivity, primitive gcd one, and unique positive integer scaling. The ordered rays are disjoint by unique decoding.

The cancellation of the two low-counter floor corrections and the `2k+1` exceptional rays yield exactly

`A(X)=F_2(floor(X/10))+F_16(floor(X/16))-F_16(floor(X/80))`.

The digit recurrence gives the stated coefficients `b(b+1)`, `3b-1`, and `2/(b-1)`; the requested integer-base wording is the only issue in this portion. The shell law is `v_2(X)^2` when `5|X`, and `floor(v_2(X)/4)^2` otherwise. Represented totals are precisely multiples of 10 or 16, with distinct-scale density `3/20`.

The absolutely convergent reciprocal sum is `rho=3/5+68/1125=743/1125`. The fractional-part expression is nonnegative. Splitting at `L=floor(log_2 X)` gives the correctly strict bound `0<=E(X)<L^2+4L+6`. The article also correctly says the encoded fraction among all positive triples tends to zero.

The subsequence uses `M>=1`. Its cutoff is divisibility, not primitive size; `(3,3)` at total 16 below `X_1=20` is retained as a clear counterexample to the wrong size cutoff. The jump `(M+1)^2` and left-neighbor formula yield normalized cumulative liminf zero and limsup one with base-two logarithms.

The four exact `(alpha_r,beta_r)` rows are unchanged:

- `r=0`: `(34/15,1261/225)`
- `r=1`: `(61/30,2329/450)`
- `r=2`: `(31/15,1189/225)`
- `r=3`: `(32/15,1223/225)`

The proof derives them from the base-16 digit differences `(4,0),(8,0),(1,1),(2,2)` and checks `M=1,2` separately.

The inverse is explicitly with multiplicity. Its defining strict inequality gives `0<=rho D_n-n<rho+E(D_n-1)`, preserving the sharp coefficient. First and last shell ranks have respectively the exact deviations `[M^2+(2+alpha_r)M+beta_r]/rho` and `[alpha_r M+beta_r]/rho`. Thus the inverse slope and sharp limsup are both `1125/743`, with liminf zero. The different distinct-scale inverse `(20/3)n+O(1)` is kept separate.

## 5. Evidence and visual inspection

The article distinguishes retained packet computations, completed independent audits, its own English proofs, and report-owned typesetting. Recorded counts agree with the dossiers; none is described as a newly executed scientific check in this assembly. Audit acceptance includes the final sparse-support refinement and the stated dependency boundaries.

Every page was inspected at its supplied 1020 by 1320 pixel resolution (120 dpi):

- Pages 1–3: title, abstract, the three main theorems and contents are readable; the main theorem is not split
- Pages 4–8: clipping, interpolation, six residuals, boundary cases and support table are clear; Figure 1 has accurate class codes, tail shading, and the example `(7,9)->(16,4,6)` without overlap
- Pages 9–12: all POWER residuals, adapters, fixture, witness ledger, degree identity and physical boundary are readable
- Pages 13–15: counting definitions, floor/digit/shell formulas and Figure 2 are clear; the twelve bars through 80 agree with the shell formula, including the height-9 bar at 40 and height-16 bar at 80
- Pages 16–18: cumulative error, four residue rows, inverse statements and endpoint equations are legible; no displayed formula is clipped or collides with its number or footer
- Pages 19–21: audit scope, pinned theorem citation, future questions and bibliography are legible; hash strings and long references stay within the page

All figures and tables are meaningful and non-overlapping. No missing glyph, unresolved reference, overfull box, or underfull box warning was found. The sole log warning concerns disabled shell escape, which is consistent with the intended build boundary. Ordinary page-spanning proofs remain readable. The reviewed PDF has no substantive visual blocker.

## 6. Requested correction and stopping boundary

Requested wording: use “For integers `b>=2` and `n>=0`” at the definition of `F_b`, and explicitly retain those integer domains in Proposition 8.2. No equation, coefficient, source packet, audit record, or scientific claim needs revision.

Following that small clarification, bind acceptance to the final TeX/manuscript/PDF pins and visually check any changed pages. A different PDF, manuscript, or release archive is not authenticated solely by the initial-candidate pins above.


## Final-binding addendum

The corrected final manuscript and its 21-page PDF are accepted. The author applied exactly the two requested integer-domain clarifications and no other manuscript edit. Reversing those two strings in memory recovers the initial flattened-TeX SHA-256 exactly.

Final accepted bindings:

- Flattened `Report66.tex`: SHA-256 `a5e165a083800b93b56a122920c7e50e2304e1e27eea58080fbb4a3ad564a0b8`
- `manuscript/MANUSCRIPT_PINS.json`: SHA-256 `ad42c8401fac8b7f6c7e0e03ad8eb2de792862a39463f7f0e686daef68ec30e1`
- `Report66.pdf`: 420,317 bytes, 21 pages, SHA-256 `27209f12b5e2bf07c1851a5db538a6124c171467d92bff6f45b79fe85f65d69f`

The final PDF under `build4` and the PDF installed in the release have identical bytes. Its build receipt reports `PASS`, dependency-lock verification and release preservation. Packaging/archive authentication remains outside this manuscript review.

A fresh byte comparison shows that only page rasters 13 and 14 changed. Those two final pages were individually re-inspected at 120 dpi: both domain edits are present, all formulas and surrounding content remain correct, and there are no layout defects. The other 19 rasters are byte-identical to the pages already inspected in full. The final log still has no overfull/underfull boxes, undefined references or missing-glyph errors.

A final read-only comparison again confirms all 40 frozen source/audit files and all six pinned directories retain their bytes, modes and modification times. `FINAL_ACCEPTANCE.json` records the exact final bindings, packaged-PDF equality, two-edit check, and per-page visual disposition. No further correction is requested.
