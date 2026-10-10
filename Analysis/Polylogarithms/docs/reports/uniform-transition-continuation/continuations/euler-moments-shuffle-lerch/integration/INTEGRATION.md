# Integration notes for Polylogarithms: Uniform Continuation

## Source revision and purpose

These notes refer only to ProveIt commit
`3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f`, at
<https://github.com/VladimirReshetnikov/ProveIt/tree/3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f/Analysis/Polylogarithms/docs/manuscript>.

The archive is a proposed continuation. It does not modify the source repository.
`proposed_status_updates.tex` contains individually marked replacement or insertion
blocks. Copy the selected block into its stated location after integrating the
relevant proof section. It is a patch-text collection, not a file to `\input`
wholesale: some blocks belong inside an existing theorem or figure.

The cautions about universal Euler errors, noncompact moment ratios, and
fixed-index zero expansions were mathematically justified at the pinned revision.
The new proofs supersede specific open-status sentences. They do not reveal a
flaw in the original restricted theorems.

## Proof sections and their placement

Chapter filenames below are relative to
`Analysis/Polylogarithms/docs/manuscript/chapters/`.

| Archive section | Suggested placement | Labels that the status text uses |
| --- | --- | --- |
| `sections/02_euler.tex` | A new Chapter 5 section after the real-order Euler material; `05-certified-computation.tex` currently inputs `05-real-euler.tex`. Earlier Gaussian discussions may use forward references. | `newEuler:lem:scalar`, `newEuler:thm:domination`, `newEuler:cor:sharp`, `newEuler:prop:rational`, `newEuler:prop:narrow` |
| `sections/03_moments.tex` | After the reflected-moment material in Chapter 7. `07-integration.tex` currently inputs `07-reflected-moments.tex`. | `sec:all-ratios`, `thm:all-ratio`, `eq:uniform-phase`, `eq:uniform-moment-expansion` |
| `sections/04_lerch.tex` | After the fixed-index concentration and eventual-zero material in Chapter 9; retain the later low-index sharp classifications. | `efflerch:thm:explicit`, `efflerch:cor:growing`, `efflerch:prop:terminal` |
| `sections/05_shuffle_and_identities.tex` | With the Gaussian shuffle/relation-matrix and frozen-candidate material in Chapters 4–5. | `oi:thm:integral`, `oi:cor:basket`, `conj:S10`, `sec:candidates` |

The joint and proportional moment results are present in the pinned **companion
report**, at
`Analysis/Polylogarithms/docs/reports/uniform-transition-continuation/sections/04-joint-moments.tex`
and `04b-proportional-moments.tex`. They are not direct inputs of the pinned
manuscript. The optional report updates below should not be mistaken for existing
Chapter 7 input locations.

The new moment proof states its inherited global slope lemma explicitly. Preserve
its attribution, the unchanged `integration/inherited_global_slope.tex`, the exact
verifier, and the replay record. The uniform expansion is a new consequence of
that inherited monotonicity theorem.

### Label and notation integration

The final proof sections have no label collisions with the pinned manuscript.
During assembly, the new shuffle section label was changed to `oi:sec:shuffle`
to avoid the manuscript's existing `sec:shuffle`. That correction is already
applied in this archive; no additional label rename is required. The theorem
labels listed in the table above also do not collide.

Use the manuscript's theorem styles and bibliography conventions when copying the
fragments. Preserve each section's explicit meaning of its local `F` notation:
`F_{a,b}` is the depth-two polylogarithm, `F(x)=-\psi(x)` is used only in the
moment argument, and `F_{n,k}^\rho` is the signed Lerch derivative normalization.
Do not identify those functions through a global macro substitution.

## Exact review anchors for the proposed text

The block IDs below match comments in `proposed_status_updates.tex`. Labels and
literal paragraph starts identify the source location without relying on page or
line numbers.

| ID | Pinned source and exact anchor | Operation and reason |
| --- | --- | --- |
| E1 | `05-subcritical-stieltjes.tex`, theorem label `subpick:thm:Gaussian-order`; final statement paragraph starting `This is a magnitude bound;` | Replace only that three-line caution. The magnitude theorem alone is still distinguished from the new comparison of every remainder. |
| E2 | Same file; paragraph starting `The numerical axis experiment finds`, immediately after the proof of `subpick:thm:axis-maximum` | Replace that diagnostic-only status paragraph with a reference to the new exact narrow enclosure. |
| E3 | Same file; complete `\caption{...}` immediately preceding `\label{subpick:fig:Gaussian-axis}` | Replace the caption only. Preserve the existing image and label; its shaded interval remains the original coarse bracket. |
| E4 | `10-discovery.tex`, subsection `Real-order geometry after the positive-difference theorem`; paragraph starting `The Gaussian experiments have also led to proofs` and ending `does not furnish that universal Euler bound.` | Replace the paragraph. Close the universal Euler question, retain the sharper critical constant, and keep quartic/Bessel questions open. |
| M1 | `07-reflected-moments.tex`; paragraph immediately following the proof of `reflected:cor:sharp`, starting `This fixed-$m$ corollary does not supply` | Replace the two-sentence paragraph. Retain its restriction for the old approximation and point to the different uniform algebraic expansion. |
| M2 | Same file; final paragraph under `\paragraph{Verification and remaining questions.}`, starting `The fixed-reflected-exponent signed remainder is now supplied` | Replace the remaining status paragraph through the end of that file. Do not alter the preceding verification description. |
| M3 | Companion `04b-proportional-moments.tex`; complete final paragraph headed `\paragraph{What remains open after this theorem.}` | Replace the paragraph. The all-ratio bridge is proved at algebraic accuracy; analytic simplification of the global slope certificate remains open. |
| M4 | Companion `04-joint-moments.tex`; paragraph headed `\paragraph{Editorial correction to the research status.}` | Replace that paragraph only. Preserve the theorem, its transition-specific polynomial expansion, and the separate optimal-truncation questions. |
| M5 | `10-discovery.tex`; after the subsection `Further positive kernels and approximation regimes`, immediately before `\subsection{A focused path toward formal verification}` | Insert a short new moment-status subsection. |
| M6 | Companion `04-joint-moments.tex`, first item under `Further research questions`, starting `\item Prove a uniform continuation of the transition when` | Replace the item with the remaining question about the older transition-specific polynomials beyond compact transition parameter. |
| M7 | Same companion list, item starting `\item Build a uniform approximation joining the interior saddle to` | Replace the item with explicit uniform matching between the proved regimes and their distinct error scales. |
| L1 | `09-zero-geometry.tex`; complete remark titled `What uniformity does not say`, following `zeros:thm:expansion` | Replace the remark. Its fixed-index/compact-scale restrictions remain correct; the new leading zero-location theorem has a different domain and error. |
| L2 | Same file; theorem label `zeros:thm:zeroasympt` | Insert after the complete proof of this theorem. Preserve the sharper fixed-index offsets and higher corrections. |
| L3 | `10-discovery.tex`; complete paragraph under `\subsection{Zero geometry beyond a fixed Laurent index}` | Replace the paragraph. Record the explicit sufficient threshold, the proved growing-index range, and the terminal-branch theorem. |
| L4 | `09-higher-zero-transitions.tex`; final paragraph starting `This finite sequence suggests further threshold questions;` | Replace this final paragraph while preserving the displayed sharp values for indices 1 through 7. The conjectural formula for general sharp thresholds remains unresolved. |
| C1 | `10-discovery.tex`; after the final paragraph of `research:sec:S8-rejected` | Append the new candidate-status paragraph. Keep the old rejected vector and its exact exclusion intact. |
| A1 | `10-discovery.tex`; end of the subsection `Certificates, integral structure and arithmetic evaluation` | Append the shuffle-lattice status paragraph. Its conclusion concerns the stated formal presentation, not independence of evaluated periods. |

## Mathematical status to preserve

### Euler constants

The new theorem proves the least constant uniform over `a,b>0` and all integers
`N>=1` is

`C_* = max_{b>0}(beta(b) + 2^(-b) eta(b))`.

For fixed `b`, the same expression `C(b)` is the least constant uniform in `a>0`
and `N`. Equality in the scaled bound occurs only after adjoining the outer-order
axis, at `(a,b,N)=(0,b_*,1)`. The positive-order inequality is strict.

Keep all of the following existing results:

- The constant-one theorem on its stated `a>=1` domain and the existing
  counterexamples to dropping that hypothesis.
- The sharper critical/subcritical constant `pi/4+log(2)/2` and its sharpness.
- The last sentence of the proof of `subpick:cor:sharp-critical`: the **same
  critical constant** does not extend to arbitrary supercritical orders. The new
  theorem uses the larger constant `C_*`; that caution remains correct.
- The fixed-pair scaled-error monotonicity theorem on its original domain.
  Scaled errors are not asserted to decrease for every supercritical pair.

The new exact brackets for the maximizing point and height supplement the
original analytic `1<b_*<2` bracket. Existing figures remain numerical plots,
even though the location and height now have independent exact certificates.

### Reflected moments

The all-ratio theorem gives relative algebraic error through every fixed order,
uniformly for real `0<=m<=n` as `n` tends to infinity. Reflection covers the other
half of the nonnegative quadrant, including either axis.

The new phase includes the exponential Jacobian term. Its finite-exponent saddle
need not equal the saddle of a previous phase that placed that factor in the
amplitude. Preserve the older phases and their stated domains. Do not promote the
fixed-`m` exponentially accurate or least-term results to uniform estimates for
growing `m`. The all-ratio theorem does not supply such an exponential error law.
Likewise, it does not automatically make the older transition-specific
coefficient polynomials uniformly accurate for every unbounded transition
parameter.

### Lerch and Stieltjes zeros

For integer `n>=2`, the new sufficient threshold is

`K_n = 576 n^2 (3n)^(2n-4)`.

For every integer `k>=K_n`, all `rho` in the closed interval `[0,1]` have exactly
`n` simple positive zeros. Every branch obeys logarithmic relative error at most
`8n/sqrt(k)`. The growing-index corollary holds for
`n <= alpha log(k)/log(log(k))`, for each fixed `0<alpha<1/2`.

This is a sufficient bound, not the least threshold. Preserve the much sharper
low-index results. In particular, do not replace the known index-two threshold
`k=1` by the conservative general value `K_2=2304` as though it were optimal.
The full moving-zero expansion for all `n=O(log k)` remains unproved.

The last positive zero moves strictly left as `rho` increases whenever that
terminal zero is simple and persists. In the saturated regime it is strictly
decreasing on `[0,1]`; no finite derivative at `rho=1` is asserted. Global
monotonicity of every nonterminal branch remains a separate problem.

### Shuffle structure and candidates

Integral equivalence to `diag(1,3,...,2m-1)` proves the arithmetic structure of the
specified shuffle minor. The related determinant and inverse have published
antecedents; retain the Zagier/Ma/Ma–Teo attribution. The formal quotient does not
assert linear independence of the corresponding values at `i`.

`S_6` remains unresolved. The retained `S_{10}` and `S_{12}` vectors remain
conjectural: their exact proximity intervals contain zero and cannot prove
identity. The rejected first `S_{12}` search vector is a different record with an
exact nonzero residual. Preserve that distinction and the pinned manuscript's
existing `S_8` rejected-vector certificate. A rejected vector does not exclude
all possible relations in its basket.

## Review and replay

Run the archive's documented exact replay commands before moving certificate
outputs into manuscript verification directories. Keep the frozen candidate
inputs, arithmetic precision, theorem dependencies, and full rational endpoints
with the files that use them. Floating-point diagnostics and plots should retain
their current labels. The source history is not being rewritten as though the
newly resolved questions had already been settled at the pinned revision.
