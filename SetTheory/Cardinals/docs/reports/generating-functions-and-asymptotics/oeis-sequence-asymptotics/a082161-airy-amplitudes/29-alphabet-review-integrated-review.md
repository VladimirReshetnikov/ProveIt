# Integrated mathematical review

Reviewed 2 October 2026.

## Verdict

**Pass for the mathematical claims as stated. No required content corrections.** The report proves an exact product comparison and transfers the published relaxed-tree order estimate to fixed larger alphabets. Its inverse theorem is an asymptotic enclosure with existence constants. It does not claim an amplitude equivalent or an effective threshold-rounding algorithm. The frozen singular-boundary calculation is a research observation, not a substitute for an amplitude proof.

This review covers the report's complete TeX source, the accompanying exact-check programs, and the claimed mathematics. Visual PDF quality and archive completeness are separate checks.

## Reviewed version

- Source: `article/larger-alphabet-automata.tex`
- Source SHA-256: `6cb07be19ea4d54a54588f2f3340e2bb5fe7e1a12821cc303a9ede4b7cd54069`
- Corresponding current PDF: `article/larger-alphabet-automata.pdf`
- PDF SHA-256: `168bb547f66da2008a771ad52053385c7f417f284c1a55da5a88a5615baae713`

The source hash pins the mathematical review. The PDF hash identifies the corresponding deliverable available during review; it does not by itself certify visual quality or build reproducibility. Changes to the source after this hash require a delta review.

## Exact counting and comparison

The auxiliary boundary b(-1,0)=1 is stated explicitly, correctly repairing the first-row ambiguity in the terse published recurrence. Without it the initial value would be B_1=2 rather than the correct B_1=1. The source correctly distinguishes n transient states from n+1 total states and restricts the comparison to n>=1.

The completed-run weights satisfy, exactly,

W_m(l)/(2V_m(l)) = 1 for l<k,

W_m(l)/(2V_m(l)) = 1 - 1/[2(m+1)^(k-1)] for l>=k.

Their positivity and the common triangular support justify induction in the positive convolution. Each history has one run at each successive level, so the exclusion losses multiply once per level; they are not multiplied once per individual horizontal step. The diagonal endpoint identities and the common trailing-run reconstruction are correct.

The lower product is positive for k>=3 and is bounded uniformly in k and n by (2 sqrt(2)/pi) sin(pi/sqrt(2)). The report carefully limits the inherited asymptotic Theta estimate to each fixed k: uniformity of the product constant alone would not justify a growing-alphabet asymptotic.

The finite-level approximation retains the exact weights for m<M and removes subsequent losses. Thus the omitted factors begin at j=M+1, as stated. The bound 1/[2(k-2)M^(k-2)] follows from the product inequality and the integral estimate. The conditional reduction to fixed-M ratio limits is valid; the report does not assert those limits have been established.

## Index conversion and logarithmic coefficient

The transient-state formula uses alpha=(2k-1)/3. Passing to N=n+1 total states while writing the factorial as (N!)^(k-1) changes the exponent to alpha-(k-1)=(2-k)/3. The report makes this conversion correctly.

With q=k-1 and lambda=C_k^(1/q)/e, Stirling's formula gives

log B_n = q n log(lambda n) + beta n^(1/3) + eta log n + O_k(1),

eta=alpha+q/2=(7k-5)/6.

The unspecified multiplicative constants in Theta become a bounded logarithmic error, rather than an assumed convergent constant. This distinction is maintained throughout the inverse section.

## Lambert-W inversion

For y large, t=y/[q W(lambda y/q)] solves f(t)=y for f(t)=q t log(lambda t). Its derivative is q[1+log(lambda t)]. The source uses the correction

nu=t-[beta t^(1/3)+eta log t]/[q(1+log(lambda t))].

Writing the correction as delta gives delta=O(t^(1/3)/log t). The Taylor remainder is

O(delta^2/t)+O((t^(-2/3)+t^(-1))|delta|)=o(1).

Consequently F(nu)-y=o(1), while F'(nu) is asymptotic to q log nu. A bounded logarithmic error therefore produces an O_k(1/log nu) location uncertainty. This proves the displayed inversion at sequence values and the existence of constants in the threshold enclosure.

The integer rounding is safe. If L=nu-K/log nu and U=nu+K/log nu, every sufficiently large integer below L has B_n<exp(y), and every integer at or above U has B_n>=exp(y), after K is chosen large enough. Any finitely many smaller indices are excluded by increasing the lower threshold on y. Thus ceil(L)<=I_k(exp(y))<=ceil(U). No unjustified equality with ceil(nu) is asserted. A shrinking real error can still straddle an integer, which is why the two ceilings must remain.

The injection L -> aL proves B_(n+1)>=k B_n for n>=1: all old residuals are retained, the new initial residual has larger maximum word length than any old residual, and different first letters give disjoint nonempty languages. The threshold is therefore well defined. The stated constants are non-effective existence bounds; the theorem supplies no certified numerical value of K or a universal finite starting point.

## Frozen singular-boundary calculation

The block matrices T_r=qI+S* for r<q and T_q=I+qS follow from the two jump sizes and the residue labeling. Direct multiplication gives the stated exceptional bottom diagonals of the right and left Jacobi products. Solving at the bulk squared edge k^2 yields right/left constants (q/k,1) for r<q and (1,1/k) for r=q.

Converting the corresponding zeros to physical coordinates gives r-q for r<q and -1 for r=q, hence the offset cycle q,q-1,...,1,1. The two profiles match within one step but their boundary offsets vary between residues unless k=2. These exact frozen identities are correct.

The source appropriately presents a possible boundary-scale tracking mismatch and the need for further cancellation or matched-profile analysis. It does not infer a rigorous asymptotic for the finite varying operator, a spectral contraction theorem, or an amplitude from the frozen calculation. The zero-pattern obstruction to positive diagonal symmetrization also holds for k>=3.

## Executed verification

The following supplied programs were inspected and rerun successfully:

- `verify.py`: exact signed/renewal reconstruction, all-cell comparisons, truncation bounds, and stated numerical terms for k=2,...,8 through 16 transient states
- `check_inverse_and_boundary.py`: exact rational singular-boundary identities for k=2,...,12, and high-precision checks of the explicit inverse model for k=3,...,8 at n=10^3,10^6,10^9,10^12,10^15

The inverse numerical tests concern the explicit model F, not effective enclosures for the actual DFA sequence. They support algebraic checking but do not replace the asymptotic proof.

The earlier independent renewal audit additionally checked all supported array entries through n=30 for k=2,...,8 and directly enumerated canonical acyclic automata for smaller sizes. Its script and output are included separately. Those direct counts agree with the recurrence.

## Scope and remaining questions

The review takes the published relaxed-tree Theta theorem as an external input; it does not reprove that paper's full computer-assisted Airy analysis. The report's bounded later-literature search is appropriately described without a universal novelty claim. No new source search was needed for this integrated pass beyond the earlier primary-source verification.

The outstanding analytic issues remain a limiting amplitude, fixed-defect endpoint-ratio convergence, and higher-order corrections. None is silently assumed in the main comparison, logarithmic formula, or inverse enclosure.
