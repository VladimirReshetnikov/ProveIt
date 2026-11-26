# Final mathematical referee review

Reviewed: the actual manuscript `output/grh_transfer_2026-11-25/report.tex` and every file in its `sections/` directory, including the analytic target, frame certificates as displayed, inherited lattice and period assertions, and the stated evidence boundaries.

## Verdict

The main mathematical arguments are sound and the limits of the results are accurately stated. The review identified one hypothesis correction in the budget proposition and short clarifications to the analytic and source-modulus statements. All were applied to the delivered manuscript, as recorded below. No new nonabelian RH, unproved uniform frame estimate, or unverified Lean build is claimed.

## Resolution in the delivered manuscript

- The odd-cocycle budget proposition now assumes `b >= exp(1)`, `q0 >= 1`, and positivity of all divided parameters.
- The initial Mellin integral, its half-plane of convergence, the elementary `O((log x)^2)` bound, and the regularity for real `c >= 1` are explicit.
- The use of the source fractional lattice now explicitly restricts `q` to an admissible source cyclotomic modulus divisible by 229.
- The period-root discussion distinguishes compatible choices from independently selected principal roots and claims only the inherited norm identities where required.

The following sections retain the reasoning behind the review and its recommendations; they describe issues that have been resolved, not outstanding corrections.

## Required correction

In `sections/remaining.tex`, Proposition “Permissible odd-cocycle growth” assumes only x>1 and b>1. The conclusion “log X<=b makes this contribution negligible as x tends to infinity” does not follow if b approaches 1 rapidly.

Concrete repair: require b>=exp(1), or explicitly retain the source condition log b approximately x^epsilon for a fixed epsilon>0. Also state positivity of m,k,r,t,f,a and q0>=1 so every division and inequality has the indicated sign. With these conditions the proof and the constant 90 are correct:
tmk<=5r^2m<=90x^(21/2), fa>=phi(q0)x^12 b, giving x^(-3/2).

This correction was sent to root immediately. It does not affect the intended source-scale application.

## Analytic target: checked

The correct initial transform is
F(s)=integral from 1 to infinity of R_F(x)x^(-s) dx, initially Re s>1.
The displayed formula and the constant 1+gamma_F are correct. Near s=1,
-zeta_F'/zeta_F=1/(s-1)-gamma_F+O(s-1),
and the two principal parts cancel exactly. At a zero omega the residue is m_omega/[omega(1-omega)].

The dyadic positive-part estimate gives absolute, locally uniform convergence of H in Re s>1/2. The positive-part Landau proof is valid: the negative part is nonnegative and has a finite convergence abscissa; a real pole with nonpositive residue is incompatible with its positive real values, and a removable singularity contradicts Landau at the finite abscissa. For c in (1/2,1), the relevant residues have the needed sign. At c>=1, the continued transform is regular.

Recommended explicit additions:
- define the Mellin integral above rather than leaving the transform convention implicit;
- note that a_F(n)<=6 Lambda(n)<=6 log n gives R_F(x)=O((log x)^2), so the negative-part convergence abscissa is finite and at most 1;
- mention regularity at real c>=1 in the residue-sign sentence.

The Dedekind-zeta factorization, unramified Frobenius coefficient identity, Hecke realization of the two-dimensional S3 factor, and passage from zeta_F zeros to that factor are correct in the stated open critical-strip sense. Holomorphy of that factor is properly treated as classical, not newly proved.

## Frames and fields: checked

- The ordinary integral-frame obstruction M D^(-1) subset O_F is correct.
- The integral-lattice eventual converse via signed rank-one matrices plus a rational positive reserve is correct.
- The cubic discriminant, splitting-field tame inertia argument, and integral-basis inference are valid.
- The displayed eight-vector interpretation is seven distinct columns with one repeated. Optimality concerns M=229, not vector count, and is correctly stated.
- The unramified cyclic cubic base-change argument and unchanged root discriminant are valid.
- The fractional Hermitian trace-dual formula and projectivity over O_K are correct.
- The general projective Hermitian eventual-frame proof is valid; positive dimension now eliminates the earlier empty-maximum issue.
- The CRT local-generator lemma is correct.
- The source theorem in Grunwald is correctly presented as an existing internal result newly applied to this benchmark.

One scope clarification is recommended: before reusing the source lattice A0 and its primitive 5040th root, say that q is now an admissible source cyclotomic modulus divisible by 229. The unramified-field theorem itself remains true for every q divisible by 229; the subsequent application has the source's additional hypotheses.

## Period normalization: checked

The final text correctly distinguishes inheritance of norm identities from literal equality of independently chosen principal roots. Under cubic base change the defining quantity is cubed and f triples, so the old root is valid but the new principal choice may differ by a root of unity. All conjugate archimedean and p-adic norms agree. The two old unit witnesses therefore pull up to the induced CM type and may be prescribed in the projective frame theorem.

No tower-uniform estimate follows from this inheritance, and the manuscript correctly leaves that quantitative issue open.

## Evidence boundary

The manuscript accurately separates:
- exact integer/rational certificate checks;
- self-contained mathematical proofs;
- qualitative existence from quantitative estimates;
- source inspection/static scanning from Lean kernel execution;
- directly read earlier reports from predecessor summaries;
- prior class-group results from new work in this report.

No optional re-testing or new source edits were made during this review.

