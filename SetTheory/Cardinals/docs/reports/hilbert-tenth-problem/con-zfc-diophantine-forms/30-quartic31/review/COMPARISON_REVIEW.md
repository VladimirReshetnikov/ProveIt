# Pinned wave-3 comparison and independent Jones audit

Repository: VladimirReshetnikov/ProveIt. Commit: `ae3007ca4467011e0e051c84acb4a1dd13971b0e`.
Root: `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
Every source below is pinned, not a moving-main observation. `SOURCE_LEDGER.json` records the exact Git blob ID, verified local SHA-256 and byte count for 40 files. The eight tree JSON files inventory all packages. Root README was also read. No received Python or Lean code was executed, no compiler was installed and no repository state was changed. All executed audits here were newly authored and read inert JSON only.

## Current final synthesis (supersedes intermediate evaluator counts below)

The final audited synthesis uses the new31-variable normalized quartic, package19's whole compact943 coefficient tuple, sharper magnitude companions, and the fresh radix/Horner evaluator. It has9 nonnegative unknowns,1,840 operations, exact degree120724*5^32+366,404 fixed leaves, and index z_star=2^45933757. See FINAL_NINE_REVIEW.md and NU31_INDEPENDENT_AUDIT.json for authoritative final details. The same-polynomial nu32 control was subsequently reduced from2,915 to1,704 operations; older2,915 figures below describe an intermediate checkpoint, not the final frontier.

## Main findings

1. Package 18 really delivers an explicit ordinary polynomial in nine nonnegative unknowns. This is stronger than citing the existence of a nine-variable universal polynomial or supplying an unspecified recursively enumerable-set index. Its 348 fixed leaves have finite bounded recipes; no index is existentially uninstantiated. Those numbers are defined but not materialized.
2. Its headline polynomial is an unformalized, explicit specialization of Jones's `wset_iff_nine` at a normalized 32-witness quartic and input 1, followed by a newly proved two-radical finalizer. The public existential theorem `nine_unknowns` uses a different 58-witness generic route. These must not be conflated.
3. All eight packages have useful contributions under different size criteria. There is no scalar winner. The old 67-operation equation still beats every wave-3 single equation on operation count; the 59-operation system uses a different convention (comparisons are free) and more variables.
4. A new independent rewrite in this review evaluates exactly package 18's same polynomial in 2,915 live binary operations rather than 20,531, an 85.80% reduction. Variable count, fixed leaves, polynomial and exact degree are unchanged. This is an arithmetic-circuit improvement, not a new nine-variable representation theorem.
5. The substantive shared proof lemma in 17,19,20,21,22 is Pell saturation: a rational second coordinate in `J^2 V^2-(J^2-1)y^2=1`, with integers J>=2,V, is integral. It cannot be replaced by the false general assertion that rational roots of nonmonic integral quadratics are integral.

## Main comparison

Notation: u/e/d/o = supplied unknowns/equations/total degree/binary arithmetic operations. Degree treats fixed coefficient ports as degree zero. Each binary +,−,×, including fixed-scalar multiplication and squaring, costs one. Reuse and system comparisons cost zero. Most entries are positive-domain, Z and N are explicitly marked.

| Package | Characteristic contribution | Representative original metrics | Review status here |
|---|---|---|---|
|16 integer27|Smaller separating weight, signed-domain lifting|13/1/515/84; 27Z/1/1004/139|Both literal circuit counts and liveness independently verified; degree claims not rederived here.|
|17 primitive12|Sixteen separated primitive-element branches; rational Pell integrality|12/1/2601/167; 26Z/1/5265/229|Positive proof inspected: separation accounts for complex roots, primitive-element invariance recovers rational coordinates, Pell lemma restores integrality. Product modulo-four guard is necessary. Headline 12-circuit count verified.|
|18 jones9|Concrete Jones specialization and radical finalizer|9N/1/(161844*5^33+484)/20531; 12/1/1609/151|Nine-variable source formulas, index recipe, coefficient algebra, exact degree, count and liveness independently checked. Direct-12 circuit count checked.|
|19 wang943|Four-root saturation and much smaller materialized compiler tuple|12/1/1257/139; 26Z/1/2465/192; 15/1/44/76; 943 tiles,B=2^(5^10)|Prior parent construction. 12-circuit count independently verified in this pass. Compiler semantics/materialization are separate audits, not established by count checks.|
|20 root12|Outer main-root separation around inner three-root polynomial|12/1/1145/123; 13/1/515/84|Positive proof inspected: uniform bounds include complex inner roots, recover integer main root before inner integrality, then prove gamma>0. Literal 12-circuit count verified.|
|21 norm12|Two nested quadratic norms|12/1/1353/116; 12/3/1344/112; 26Z/1/2657/168|Positive/integer circuit counts independently verified. Other workers audit/consolidate mathematical improvements.|
|22 monic12|Monic resultant and cheaper retained-coordinate system|12/1/1529/117; 13/1/319/91; 16/7/24/59|Three circuit counts/liveness independently verified. 59-op transport shift proof inspected and valid conditional on inherited compiler theorem.|
|23 separating12|Odd scale and low-degree 27-integer polynomial|12/1/1369/144; 27Z/1/172/116; normalized 27Z degrees274/216 at114/115ops|Four literal counts independently verified. Signed-domain mathematics assigned separately.|

The integer26 and low-degree rows not independently fetched/count-audited in this pass retain the packages' stated metrics. The count audit includes fifteen chosen circuits across all eight packages; see its exact machine-readable list rather than inferring every packet was audited.

## Mathematical checks that matter

### Jones specialization

`primary/NineMain.lean` gives `wset_iff_nine` with degree<=4, normalized polynomial, admissible Index and positive dummy input. Its `varsOf_nat'` confirms exactly six positive shifts: g,h,s,w,i,j; epsilon,phi,n remain nonnegative. `primary/NinePoly.lean` matches the displayed R polynomial, two radicands, squared divisor and dividend, and positive margin. It also proves JF is nonzero for every integer intermediate assignment. The new finalizer reproduces that nonvanishing argument directly.

The finalizer is

F = [Theta^2-Omega^2(a0+V0^2 a1)]^2 -4 Omega^4 V0^2 a0 a1,
Omega=d(2m-1), Theta=dn+c-Omega(c+V0 V1).

Its factorization into four signed radical factors is an exact polynomial identity. If a factor vanishes, r0+V0*r1 is rational. For a nonzero sum, squaring isolates r0 rational and then r1 rational. For zero sum, strict separation |r0|<V0 forces the integral radicand a1 to have absolute value<1, whence both radicals vanish. Thus no square-class independence assumption is needed. Rational square roots of integers are integers. The offset Z=c+V0V1+r0+V0r1 is >=c+1, so the vanishing factor enforces divisibility and m>0. Conversely n=(2m-1)Z-c/d is a positive integer. Squared divisibility is equivalent to the unsquared condition over integers.

The index audit independently expands the 23 supplied quadratic residuals after x->x+1 and sums squares. It matches all 508 sparse symbolic terms, all 346 weighted coefficient records and their powers, and the 20-term bound s. The fifth residual equals 1 at the all-ones tuple independent of the four fixed ports, establishing normalization. Multipliers `(4-|alpha|)! product alpha_j!` are correct, including slack factorial. The bound `sum|c_alpha| <=24 sum rho_j^2=s-2` makes z=2^s admissible. u and y are explicit evaluations of the index polynomials, not unspecified parameters.

An independent symbolic leading-term pass, with all fixed leaves algebraically independent and all nine unknowns specialized to t, certifies every gate's leading term with no unresolved cancellation. Both the original and rewritten circuits have exact degree

161844*5^33+484 = 18841121345758438110351562984

and diagonal leading coefficient 2^328, independent of the fixed tuple. This gives an exact total-degree certificate, not merely a modular lower-bound diagnostic.

### Pell saturation and root bounds

Package 17's Pell proof writes J^2−1=d0*s0^2 with d0 squarefree. Rational z=s0*y is integral because its denominator squared divides squarefree d0. The ordinary integral Pell group then shows J=x_m dividing x_n implies n is an odd multiple of m: reduce/refelect the index modulo2m and use strict increase x_0,...,x_m. Consequently s0 divides the second coordinate. This handles the actual denominator gap.

Package 20's outer norm proof does not assume a recovered gamma is positive. It first bounds all complex inner roots |x|<S, uses L=HS+1 to force G a square, proves its selected root b positive, recovers rational auxiliary roots and Pell-saturates y, then derives H|(b-b0). Only afterward does first-Pell growth imply c>X and gamma>0. These ordering choices are mathematically important and not interchangeable with a bare resultant calculation. Its smaller-weight13 proof explicitly proves main Pell index>=3 before using the stronger k bound, avoiding the unjustified shortcut R<k from a weak signed bootstrap.

Package 22's 59-operation system uses z_old=z_new+1. The transport identity is exact. Soundness is immediate from a positive new solution. Completeness requires proving z_old>=2, which its proof obtains from C>0 and w>q>F after inherited Pell/compiler semantics. Thus this is a true positive-domain zero-set shift, not subtraction of1 from an arbitrary positive variable.

## New same-polynomial circuit improvement

Let T=calB, nu=32, L=5^(nu+1), r=5^nu. The digit polynomial is z times its complete homogeneous baseline plus346 sparse corrections.

1. Precompute p_j=T^(5^j) by p_(j+1)=p_j^5, using three multiplications per step.
2. Compute baseline weights v_nu=1 and v_j=v_(j+1)*p_j^4; then v_j=T^(r-5^j). The baseline is T^r*h4(T^r,v_0,...,v_nu), with the same ascending complete-homogeneous recurrence as the original.
3. Sort nonzero correction exponents E_i=L-expo(alpha_i) in descending order. Horner-recur A<-A*T^(E_previous-E_i)+c_i, then multiply by T^(E_min).
4. Evaluate needed fixed powers from shared radix-five digits. Cache products over each consecutive equal-digit run. These are multiplication-only identities; neither negative exponents nor division is introduced.
5. Preserve every downstream gate and semantic polynomial. Reuse the new power table in surviving q,ell,lambda and other pure-T power subgraphs.

The resulting `nine_optimized/nine_majorant_runs.json` has 2,915 live operations:664 additions,22 subtractions,2229 multiplications; nine unknown leaves,348 fixed leaves. The original had20531 operations. All35 named nodes matched on64 independent random fixed-leaf/input tests modulo four primes (2240 comparisons). Those tests supplement, rather than establish, the exact Horner and radix identities. The independent leading-term audit verifies unchanged degree uniformly.

This rewriter can be used on a later finalized Jones DAG with the same named digit-polynomial interface; it does not assume its semantic correctness and must be audited after any changed weights or parent quartic.

## Integration cautions

- Wave3 supersedes earlier directories. Pinned wave2 files survive in history and vendor copies; do not cite a deleted moving-main path.
- The full coefficient tuple must be moved together: beta=B−1,K0=D_C+B D_R,MC,and shifted MF. Never splice components between compiler variants or confuse native and shifted masks.
- A compact compiler radix exponent (e.g. B=2^(5^10)) is not the Jones witness parameter nu. Here nu=32, the number of normalized-quartic witnesses. Taking nu=9 solely because the compiler uses a small exponent is invalid.
- Positive, natural and unrestricted-integer domains are distinct. Shifting all nine natural variables by x−1 yields a positive-domain polynomial, but changes the circuit and requires its own count; package18 describes but does not ship that circuit.
- Materializing four backend coefficients does not materialize the much larger z,y index constants or every expanded coefficient of the final nine-variable polynomial.
- All wave3 mathematical reductions are ordinary proofs intended to formalize inZFC. None is a newly kernel-checked end-to-end theorem. Lean source inspection does not imply builds were rerun or that Lean soundness proves internal ZFC provability.
- The target equivalence does not establish consistency. Nor does consistency alone imply ZFC cannot prove its inconsistency; avoid an unsupported two-sided independence claim.
- Intake removal of duplicated files makes all eight delivered drivers incomplete in their placed directories. This is packaging/reproducibility, not by itself a mathematical defect. We executed none of those drivers.

## Artifacts

- `SOURCE_LEDGER.json`:40 exact pinned Git blobs, with local digests.
- `INDEPENDENT_REVIEW_AUDIT.json`: exact index and degree checks plus15 circuit counts.
- `independent_review_audit.py`: newly written audit implementation.
- `optimize_nine_circuit.py`: newly written data-only polynomial-preserving rewriter.
- `nine_optimized/AUDIT.json`: operation/liveness and residue checks.
- `nine_optimized/nine_majorant_runs.json`:2,915-operation version of the same original polynomial.

This note is a focused mathematical/source review, not a claim to have independently reproved the entire K215 calibration or native-window compiler.
