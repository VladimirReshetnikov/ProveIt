# Foundation and adapter audit

Audit date: 2026-10-23. Repository snapshot: `124c07c0b77a9e20e84676514d8b1ff78536ea3f` (root should confirm its exact checkout pin). All paths below are relative to ProveIt.

## 1. What the checked endpoint actually establishes

`Computability/DiophantineConsistency/Lean/DiophantineConsistency/ZFC.lean` proves unconditional external Lean equivalences between its `HasNaturalZero` predicate and `BProv ZFCax_s [] Form.fBot`. It defines `ConZFC` as the negation of that actual syntactic proof predicate. The nine-slot polynomial is selected through `Classical.choose (Jones1982.nine_unknowns hA)`; the 58-slot quartic is similarly chosen from `rePred_quartic58`. The existence arguments do not assume consistency.

These results do not export numeral coefficients. The classical choice definition of a representation of a constant predicate is insufficient by itself to identify an arithmetic equation with a fixed supplied coefficient tuple. In particular, a classical selector is permitted to choose the constant polynomial 0 or 1 depending on the truth value of the constant predicate, even though the constructive MRDP proof supports an effective route. The executable coefficient compiler tracked by `COMPILER.md` has not yet completed that route.

The local checked P69/P73/P75 reductions are stronger than sample comparisons: their Lean theorems prove equality of complete positive zero sets with the literal P67 baseline. They do not establish the native-window compiler-to-ZFC bridge. `STATUS.md` expressly lists both that bridge and a derivation in the object-language ZFC proof calculus as open formalization obligations.

This distinction does **not** refute an ordinary mathematical proof formalizable in ZFC. A paper can compose finite simulation, integer arithmetic, Pell theory, and the established foundational calibration without presenting a kernel-checked object-language proof. Such a paper should state that proof level and its imported theorems explicitly.

## 2. Exact semantic dependency chain available to an adapter

1. Literal K215 transitions represent a particular blank-tape computation. The checked endpoint is `BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`. The active consistency bridge also uses the concrete six-register enumerator, `KEndpoint.c222_iff_zf_refutation`, and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
2. The ordinary Wang943 language theorem turns that blank computation into a marked periodic tiling. The origin contains Start. A designated second tile is globally impossible; forbidding it therefore does not discard a genuine tableau. Soundness permits arbitrary periods and multiple marked strips; completeness chooses a padded rectangle with one Start.
3. The native coefficient adapter converts that language into two mask disjointness conditions and the exact transport relation. Four ports must be rebound together: `beta=B-1`, `K=DC+B*DR`, `MC`, and `MF_source=MF_native+B-1`. In particular, `MF_source` is not the native high mask.
4. The Pell/mask arithmetic constructs P67 and related positive systems. Its ordinary proof is retained in package36 `proofs/INHERITED_P67_PROOF.md`, `proofs/INHERITED_PELL_AUDIT.md`, and `proofs/INHERITED_ORDINARY_PROOF.md`. Package36's `coefficients/PROOF.md` proves the newer complete coefficient binding against that interface. Package44's `native/PROOF.md` supplies a different complete binding by aggregate complement coding.
5. The retained16 system and its gate-introducing quadratic31 lift preserve positive solvability. The successor substitution `p_i=n_i+1` transports all positive coordinates to nonnegative digit coordinates. The parent equations are the explicit 22 quadratic rows in package40 `report.tex`, section 2. The row ordering places a residual with value +1 at the all-zero tuple last.
6. Quadratic digit packing produces a source divisibility instance. Its universal mathematical requirements are selected monomial isolation, band isolation, bounds valid for every nonnegative digit tuple, positive leading coefficient, and unique digit recovery. The polynomial finalizer may then use Sun's integer reduction or the proved Jones natural-variable route with its stated domains.
7. Negating the resulting existence equivalence gives the desired absence-of-solutions equivalence to syntactic consistency. Nothing in this chain proves either side alone.

The foundational calibration includes more than finite simulation: the existing project documents mention a seed/quotient-model construction, first-order completeness, and the ZF/ZFC refutability equivalence via constructibility. Do not describe the entire endpoint as only a finite circuit check or derive it from a blanket assertion that ZFC proves Lean sound.

## 3. Strong-square relaxation: the exact lemma

This is the key distinction between P67 and the retained16/quadratic31 parent. Let A>=2, Delta=A^2-1, and let

    c=psi_A(p),   p>=1,   c>A*Delta^2.

Suppose i,f are positive integers and

    (i*c^2)^2 = Delta*(f^2-1).

Then there is m>=1 with

    f=chi_A(m),   p|m,   c|m,   i*c^2=Delta*psi_A(m).

The conclusion does not say `c^2 | psi_A(m)`. The weaker conclusion above is precisely what the signed auxiliary-index argument needs.

### Proof of rank recovery

Write Delta=d0*s0^2 with d0>1 squarefree. Since s0^2 divides (ic^2)^2, s0 divides ic^2. Squarefreeness then implies d0 divides (ic^2)/s0. Thus y=(ic^2)/(d0*s0) is an integer and f^2-d0*y^2=1.

Let F+y0*sqrt(d0) be the least positive integer-coordinate norm-one unit. Every positive integer-coordinate unit is a power of it: reduce by the appropriate power and use its minimality. For some e>=1, A=chi_F(e), s0=y0*S with S=psi_F(e), and Delta=(F^2-1)S^2. Pell composition gives psi_F(ep)=S*c. For some u>=1, the relaxed solution gives

    f=chi_F(u),   ic^2=(F^2-1)S*psi_F(u).

Set T=(F^2-1)S=Delta/S and g=gcd(u,ep). Strong divisibility gives

    h=gcd(psi_F(u),psi_F(ep))=psi_F(g).

Because c^2 divides T*psi_F(u), the number gcd(c^2,T*psi_F(ep)) divides T*h. The former gcd is gcd(c^2,Delta*c)=c*gcd(c,Delta)>=c. Hence h>=c/T>=c/Delta.

If g<ep, then 2g<=ep. Pell doubling and monotonicity give

    2*h^2 < psi_F(2g) <= psi_F(ep)=S*c < A*c.

But h^2>=c^2/Delta^2>A*c by the independently supplied size bound. Contradiction. Therefore ep divides u. Write u=em; then p divides m and composition yields ic^2=Delta*psi_A(m).

### Divisibility of the auxiliary index

Write m=p*t and D=chi_A(p). Expanding `(D+c*sqrt(Delta))^t`, and dividing its square-root coefficient by c, gives

    psi_A(pt)/c = t*D^(t-1) (mod c).

As gcd(D,c)=1 and c^2 divides Delta*psi_A(m), this implies c divides Delta*t. On the other hand,

    c=psi_A(p)=p*A^(p-1) (mod Delta),

and gcd(A,Delta)=1, so gcd(c,Delta)=gcd(p,Delta). This gcd divides p. Consequently c divides p*t=m.

### Why the large-index hypothesis is available

The blank-source proof establishes the first Pell index n>=(R-1)/2>=24 before using the auxiliary norm, and compares P0=2XY^2+1>A with c>k to obtain p>n. The elementary estimate psi_A(p)>=(2A-1)^(p-1) therefore gives c>A*Delta^2 with considerable margin. There is no circular use of the recovered target p=R.

### Completeness and the exact source

Starting from the normalized P67 strong witness `f^2-1=Delta*(i_old*c^2)^2`, set `i_new=Delta*i_old`. Then `(i_new*c^2)^2=Delta*(f^2-1)`, and the auxiliary coefficient `Delta*(f^2-1)` is unchanged. Thus the whole original positive witness can be transported.

Full original proof: `Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md`. Blank-source specialization: package36 `proofs/INHERITED_ORDINARY_PROOF.md`, sections 4-7. I found no squarefreeness gap or illicit cancellation in this proof.

## 4. Boundary conditions that a new short adapter must retain

* The supplied witness domain is essential. P67 is over fifteen strictly positive integers. Signed extensions have their own proofs and do not follow merely from the formal polynomial expression.
* The transport factor being an integer unit only implies C>=0. The boundary C=0 can give transport value -1. The index-recovery argument must first establish Nk=+1; only then is C>0 obtained.
* The pretyping bound available after blank specialization is `R<q^4-q^3+q^2-1`, not the stronger historical bound `R<q^4-q^3`. The proof order recovers p=R before removing index wraps, so E>R+2 suffices.
* The asymmetric scale X=wq must first be shown equal to 2^R. Only afterward does q^3 divide X, allowing the symmetric half-binomial kernel to be reused.
* A coefficient replacement that is valid on the strong-norm locus is not a polynomial identity globally. Prove that either full zero set forces the strong norm to +1 before using the replacement.
* Fixed coefficient recipes must be independent of whether K215 halts. Recompute downstream Jones index constants after rebinding a native tuple.
* A parameterized proof's numeral ports can be treated as algebraically independent when checking expressions and degree upper bounds. The final nonzero leading coefficient must still be certified for the actual fixed tuple.

## 5. Support-aware packing lemma audited

Let w0=0 and w1,...,wn be distinct positive integers, all at most W. Let S be the union of padded degree-two monomial supports of all residuals. Require that every alpha in S has a weight sum unique among *all* unordered pairs of indices 0,...,n. Collisions between pairs outside S are harmless.

For C(Z)=(1+sum_i x_i Z^wi)^2, a selected coefficient is exactly `(2!/product_i alpha_i!)*x^alpha`, with alpha padded at coordinate 0. Consequently a reversed coefficient `product_i alpha_i! * p_alpha` extracts `2*p_alpha*x^alpha`. With target rows H_j spaced by 2W+1, every selected target coefficient is exactly twice its residual and no other row contributes.

The nonselected collisions do not increase the existing global carry bound: all coefficients of C are nonnegative and sum to `(1+sum x_i)^2`. Coefficients of the reversed packing remain bounded by 2H because selected support exponents are isolated and row bands are disjoint. Therefore every product coefficient has absolute value at most `2H*(1+sum x_i)^2`, exactly as in the complete Sidon proof.

Distinct positive weights preserve unique digit recovery. The last row's constant coefficient +1 remains the unique highest term in the reversed packing, since no positive coordinate has weight zero. This is the specific property required to retain positive source bounds. Coordinate weights must not be sorted without applying the same permutation to all residual coordinates.

This support-aware weakening is a valid substantive improvement over demanding that all padded pair sums be distinct. Its finite certificate must test each selected support pair against all 528 pairs, not merely against other selected support pairs.

### 5.1 Further certified overlap of row bands

The final adapter also relaxes uniform row separation. For targets H_i and row j, require that

    H_i-H_j = weight(beta)-weight(alpha),

where alpha is in row j's support and beta is any padded pair, holds only for i=j and beta=alpha. This is exactly the condition for no unwanted contribution at a selected output. It also implies distinct reversed D exponents: a collision between `(j,alpha)` and `(k,gamma)` would be detected at output j using beta=alpha.

The newly frozen layout has W=179, Hmax=5775, 136 distinct D exponents, and 22 row targets. The independent checker reconstructs the shifted parent and checks 1,579,776 all-pair/output conditions, with no contamination. Its last row is the negative of original row 9, whose shifted constant is +8; hence D's leading coefficient is +16. The earlier constant +1 statement applies to the historical/uniform row order only. Both positive constants are sufficient for the positivity and nonzero-origin source arguments.

Receipts: `SUPPORT_OVERLAP_INDEPENDENT.json`; replay: `python3 -O check_support_independent.py PACKAGE_DIRECTORY`. The checker imports only Python's standard library, not the author construction helper.

## 6. Primary Sun source and its scope

I independently retrieved the primary paper `https://arxiv.org/html/2609.01594v2`, Zhi-Wei Sun, *Ten unknowns for Hilbert's tenth problem over the integers*, version 2, 2 September 2026. Theorem 1.1 represents any r.e. subset of N by a polynomial with ten unrestricted integer witnesses. The source is a preprint; it is not formalized by the repository's current Lean tree.

For homogeneous divisibility combination, Lemma 2.6 requires S!=0; at S=0 its polynomial equals T^(2^k). Any specialized finalizer must separately rule out that degenerate boundary. For all references in the user-facing report, use the primary paper URL and the exact pinned repository paths, not this audit's retrieval metadata.

## 7. Optional native coefficient direction (not a completed result)

Package44 retains dedicated occupied bits for all four edge labels. It appears possible to replace each original label by a nonzero code: there are 250 horizontal labels and 439 vertical labels, so widths 8 and 9 suffice. Equal opposite edge codes still force equal labels. If one neighboring cell were empty, its copied edge vector would be zero, contradicting the occupied cell's nonzero code. Hence occupancy propagates without separate high bits.

Keeping the three anchor bits gives 37 aggregate payload bits and support size 982. Ordering edge codes by their weighted frequency, with frequent labels given the largest nonzero codes, reduces the aggregate complement coefficient sum. A preliminary exact calculation gives a conservative carry threshold fitting b=65 rather than 67; with the same L=8807 this would give d=572455 rather than 590069. This is only a candidate until the changed finite geometry, population padding, and prime controller are completed. Do not include it as a delivered coefficient improvement without those certificates.
