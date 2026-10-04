# Independent audit of the two- and one-witness bounded-table compilers

4 October 2026. Source packet: `two-witness-tensor-compiler-20261004`.

## Verdict

**PASS. No mathematical correction is required for either native compiler, its stated cost bounds, the fixed-table zero-versus-one auxiliary-variable classification, or the displayed paid compositions.** The native claims are elementary and self-contained. The POWER compositions remain conditional on the specifically pinned constructive Pell theorem pair, exactly as the source says. They have infinite complete fibers, despite unique decoded/native projections.

This is an independent static mathematical and exact-algebra audit. It does not execute or formally rebuild the Pell source, an author checker, any earlier scientific code, any counter interpreter, any physical simulator, or any saved schedule. It does not certify new physical results, novelty, global arity or degree optimality, or an unbounded-horizon fixed polynomial.

## 1. Audited object and evidence boundary

The exact source manifest is SHA-256

`b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82`.

The exact delivered source archive is SHA-256

`897a7bee8ab8f0758b8c3b035b7be0d06d9521a9769919266ab30057a6702c8c`.

Individual main text pins are:

- `PROOF.md`: `d966f922c023190fa71c96e88a2a3c62168dc87f1a08d1fc14b1ae28a3aa422f`
- `ONE_WITNESS.md`: `9135dd0e829adb3190e99ed1b62f8d419f9f7540cfd92a1acd1635726fa7172c`
- `REVIEW_TWO_WITNESS.md`: `832e12eccb873e9c4cb998fa452038c0b8dbfa37f6eedeb9b7bc98e86b9a27b4`
- `PRESERVATION.md`: `2923d263ac08eda9b85854d2f994e7efbeee3dff36fbcbead372f8dfb19ab37b`

The complete two native proofs, main README, scope review, preservation explanation, source pins, retained POWER12 proof and audit, retained predecessor proof and audit, and retained mathematical dependency proofs were read as inert text. The duplicated `compressed_PROOF.md` is byte-identical to the predecessor proof. The relevant actual Pell recurrence, theorem statements, and constructive branches were inspected in the retained source. The source's 358-line checker was read but never imported or executed; its checks were not treated as the proof.

The fresh `check_independent.py` was authored from the displayed mathematics and inspected before execution. Its interpolation construction uses synthetic division of the full node polynomial, followed by exact integer denominator clearing. It does not call the author's binomial-basis implementation. Its sparse-polynomial arithmetic, finite-table evaluation, closure logic, and instrumented arithmetic circuits are independently written. Ordinary input JSON, gzip coefficient lists, and ZIP members are data only. All 31 source manifest payloads match their pins, the file-set is exact, and all 32 archived files match the source directory. All 13 dependency copies match their pins and their local original bytes.

Finite evidence corroborates the formulae. It cannot establish arbitrary-program table correctness, universal positive-integer equivalence by enumeration, or all-exponent POWER correctness. Those statements are established by the mathematical arguments below and the explicitly scoped imported theorems.

## 2. Clipping: input size, loops, and first-arrival semantics

Each permitted native transition changes each counter by at most one and decreases it by at most one. Clip an initial natural counter at T. Inductively, along a common branch history, an initially smaller counter is equal in both runs. An initially large counter has representative value at least T−t after t transitions, and its original counterpart differs by the fixed nonnegative initial offset. At every instruction entry t<T, the lower bound is strictly positive. Thus every tested counter has the same zero/nonzero status, the same branch is taken, and the induction proceeds through transition T.

This proves equality of the control-state prefix, not equality of final counters. At time T the representative can first become zero without damaging any prior test. Loops make no difference to induction. An absorbing halt convention preserves the first arrival within the prefix, so both by-T and first-exactly-T tables are justified.

The positive-coordinate threshold is K=T+1 because A=a+1. There are K² clipped representatives, and evaluating each for at most T native transitions gives the stated K²T transition ceiling. Each representative counter starts at most T and receives at most T increments, so is at most 2T. This is a construction-cost statement, not an executed interpreter, free advice, or a claim of efficient computation in log T.

At T=0 only whether the initial state is H matters. Initially halted programs give the full by-T table at every horizon and an empty exact-T table when T>0. Both native constructions cover these cases.

## 3. Two-witness compiler: cleared interpolation and recovered domains

For the K nodes 1,…,K, let R(z)=∏(z−h). Synthetic division gives R(z)/(z−i), whose value at i is

`(-1)^(K−i)(i−1)!(K−i)!`.

Multiplying by c=(K−1)! divided by that value gives the source's integer signed-binomial basis ℓ_i. Thus ℓ_i(j)=cδ_ij. Summing the basis gives c as a polynomial: the difference has degree at most K−1 and K roots. Tensoring gives F_S(i,j)=0 for accepted nodes and c² for rejected nodes. In particular F_full=0 and F_empty=c² identically. There is no input-dependent denominator.

Set u=A−r+1 and v=B−s+1. These are expressions, not assumed-positive variables. If the five-square polynomial vanishes, each residual is zero over the reals. The range products first force u,v∈{1,…,K}. The positive-integer domain then gives A−u=r−1≥0. If u<K, the classification factor forces r−1=0, hence A=u. If u=K, it instead gives A≥K. These are exactly u=min(A,K), and similarly for v.

Therefore every zero uniquely fixes

`r=A−min(A,K)+1`, `s=B−min(B,K)+1`.

These are positive and at most A,B respectively. The table residual now enforces acceptance. Conversely this pair satisfies the range and classification residuals and satisfies the table residual precisely for an accepted clipped input. Thus the full native witness fiber is a singleton or empty.

Strict positivity is essential. At K=3, S={(3,1)}, A=2, B=1, r=0, s=1, all five residuals vanish but the actual clipped input (2,1) is rejected. This is outside the stipulated domain, not a counterexample to the theorem. The fresh checker verifies it as a domain challenge.

At T=0 the separately defined five slots are A−r, B−s, 0, 0, ε. Their sum of squares has degree two and six nonzero monomials for ε=0, seven for ε=1. The accepted pair is (A,B). The source properly identifies this as a separate definition: keeping the generic K=1 classification factors would produce redundant degree-four terms.

## 4. Exact degree, fixed program, and the exact-T distinction

For K≥2 the range residuals have degree K and both classification residuals degree two. If f(x,y) is nonzero, replacing (x,y) by (A−r+1,B−s+1) preserves its degree: its leading homogeneous part remains nonzero because setting r=s=0 recovers f_top(A,B). Finally, a sum of squares of real homogeneous polynomials can vanish identically only if every summand is zero. Consequently the exact degree is

`max(2K,4,2 deg F_S)`, with deg 0=−∞.

Since F_S has degree at most 2K−2, this is at most 4K−4=4T. Empty and full tables have degree 2K. At K=2 every table has degree four.

For S={(1,1)}, F_S=c²−ℓ_1(x)ℓ_1(y). The coefficient of x^(K−1)y^(K−1) is −1, giving exact degree 2K−2 for F_S and 4K−4 for the final polynomial. The stated two-test program accepts precisely native (0,0), first on transition two, and sends every positive tested branch to an increment-only sink. It realizes this same table at every by-horizon T≥2, so one fixed program attains the displayed upper bound for all such T.

Its first-exactly-T table is singleton at T=2 and empty for T>2. The source does not falsely extend the fixed-program statement to those exact-time tables. For each fixed T≥2, a chain of T−2 increments after the successful second test delays the first halt to T; that program depends on T. The distinction between fixed-program by-horizon sharpness and horizon-dependent exact-time sharpness is mathematically correct.

These are exact degrees of the displayed presentation, not lower bounds against other polynomials computing the same predicate.

## 5. Two-witness coefficients, support, storage, and arithmetic operations

After substitution, `u−i=A−r−(i−1)` has coefficient 1-norm i+1. With B_K=(K+1)! and L_K=2^(K−1)B_K, submultiplicativity and the binomial sum give

- range norms at most B_K
- summed basis norms at most L_K in each coordinate
- tensor residual norm at most L_K²
- each classification residual norm at most 2(K+1)

Squaring and adding yields the stated uniform norm bound

`Q_K=L_K^4+2B_K²+8(K+1)²`.

Each coefficient magnitude is at most Q_K and hence needs no more than ceil(log₂(Q_K+1)) magnitude bits, plus a sign bit. This is O(K log(K+1)). The factorial bounds are valid after the affine substitutions, rather than only before them.

F_S(u,v)² has degree at most 2K−2 in each variable pair (A,r) and (B,s). The Cartesian product of these pair-support sets has `binom(2K,2)²=K²(2K−1)²` possible monomials. The other squares use only one pair and have degree at most 2K. The additional two pair-degree layers contribute at most

`2[binom(2K+2,2)−binom(2K,2)]=8K+2`.

Thus the stated O(K⁴) support ceiling holds. Four binary exponents per monomial require O(log K) bits each, giving O(K⁵ log(K+1)) expanded bits with the coefficient bound. The predecessor instead has O(K²) narrow-support monomials and O(K⁴ log(K+1)) expanded bits. The source correctly calls this a tradeoff between upper bounds, not an instancewise ordering or a tight lower-bound comparison.

The direct shared circuit ledger is independently realizable and instrumented. Form u,v using four additions/subtractions; form all 2K differences; form the two shifted slacks. A basis uses K−2 products of factors and one signed-coefficient multiplication, so all bases cost 2K(K−1) multiplications. Ranges add 2(K−1), classifications add two, m rejected cell products add m, and the five squares add five. Summing the m terms and the five squares gives exactly the advertised upper-bound ledger:

`M=2K²+m+5`, `A=2K+10+max(m−1,0)`.

Hence M+A≤4K²+2K+14. This ledger charges multiplication by signed binomial constants and retains zero slots; further simplification may save gates. Constants, table bits, and circuit indices give O(K² log(K+1)) factored storage.

The coefficient-generation O(K⁵) arithmetic bound is also valid. Construct K univariate bases in O(K³); form and square the bivariate interpolation coefficients in O(K⁴); substitute one coordinate in O(K⁴), producing O(K³) entries; substitute the second in O(K⁵). The requisite affine powers have smaller construction cost. Product/triangle bounds, allowing an extra exponential-in-K affine-expansion factor, keep intermediate coefficient bits O(K log(K+1)). Integer-operation counts do not imply unit-cost bit complexity.

## 6. One-witness disjoint-cell product and exact degree

For K≥2, p_K(x)=∏_(h=1)^(K−1)(x−h)² is nonnegative on all real inputs. On positive integers it vanishes exactly below K and is strictly positive at or above K. Each displayed cell factor is therefore a nonnegative sum of squares. Its positive zeros force the fixed coordinates to their cell values and force w to the product of p_K over exactly its tail coordinates (or w=1 with no tails).

If w>0, a zero tail-product target cannot masquerade as a tail value. Thus the factors' positive zero sets are disjoint in the input coordinates and cover exactly their respective clipped cells. A zero of the product selects an accepted cell; a fixed accepted input selects only one such cell and hence exactly one positive w. This establishes the claimed full native uniqueness, even when many table cells are accepted.

At K=3, accepting only (1,3) would spuriously accept A=1,B=2 with w=0, demonstrating again why the positive witness hypothesis matters. Empty S gives the constant polynomial 1 and no solutions. At K=1 the explicit choices (w−1)² and 1 have degrees two and zero; the rejected case has an unused formal witness, as disclosed.

An interior factor has degree two, an edge factor 4T, and the corner factor 8T. Each is a nonzero polynomial. Degree is additive in the integral domain R[A,B,w], so

`D_S=2n_I+4Tn_E+8Tn_C`.

The bounds n_I≤T², n_E≤2T and n_C≤1 give D_S≤10T²+8T. The full table attains this degree for this product, although its predicate also has constant representations. For nonempty S the coefficient of w^(2|S|) is one, so the formal witness genuinely occurs.

The product-of-SOS distinction is real. Distributing the product yields exactly `3^(n_I)2^(n_E)` literal square slots, with empty product 1². It does not make Q_S one residual square. Already a single interior factor cannot be a polynomial square: any square of its total degree two would be the square of a linear form; its nonzero A² and B² coefficients would force a nonzero AB coefficient, contrary to the factor. Squaring Q_S preserves zeros but doubles its degree contribution. The fresh checker separately verifies all distributive SOS identities for K≤2.

## 7. One-witness size and gate bounds

All roots of p_K are positive with multiplicities, so its coefficients alternate in sign and its coefficient norm is exactly `(K!)²=P_K`. The displayed factor norms are bounded by

`M_I=2K²+4`, `M_E=K²+(1+P_K)²`, `M_C=(1+P_K²)²`.

The product norm is at most `C_S=M_I^n_I M_E^n_E M_C^n_C`. Counting cell types, rather than charging the largest factor to every cell, gives coefficient magnitude bits O(K² log(K+1)). With three variables and degree O(K²), `binom(D_S+3,3)=O(K⁶)` is a support ceiling. Three exponent fields and signed coefficients give O(K⁸ log(K+1)) expanded bits. Squaring the block replaces D_S by 2D_S and C_S by C_S² without changing these asymptotic orders.

For the factored circuit, form 2T coordinate differences, their 2T squares, and the two products using 2(T−1) further multiplications. Preparing the four w-related squares adds four subtractions and five multiplications (including p_K(A)p_K(B)). Each interior cell adds two additions, each edge one, and the final product N−1 multiplications when N≥1. Therefore

`M≤4T+3+max(N−1,0)`, `A≤2T+4+2n_I+n_E`.

For N≥1 their sum is at most 3T²+10T+7. Empty S can simply return 1 without arithmetic; squaring the final block adds one multiplication. The independent instrumented circuit attains these exact unsimplified counts. Table generation and integer sizes remain separately paid costs.

For expansion, interior factors have at most seven monomials; edge factors at most 6T+5 (the constant terms overlap); the corner at most `1+(2T+1)²+(4T+1)²`. Summing these factor-support bounds over all cells is O(K²). Every partial product has at most O(K⁶) monomials. Iterated ordinary convolution therefore needs O(K⁸) coefficient operations; intermediate coefficient bits obey the same product-of-norms bound. A naive self-convolution costs O(K¹²). No hidden bit-complexity or optimality assertion occurs.

## 8. Exact zero-versus-one classification

The necessity argument is valid even for real-coefficient, non-SOS polynomials. If an accepted cell has a set J of tail coordinates, fix all other coordinates at the cell values. The restricted polynomial vanishes on an infinite Cartesian grid in J. A univariate polynomial has finitely many roots unless zero; induction on |J|, treating it as a polynomial in the last coordinate, proves that the restriction is identically zero. It consequently vanishes on the entire coordinate flat, including every positive value below K in the former tail coordinates.

Thus any zero-witness representation forces acceptance of every joint replacement of tail coordinates. Replacing only fixed coordinates is neither required nor justified. In particular an accepted all-tail corner forces the full table. The criterion is a coordinate-flat closure condition, not the usual order-ideal condition on all coordinates.

For sufficiency, for each accepted cell a form the sum of squared deviations in its non-tail coordinates, and multiply those factors. At positive inputs a factor vanishes exactly on that cell's coordinate flat. Closure ensures this flat has no rejected clipped point. Conversely the factor belonging to an accepted input's own clipped cell vanishes. The empty table gives 1; an accepted all-tail cell gives a zero factor and, by closure, the full table. Without an all-tail cell and with nonempty S, all factors have exact degree two, so the displayed degree is 2|S|, not claimed minimal.

This proves zero auxiliaries suffice exactly under closure. If closure fails, the infinite-grid argument excludes every zero-auxiliary polynomial equality, while the previous construction supplies one positive auxiliary. Therefore the minimum is exactly zero or one in the stated class: a fixed finite clipping table, positive integer inputs, one polynomial equality, table-dependent integer coefficients, and no degree restriction. At K=1 both tables have minimum zero. This does not classify the POWER composition or any unrestricted MRDP/global universal-polynomial problem.

The independent enumeration checks every one of 530 two-dimensional tables through K=3. The closure counts are 2, 6 and 48. Every closed-table construction is evaluated on finite positive grids; every nonclosed table has an explicit finite closure obstruction. These checks support the all-input argument rather than replacing its infinite-grid step.

## 9. d-input extension

For fixed d≥1, the same factor fixes non-tail coordinates and uses `w−∏_(tail coordinates) p_K(X_l)` for its final residual. Strict positivity and nonnegative p_K again identify precisely the tail coordinates, with one unique positive witness. The degree is two for a cell with no tails, and 4Tt for a cell with t≥1 tails. There are T^d no-tail cells. Counting the total tail-coordinate occurrences over all K^d cells gives dK^(d−1), so

`deg Q_S≤2T^d+4dT(T+1)^(d−1)`.

For fixed dimension this is O(T^d), and the dense support bound in d+1 variables is `binom(deg Q_S+d+1,d+1)`. No dimension-uniform polynomial-size conclusion is asserted. The same infinite-grid necessity and coordinate-flat product sufficiency prove the zero-versus-one classification in every fixed finite dimension.

The fresh checks cover 20 d-dimensional full-table degree ledgers (d=1,…,5; K=2,…,5), all 260 one- and three-dimensional K=2 tables for closure, and 13,848 associated positive assignments. The general argument does not depend on these dimension samples.

## 10. Conditional POWER boundary and paid compositions

The retained number-theoretic source is mathlib4 commit

`ac77769fabe23cb237559e7f56578dbead91499f`,

`Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256

`993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`.

The imported statements are `Pell.matiyasevic` at lines 760–766 and `Pell.eq_pow_of_pell` at lines 860–864; the recurrence and constructive positive branches agree with the retained derivation. This audit checks the mathematical mapping to that local source. It does not independently rebuild Lean or authenticate the remote repository history.

The module has six direct positive leaves and six positive adapters for natural aliases, output included once. Aliases themselves are adapter minus one. The source correctly does not treat a natural alias such as d_yC as a separately positive leaf. The five base-two residuals in both new proofs agree with the retained POWER12 formula.

From H5=0, α=Z/4>0 has integer square, so coprime numerator/denominator divisibility gives an integer α. Its norm and ω≥2,g≥1 give α>ω≥2. Next H2=0 makes u=U/(4q_α) have integer square, hence integral, with |u|≥α. Since β=α+q_αu>0 and q_α is a positive integer, a negative u would force β≤0. Therefore u>0. The restored x and s are positive by their definitions, α>2, M>2o and natural quotients; dividing the residuals by nonzero squares restores all Pell norms and the eliminated congruences.

The first theorem at positive index C identifies x,y with the C-th Pell pair; y≥C excludes its zero branch. The second theorem with base two, exponent C and target 2o uses M>2o, ω≥2,C, and the auxiliary norm, giving 2^C=2o. Ordinary α−2 agrees with the theorem's natural subtraction; every norm equation with natural subtraction equal to one is equivalent to the displayed ordinary equality.

The older congruence quotients really can be chosen natural. The norms and v=y²q_v≥y give u≥α and u≥x. If z=r+Lq with z,L>0, 0<r≤L and integral q, then q≤−1 would give z≤0; hence q≥0. Apply this to β modulo u with residue α, to s modulo u with residue x, and to t modulo 4y with residue C≤y. For the final quotient, put h=x−y(α−2). The identity x²−[y(α−2)]²=(4α−5)y²+1>0 proves h>0. Its congruence h≡2o modulo M, together with 0<2o<M, makes (h−2o)/M natural by the same lemma. This recovers every one-sided quotient without assuming it from a fixture.

Completeness imports the constructive theorem pair, uses those nonnegative quotient recoveries, and uses the strict progression β_k=β_0+4yu k, k≥1. Integer-polynomial Pell coordinates preserve the two required congruences. The positive-residue lemma gives nonnegative sigma and tau quotients. The progression makes q_α positive and makes retained q_b strictly increase, proving infinitely many full module witnesses at every accepted index/output, including C=1. The independent algebra checks the entire stated exponent-zero family as five polynomial identities in a free parameter, not only at sampled values.

For positive gaps, D>0 and each equation `(20g_i−D)o=2D` forces its denominator positive and uniquely fixes o=2D/(20g_i−D). POWER then uniquely fixes A,B by injectivity of powers of two. Unencoded positive triples have no solution; no promise that arbitrary inputs were pre-encoded is needed.

The two-witness ledger is 2 counters + 24 full module leaves + 2 native witnesses = 28 witnesses, plus 3 inputs = 31 variables. The literal slots are 2 gap + 10 POWER + 5 compiler = 17. The native projection (A,B,p,q,r,s) is unique, while full fibers are infinite by varying either module progression.

The one-witness ledger is 2+24+1=27 witnesses and 30 total variables. E has exactly 12 square slots. E+Q_S is 12 squares plus one nonnegative product-of-SOS block; its distributed presentation has 12+3^(n_I)2^(n_E) slots for K≥2. E+Q_S² has exactly 13 literal residual-square slots. At K=1 the two choices Q_S themselves are squares, and zero/unused formal slots or variables remain counted. Projection (A,B,p,q,w) is unique; full fibers remain infinite.

The independent expansion gives POWER residual degrees 4,10,10,1,6 and exact SOS degree 20 with 12,858 monomials. The coefficient of `J^4 q_alpha^4 d_yC_plus^8 q_v^4` is one; q_v occurs only in H2. This monomial is absent from the other module, the gaps, and the native block. The two-witness composition consequently has exact degree max(20,deg P), including degree 20 at T=0.

For the one-witness presentation, a globally nonnegative polynomial has a nonnegative leading homogeneous part: evaluate at λX and divide by λ^D as λ→+∞. Nonzero such top parts cannot cancel in a sum. Thus the exact degrees are max(20,D_S) for E+Q_S and max(20,2D_S) for E+Q_S², with the stated ceilings and T=0 exception. The fixed-size decoding block adds only T-independent support, so no dense 30-variable estimate is needed for the native asymptotic support/storage bounds.

## 11. Independent completed evidence and reproducibility

`evidence/final/results.json` and `evidence/final.log` are the authoritative completed fresh run. It includes:

- 285 interpolation-node identities and nine basis-sum identities
- 48 complete two-witness expansions with degree, norm and refined support-shape checks
- 46 instrumented two-witness gate instances
- 530 small tables; 13,074 canonical two-witness assignments and 6,688 literal positive witness-box assignments, with direct-versus-expanded equality in the latter
- 69,942 one-witness candidate assignments; 28 complete one-witness expansions; 26 instrumented gate instances; 112 direct-versus-expanded assignments including negative/zero coordinates; 18 distributed-SOS identities
- All 530 two-dimensional closure tests; 1,314 zero-witness polynomial assignments; 474 nonclosed-table obstructions
- 20 d-input degree ledgers, 260 additional dimension/closure tables, 13,848 d-input assignments
- One complete POWER expansion and its coefficient-one degree certificate; five symbolic family identities; five complete positive fixtures and 60 rejected single-leaf positive perturbations
- Ten complete two-witness compositions, five one-witness product compositions, and four fully expanded squared-block compositions
- 45 complete gap assignments and 45 changed-gap rejections
- Complete coefficient equality with all 14 retained source coefficient records: 12 native residual/polynomial records and two full 31-variable compositions
- All source manifest, archive, and dependency-pin checks

One additional squared-block case, the full K=3 one-witness table, is recorded by its exact native degree and the proved degree-doubling argument; it is deliberately not described as a fully expanded square. The fully expanded unsquared block has degree 56. The checker makes that distinction explicitly instead of implying the large self-convolution was performed.

The initial independent run also passed; its authentic `run1.log` and evidence are retained. Additional direct-versus-expanded, distributed-SOS and literal-ledger assertions were then added, inspected, and run successfully. These are extensions of this audit's own checker, not reruns of an author or prior-packet script.

For a portable algebra replay, use Python 3.9 or newer and a new output path:

    python3 check_independent.py --source /path/to/two-witness-tensor-compiler-20261004 --out /path/to/new-evidence

Optionally add `--archive /path/to/two-witness-tensor-compiler-20261004.zip` to check the exact archive. The algebra checker uses no original absolute paths; only the supplied source packet is needed, and its scripts are never executed. It refuses an output directory inside the source and refuses to reuse an existing output directory. No third-party package or network is needed. Selected complete independent coefficient lists and all native residuals are in `expansions.json.gz`, with explicit variable order and decimal integer coefficients.

The separate `preserve.py` and `check_provenance.py` intentionally verify the original local historical paths and release metadata. They are not advertised as source-free portable algebra interfaces. The audit README records the performed relocated replay and the final integrity checks.

## 12. Preservation and historical Report68 qualification

A fresh current inventory was captured before the new algebra work. It includes 1,141 entries across the exact source packet, its archive, the retained compiler/POWER packets and audits, and Reports66–68. It records bytes/hashes, sizes, file/directory modes and nanosecond mtimes; access times are excluded because reading may change them. The matching final inventory establishes this audit's preservation interval. No input was written, chmodded, retimestamped, restored to an obsolete snapshot, or used as an output destination.

The source's older 912-entry before/after records have 17 differences, all within the concurrently sealed Report68 tree. The audit independently recomputed that historical diff and matched the source's retained change list. That does not prove whole-interval Report68 preservation, and neither the source nor this audit claims it. It does not excuse changes outside that tree.

The source's separate post-seal before/after inventories agree in all 332 entries and still match current files. Fresh checks verify Report68's final manifest SHA-256

`2a95eb0ba3f1f7bd2e53de2b0595d5b2439de11bc3c6b5925f15d63046f98493`

and final receipt SHA-256

`d1781eeedb6f253e5e3a90551bd878c202d60ed4266619c7ceb61545d259240e`.

All 299 manifest payload files and 31 manifest directories match their hashes where applicable, sizes, modes and nanosecond mtimes. No scientific Report68 checker or release tool was executed. `evidence/provenance.json` records this read-only verification.

## 13. Scope conclusions

The results are finite-table compiler families indexed by T. Their tables, degrees, coefficients and construction costs vary with T. They do not produce one fixed unbounded-halting polynomial by treating T as a free input. Native witness uniqueness is genuine and global on positive integers; the POWER composition explicitly loses finite-foldness. The zero-versus-one classification is a precise and proved fixed-table statement, without a degree restriction; it is not global witness minimality for arithmetic representations. Support, coefficient and storage ceilings are upper bounds, not tightness claims. No novelty, priority, physical-trajectory extension, minimal degree, or efficient Pell-witness claim follows or is needed.
