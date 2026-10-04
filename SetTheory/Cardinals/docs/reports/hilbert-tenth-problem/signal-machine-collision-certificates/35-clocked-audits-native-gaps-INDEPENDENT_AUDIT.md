# Independent audit: native-gap bounded-halting continuation

4 October 2026. **Verdict: accepted as stated, within its explicit theorem dependencies and scope. No mathematical correction is required.**

This audit reconstructs the arithmetic composition independently. It does not certify a new Lean build, rerun the author's checker, simulate physical signals, run a counter-machine interpreter, or claim a new universality or minimality result. The accepted predicate is **encoded-input, bounded-instruction-horizon halting** on three positive integer physical gaps.

## 1. Exact subject and source binding

The audited candidate is `native-gap-halting-continuation-20261004`, with these immutable pins:

- `PROOF.md`: `8cc5911e528d0555ee89fe63f0e30b8a3eac4a32e3e4237ee9b00a38107a7d1b`
- `MANIFEST.json`: `224da321a9eb86b8a296948d6429ea164b245975fd4a4edab7b361b471c6c382`
- retained Pell source: `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`
- Pell Git blob SHA-1, independently recomputed using the Git object header: `6ede8ed67569fc1ddf2b4c09f0feb30ca42fca7e`

All fourteen manifest-listed files, plus the manifest itself, were checked against their recorded bytes and hashes. The complete file set agrees with the manifest. All eight retained dependency copies were also compared byte-for-byte against the origin paths in `SOURCE_PINS.json`; all match. The source files were read as inert text/bytes/JSON only. No candidate or upstream program was imported or executed.

The two theorem statements actually retained are at lines 760–766 and 860–864 of `dependencies/pell-source.lean`: `Pell.matiyasevic` and `Pell.eq_pow_of_pell`. The retained source attributes them to mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, `Mathlib/NumberTheory/PellMatiyasevic.lean`. This audit binds to the retained bytes and checks the adapter against the actual statements and their surrounding constructive proof, rather than to a remembered theorem formulation. The primary-source location is:

https://github.com/leanprover-community/mathlib4/blob/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean

The proof, adapters, complete author checker, and relevant retained physical/trace/POWER expositions were inspected inertly. The arithmetic reconstruction below does not inherit the author's finite-check results as proof.

## 2. The full POWER adapter, in both directions

One module has index C>0 and output o>0. It has thirteen directly positive leaves, including o; two positive leaves whose values plus one are alpha,beta; and eleven natural aliases, each represented by a positive leaf minus one. Thus there are **26 positive leaves including the output**, not 26 auxiliary leaves in addition to the output. C is the already counted initial shifted-counter witness, and is not a new module leaf.

The fifteen residuals in Section 3 were matched individually against the source statements. The mapping is:

| Source theorem data | Candidate expression or constraint |
|---|---|
| Matiyasevic a,k,x,y | alpha,C,x_p,y_p |
| a>1 and k<=y | alpha=alpha_++1; residual 9 and natural d_yk |
| three Pell equalities | residuals 1,2,3 |
| b>1 and b congruent 1 modulo 4y | beta=beta_++1; residual 4 |
| b congruent a modulo u | residual 5 |
| v>0 and y² divides v | positive v_p,q_v; residual 6 |
| s congruent x modulo u | residual 7 |
| t congruent k modulo 4y | residual 8 |
| power theorem n,k,m | 2,C,2o |
| n<=w and k<=w | residuals 10,11 and natural slacks |
| m<t, with source modulus t | candidate M=2o+J_p, J_p>0 |
| auxiliary Pell equality | residual 13, with source z=candidate g |
| 2an=t+n²+1 | 4alpha=M+5, residual 14 |
| final Pell congruence | residual 15 modulo M |

### 2.1 Soundness

Residuals 1–9 supply the nonzero-index existential branch of the exact `matiyasevic` statement. Its special pair `(x,y)=(1,0)` is unnecessary and impossible here because y_p>=C>=1. Natural quotient pairs encode each congruence with both possible signs. Residual 4 supplies beta congruent to 1; residual 6 supplies the divisibility and positive v required by the theorem. Thus x_p,y_p are exactly the Pell pair for parameter alpha at index C.

Residuals 10–12 imply w>=2, w>=C, M>2o. Residual 13 gives

    alpha² = 1 + ((w+1)²-1)w²g².

Since w>=2 and g>=1, its right-hand side is greater than w². With alpha positive this proves alpha>w>=2. In particular alpha-2 is nonnegative. Residual 14 is precisely the modulus identity for source base n=2, including the constant **5**, and residual 15 is the required congruence. All hypotheses of the positive-base, positive-index branch of `eq_pow_of_pell` are met. Its conclusion is 2^C=2o. Since C>=1, cancellation of 2 gives o=2^(C-1).

### 2.2 Completeness and positive leaves

Assume o=2^(C-1). Then 2^C=2o with positive base and positive index, so the forward direction of `eq_pow_of_pell` supplies w,alpha,M,g and alpha>1, with the strict modulus inequality and all auxiliary conditions. Its other disjuncts have C=0 or base 0 and cannot be the applicable branch.

The auxiliary g cannot be zero: the auxiliary Pell equality would then force alpha²=1, contrary to alpha>1. Hence its requested positive domain is legitimate. The theorem supplies w>=2, w>=C and M>2o, giving nonnegative d_wb,d_wk and positive J_p.

Take the Pell pair x_p,y_p at index C and apply the forward direction of `matiyasevic`. Because C>=1 and C<=y_p, y_p is positive; consequently the theorem's zero-pair alternative is excluded and it supplies the existential nonzero branch. The three Pell equations imply x_p,u_p,s_p are at least 1. The source explicitly supplies v_p>0. As y_p² divides v_p and y_p>0, the quotient q_v is positive. Since beta>1 and beta is congruent to 1 modulo positive 4y_p, `(beta-1)/(4y_p)` is a positive integer q_b. Finally t_p cannot be zero: t_p congruent to C modulo 4y_p, together with 1<=C<=y_p<4y_p, would otherwise make a positive C smaller than its positive divisor. Therefore t_p is positive too.

Every signed congruence quotient admits a difference of two natural integers. Each natural slack or quotient is then represented by a positive leaf one larger. Alpha and beta have positive predecessor leaves because they exceed 1. This constructs all 25 positive auxiliary leaves beyond o, including when C=1 and the semantic exponent is zero.

### 2.3 Truncated subtraction is handled exactly

For natural U,V, `U-V=1` using truncated natural subtraction is equivalent to the ordinary equality U=V+1: if U<=V the truncated result is zero, and otherwise subtraction is ordinary. This applies to the outer subtraction in every source Pell identity. The inner alpha²-1, beta²-1 and (w+1)²-1 are nonnegative by the already established domains. The potentially more delicate alpha-2 in the power congruence is ordinary subtraction because residual 13 forces alpha>w>=2. No negative term has been silently substituted into a natural-subtraction expression.

### 2.4 Concrete full fixtures

The displayed exponent-zero fixture is correct. In particular w=2,g=3 gives `(w+1)²-1=8` and `(wg)²=36`, hence alpha²-1=288 and alpha=17. The values M=63, x_p=s_p=17, y_p=t_p=1, u_p=577, v_p=34 satisfy all fifteen residuals with the stated quotient leaves and positive adapters.

The independent checker additionally constructs and evaluates a complete nonzero-exponent fixture at **C=2,o=2**. It uses alpha=17,w=2,g=3,M=63, x_p=577,y_p=34, a separately evaluated Pell pair at index 136 for u_p,v_p, and a CRT choice beta congruent to 17 modulo u_p and to 1 modulo 136. It then evaluates the beta-Pell pair at index 2 and constructs all quotient pairs explicitly. The largest leaf has 1397 bits; all 26 leaves are positive and all fifteen residuals vanish. Exact integer values are retained in `run-1/power-fixtures.json`.

These examples support the translation but do not replace the all-exponent source-theorem argument.

## 3. Native-gap decoding and uniqueness of the decoded values

The external inputs are precisely positive g1,g2,g3. D=g1+g2+g3, x=g1 and y=g1+g2 are expressions, not additional inputs or witnesses. Put A,B>0, with the two paid modules enforcing P=2^(A-1), Q=2^(B-1).

The two gap residuals imply `(20g1-D)P=2D` and `(20g3-D)Q=2D`. Since D,P,Q>0, both denominators 20g1-D and 20g3-D are positive. Dividing by positive quantities gives exactly

    g1/D = 1/20 + 1/(10P),
    g3/D = 1/20 + 1/(10Q).

This is the intended encoding with a=A-1,b=B-1. Conversely the encoding supplies these two equations, unique shifted counters, and unique power outputs. There is no denominator-clearing extraneous branch and no missing sign witness.

The input alone forces P=2D/(20g1-D), Q=2D/(20g3-D). Distinct nonnegative exponents give distinct powers of two. Thus A,B,P,Q are unique at an accepted input. Both endpoint proportions lie in (1/20,3/20], and the middle proportion in [7/10,9/10), so the physical section order is automatic.

An unencoded positive triple has no witness even if some other physical behavior on that triple reaches a halt label. The theorem does not concern unrestricted physical halting on all positive triples. The ordinary decoder's denominator, divisibility and power-of-two tests agree with this scope; they do not stand in for the paid module equations.

## 4. Bounded trace and first-halt semantics

For fixed finite deterministic program data, each nonhalting instruction has the specified one increment edge or two distinct conditional edges, and there is exactly one halt loop. State codes are distinct fixed integers; they need not be positive. E=I+2C+1 and Z=C in the instruction-count notation.

The selector equation `(w-1)(w-2)=0` over positive integers makes s=w-1 equal 0 or 1. The one-hot equation selects exactly one edge at each time. Consequently control equations compare actual source/target codes, rather than sums that could disguise several simultaneously selected edges. Counter update residuals enforce the stated displacement. A selected zero edge forces the tested shifted counter to be 1. A selected decrement from 1 would make the next shifted counter zero, forbidden by the witness domain. Thus the omitted explicit positive-decrement guard is validly supplied by next-counter positivity.

Starting from A,B and q0, deterministic instruction semantics fix the selected edge and next counters at every step. Induction fixes all selectors, including inactive w=1 selectors. Reaching H permits only the unique absorbing edge. A computation halting by T extends uniquely with virtual halt padding, and any satisfying T-step trace gives precisely this padded computation. Trace witnesses are unique for fixed decoded A,B.

For T>=1 the extra residual `sum_{t<T} s_(t,h)` excludes early halt exactly because all its summands are nonnegative. If first arrival is k<=T, it equals T-k, so the exact-halt polynomial adds `(T-k)²`. The final control residual still forces arrival by T. In particular an initially halted run is accepted by the by-horizon version and rejected by the exact version whenever T>0.

At T=0 there are no trace witnesses and exactly one **residual slot**, the constant q0-H. By-horizon and exact-horizon coincide. If q0=H that residual polynomial is identically zero; it is nevertheless an entry of the specified list. The native-gap and POWER residuals remain present, so the composed polynomial retains degree 12 and enforces the encoded subset even at T=0.

## 5. Literal ledger, joint degree and witness fibers

For T>=1 the trace residual counts are TE selectors, T one-hot residuals, 2T updates, TZ zero guards and T+1 control residuals. Their total is T(E+Z+4)+1, with T(E+2) positive witnesses. The single constant slot at T=0 continues the same arithmetic count formula.

The composition adds A,B and two independent 26-leaf modules. Therefore:

    positive witnesses = 2 + 26 + 26 + T(E+2) = T(E+2)+54,
    residual slots = 2 + 15 + 15 + T(E+Z+4)+1 = T(E+Z+4)+33,
    total variables, including three inputs = T(E+2)+57.

The first-halt-exactly-T version adds one residual when T>=1, no witness, and no degree. Equivalently the first two counts are T(I+2C+3)+54 and T(I+3C+5)+33. Counting A,B,P,Q plus two further sets of 26 leaves would incorrectly count P,Q twice.

These are counts of the **literal displayed residual list**, not independent constraints or distinct nonzero polynomials. Identically zero control residuals in a halt-only zero-coded graph remain slots. The independent receipts explicitly distinguish slot counts from counts of nonzero residual polynomials.

After every positive shift, the module residual degree list is exactly

    4,4,4,2,2,3,2,2,1,1,1,1,6,1,2.

Gap residuals have degree 2, and trace residuals have degree at most 2. In each module residual 13 has leading homogeneous part -w^4 g^2. All other residuals have degree at most 4. Hence the complete sum of squares has degree-twelve homogeneous part exactly

    w_left^8 g_left^4 + w_right^8 g_right^4.

Both monomials have coefficient 1 and use separate module leaves. The joint total degree is exactly 12, even at T=0 and for a logically unsatisfiable nonhalt initial state. Degree is measured before using constraints to eliminate any independent leaf; it is not a restricted-variety or witness-eliminated degree claim.

Uniqueness does **not** extend to full witnesses. Increasing both natural aliases alpha_1 and alpha_2 in either module by an arbitrary common nonnegative integer preserves every residual and preserves positivity of their adapter leaves. They occur only through their difference in residual 5. This gives infinitely many distinct full witness tuples for every accepted input. The theorem correctly claims unique decoded counters and unique trace projection, with infinite nonempty complete fibers.

## 6. Primitive scale and exact bit lengths

For m=max(a,b), the candidate integers U=2^m+2^(m-a+1), W=2^m+2^(m-b+1), V=20·2^m-U-W have the required normalized coordinates. U,W<=3·2^m implies V>=14·2^m>0.

The small cases are separate and correct: (a,b)=(0,0) gives (3,14,3), gcd 1; (1,1) gives (4,32,4), gcd 4; mixed m=1 gives (6,30,4) or (4,30,6), gcd 2.

For m>=2 at least one endpoint equals 2^m+2, whose 2-adic valuation is exactly 1. Both endpoints and V are even, so the common gcd has exactly one factor of 2. It divides the total 20·2^m; hence its only possible odd factor is a single 5. Since U=2^(m-a)(2^a+2), divisibility by 5 occurs precisely when a≡3 modulo 4; the same holds for W. V adds no extra condition because the total is divisible by 5. Therefore the gcd is 10 if a≡b≡3 modulo 4, and 2 otherwise. This proves every line of the claimed gcd formula.

The primitive triple is (U/c,V/c,W/c), with D_min=20·2^m/c. Any other integer realization of this same normalized shape is a rational scalar multiple of this triple. A Bézout combination of its three primitive coordinates equals 1; applying it to the multiple proves that scalar is an integer. Thus the primitive realization is the exact minimum total scale for this encoding, and all realizations are its unique positive integer multiples.

The exact scale bit lengths follow directly: 5 at (0,0), 4 at (1,1), 5 in mixed m=1, then m+2 for c=10 and m+4 for c=2. In the c=10 case D_min=2^(m+1) exactly; in the c=2 case it is 10·2^m. The middle gap is largest and at least 7D_min/10>D_min/2, yielding the claimed one-bit bracket between its bit length and that of D_min.

Accordingly the primitive gap bit height is m+O(1), whereas its numerical height is proportional to 2^m. In terms of the bit length ell of m>=1, the bit height is Theta(2^ell). This is a cost of this particular coordinate encoding; it is not a lower bound for other encodings. The proof gives no bound on Pell witness height.

The decoder bound P,Q<=2D follows from the positive integral denominators, and gives a,b<=floor(log2(2D)). Ordinary arithmetic therefore decodes in time polynomial in the input gap bit length. This does not imply an efficient expansion of a gap encoding from binary counters or an unbounded-halting algorithm.

## 7. Physical transport and evidence boundaries

The retained physical proof uses x=g1 and y=D-g3, so its initialization is exactly the one enforced here. It proves the fixed-program, five-live-signal instruction-section interface and preserves D. Its transition bounds are strictly D<elapsed<10D and at most 32 binary collisions per simulated nonhalting instruction. Thus for a first halt after k>0 native instructions the physical prefix has kD<elapsed<10kD and at most 32k collisions. At k=0 the initial section already has the designated label.

This is transport through the retained physical theorem, not a new simulation audit or a fixed-collision-horizon equivalence. The virtual arithmetic halt loop does not require post-halt physical instructions. The audit does not extend the retained compiler claim to arbitrary unencoded gaps.

T indexes a growing-arity family. It is not a quantified extra input of a fixed-arity unbounded-halting polynomial. No operation count, optimized circuit, minimum witness count, unique complete witness, new five-signal universality, or new formal-verification claim follows from this audit.

## 8. Independent checker and replay

`check_native_gap.py` was newly authored, inspected in full, then run. It imports only Python standard-library modules. It reads candidate files inertly and constructs a separate sparse integer-polynomial representation; it does not import the author checker or any scientific source. Its fresh finite graph differs from the author's graph. Literal trace paths and counter rows are declared fixtures; no machine interpreter discovers or executes a path. The small Pell recurrences only construct two concrete integer module assignments.

The passing run records:

- 30 full symbolic constructions: three graphs, five horizons including T=0, and both halt variants
- exact leaf, slot, degree, leading homogeneous-part and support checks on every construction
- 27 complete native assignments, including rejected T=0/exact-halt variants; four initial counter pairs cover both A and B conditional outcomes
- all fifteen residuals for complete positive POWER fixtures at semantic exponents 0 and 1, plus the literal displayed exponent-zero fixture
- scaled inputs, changed-counter and changed-gap rejection, and a large common quotient-pair shift preserving a full accepted assignment
- 16,641 counter pairs a,b in [0,128], with primitive scales independently cross-checked against the lcm of reduced rational coordinate denominators
- 49,923 scaled exact decodings
- all 142,880 positive gap triples with D<=96, of which exactly 43 are encoded, compared against an independently generated rational-shape list
- unchanged source content, modes, sizes and modification times before and after execution

Replay requires Python 3.9 or newer and a fresh external output directory:

    python check_native_gap.py --source PATH_TO_CANDIDATE --output NEW_EXTERNAL_DIRECTORY

The checker refuses an existing output directory or one nested inside the frozen source, and refuses source symlinks. It writes only two receipts in the supplied output directory, after the checks pass. Its source binding rejects a modified proof or manifest before arithmetic evidence is accepted.

A relocated replay was performed from `/tmp`, with a copied checker and independently located candidate. It passed with the same fixtures and mathematical evidence. The raw receipts differed only in filesystem-specific directory sizes (4096 versus 200/60); all file bytes, file metadata, mathematical outcomes and fixture values agreed. The recorded `PORTABILITY.json` comparison excludes only those directory-size fields. This distinction does not weaken the within-run source immutability check.

The finite evidence is supporting evidence for the conventional arguments in Sections 2–7. It is not an exhaustive proof over all powers, programs, horizons or native triples, and it does not replace the pinned all-exponent Pell theorems.

## 9. Release qualifications

The candidate is mathematically acceptable without edits. Any later manuscript should preserve the following qualifications prominently:

1. Encoded positive triples and bounded instruction horizon are part of the predicate
2. P,Q are included in the 26 leaves of their modules
3. Residual counts are literal slots, including zero constants
4. All 30 module residuals are paid; the theorem is not a black-box exponential predicate
5. Unique decoded counters/trace coexist with infinite complete witness fibers
6. Exact degree is jointly in the three inputs and declared independent positive leaves
7. All-exponent completeness uses the retained theorem pair, without a claimed fresh Lean build
8. Physical transport is prefix-to-first-halt transport through the retained compiler theorem

This audit changes no candidate file and assigns no report number.
