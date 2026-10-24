# Independent mathematical audit: a common power frame and source majorant

Scope: this is an ordinary mathematical audit of proposed changes to the Shared_Certificates positive-power compiler. It is not yet a check of a new literal implementation. The previous exponentiation graph is an imported Pell–Matiyasevich characterization; its exact positive-domain conditions are retained or explicitly restored below.

## 1. One frame for any finite family of positive powers

Let the finite requested positive power equations be `m_i = n_i^k_i`, with all `n_i,k_i >= 1`. Introduce

`W = 2 + sum_i (n_i + k_i + m_i)`

(or sum over the finite distinct requests). In an existential polynomial system it is harmless that W is defined from the power outputs: completeness first selects the true finite source values, and then selects auxiliary arithmetic witnesses. A topological order on the *original semantic expression DAG* suffices; the complete polynomial equations need not form an acyclic assignment graph.

Retain one natural A, one natural z0, Z=z0+1, and the single Pell equation

`A^2 - W(W+2) (W Z)^2 = 1`.

Since W>=2 and Z>=1, this forces `A^2 > W^4`, hence `A>W^2` on the nonnegative domain. Every n_i,k_i,m_i is at most W. Set `T_i=2 A n_i - n_i^2 -1`. Because `1<=n_i<=W<A`, the quadratic `2An-n^2-1` increases on the permitted integer interval, so

`T_i >= 2A-2 > 2W^2-2 >= W >= m_i`.

Thus the original local conditions `A>=2`, `W>=n_i`, `W>=k_i`, and `T_i>m_i` hold. Their former natural slack coordinates can be restored as `A-2`, `W-n_i`, `W-k_i`, and `T_i-m_i-1`. The original last norm is exactly the one displayed, since `(W+1)^2-1=W(W+2)`. No deleted comparison is taken on faith.

For completeness, take any genuine finite source witness and compute all true positive powers in source dependency order. This fixes the n_i,k_i,m_i and hence W. Write Pell polynomials

`chi_b(j)+psi_b(j)sqrt(b^2-1) = (b+sqrt(b^2-1))^j`.

For b=W+1 the recurrence modulo W gives `psi_b(j) = j (mod W)` (initial values 0,1; recurrence coefficient 2b=2 mod W). Therefore

`A=chi_(W+1)(W)`, `Z=psi_(W+1)(W)/W`

are positive integers satisfying the common norm. In fact any sufficiently large positive index divisible by W supplies another common frame. This proves common existence directly; it is stronger and more precise than saying independent frames are each cofinal.

## 2. Share the entire index certificate by exponent

With common A, every request with exponent k has the same canonical

`X=chi_A(k)`, `Y=psi_A(k)`.

The index certification subgraph depends only on A,k, not the base n or output m. It comprises `Y>=k`, two norms at A, one norm at B, `B=1 mod4Y`, positive divisibility `Y^2|V`, and the two index congruences `B=A modU`, `S=X modU`, `R=k mod4Y`. Thus one copy per *syntactically identical* exponent is automatically safe, provided all those constraints remain.

There is a simultaneous explicit canonical choice for each such certificate. Choose an even positive matrix period modulo Y^2 for the Pell matrix at A, and let U,V be its corresponding Pell coordinates. Then `Y^2|V`, `V>0`, and U is odd. The norm implies gcd(U,Y)=1, so gcd(U,4Y)=1. CRT gives an arbitrarily large integer `B>=2` with

`B=A modU`, `B=1 mod4Y`.

Set `S=chi_B(k)` and `R=psi_B(k)`. Polynomial recurrences give `S=X modU` and `R=k mod4Y`. Every original index-certificate constraint follows, including natural quotient/slack restorations. The finite matrix period exists since the Pell companion matrix has determinant1 and hence is invertible modulo Y^2.

The *base-specific* power congruence remains separate:

`X + nY = AY + m (mod T)`, `T=2An-n^2-1`.

For genuine powers it follows by substituting `sqrt(A^2-1)=A-n` modulo T, since `(A-n)^2 = A^2-1 mod T`. This gives `X-(A-n)Y=n^k mod T` by the binomial/Pell polynomial identity. The inherited power theorem then supplies soundness, with every original bound restored as in §1.

## 3. A cheap exact upper bound on a nonnegative arithmetic source

Suppose the split source is represented by a finite arithmetic DAG using nonnegative constants, variables, addition and multiplication, with variable x_j bounded by a nonnegative B_j. Let

`R = 2 + sum(distinct bound expressions B_j)`.

Then R>=2 and x_j<=R. Assign an exponent to every node:

- variable: 1;
- constant c>=2: `ceil(log_2 c)`; constant1 may use0 or the looser1; constant0 is identically0 and may use0;
- addition: `max(e_left,e_right)+1`;
- multiplication: `e_left+e_right`.

Induction proves the value at each node is at most R raised to its assigned fixed exponent. At an addition use `u+v <= 2R^max <= R^(max+1)`; at a multiplication multiply the two inductive inequalities. Constants obey `c<=2^e<=R^e`. The exponent is a fixed natural numeral computed once from the finite source graph, not a quantified or variable exponent.

If the two split outputs are E,F, use `D=max(e_E,e_F)+1`; then `E+F<=R^D`. Consequently `H=R^D+t+V+1` exceeds E+F and also dominates t and V, as required by the source's factorial/CRT bound. `R^D` is emitted by ordinary repeated squaring with fixed D, costing O(log D) multiplication nodes. No exponentiation predicate or variable exponent remains here.

The source contains signed residuals but is evaluated by nonnegative *pairs* `(E,F)`. Apply the induction to the pair DAG actually emitted. Applying it to the unsplit signed polynomial requires an absolute-value triangle-bound DAG; using cancellation as though all coefficients were positive would be invalid. The root's proposed pair/absolute-circuit bound avoids this issue.

## 4. Optional shared binomial radix audit

For a finite family of binomial calls `choose(n_i,k_i)`, choose a common N>=all n_i and set `q=2^N+1`. Every binomial coefficient in `(1+q)^n_i` is at most `2^n_i<=2^N<q`, so its base-q digits have no carries. The existing quotient/remainder formula selecting digit k_i therefore computes `choose(n_i,k_i)` exactly, including k_i>n_i, where it returns0. The common radix does not change the digit proof.

As with W, N may be chosen from the intended semantic inputs after computing the genuine source values. Any syntactic cycle introduced in auxiliary equations is not a logical obstacle; the completeness proof must state this order. A shared radix permits a common power `q^k` for repeated k and often a common exponent certificate for calls with identical n.

## Literal audit obligations

1. Require every called n_i,k_i to be positive on the full source zero set before omitting zero-case branches.
2. Prove global W definition contains every live requested base, exponent and output (or prove a larger explicit bound).
3. Retain Z>0; without it A=1 would satisfy the common norm and invalidate the inequalities.
4. Keep each base-specific T definition and modular power congruence.
5. Share index gadgets only when their exponent atoms are identical or backed by retained equality rows.
6. Confirm all source pairs and range bounds are included in the majorant; check the computed D by independent traversal.
7. Any elimination of a natural coordinate whose restoring affine expression has negative coefficients needs a separate nonnegativity proof. Ordinary nonnegative-affine elimination is already safe.

## 5. Eleven local coordinates and no independent uniform bound

The direct Horn source originally has13 local coordinates
`p,q,v,a,b,c,d,S,Sp,u,r,vq,rp`. Choose one outer m bounding all seven labels/schema coordinates, rather than only p,q,v. The strengthened bounded source is equiconsistent: every finite Horn proof has a finite maximum for all its local witnesses, and enlarging m is permitted before choosing the carrier `M=(m+1)^t` and accumulator states.

Use local bounds m for the seven labels/schema coordinates, y for S and Sp, and x for u and vq. Delete r,rp and their two remainder-inequality rows. Retain

`x = S + (1+(i+1)y)u`,
`x = Sp + (1+(i+2)y)vq`.

Require y>=M+1 globally, for example by retaining the original first endpoint remainder constraint, or substituting `y=M+1+y0` with y0 natural. Since y>=1 and `S,Sp<=y`, both displayed S coordinates are strict remainders modulo their respective divisors. Consecutive local rows therefore identify the same middle state: a natural number has a unique remainder in `[0,D-1]`. The initial endpoint state M+1 and final state1 likewise lie below their divisors, so the complete accumulator chain is recovered exactly. The source proof then applies.

The original local r,rp can be restored as `D_i-S-1` and `D_(i+1)-Sp-1`, nonnegative by the strict bounds. Local quotients automatically satisfy `u,vq<=x` because they are nonnegative and their respective divisors are at least1. Hence the new quotient bounds do not exclude any canonical witness.

For completeness choose in order:

1. A finite Horn certificate and t>=1, then m>=all seven coordinates.
2. M and its finite canonical accumulator sequence S_0,...,S_t.
3. A y at least every S_i and M+1 and divisible by t!.
4. CRT x satisfying `x=S_i mod(1+(i+1)y)` for 0<=i<=t, enlarged by a product of moduli until x>=all S_i.
5. Nonnegative quotients `(x-S_i)/(1+(i+1)y)`, all at most x.

The divisors are pairwise coprime: a common prime of `1+(i+1)y` and `1+(j+1)y` divides `(j-i)y`, is coprime to y, and would divide j-i<=t. Since t! divides y, that is impossible. Divisibility t!|y is a completeness choice, not needed for soundness of a supplied certificate.

Thus the separate outer slack U and V=m+U are unnecessary. A majorant radix `R=2+t+x+y+m+M0` bounds every source input in this reduced representation. The exact source DAG must now exclude the two deleted remainder rows.

## 6. Deferred global binomial scale: why the apparent cycle is harmless

Allocate each binomial output while constructing the original semantic macro DAG. After all binomial requests `(n_i,k_i)` have been recorded, put

`N = sum(distinct n_i)`, `q=2^N+1`.

All current calls have positive n_i, so N>0; alternatively1+sum works uniformly. Materialize every digit certificate with this same q, using numerator `(q+1)^n_i` and denominator `q^k_i`.

Soundness proceeds in this exact order:

1. The shared power theorem is a relation theorem valid on arbitrary positive n,k. It does not require the inputs already to have their intended source interpretations. Hence all power graphs are correct simultaneously, including the q graph.
2. Pure nonnegative arithmetic gives N>=n_i and hence q>2^n_i for every call.
3. Every binomial digit graph is now correct simultaneously. Its inputs may include other binomial outputs, but correctness is a pointwise relation and does not assume their semantics.
4. Only now use induction on the original semantic macro DAG to conclude that factorials, moduli products, and the outer source have their intended values.

Completeness uses the reverse constructive order: evaluate the genuine semantic DAG first (including true binomial outputs), form N and q, choose the new internal binomial powers, form W from every final requested positive power, choose the common Pell frame, and finally choose all index and congruence witnesses. This is a concrete simultaneous solution; no fixed-point theorem or circular existence assumption is involved.

## 7. Audit of the emitted synchronized implementation

Inspected source pins and reproducible finite receipts are recorded in `SYNCHRONIZED_CHECK.json` and `SYNCHRONIZED_CHECK_OPTIMIZED.json`. The authored checker `verify_synchronized.py` independently expands every residual square and verifies the following scope:

- The new C222 source function's AST is exactly the inherited function after deleting only the two beta-remainder inequality rows; all formula constructors, Horn branches, accumulator rows and beta quotient rows are unchanged.
- The413-node exponent certificate validates D=6,893,169. The emitted H is exactly R^D by an independent symbolic power traversal. This certificate already bounds E+F+t+x+y+m+1, so H> E+F and all bounds without an extra additive tail.
- The actual global frame bounds precisely every input and output atom of all27 positive power calls. It has22 distinct exponent certificates and10 distinct base moduli.
- All27 exponents are syntactically positive even if power/binomial/factorial output variables initially have lower bound0. Every base is forced positive independently by `2An=T+n^2+1` with T natural. Hence power soundness does not presuppose factorial soundness.
- There are14 binomial calls, all with positive upper and lower arguments, sharing the certified common radix.
- The literal intermediate polynomial has1151 nonnegative variables,987 quadratic rows,6088 monomials, maximum absolute coefficient63,908,952, and exact degree4. Every variable occurs. A later contraction, if performed, needs its own certificate.

The implementation also orients congruence quotients nonnegatively. This restriction is complete for the index gadget by choosing CRT B>=A. Then `chi_B(k)>=chi_A(k)` and `psi_B(k)>=k`, so every one of its three congruence quotients is nonnegative.

For the base-specific power congruence the exact identity is

`chi_A(k) - (A-n)psi_A(k) - n^k`
` = (2An-n^2-1) * sum_(j=0)^(k-2) n^j psi_A(k-1-j)`.

The sum is empty when k=1 and otherwise has nonnegative terms for A>=2,n>=1. It proves the stronger quotient orientation; a bare modular congruence would not suffice. One proof uses the recurrence on both sides: the quotient h_k has h_0=h_1=0, h_2=1, and `h_(k+1)=2A h_k-h_(k-1)+n^(k-1)`. The convolution sum satisfies this recurrence.

The only remaining use of two-sided congruences is allowed a common natural offset: for finitely many integer quotients d_i choose one L>=max(0,-d_i), then represent all d_i=(L+d_i)-L. This simultaneous selection is exact and does not assume common quotient signs.

The checker additionally runs52 shared-binomial digit fixtures and504 exact Pell-quotient identity fixtures. These are supplementary transcription regressions; the universal arguments in this note and the retained exponentiation theorem are the mathematical justification.
