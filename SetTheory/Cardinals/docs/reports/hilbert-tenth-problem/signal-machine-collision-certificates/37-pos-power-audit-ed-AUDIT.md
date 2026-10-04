# Independent audit: exact interpolation degree

Date: 2026-10-04 UTC

## Verdict

**PASS on the mathematical claims, with one nonblocking scope clarification.** The exact-degree theorem, both leading-coefficient formulas and their signs, the entire top homogeneous part of the six-square polynomial, the horizon-zero exception, the native-gap degree corollary, and the support ceiling are justified for their stated scopes. This conclusion comes from a fresh derivation of the proof, supported by independently authored exact-integer computations, rather than assuming the author's or parent's assessment.

Audited candidate: `/workspace/shared/interpolation-exact-degree-20261004`.

- `PROOF.md`: SHA-256 `7088b697d9b6887c29c35c179f19bf0a2effd6fc3abdea7db64fe9a770f4bdcb`
- `MANIFEST.json`: SHA-256 `fed0313f8f623cce051ceba49cd39cc6f739f3a75053189218c6139a5f4a9715`

The complete candidate proof was read. Its literal residuals, support classification and optional composition were cross-checked against the retained three-witness proof. This audit establishes the new degree assertions; it does not purport to re-prove the imported Pell theorem, physical semantics or the entire earlier halting construction.

## 1. Interpolation and symmetry

Put N=K² and c=(N−1)!. The cleared Lagrange weight at node i is

    w_i = (−1)^(N−i) binom(N−1,i−1).

Multiplication by the product of z−h for h≠i gives value c at i and zero at every other node. Thus the integer polynomials in the retained construction are exactly cU and cV. Scaling by positive c does not change a nonzero polynomial's degree.

Writing i=(u−1)K+v with 1≤u,v≤K gives N+1−i=(K−u)K+(K+1−v). Hence u_(N+1−i)=K+1−u_i. Interpolation uniqueness proves U(N+1−z)=K+1−U(z). The centered polynomial is odd; when K is odd and K≥3, the allowed degree N−1 is positive and even, so its coefficient vanishes and deg U≤N−2.

**Editorial clarification:** candidate Section 2 says only “If K is odd” at this step. It should say “If K is odd and K≥3.” Read literally at K=1, the stated degree bound would be false because U=1. The main interpolation theorem is already scoped to K≥2, and the candidate separately handles K=1 correctly. This is a local qualification, not a failure of any claimed exact-degree result; the source was left unchanged.

For K≥2, z+K−KU(z) has degree at most N−1 and the prescribed V-values. Therefore V=z+K−KU identically. Once deg U≥2, V has the same degree and leading coefficient −K times that of U. The K=1 exception is essential and correctly separated: both interpolants are the constant 1, and the displayed linear identity is not an identity of those constants.

## 2. Boundary coefficients

For q≥1, expansion of the qth forward difference of the step values, followed by the binomial-tail identity, yields

    Δ^q u_1 = Σ_(h=1)^(K−1) (−1)^(q−hK) binom(q−1,hK−1),

provided every boundary hK≤q. The constant sequence contributes zero. The identity follows directly by subtracting adjacent Pascal terms; its lower index hK is correct because u_(k+1) jumps precisely at k=hK.

For even K, q=N−1 is odd and all hK are even. The difference is a strictly negative sum of positive binomial coefficients. Since q! times the degree-q coefficient equals this difference, the degree is N−1 and

    a_K = −Σ_h binom(N−2,hK−1).

For odd K≥3, q=N−2 is odd and the boundaries still fit because K²−K≤K²−2. Symmetry already supplies the needed degree bound. The difference is

    S_K = Σ_h (−1)^(h+1) binom(K²−3,hK−1),

and the cleared coefficient is cS_K/q!=(N−1)S_K. No missing factorial, off-by-one node, or parity error occurs.

## 3. Odd-K nonvanishing, independently checked

Let n=K²−3. Averaging powers over the K roots of r^K=−1 annihilates all exponents not divisible by K, and sends r^(hK) to (−1)^h. Applying this to r(1+r)^n gives −S_K. The only contributing h are 1,…,K−1; the real root −1 contributes zero since n>0.

The remaining roots pair as exp(±2iθ_l), where θ_l=(2l+1)π/(2K) for 0≤l≤(K−3)/2. The positive-angle term has real part

    2^n cos(θ_l)^n cos((K²−1)θ_l).

The phase sign is exactly

    cos((K²−1)θ_l) = (−1)^((K−1)/2+l) sin(θ_l),

because K is odd. Including both conjugates and the minus sign from −S_K yields

    S_K = (−1)^((K+1)/2) (2^(n+1)/K)
          Σ_l (−1)^l sin(θ_l) cos(θ_l)^n.

For f(θ)=sin θ cos^n θ, its derivative has the sign of 1−n tan²θ. Since n≥(2/3)K² and

    1/√n ≤ √(3/2)/K < 3/(2K) < π/(2K) = θ_0 < tan θ_0,

all sampled angles lie strictly in its decreasing region. Each f(θ_l)>0, so pairing consecutive terms makes the alternating sum strictly positive. For K=3 there is just one positive term, which is covered explicitly. Consequently S_K has sign (−1)^((K+1)/2), is never zero, and deg U=N−2.

Together with the even case, the minimum degree for K≥2 is 3. This validates the earlier use of the V identity. The argument is an all-K proof using elementary identities and calculus; numerical trigonometry is neither needed nor used.

## 4. Six-square polynomial and the T correspondence

For K≥2 let d be the proven interpolation degree and a=a_K. In joint total degree in A,B,j,r,s, the only degree-2d term of R_A is −a²j^(2d): the competing A U₀ term has degree d+1<2d. The analogous term of R_B is −K²a²j^(2d). Squaring produces the combined term

    (1+K⁴)a⁴j^(4d).

The other four squares have degrees at most 2N, 2d, 2d and 2N. The strict gap 4d−2N is 2N−4>0 for even K≥2 and 2N−8>0 for odd K≥3. Thus there are no other terms of total degree 4d; the stated positive coefficient cannot cancel. This reasoning covers every acceptance subset, including empty and full sets.

At K=1, the classification products vanish and the polynomial reduces to (j−1)²+(A−r)²+(B−s)²+H_S², with H_S either 1 or j−1. Both cases have degree 2. With K=T+1 this proves degree 2 at T=0, 4(T+1)²−4 for positive odd T, and 4(T+1)²−8 for positive even T.

## 5. Support and native-gap consequences

The support types are disjoint. Their respective ceilings are 4d+1 pure-j powers; 2(2d+1) powers multiplied by A² or B²; 2(3d+1) multiplied by A or B; 2(d+1) multiplied by r or s; and four monomials r²,s²,Ar,Bs. Their sum is 16d+11. The inequality 2N<4d places both root-product squares in the pure-j allowance. This is a ceiling, not an all-K exact support claim.

In the retained native-gap composition, each E_13 has top term −w⁴g², hence its square contributes w⁸g⁴ with coefficient 1. Every other POWER residual has degree at most four and the gap residuals have degree two. The two modules use distinct internal leaves absent from P. Therefore the composed degree is max(12,deg P). At T=1 the degrees tie at 12, but the module terms remain distinct from j^12; at T=0 the degree is 12; for every T≥1 it equals the degree of P. No number-theoretic correctness theorem is needed for this literal degree calculation.

## 6. Independent executable evidence

`independent_check.py` was freshly written, displayed and fully inspected before execution. It is standalone Python 3 using only the standard library and exact integers. It does not read or import candidate code. It reconstructs interpolants using synthetic division of the complete node product and scaled Lagrange summation, independently of the candidate's difference/Newton implementation. Its separate large-range check obtains the highest two Lagrange coefficients directly from elementary symmetric coefficients of the basis products.

Results: **PASS**.

- K=1,…,101: direct leading-coefficient checks, odd leading cancellation, the two boundary formulas, signs, and the exact root-filter constant coefficient in the quotient by x^K+1
- K=1,…,10: complete U₀,V₀ reconstruction, all 385 node pairs, reflection and the applicable U/V identity
- K=1,…,8: 565 complete five-variable SOS expansions, including every acceptance subset for K=1,2,3 (2+16+512 cases), and seven explicitly recorded subsets for each K=4,…,8
- Each nontrivial expansion: entire top homogeneous part, joint degree, support ceiling and every allowed monomial type
- All 15 positive-adapted POWER residual degrees: 4,4,4,2,2,3,2,2,1,1,1,1,6,1,2; complete module-sum degree 12 and its unique top monomial

Sample cleared leading coefficients at K=2,3,4,5 are −2, 72, −4160 and −4125000. Finite computation supports the proof; it does not establish its universal quantifier. The evidence contains full reconstructed interpolation coefficients and a deterministic hash for each expanded SOS polynomial.

No author script, upstream implementation, Lean, counter-machine interpreter, physical simulator, floating-point trig routine, or network lookup was executed.

## 7. Integrity and reproduction

All 17 entries of the candidate's manifest match their recorded sizes and hashes, with complete coverage of the candidate files other than the manifest itself. All eight retained source pins match both their copies and recorded origins; the extra inert source hash also matches.

The complete candidate and original three-witness source trees were inventoried before and after this audit: **33 files and 7 directories, exactly unchanged in path, bytes, SHA-256, permission mode and nanosecond mtime**. The audit files are in a separate sibling directory. Access times are outside the promised preservation scope.

Standalone algebra reproduction, from this audit directory:

    python3 independent_check.py --output independent_results.reproduced.json
    cmp independent_results.json independent_results.reproduced.json

Source checks, when the recorded source paths are available:

    python3 verify_sources.py ../interpolation-exact-degree-20261004
    python3 inventory.py ../interpolation-exact-degree-20261004 \
      ../three-witness-bounded-halting-20261004 \
      --output sources_rechecked.json --compare sources_before.json

`MANIFEST.json` in this audit directory supplies exact hashes for all delivered audit files except itself. It is separate from the candidate manifest. No source report is edited or renumbered, and no novelty, minimality or fixed-polynomial unbounded-halting claim is added.
