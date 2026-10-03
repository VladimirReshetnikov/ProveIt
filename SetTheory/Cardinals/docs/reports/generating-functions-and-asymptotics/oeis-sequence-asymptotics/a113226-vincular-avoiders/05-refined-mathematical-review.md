# Fresh independent mathematical audit of the A113226 refinement

Date: 2 October 2026 (UTC)

## Conclusion and scope

No material mathematical defect or unresolved proof gap was found in the compact-positive-parameter and compact-interior-density results stated in the two sources below. The precise local-count expansion, the record-to-cycle bijection, and the conditional Poisson correction are supported by the reviewed arguments and by the new independent computations described here.

This is an adversarial mathematical review with finite exact and symbolic checks. It is not formal verification, conventional peer review, an exhaustive novelty search, or a certification of explicit finite-n remainder constants. It does not extend the results to either endpoint-density regime or to exponentially complete expansions. The original A113226 report was neither changed nor re-audited for this addendum.

Reviewed files, SHA-256:

- `refined-proof.md`: `c35244db96cba1e42f338ba86203c8cbf4c6637013b2c1bd1133036ba1613ed8`
- `a113226-refined-addendum.tex`: `b4fe1a9e86c48cd1534f0da53915adf98022345857d625b7a65e36871f71b252`

The TeX's mathematical statements agree with the expanded companion proof. Source hashes were checked again after completing the audit. This review is independent of the earlier `root-refinement-review.md`; that earlier review is historical supporting material, not the source of the present conclusion.

## 1. Exact marking and the record-to-cycle map

The interpretation of the nonempty strict downsets, the successive difference blocks E_i, and the final isolated block agrees with BCK Proposition 7, checked directly in the [primary paper](https://arxiv.org/html/2311.08023v2).

The record construction is sound. Between successive strict records of max E_i, the first E maximum dominates every later E label in the segment, and every M label exceeds that first maximum. Hence the segment is a separated cycle. The inverse's rotation is unique because labels are distinct, and sorting cycles by their largest E label ensures every M label exceeds all earlier E labels. No record is created inside a normalized cycle, so the two constructions are inverse, including the empty and all-isolated cases.

On a component with n specified labels, the E labels must be its a smallest labels. Consequently no binomial choice of the E label set is missing. The factor m!(m−1)! correctly counts matching of the two block partitions and cyclic ordering of their matched pairs. Counts depend only on the size of a component's label set, through order-preserving standardization, so the exponential counting formula applies despite the label inequalities. The beta-integral derivation independently gives the same factor: (m!)²/m, not (m!)².

A new implementation, `fresh-independent-audit.py`, enumerates the actual strict downset of each successively added natural label. It requires all parents to have empty downset and all nonempty downsets to be pairwise comparable. These are exactly the absence of 3-chains and induced 2+2. It does not enumerate binary words and does not import the existing word, bijection, recurrence, or saddle programs.

Through n=8 it checked all 30,326 posets, with totals

1, 1, 2, 6, 23, 107, 585, 3669, 25932.

Every refined row agrees with the supplied exact data, every joint (k,j) count agrees with the binomial isolated-element identity, every cycle round trip succeeds after deliberate rotations and reorderings, and every one-cycle count agrees with the component formula. For n=8 the independently recovered row is

1, 769, 10619, 13398, 1145.

## 2. Joint analytic domain and local expansion

For real positive u, the modulus inequality is strict away from the unique point x=1/2, z=rho(u). Equality in the exponential-series triangle inequality forces positive real z; the endpoints in x give zero. On the normalized compact set away from z/rho=1, the denominator thus has a positive uniform lower bound. Continuity supplies a common open neighborhood in z/rho and complex u.

Near the pinch, formulas (5)–(6) genuinely provide a jointly analytic S and R and a single square-root factor. In particular, 1−q²=a w+O(w²), with a bounded away from zero on each relevant compact set. The apparent quotient in S is removable. The arctangent-inverse series for R converges normally after uniformly reducing the neighborhood. Branches are fixed by their positive real values, and the local representation agrees with the original integral on an open overlap. These facts justify a common normalized slit/dented domain; the argument does not incorrectly classify apparent q=−1 points as actual singularities.

A direct symbolic expansion in the new audit independently reproduces S(0)=1, R(0)=K, s1, s2, and r1, including

s1=(a²−3)/(8a), s2=(9a⁴+10a²−15)/(384a²), r1=(4−a³)/(6a).

## 3. Complex saddle circle, its residual linear phase, and connectors

The proposed circle remains in the common domain for sufficiently large n. Locally its normalized t has positive real part, uniformly for u in a sufficiently small complex neighborhood. Away from the pinch, the preceding compactness argument applies.

The approximate circle does have a nonzero derivative of the full exponent. More explicitly, with delta=n^(−1/3), its angular derivative at zero is

−i[c+g1/(2 sqrt(c))] delta^(−1)+O(1).

Multiplication by theta=delta² y gives O(delta |y|), exactly the scale used in the proof. On y=sqrt(delta) X this is O(delta^(3/2)|X|). Thus it cannot overwhelm the quadratic Gaussian loss, and it only produces the small shift accounted for by the coefficient expansion. The proof does not falsely assume the circle is the exact saddle contour.

The three noncentral regions have the claimed bounds: a quadratic loss near y=0; a fixed positive loss on epsilon≤|y|≤M, stable under small complex perturbations; and a bound of order delta^(−1)/sqrt(M) farther along the local arc, where the extraction factor has fixed radial modulus. The outer compact arc has bounded logarithm. These estimates make the omitted Gaussian-cutoff tails smaller than every algebraic order, uniformly in u.

The connector prescription is valid. At real u, a circle endpoint with theta of order c epsilon delta² and the corresponding endpoint of t=c delta²(1±i epsilon) differ only at higher order after scaling. They lie in an open strict-loss neighborhood, so a short connector is available. For complex u sufficiently close to a real base point, both endpoints and a continuous connector remain in that neighborhood, avoid zero and the branch cut, and retain fixed loss. A finite cover of the real compact parameter interval gives uniform choices. Here the central integral may first be extended to the fixed scaled endpoints by restoring the already negligible tails; those fixed-endpoint connectors need not attach directly to the shorter logarithmic cutoff.

## 4. All-orders coefficient control and the marking gap

After deformation, the exact extraction exponent is log H−(n+1)log(1−t). This gives all four lines of Q, including the separate −log(1−t) contribution; the Jacobian and complex Gaussian give the stated amplitude. The convergent local series allow arbitrary finite truncation on the logarithmic cutoff. Gaussian domination removes polynomial/logarithmic growth in the integrated remainder. Odd half-orders integrate to zero by parity, for complex c as well as real c. This supports the stated O(delta^(J+1)) remainder for every fixed J, and holomorphy plus Cauchy estimates gives parameter derivatives on a smaller neighborhood.

The global marking-phase lemma is also valid. On |z|≤rho(u), a denominator zero can only occur at the equality point of the modulus estimate, but there the product is e^(i theta), which differs from 1 when |theta|≥epsilon. The full set including x, u, theta, and z/rho is compact. Its nonzero denominator therefore persists in a uniformly larger disk. The integral and its exponential remain bounded, and Cauchy's estimate gives the asserted exponential-in-n marking gap. There is no hidden lattice-periodicity saddle.

For the second saddle, V>0 and real-on-real analyticity give the required small-theta Gaussian bound. The stretched term changes the saddle at order n^(−2/3); retaining it generates the b1 correction. The parity and Gaussian remainder argument survives the extra first-saddle amplitude expansion and its derivatives. There is no missing intermediate angular region between the complex-uniform first theorem and the global gap.

The new audit uses a direct series expansion of the exact first-saddle exponent, then an integer-partition/multinomial expansion of its exponential. It matches a1, a2, and a3 in the supplied output without importing the generator. A separately specified degree-six second-saddle exponent with the amplitude derivative term matches b1, b2, and b3 by the same independent expansion mechanism.

## 5. Conditional Poisson law, total variation, and covariance

The isolate multiplier leaves a1 unchanged, changes a2 by −(s−1)rho c, and changes d' by (s−1)rho'. Substitution into b2 and division by the s=1 expansion gives exactly formula (30). The denominator is uniformly nonzero for all sufficiently large n in the stated compact-density range.

As a separate check, the exact identity

E[J_n | K_n=k] = n A_(n−1,k)/A_(n,k)

reproduces the coefficient of n^(−2/3) without using the b_j algorithm. Along fixed k, decreasing n by one changes v by alpha/(n V)+O(n^(−2)). The stretched factor contributes rho[−c+3 alpha c'/V]. Since rho'=−rho alpha, this equals the manuscript's −[rho c+3c'rho'/V].

Uniformity and holomorphy on a fixed |s|≤R with R>1 suffice for total variation: Cauchy bounds each probability-coefficient error by C n^(−2/3) R^(−j), and summing over j is finite. This is stronger than pointwise generating-function convergence and correctly supplies the claimed rate. The same argument applies unconditionally.

Differentiating the complex-uniform tilted isolate transform gives covariance rho' evaluated at u=1, plus O(n^(−2/3)), where the prime is in log u. Its value is −1/2. Direct use of the supplied integer rows gives covariance approximately −0.47344143, −0.48252361, and −0.48862852 at n=100,200,400, respectively, consistent with the claimed error scale. These numerical observations are checks, not proofs of the bound.

## Reproduce this audit

Run `python fresh-independent-audit.py` with Python, SymPy, and mpmath. It writes only `fresh-independent-audit.json`, records the reviewed source/data hashes, and uses no release computation module. The JSON includes the exhaustive direct-poset results, both independent symbolic saddle comparisons, local singular-coefficient checks, conditional correction identity, and exact-row covariance spot checks. The full n=400 recurrence replay, PDF rebuild, and page-by-page visual QA are separate release checks and are not represented as having been independently repeated by this mathematical audit.
